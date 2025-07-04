#nullable enable
using System;
using System.Collections.Generic;
using System.CommandLine;
using System.Linq;
using System.Reactive.Subjects;
using System.Threading;
using System.Threading.Tasks;
using DafnyCore;
using DafnyCore.Options;
using DafnyDriver.Commands;
using Microsoft.Boogie;
using Microsoft.Dafny.Compilers;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Util;
using VC;
using System.IO;

namespace Microsoft.Dafny;

public static class GradualCommand {

  static GradualCommand() {
    // Note these don't need checks because they are only "dafny verify" options;
    // they can't be specified when building a doo file.
    OptionRegistry.RegisterOption(FilterSymbol, OptionScope.Cli);
    OptionRegistry.RegisterOption(FilterPosition, OptionScope.Cli);
    OptionRegistry.RegisterOption(PerformanceStatisticsOption, OptionScope.Cli);
  }

  public static readonly Option<int> PerformanceStatisticsOption = new("--performance-stats",
    "Report a summary of the verification performance. " +
    "The given argument is used to divide all the output with, which can help ignore small differences.") {
    IsHidden = true
  };
  public static readonly Option<string> FilterSymbol = new("--filter-symbol",
    @"Filter what gets verified by selecting only symbols whose fully qualified name contains the given argument, for example: ""--filter-symbol=MyNestedModule.MyFooFunction"". Place a dot at the end of the argument to indicate the symbol name must end like this, which can be useful if one symbol name is a prefix of another.");

  public static readonly Option<string> FilterPosition = new("--filter-position",
    @"Filter what gets verified based on a source location. The location is specified as a file path suffix, optionally followed by a colon and a line number or line range. For example, `dafny verify dfyconfig.toml --filter-position=source1.dfy:5-7` will only verify things that between (and including) line 5 and 7 in the file `source1.dfy`. You can also use `:5`, `:5-`, `:-5` to specify individual lines or open ranges. In combination with `--isolate-assertions`, individual assertions can be verified by filtering on the line that contains them. When processing a single file, the filename can be skipped, for example: `dafny verify MyFile.dfy --filter-position=:23`");

  public static Command Create() {
    var result = new Command("gradual", "Verify the program, if it fails convert non ghost failing assertion to runtime checks (convert them to expect statements does what is intended).");
    result.AddArgument(DafnyCommands.FilesArgument);
    foreach (var option in VerifyOptions) {
      result.AddOption(option);
    }
    DafnyNewCli.SetHandlerUsingDafnyOptionsContinuation(result, (options, _) => HandleVerification(options));
    return result;
  }

  private static IReadOnlyList<Option> VerifyOptions =>
    new Option[] {
        PerformanceStatisticsOption,
        FilterSymbol,
        FilterPosition,
        DafnyFile.DoNotVerifyDependencies
      }.Concat(DafnyCommands.VerificationOptions).
      Concat(DafnyCommands.ConsoleOutputOptions).
      Concat(DafnyCommands.ResolverOptions);


  public static async Task<int> HandleVerification(DafnyOptions options) {
    if (options.Get(CommonOptionBag.VerificationCoverageReport) != null) {
      options.TrackVerificationCoverage = true;
    }

    var compilation = CliCompilation.Create(options);
    compilation.Start();

    var resolution = await compilation.Resolution;

    if (resolution != null) {
      Subject<CanVerifyResult> verificationResults = new();
      
      ReportVerificationDiagnostics(compilation, verificationResults);
      var verifyIdentifyFailed = VerifyFailedAssertion(compilation, resolution, verificationResults);
      var verificationSummarized = ReportVerificationSummary(compilation, verificationResults);
      var proofDependenciesReported = ReportProofDependencies(compilation, resolution, verificationResults);
      var verificationResultsLogged = LogVerificationResults(compilation, resolution, verificationResults);

      // our new hook: collect & mark error locations
      //Old code
      compilation.VerifyAllLazily().ToObservable().Subscribe(verificationResults);
      await verificationSummarized;
      await verificationResultsLogged;
      await proofDependenciesReported;
      await verifyIdentifyFailed;
    }
    return await compilation.GetAndReportExitCode();
  }
  
  public static void WriteProgramToFile(Program program, string filePath) {
    using var writer = new StreamWriter(filePath);
    var printer = new Printer(writer, program.Options, PrintModes.Everything, null);
    printer.PrintProgram(program, /* showBpl */ false);
  } 
  public static async Task VerifyFailedAssertion(
    CliCompilation compilation,
    ResolutionResult resolution,
    IObservable<CanVerifyResult> verificationResults) {

    var failMethodsInfo = CollectFailures(verificationResults);
    await verificationResults.WaitForComplete();
    if (failMethodsInfo.Count == 0) {
      return;
    }
    var program = resolution.ResolvedProgram;
    Console.WriteLine($"Original Program: {resolution}");
    foreach (var methodResult in failMethodsInfo) {
      ProcessMethodFailures(methodResult);
    }
    Console.WriteLine($"Modified Program: {program}");
    WriteProgramToFile(program, "ModifiedProgram.dfy");  
    Console.WriteLine("Created new program with expect statements");
  }
  
  private static List<CanVerifyResult> CollectFailures(
    IObservable<CanVerifyResult> verificationResults) {

    var fails = new List<CanVerifyResult>();
    verificationResults.Subscribe(result => {
      foreach (var taskResult in result.Results) {
        if (taskResult.Result.Outcome == SolverOutcome.Invalid) {
          fails.Add(result);
          break; // no need to scan the rest of this result.Results
        }
      }
    });
    return fails;
  }
  
  // 2) For one Method’s failure batch, convert each counterexample and update AST.
  private static void ProcessMethodFailures(CanVerifyResult methodResult) {
      // The object 'methodResult.CanVerify' is typically some ICallable. We want the AST Method instance inside 'program'.
      if (!(methodResult.CanVerify is Method method)) {
        // If it's not a normal Method (e.g. a function or something else), bail out for now.
        return;
      }
      Console.WriteLine("Created new program with expect statements"); 
      // Now that we have the exact Method AST node, process each counterexample
      foreach (var verificationResult in methodResult.Results) {
        foreach (var counterExample in verificationResult.Result.CounterExamples) {
          // Regular Assertion working
          var originalToken = ConvertBoogieToken(counterExample.FailingAssert.tok);
          if (originalToken is SourceOrigin sourceOrig) {
            // It is a source token, probably a return on a function
            var endTok = sourceOrig.EndToken;
            LocateAndReplaceAssert(method, endTok);
          }
        }
      }
  }
  
  // 3) Turn a Boogie token to the “true” Dafny token (e.g. a SourceOrigin’s StartToken).
  private static IToken ConvertBoogieToken(IToken boogieTok) {
    return BoogieGenerator.ToDafnyToken(true, boogieTok);
  }
  
  // 4) Run the visitor, find the AssertStmt, build an ExpectStmt, and swap it in.
  private static void LocateAndReplaceAssert(Method method, IToken originalToken) {
    var visitor = new FindExpressionAndParentByTokenVisitor(originalToken);
    visitor.VisitMethod(method);

    if (visitor.MatchingStatementWithAllParent.Count == 0) {
      return;
    }

    // We only care about the first match (expr + its parent chain).
    var (generalStmt, parents) = visitor.MatchingStatementWithAllParent[0];
    AssertStmt assertStmt;
    if (generalStmt is AssertStmt) {
      assertStmt = (AssertStmt)generalStmt;
    } else {
      return;
    }

  Console.WriteLine($"Found failing location at (Line:{originalToken.line}, Col:{originalToken.col}).");
    ExpectStmt newExpect = new ExpectStmt(
      assertStmt.Origin,
      assertStmt.Expr,
      null,        // or null if you don’t want a message
      assertStmt.Attributes
    );
    // Walk parents in reverse (deepest child → root)
    foreach (var parent in parents.Reverse()) {
      // Step A: If this is the AssertStmt itself, build a new ExpectStmt placeholder
      // Step B: Once we have foundAssert, look for its enclosing BlockStmt
      if (parent is BlockStmt blockStmt) {
        var body_n = blockStmt.Body.Count;
        if (body_n > 0) {
          for (var i = body_n - 1; i >= 0; i--) {
            if (assertStmt.Equals(blockStmt.Body[i])) {
              //Insert Expect statement in the place of assert Stmt
              blockStmt.Body[i] = newExpect;
            }
          }
        } else {
          blockStmt.Body[0] = newExpect;
        }
        return;
      }
    }
  }
  
// Visitor to find expression and its parent by token
  private class FindExpressionAndParentByTokenVisitor : ASTVisitor<IASTVisitorContext> {
    public readonly List<(Statement Stmt, INode Parent)> MatchingStatement = new();
    public readonly List<(Statement Stmt, Stack<INode> Parents)> MatchingStatementWithAllParent = new();
    private readonly IToken targetToken;
    private readonly Stack<INode> parents = new();

    public FindExpressionAndParentByTokenVisitor(IToken targetToken) {
      this.targetToken = targetToken;
    }

    public override IASTVisitorContext GetContext(IASTVisitorContext context, bool inFunctionPostcondition) {
      return context;
    }
    protected override void VisitStatement(Statement stmt, IASTVisitorContext context) {

      
      if (TokensInStatement(stmt)) { // in case of asset this will be an assert
        var parent = parents.Count > 0 ? parents.Peek() : null;
        if (parent is Node node) {
          MatchingStatement.Add((stmt, node));
          var parentsCopy = new Stack<INode>(parents); 
          MatchingStatementWithAllParent.Add((stmt, parentsCopy));
        }
      }
      parents.Push(stmt);
      base.VisitStatement(stmt, context);
      parents.Pop();
    }
    private bool TokensInStatement(Statement stmt) {
      foreach (var token in stmt.CoveredTokens) {
        if (token.Equals(targetToken)) {
          return true;
        }
      }
      return false;
    }
  } 
public static async Task ReportVerificationSummary(
    CliCompilation cliCompilation,
    IObservable<CanVerifyResult> verificationResults) {
    var statistics = new VerificationStatistics();

    verificationResults.Subscribe(result => {
      foreach (var taskResult in result.Results) {
        var runResult = taskResult.Result;
        Interlocked.Add(ref statistics.TotalResourcesUsed, runResult.ResourceCount);
        lock (statistics) {
          statistics.MaxVcResourcesUsed = Math.Max(statistics.MaxVcResourcesUsed, runResult.ResourceCount);
        }

        switch (runResult.Outcome) {
          case SolverOutcome.Valid:
          case SolverOutcome.Bounded:
            Interlocked.Increment(ref statistics.VerifiedSymbols);
            Interlocked.Add(ref statistics.VerifiedAssertions, runResult.Asserts.Count);
            break;
          case SolverOutcome.Invalid:
            var total = runResult.Asserts.Count;
            var errors = runResult.CounterExamples.Count;
            Interlocked.Add(ref statistics.VerifiedAssertions, total - errors);
            Interlocked.Add(ref statistics.ErrorCount, errors);
            break;
          case SolverOutcome.TimeOut:
            Interlocked.Increment(ref statistics.TimeoutCount);
            break;
          case SolverOutcome.OutOfMemory:
            Interlocked.Increment(ref statistics.OutOfMemoryCount);
            break;
          case SolverOutcome.OutOfResource:
            Interlocked.Increment(ref statistics.OutOfResourceCount);
            break;
          case SolverOutcome.Undetermined:
            Interlocked.Increment(ref statistics.InconclusiveCount);
            break;
          default:
            throw new ArgumentOutOfRangeException();
        }
      }
    }, e => {
      Interlocked.Increment(ref statistics.SolverExceptionCount);
    });
    await verificationResults.WaitForComplete();
    await WriteTrailer(cliCompilation, statistics);
    var performanceStatisticsDivisor = cliCompilation.Options.Get(PerformanceStatisticsOption);
    if (performanceStatisticsDivisor != 0) {
      int Round(int number) {
        var numberForUpRounding = number + performanceStatisticsDivisor / 2;
        return (numberForUpRounding / performanceStatisticsDivisor) * performanceStatisticsDivisor;
      }
      var output = cliCompilation.Options.OutputWriter;
      await output.WriteLineAsync($"Total resources used is {Round(statistics.TotalResourcesUsed)}");
      await output.WriteLineAsync($"Max resources used by VC is {Round(statistics.MaxVcResourcesUsed)}");
    }
  }

  private static async Task WriteTrailer(CliCompilation cliCompilation,
    VerificationStatistics statistics) {
    if (cliCompilation.Options.Verbosity <= CoreOptions.VerbosityLevel.Quiet) {
      return;
    }

    if (!cliCompilation.DidVerification) {
      return;
    }

    var output = cliCompilation.Options.OutputWriter;

    await output.WriteLineAsync();

    if (cliCompilation.VerifiedAssertions) {
      await output.WriteAsync($"{cliCompilation.Options.DescriptiveToolName} finished with {statistics.VerifiedAssertions} assertions verified, {statistics.ErrorCount} error{Util.Plural(statistics.ErrorCount)}");
    } else {
      await output.WriteAsync($"{cliCompilation.Options.DescriptiveToolName} finished with {statistics.VerifiedSymbols} verified, {statistics.ErrorCount} error{Util.Plural(statistics.ErrorCount)}");
    };
    if (statistics.InconclusiveCount != 0) {
      await output.WriteAsync($", {statistics.InconclusiveCount} inconclusive{Util.Plural(statistics.InconclusiveCount)}");
    }

    if (statistics.TimeoutCount != 0) {
      await output.WriteAsync($", {statistics.TimeoutCount} time out{Util.Plural(statistics.TimeoutCount)}");
    }

    if (statistics.OutOfMemoryCount != 0) {
      await output.WriteAsync($", {statistics.OutOfMemoryCount} out of memory");
    }

    if (statistics.OutOfResourceCount != 0) {
      await output.WriteAsync($", {statistics.OutOfResourceCount} out of resource");
    }

    if (statistics.SolverExceptionCount != 0) {
      await output.WriteAsync($", {statistics.SolverExceptionCount} solver exceptions");
    }

    await output.WriteLineAsync();
    await output.FlushAsync();
  }

  public static void ReportVerificationDiagnostics(CliCompilation compilation, IObservable<CanVerifyResult> verificationResults) {
    verificationResults.Subscribe(result => {
      // We use an intermediate reporter so we can sort the diagnostics from all parts by token
      var batchReporter = new BatchErrorReporter(compilation.Options);
      foreach (var completed in result.Results) {
        Compilation.ReportDiagnosticsInResult(compilation.Options, result.CanVerify.FullDafnyName,
          BoogieGenerator.ToDafnyToken(true, completed.Task.Token),
          (uint)completed.Result.RunTime.TotalSeconds,
          completed.Result, batchReporter);
      }

      foreach (var diagnostic in batchReporter.AllMessages.Order()) {
        compilation.Compilation.Reporter.Message(diagnostic.Source, diagnostic.Level, diagnostic.ErrorId, diagnostic.Token,
          diagnostic.Message);
      }
    });

  }

  public static async Task LogVerificationResults(CliCompilation cliCompilation, ResolutionResult resolution,
    IObservable<CanVerifyResult> verificationResults) {
    VerificationResultLogger? verificationResultLogger = null;
    var proofDependencyManager = resolution.ResolvedProgram.ProofDependencyManager;
    try {
      verificationResultLogger = new VerificationResultLogger(cliCompilation.Options, proofDependencyManager);
    } catch (ArgumentException e) {
      cliCompilation.Compilation.Reporter.Error(MessageSource.Verifier, cliCompilation.Compilation.Project.StartingToken, e.Message);
    }

    verificationResults.Subscribe(result => verificationResultLogger?.Report(result),
      e => { },
      () => {
      });
    await verificationResults.WaitForComplete();
    if (verificationResultLogger != null) {
      await verificationResultLogger.Finish();
    }
  }

  public static async Task ReportProofDependencies(
    CliCompilation cliCompilation,
    ResolutionResult resolution,
    IObservable<CanVerifyResult> verificationResults) {
    var usedDependencies = new HashSet<TrackedNodeComponent>();
    var proofDependencyManager = resolution.ResolvedProgram.ProofDependencyManager;

    verificationResults.Subscribe(result => {
      ProofDependencyWarnings.ReportSuspiciousDependencies(cliCompilation.Options, result.Results,
        resolution.ResolvedProgram.Reporter, resolution.ResolvedProgram.ProofDependencyManager);

      foreach (var used in result.Results.SelectMany(part => part.Result.CoveredElements)) {
        usedDependencies.Add(used);
      }
    }, e => { }, () => { });
    await verificationResults.WaitForComplete();
    var coverageReportDir = cliCompilation.Options.Get(CommonOptionBag.VerificationCoverageReport);
    if (coverageReportDir != null) {
      await new CoverageReporter(cliCompilation.Options).SerializeVerificationCoverageReport(
        proofDependencyManager, resolution.ResolvedProgram,
        usedDependencies,
        coverageReportDir);
    }
  }
}
