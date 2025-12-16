module

public import Lean.Linter.Sets -- for the definition of linter sets
public import Lean.LibrarySuggestions.Default -- for `+suggestions` modes in tactics
public import Mathlib.Tactic.Linter.CommandStart
public import Mathlib.Tactic.Linter.DeprecatedSyntaxLinter
public import Mathlib.Tactic.Linter.DirectoryDependency
public import Mathlib.Tactic.Linter.DocPrime
public import Mathlib.Tactic.Linter.DocString
public import Mathlib.Tactic.Linter.EmptyLine
public import Mathlib.Tactic.Linter.GlobalAttributeIn
public import Mathlib.Tactic.Linter.HashCommandLinter
public import Mathlib.Tactic.Linter.Header
public import Mathlib.Tactic.Linter.FlexibleLinter
-- This file imports Batteries.Tactic.Lint, where the `env_linter` attribute is defined.
public import Mathlib.Tactic.Linter.Lint
public import Mathlib.Tactic.Linter.Multigoal
public import Mathlib.Tactic.Linter.OldObtain
public import Mathlib.Tactic.Linter.PrivateModule
-- The following import contains the environment extension for the unused tactic linter.
public import Mathlib.Tactic.Linter.UnusedTacticExtension
public import Mathlib.Tactic.Linter.UnusedTactic
public import Mathlib.Tactic.Linter.UnusedInstancesInType
public import Mathlib.Tactic.Linter.Style
-- This import makes the `#min_imports` command available globally.
public import Mathlib.Tactic.MinImports
public import Mathlib.Tactic.TacticAnalysis.Declarations
-- This is a redundant import, but it is needed so that
-- the linter doesn't complain about `ParseCommand` not importing `Header`.
-- This can be removed after https://github.com/leanprover-community/mathlib4/pull/32419
public import Mathlib.Util.ParseCommand

/-!
This is the root file in Mathlib: it is imported by virtually *all* Mathlib files.
For this reason, the imports of this file are carefully curated.
Any modification involving a change in the imports of this file should be discussed beforehand.

Here are some general guidelines:
* no bucket imports (e.g. `Batteries`/`Lean`/etc);
* every import needs to have a comment explaining why the import is there;
* strong preference for avoiding files that themselves have imports beyond `Lean`, and
  any exception to this rule should be accompanied by a comment explaining the transitive imports.

A linter verifies that every file in Mathlib imports `Mathlib.Init`
(perhaps indirectly) --- except for the imports in this file, of course.

## Linters

All syntax linters defined in Mathlib which are active by default are imported here.
Syntax linters need to be imported to take effect, hence we would like them to be imported
as early as possible.

All linters imported here have no bulk imports;
**Not** imported in this file are
- the text-based linters in `Linters/TextBased.lean`, as they can be imported later
- the `haveLet` linter, as it is currently disabled by default due to crashes
- the `ppRoundTrip` linter, which is currently disabled (as this is not mature enough)
- the `minImports` linter, as that linter is disabled by default (and has an informational function;
  it is useful for debugging, but not as a permanently enabled lint)
- the `upstreamableDecls` linter, as it is also mostly informational

-/

@[expose] public section

/-- Define a linter set of all mathlib syntax linters which are enabled by default.

Projects depending on mathlib can use `set_option linter.mathlibStandardSet true` to enable
all these linters, or add the `weak.linter.mathlibStandardSet` option to their lakefile.
-/
register_linter_set linter.mathlibStandardSet :=
  -- linter.allScriptsDocumented -- disabled, let's not impose this requirement downstream.
  -- linter.checkInitImports -- disabled, not relevant downstream.
  linter.flexible
  linter.hashCommand
  linter.oldObtain
  linter.privateModule
  linter.style.cases
  linter.style.induction
  linter.style.refine
  linter.style.commandStart
  linter.style.cdot
  linter.style.docString
  linter.style.dollarSyntax
  linter.style.emptyLine
  linter.style.header
  linter.style.lambdaSyntax
  linter.style.longLine
  linter.style.longFile
  linter.style.multiGoal
  linter.style.nativeDecide
  linter.style.openClassical
  linter.style.missingEnd
  linter.style.setOption
  linter.style.show
  linter.style.maxHeartbeats
  linter.unusedDecidableInType
  -- The `docPrime` linter is disabled: https://github.com/leanprover-community/mathlib4/issues/20560

/-- Define a set of linters that are used in the `nightly-testing` branch
to catch any regressions.
-/
register_linter_set linter.nightlyRegressionSet :=
  linter.tacticAnalysis.regressions.linarithToGrind
  linter.tacticAnalysis.regressions.omegaToLia
  linter.tacticAnalysis.regressions.ringToGrind
  linter.tacticAnalysis.regressions.tautoToGrind
