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
