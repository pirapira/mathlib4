/-
Copyright (c) 2021 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Kyle Miller
-/
module

public meta import Lean
public meta import Mathlib.Tactic.PPWithUniv
public meta import Mathlib.Tactic.ExtendDoc
public meta import Mathlib.Tactic.Lemma
public meta import Mathlib.Tactic.TypeStar
public meta import Mathlib.Tactic.Linter.OldObtain
public meta import Mathlib.Tactic.Simproc.ExistsAndEq
public import Batteries.Util.LibraryNote -- For `library_note` command.

/-!
# Basic tactics and utilities for tactic writing

This file defines some basic utilities for tactic writing, and also
- a dummy `variables` macro (which warns that the Lean 4 name is `variable`)
- the `introv` tactic, which allows the user to automatically introduce the variables of a theorem
and explicitly name the non-dependent hypotheses,
- an `assumption` macro, calling the `assumption` tactic on all goals
- the tactics `match_target` and `clear_aux_decl` (clearing all auxiliary declarations from the
context).
-/

public meta section

namespace Mathlib.Tactic
open Lean Parser.Tactic Elab Command Elab.Tactic Meta

/-- Syntax for the `variables` command: this command is just a stub,
and merely warns that it has been renamed to `variable` in Lean 4. -/
syntax (name := «variables») "variables" (ppSpace bracketedBinder)* : command

end Mathlib.Tactic
