/-
Copyright (c) 2014 Floris van Doorn (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Leonardo de Moura, Jeremy Avigad, Mario Carneiro
-/
module

public import Batteries.Tactic.Alias
public import Batteries.Tactic.Init
public import Mathlib.Init
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Tactic.Basic
public import Mathlib.Tactic.Lemma

/-!
# Basic operations on the natural numbers

This file contains:
* some basic lemmas about natural numbers
* extra recursors:
  * `leRecOn`, `le_induction`: recursion and induction principles starting at non-zero numbers
  * `decreasing_induction`: recursion growing downwards
  * `le_rec_on'`, `decreasing_induction'`: versions with slightly weaker assumptions
  * `strong_rec'`: recursion based on strong inequalities
* decidability instances on predicates about the natural numbers

This file should not depend on anything defined in Mathlib (except for notation), so that it can be
upstreamed to Batteries or the Lean standard library easily.

See note [foundational algebra order theory].
-/
