/-
Copyright (c) 2021 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Kyle Miller
-/
module

public import Mathlib.Init
public meta import Lean.Parser.Command

/-!
# Support for `lemma` as a synonym for `theorem`.
-/

public meta section

open Lean
