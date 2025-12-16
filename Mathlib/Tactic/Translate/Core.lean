/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Yury Kudryashov, Floris van Doorn, Jon Eugster, Bryan Gin-ge Chen,
Jovan Gerbscheid
-/
module

public meta import Batteries.Tactic.Trans
public meta import Lean.Compiler.NoncomputableAttr
public meta import Lean.Elab.Tactic.Ext
public meta import Lean.Meta.Tactic.Rfl
public meta import Lean.Meta.Tactic.Symm
public meta import Mathlib.Data.Array.Defs
public meta import Mathlib.Data.Nat.Notation
public meta import Mathlib.Lean.Expr.ReplaceRec
public meta import Mathlib.Lean.Meta.Simp
public meta import Mathlib.Lean.Name
public meta import Mathlib.Tactic.Eqns -- just to copy the attribute
public meta import Mathlib.Tactic.Simps.Basic
public meta import Mathlib.Tactic.Translate.GuessName
public meta import Lean.Meta.CoeAttr
