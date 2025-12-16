/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Yury Kudryashov, Neil Strickland
-/
module

public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Data.Int.Cast.Defs
-- public import Mathlib.Tactic.Spread
-- public import Mathlib.Tactic.StacksAttribute

@[expose] public section

universe u v

variable {α : Type u} {R : Type v}

/-!
### `Distrib` class
-/

/-- A `Semiring` is a type with addition, multiplication, a `0` and a `1` where addition is
commutative and associative, multiplication is associative and left and right distributive over
addition, and `0` and `1` are additive and multiplicative identities. -/
class Semiring (α : Type u) extends SemigroupWithZero α,  MulOneClass α, AddMonoidWithOne α
