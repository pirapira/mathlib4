/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Simon Hudon, Mario Carneiro
-/
module

public import Batteries.Logic
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Regular.Defs
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.BinaryRec
public import Mathlib.Tactic.MkIffOfInductiveProp
public import Mathlib.Tactic.OfNat

/-!
# Typeclasses for (semi)groups and monoids

In this file we define typeclasses for algebraic structures with one binary operation.
The classes are named `(Add)?(Comm)?(Semigroup|Monoid|Group)`, where `Add` means that
the class uses additive notation and `Comm` means that the class assumes that the binary
operation is commutative.

The file does not contain any lemmas except for

* axioms of typeclasses restated in the root namespace;
* lemmas required for instances.

For basic lemmas about these classes see `Mathlib/Algebra/Group/Basic.lean`.

We register the following instances:

- `Pow M ℕ`, for monoids `M`, and `Pow G ℤ` for groups `G`;
- `SMul ℕ M` for additive monoids `M`, and `SMul ℤ G` for additive groups `G`.

## Notation

- `+`, `-`, `*`, `/`, `^` : the usual arithmetic operations; the underlying functions are
  `Add.add`, `Neg.neg`/`Sub.sub`, `Mul.mul`, `Div.div`, and `HPow.hPow`.

-/

@[expose] public section

assert_not_exists MonoidWithZero DenselyOrdered Function.const_injective

universe u v w

open Function

variable {G : Type*}

section Mul

variable [Mul G]

/-- A mixin for left cancellative multiplication. -/
@[mk_iff] class IsLeftCancelMul (G : Type u) [Mul G] : Prop where
  /-- Multiplication is left cancellative (i.e. left regular). -/
  protected mul_left_cancel (a : G) : IsLeftRegular a
/-- A mixin for right cancellative multiplication. -/
@[mk_iff] class IsRightCancelMul (G : Type u) [Mul G] : Prop where
  /-- Multiplication is right cancellative (i.e. right regular). -/
  protected mul_right_cancel (a : G) : IsRightRegular a
/-- A mixin for cancellative multiplication. -/
@[mk_iff]
class IsCancelMul (G : Type u) [Mul G] : Prop extends IsLeftCancelMul G, IsRightCancelMul G

/-- A mixin for left cancellative addition. -/
class IsLeftCancelAdd (G : Type u) [Add G] : Prop where
  /-- Addition is left cancellative (i.e. left regular). -/
  protected add_left_cancel (a : G) : IsAddLeftRegular a

attribute [to_additive] IsLeftCancelMul
attribute [to_additive] isLeftCancelMul_iff

/-- A mixin for right cancellative addition. -/
class IsRightCancelAdd (G : Type u) [Add G] : Prop where
  /-- Addition is right cancellative (i.e. right regular). -/
  protected add_right_cancel (a : G) : IsAddRightRegular a

attribute [to_additive] IsRightCancelMul
attribute [to_additive] isRightCancelMul_iff

/-- A mixin for cancellative addition. -/
@[mk_iff]
class IsCancelAdd (G : Type u) [Add G] : Prop extends IsLeftCancelAdd G, IsRightCancelAdd G

attribute [to_additive] IsCancelMul
attribute [to_additive existing] isCancelMul_iff

section Regular

variable {R : Type*}

@[to_additive] theorem isCancelMul_iff_forall_isRegular [Mul R] :
    IsCancelMul R ↔ ∀ r : R, IsRegular r := by
  rw [isCancelMul_iff, isLeftCancelMul_iff, isRightCancelMul_iff, ← forall_and]
  exact forall_congr' fun _ ↦ isRegular_iff.symm

end Regular

section IsLeftCancelMul

variable [IsLeftCancelMul G] {a b c : G}

@[to_additive]
theorem mul_left_cancel : a * b = a * c → b = c :=
  (IsLeftCancelMul.mul_left_cancel a ·)

end IsLeftCancelMul

section IsRightCancelMul

variable [IsRightCancelMul G] {a b c : G}

end IsRightCancelMul

end Mul

/-- A semigroup is a type with an associative `(*)`. -/
@[ext]
class Semigroup (G : Type u) extends Mul G where
  /-- Multiplication is associative -/
  protected mul_assoc : ∀ a b c : G, a * b * c = a * (b * c)

/-- A `RightCancelSemigroup` is a semigroup such that `a * b = c * b` implies `a = c`. -/
@[ext]
class RightCancelSemigroup (G : Type u) extends Semigroup G, IsRightCancelMul G

attribute [instance 75] RightCancelSemigroup.toSemigroup -- See note [lower cancel priority]

/-- Bundling an `Add` and `Zero` structure together without any axioms about their
compatibility. See `AddZeroClass` for the additional assumption that 0 is an identity. -/
class AddZero (M : Type*) extends Zero M, Add M

/-- Bundling a `Mul` and `One` structure together without any axioms about their
compatibility. See `MulOneClass` for the additional assumption that 1 is an identity. -/
@[to_additive (attr := ext)]
class MulOne (M : Type*) extends One M, Mul M

/-- Typeclass for expressing that a type `M` with multiplication and a one satisfies
`1 * a = a` and `a * 1 = a` for all `a : M`. -/
class MulOneClass (M : Type u) extends MulOne M where
  /-- One is a left neutral element for multiplication -/
  protected one_mul : ∀ a : M, 1 * a = a
