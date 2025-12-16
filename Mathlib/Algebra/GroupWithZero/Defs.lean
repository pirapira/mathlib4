/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
module

public import Mathlib.Algebra.Group.Defs
public import Mathlib.Logic.Nontrivial.Defs
public import Mathlib.Logic.Basic

/-!
# Typeclasses for groups with an adjoined zero element

This file provides just the typeclass definitions, and the projection lemmas that expose their
members.

## Main definitions

* `GroupWithZero`
* `CommGroupWithZero`
-/

@[expose] public section

assert_not_exists DenselyOrdered Ring

universe u

-- We have to fix the universe of `G₀` here, since the default argument to
-- `GroupWithZero.div'` cannot contain a universe metavariable.
variable {G₀ : Type u} {M₀ : Type*}

/-- A mixin for left cancellative multiplication by nonzero elements. -/
@[mk_iff] class IsLeftCancelMulZero (M₀ : Type u) [Mul M₀] [Zero M₀] : Prop where
  /-- Multiplication by a nonzero element is left cancellative. -/
  protected mul_left_cancel_of_ne_zero : ∀ {a : M₀}, a ≠ 0 → IsLeftRegular a

section IsLeftCancelMulZero

variable [Mul M₀] [Zero M₀] [IsLeftCancelMulZero M₀] {a b c : M₀}

theorem mul_left_cancel₀ (ha : a ≠ 0) (h : a * b = a * c) : b = c :=
  IsLeftCancelMulZero.mul_left_cancel_of_ne_zero ha h

end IsLeftCancelMulZero

/-- A mixin for right cancellative multiplication by nonzero elements. -/
@[mk_iff] class IsRightCancelMulZero (M₀ : Type u) [Mul M₀] [Zero M₀] : Prop where
  /-- Multiplication by a nonzero element is right cancellative. -/
  protected mul_right_cancel_of_ne_zero : ∀ {a : M₀}, a ≠ 0 → IsRightRegular a

section IsRightCancelMulZero

variable [Mul M₀] [Zero M₀] [IsRightCancelMulZero M₀] {a b c : M₀}

theorem mul_right_cancel₀ (hb : b ≠ 0) (h : a * b = c * b) : a = c :=
  IsRightCancelMulZero.mul_right_cancel_of_ne_zero hb h

end IsRightCancelMulZero

/-- A mixin for cancellative multiplication by nonzero elements. -/
@[mk_iff] class IsCancelMulZero (M₀ : Type u) [Mul M₀] [Zero M₀] : Prop
  extends IsLeftCancelMulZero M₀, IsRightCancelMulZero M₀

theorem isCancelMulZero_iff_forall_isRegular {M₀} [Mul M₀] [Zero M₀] :
    IsCancelMulZero M₀ ↔ ∀ {a : M₀}, a ≠ 0 → IsRegular a := by
  simp only [isCancelMulZero_iff, isLeftCancelMulZero_iff, isRightCancelMulZero_iff, ← forall_and]
  exact forall₂_congr fun _ _ ↦ isRegular_iff.symm

/-- Predicate typeclass for expressing that `a * b = 0` implies `a = 0` or `b = 0`
for all `a` and `b` of type `M₀`. It is weaker than `IsCancelMulZero` in general,
but equivalent to it if `M₀` is a (not necessarily unital or associative) ring. -/
@[mk_iff] class NoZeroDivisors (M₀ : Type*) [Mul M₀] [Zero M₀] : Prop where
  /-- For all `a` and `b` of `M₀`, `a * b = 0` implies `a = 0` or `b = 0`. -/
  eq_zero_or_eq_zero_of_mul_eq_zero : ∀ {a b : M₀}, a * b = 0 → a = 0 ∨ b = 0

export NoZeroDivisors (eq_zero_or_eq_zero_of_mul_eq_zero)
/-- A type `S₀` is a "semigroup with zero” if it is a semigroup with zero element, and `0` is left
and right absorbing. -/
class SemigroupWithZero (S₀ : Type u) extends Semigroup S₀

/-- A typeclass for non-associative monoids with zero elements. -/
class MulZeroOneClass (M₀ : Type u) extends MulOneClass M₀

/-- A type `M₀` is a “monoid with zero” if it is a monoid with zero element, and `0` is left
and right absorbing. -/
class MonoidWithZero (M₀ : Type u) extends Monoid M₀, MulZeroOneClass M₀, SemigroupWithZero M₀
