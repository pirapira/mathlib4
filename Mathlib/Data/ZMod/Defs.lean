/-
Copyright (c) 2022 Eric Rodriguez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Rodriguez
-/
module

public import Mathlib.Algebra.Ring.Defs
-- public import Mathlib.Data.Int.Cast.Basic

/-!
# Instances for `grind`.
-/

@[expose] public section

open Lean

variable (α : Type*)

-- This is a low priority instance so that the built-in `Lean.Grind.Semiring Nat` instance
-- (which has a non-defeq `ofNat` instance) is used preferentially.
instance (priority := 100) Semiring.toGrindSemiring [s : Semiring α] :
    Grind.Semiring α :=
  { s with
    nsmul := ⟨s.nsmul⟩
    npow := ⟨fun a n => a^n⟩
    ofNat | 0 | 1 | n + 2 => inferInstance
    natCast := inferInstance
    add_zero := by simp [add_zero]
    mul_one := by simp [mul_one]
    zero_mul := by simp [zero_mul]
    pow_zero a := by simp
    pow_succ a n := by simp [pow_succ]
    ofNat_eq_natCast
    | 0 => Nat.cast_zero.symm
    | 1 => Nat.cast_one.symm
    | n + 2 => rfl
    ofNat_succ
    | 0 => by simp [zero_add]
    | 1 => by
      change Nat.cast 2 = 1 + 1
      rw [one_add_one_eq_two]
      rfl
    | n + 2 => by
      change Nat.cast (n + 2 + 1) = Nat.cast (n + 2) + 1
      rw [← AddMonoidWithOne.natCast_succ]
    nsmul_eq_natCast_mul n a := sorry }

/-!
demonstrating an error in grind

(kernel) application type mismatch
  eq_false_of_decide (eagerReduce (Eq.refl false))
argument has type
  false = false
but function has type
  decide (2 = 0) = false → (2 = 0) = False
-/

@[expose] public section


namespace Fin

open Int

open scoped Fin.IntCast Fin.NatCast

namespace CommRing

end CommRing


end Fin

/-- The integers modulo `n : ℕ`. -/
@[to_additive_dont_translate]
def ZMod : ℕ → Type
  | 0 => ℤ
  | n + 1 => Fin (n + 1)

instance ZMod.decidableEq : ∀ n : ℕ, DecidableEq (ZMod n)
  | 0 => inferInstanceAs (DecidableEq ℤ)
  | n + 1 => inferInstanceAs (DecidableEq (Fin (n + 1)))

namespace ZMod

open Fin.CommRing in
/- We define each field by cases, to ensure that the eta-expanded `ZMod.commRing` is defeq to the
original, this helps avoid diamonds with instances coming from classes extending `CommRing` such as
field. -/
instance someStructure (n : ℕ) : Semiring (ZMod n) where
  add := sorry
  add_assoc := sorry
  zero := sorry
  zero_add := sorry
  add_zero := sorry
  nsmul := sorry
  nsmul_zero := sorry
  nsmul_succ := sorry
  add_comm := sorry
  mul := sorry
  mul_assoc := sorry
  one := sorry
  one_mul := sorry
  mul_one := sorry
  natCast := sorry
  natCast_zero := sorry
  natCast_succ := sorry
  left_distrib := sorry
  right_distrib := sorry
  zero_mul := sorry
  mul_zero := sorry
  npow := sorry
  npow_zero := sorry
  npow_succ := sorry
-- n : ZMod n = 0

-- Nat.casesOn n ((↑) : ℕ → ℤ) fun n => ((↑) : ℕ → Fin n.succ)

set_option pp.explicit true
set_option pp.rawOnError true

#check (someStructure ?_).5

@[grind =]
theorem dummy (n : Nat) :   @Eq (ZMod n)
    (@NatCast.natCast (ZMod n) (@Semiring.toNatCast (ZMod n) (someStructure n)) n)
    (match n with
      | Nat.zero => (0 : ℤ)
      | Nat.succ pred => (0 : Fin (pred.succ))
     ) := by
  sorry

example (k m : ℕ) : (m ^ 2) = m := by grind


end ZMod
