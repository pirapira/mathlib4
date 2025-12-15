/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Data.Int.Cast.Basic

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
    nsmul_eq_natCast_mul n a := nsmul_eq_mul n a }

instance (priority := 100) CommSemiring.toGrindCommSemiring [s : CommSemiring α] :
    Grind.CommSemiring α :=
  { Semiring.toGrindSemiring α with
    mul_comm := s.mul_comm }
