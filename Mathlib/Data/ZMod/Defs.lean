/-
Copyright (c) 2022 Eric Rodriguez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Rodriguez
-/
module

universe u v w

variable {α : Type u} {R : Type v}

/-! ### Additive monoids with one -/

/-- An `AddMonoidWithOne` is an `AddMonoid` with a `1`.
It also contains data for the unique homomorphism `ℕ → R`. -/
class AddMonoidWithOne R extends NatCast R, One R where
  natCast := sorry

@[expose] public section

class Semiring (α : Type u) extends One α, AddMonoidWithOne α

/-!
# Instances for `grind`.
-/

open Lean

-- This is a low priority instance so that the built-in `Lean.Grind.Semiring Nat` instance
-- (which has a non-defeq `ofNat` instance) is used preferentially.
instance (priority := 100) Semiring.toGrindSemiring [s : Semiring α] :
    Grind.Semiring α :=
  { s with
    nsmul := sorry
    add := sorry
    add_assoc := sorry
    mul := sorry
    one_mul := sorry
    npow := sorry
    ofNat | 0 | 1 | n + 2 => sorry
    natCast := inferInstance
    add_zero := by sorry
    mul_one := by sorry
    zero_mul := sorry
    mul_zero := sorry
    pow_zero a := by sorry
    pow_succ a n := sorry
    ofNat_eq_natCast := sorry
    ofNat_succ := sorry
    nsmul_eq_natCast_mul n a := sorry
    left_distrib := sorry
    right_distrib := sorry
    add_comm := sorry
    mul_assoc := sorry
  }

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
def ZMod : Nat → Type
  | 0 => Int
  | n + 1 => Fin (n + 1)

instance ZMod.decidableEq : ∀ n : Nat, DecidableEq (ZMod n)
  | 0 => inferInstanceAs (DecidableEq Int)
  | n + 1 => inferInstanceAs (DecidableEq (Fin (n + 1)))

namespace ZMod

open Fin.CommRing in
/- We define each field by cases, to ensure that the eta-expanded `ZMod.commRing` is defeq to the
original, this helps avoid diamonds with instances coming from classes extending `CommRing` such as
field. -/
instance someStructure (n : Nat) : Semiring (ZMod n) where
  one := sorry
  natCast := sorry
-- n : ZMod n = 0

-- Nat.casesOn n ((↑) : ℕ → ℤ) fun n => ((↑) : ℕ → Fin n.succ)

set_option pp.explicit true
set_option pp.rawOnError true

@[grind =]
theorem dummy (n : Nat) :   @Eq (ZMod n)
    (@NatCast.natCast (ZMod n) (@Semiring.toNatCast (ZMod n) (someStructure n)) n)
    (match n with
      | Nat.zero => (0 : Int)
      | Nat.succ pred => (0 : Fin (pred.succ))
     ) := by
  sorry

example (k m : Nat) : (m ^ 2) = m := by grind
