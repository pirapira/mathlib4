/-
Copyright (c) 2022 Eric Rodriguez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Rodriguez, Yoichi Hirai
-/
module

universe u v

class Semiring (α : Type u) extends One α, NatCast α where
  natCast := sorry

instance (priority := 100) Semiring.toGrindSemiring {α : Type u} [s : Semiring α] :
    Lean.Grind.Semiring α :=
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


/-- The integers modulo `n : ℕ`. -/
def ZMod : Nat → Type
  | 0 => Int
  | n + 1 => Fin (n + 1)

instance ZMod.decidableEq : ∀ n : Nat, DecidableEq (ZMod n)
  | 0 => inferInstanceAs (DecidableEq Int)
  | n + 1 => inferInstanceAs (DecidableEq (Fin (n + 1)))

/- We define each field by cases, to ensure that the eta-expanded `ZMod.commRing` is defeq to the
original, this helps avoid diamonds with instances coming from classes extending `CommRing` such as
field. -/
instance someStructure (n : Nat) : Semiring (ZMod n) where
  one := sorry
  natCast := sorry

@[grind =]
theorem dummy (n : Nat) :   @Eq (ZMod n)
    (@NatCast.natCast (ZMod n) (@Semiring.toNatCast (ZMod n) (someStructure n)) n)
    (match n with
      | Nat.zero => (0 : Int)
      | Nat.succ pred => (0 : Fin (pred.succ))
     ) := by
  sorry

example (k m : Nat) : (m ^ 2) = m := by grind
