/-
Copyright (c) 2022 Eric Rodriguez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Rodriguez
-/
module

public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Data.Int.Basic
public import Mathlib.Algebra.Ring.GrindInstances

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

/-!
## Ring structure on `Fin n`

We define a commutative ring structure on `Fin n`.
Afterwards, when we define `ZMod n` in terms of `Fin n`, we use these definitions
to register the ring structure on `ZMod n` as type class instance.
-/


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
    ((someStructure n).5.1 n)
    (match n with
      | Nat.zero => (0 : ℤ)
      | Nat.succ pred => (0 : Fin (pred.succ))
     ) := by
  sorry

example (k m : ℕ) : (m ^ 2) = m := by grind


end ZMod
