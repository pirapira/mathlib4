/-
Copyright (c) 2022 Eric Rodriguez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Rodriguez
-/
module

public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Regular.Defs
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.BinaryRec

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

universe u v w

/-- A semigroup is a type with an associative `(*)`. -/
@[ext]
class Semigroup (G : Type u) extends Mul G where
  /-- Multiplication is associative -/
  protected mul_assoc : ∀ a b c : G, a * b * c = a * (b * c)

/-- Bundling a `Mul` and `One` structure together without any axioms about their
compatibility. See `MulOneClass` for the additional assumption that 1 is an identity. -/
class MulOne (M : Type*) extends One M, Mul M

/-- Typeclass for expressing that a type `M` with multiplication and a one satisfies
`1 * a = a` and `a * 1 = a` for all `a : M`. -/
class MulOneClass (M : Type u) extends MulOne M where
  /-- One is a left neutral element for multiplication -/
  protected one_mul : ∀ a : M, 1 * a = a

variable {R : Type*}

/-- Recognize numeric literals which are at least `2` as terms of `R` via `Nat.cast`. This
instance is what makes things like `37 : R` type check.  Note that `0` and `1` are not needed
because they are recognized as terms of `R` (at least when `R` is an `AddMonoidWithOne`) through
`Zero` and `One`, respectively. -/
@[nolint unusedArguments]
instance (priority := 100) instOfNatAtLeastTwo {n : ℕ} [NatCast R] :
    OfNat R n where
  ofNat := sorry

/-! ### Additive monoids with one -/

/-- An `AddMonoidWithOne` is an `AddMonoid` with a `1`.
It also contains data for the unique homomorphism `ℕ → R`. -/
class AddMonoidWithOne (R : Type*) extends NatCast R, One R where
  natCast := sorry

@[expose] public section

variable {α : Type u} {R : Type v}

/-!
### `Distrib` class
-/

/-- A `Semiring` is a type with addition, multiplication, a `0` and a `1` where addition is
commutative and associative, multiplication is associative and left and right distributive over
addition, and `0` and `1` are additive and multiplicative identities. -/
class Semiring (α : Type u) extends MulOneClass α, AddMonoidWithOne α
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
    nsmul := sorry
    add := sorry
    add_assoc := sorry
    npow := sorry
    ofNat | 0 | 1 | n + 2 => inferInstance
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
  mul := sorry
  one := sorry
  one_mul := sorry
  natCast := sorry
-- n : ZMod n = 0

-- Nat.casesOn n ((↑) : ℕ → ℤ) fun n => ((↑) : ℕ → Fin n.succ)

set_option pp.explicit true
set_option pp.rawOnError true

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
