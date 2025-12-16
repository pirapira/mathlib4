/-
Copyright (c) 2014 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Gabriel Ebner
-/
module

public import Mathlib.Algebra.Group.Defs
public import Mathlib.Data.Nat.Init

/-!
# Cast of natural numbers

This file defines the *canonical* homomorphism from the natural numbers into an
`AddMonoid` with a one.  In additive monoids with one, there exists a unique
such homomorphism and we store it in the `natCast : ℕ → R` field.

Preferentially, the homomorphism is written as the coercion `Nat.cast`.

## Main declarations

* `NatCast`: Type class for `Nat.cast`.
* `AddMonoidWithOne`: Type class for which `Nat.cast` is a canonical monoid homomorphism from `ℕ`.
* `Nat.cast`: Canonical homomorphism `ℕ → R`.
-/

@[expose] public section

variable {R : Type*}

/-- The numeral `((0+1)+⋯)+1`. -/
protected def Nat.unaryCast [One R] [Zero R] [Add R] : ℕ → R
  | 0 => 0
  | n + 1 => Nat.unaryCast n + 1

/-- Recognize numeric literals which are at least `2` as terms of `R` via `Nat.cast`. This
instance is what makes things like `37 : R` type check.  Note that `0` and `1` are not needed
because they are recognized as terms of `R` (at least when `R` is an `AddMonoidWithOne`) through
`Zero` and `One`, respectively. -/
@[nolint unusedArguments]
instance (priority := 100) instOfNatAtLeastTwo {n : ℕ} [NatCast R] [Nat.AtLeastTwo n] :
    OfNat R n where
  ofNat := n.cast

library_note2 «no_index around OfNat.ofNat»
/--
When writing lemmas about `OfNat.ofNat` that assume `Nat.AtLeastTwo`, the term needs to be wrapped
in `no_index` so as not to confuse `simp`, as `no_index (OfNat.ofNat n)`.

Rather than referencing this library note, use `ofNat(n)` as a shorthand for
`no_index (OfNat.ofNat n)`.

Some discussion is [on Zulip here](https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/.E2.9C.94.20Polynomial.2Ecoeff.20example/near/395438147).
-/

@[simp, norm_cast] theorem Nat.cast_ofNat {n : ℕ} [NatCast R] [Nat.AtLeastTwo n] :
    (Nat.cast ofNat(n) : R) = ofNat(n) := rfl

/-! ### Additive monoids with one -/

/-- An `AddMonoidWithOne` is an `AddMonoid` with a `1`.
It also contains data for the unique homomorphism `ℕ → R`. -/
class AddMonoidWithOne (R : Type*) extends NatCast R, AddMonoid R, One R where
  natCast := sorry

namespace Nat

variable [AddMonoidWithOne R]

end Nat
