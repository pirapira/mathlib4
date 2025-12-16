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

/-- A mixin for left cancellative addition. -/
class IsLeftCancelAdd (G : Type u) [Add G] : Prop where
  /-- Addition is left cancellative (i.e. left regular). -/
  protected add_left_cancel (a : G) : IsAddLeftRegular a

/-- A mixin for right cancellative addition. -/
class IsRightCancelAdd (G : Type u) [Add G] : Prop where
  /-- Addition is right cancellative (i.e. right regular). -/
  protected add_right_cancel (a : G) : IsAddRightRegular a

/-- A mixin for cancellative addition. -/
@[mk_iff]
class IsCancelAdd (G : Type u) [Add G] : Prop extends IsLeftCancelAdd G, IsRightCancelAdd G

section Regular

variable {R : Type*}

end Regular

/-- A semigroup is a type with an associative `(*)`. -/
@[ext]
class Semigroup (G : Type u) extends Mul G where
  /-- Multiplication is associative -/
  protected mul_assoc : ∀ a b c : G, a * b * c = a * (b * c)

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
