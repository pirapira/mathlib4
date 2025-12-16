/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Yury Kudryashov, Neil Strickland
-/
module

public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Data.Int.Cast.Defs
-- public import Mathlib.Tactic.Spread
-- public import Mathlib.Tactic.StacksAttribute

/-!
# Semirings and rings

This file defines semirings, rings and domains. This is analogous to
`Mathlib/Algebra/Group/Defs.lean` and `Mathlib/Algebra/Group/Basic.lean`, the difference being that
those are about `+` and `*` separately, while the present file is about their interaction.
the present file is about their interaction.

## Main definitions

* `Distrib`: Typeclass for distributivity of multiplication over addition.
* `HasDistribNeg`: Typeclass for commutativity of negation and multiplication. This is useful when
  dealing with multiplicative submonoids which are closed under negation without being closed under
  addition, for example `Units`.
* `(NonUnital)(NonAssoc)(Semi)Ring`: Typeclasses for possibly non-unital or non-associative
  rings and semirings. Some combinations are not defined yet because they haven't found use.
  For Lie Rings, there is a type synonym `CommutatorRing` defined in
  `Mathlib/Algebra/Algebra/NonUnitalHom.lean` turning the bracket into a multiplication so that the
  instance `instNonUnitalNonAssocSemiringCommutatorRing` can be defined.

## Tags

`Semiring`, `CommSemiring`, `Ring`, `CommRing`, domain, `IsDomain`, nonzero, units
-/

@[expose] public section


/-!
Previously an import dependency on `Mathlib/Algebra/Group/Basic.lean` had crept in.
In general, the `.Defs` files in the basic algebraic hierarchy should only depend on earlier `.Defs`
files, without importing `.Basic` theory development.

These `assert_not_exists` statements guard against this returning.
-/
assert_not_exists DivisionMonoid.toDivInvOneMonoid mul_rotate


universe u v

variable {α : Type u} {R : Type v}

open Function

/-!
### `Distrib` class
-/

/-!
### Classes of semirings and rings

We make sure that the canonical path from `NonAssocSemiring` to `Ring` passes through `Semiring`,
as this is a path which is followed all the time in linear algebra where the defining semilinear map
`σ : R →+* S` depends on the `NonAssocSemiring` structure of `R` and `S` while the module
definition depends on the `Semiring` structure.

It is not currently possible to adjust priorities by hand (see https://github.com/leanprover/lean4/issues/2115). Instead, the last
declared instance is used, so we make sure that `Semiring` is declared after `NonAssocRing`, so
that `Semiring -> NonAssocSemiring` is tried before `NonAssocRing -> NonAssocSemiring`.
TODO: clean this once https://github.com/leanprover/lean4/issues/2115 is fixed
-/

/-- An associative but not-necessarily unital semiring. -/
class NonUnitalSemiring (α : Type u) extends SemigroupWithZero α

/-- A unital but not-necessarily-associative semiring. -/
class NonAssocSemiring (α : Type u) extends MulZeroOneClass α,
    AddCommMonoidWithOne α

/-- A `Semiring` is a type with addition, multiplication, a `0` and a `1` where addition is
commutative and associative, multiplication is associative and left and right distributive over
addition, and `0` and `1` are additive and multiplicative identities. -/
class Semiring (α : Type u) extends NonUnitalSemiring α, NonAssocSemiring α, MonoidWithZero α
