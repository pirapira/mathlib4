/-
Copyright (c) 2022 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
module

public meta import Lean.Elab.Tactic.Simp
public meta import Lean.Elab.App
public meta import Mathlib.Tactic.Simps.NotationClass
public meta import Mathlib.Lean.Expr.Basic
public meta import Mathlib.Tactic.Basic

/-!
# Simps attribute

This file defines the `@[simps]` attribute, to automatically generate `simp` lemmas
reducing a definition when projections are applied to it.

## Implementation Notes

There are three attributes being defined here
* `@[simps]` is the attribute for objects of a structure or instances of a class. It will
  automatically generate simplification lemmas for each projection of the object/instance that
  contains data. See the doc strings for `Lean.Parser.Attr.simps` and `Simps.Config`
  for more details and configuration options.
* `structureExt` (just an environment extension, not actually an attribute)
  is automatically added to structures that have been used in `@[simps]`
  at least once. This attribute contains the data of the projections used for this structure
  by all following invocations of `@[simps]`.
* `@[notation_class]` should be added to all classes that define notation, like `Mul` and
  `Zero`. This specifies that the projections that `@[simps]` used are the projections from
  these notation classes instead of the projections of the superclasses.
  Example: if `Mul` is tagged with `@[notation_class]` then the projection used for `Semigroup`
  will be `fun α hα ↦ @Mul.mul α (@Semigroup.toMul α hα)` instead of `@Semigroup.mul`.
  [this is not correctly implemented in Lean 4 yet]

### Possible Future Improvements
* If multiple declarations are generated from a `simps` without explicit projection names, then
  only the first one is shown when mousing over `simps`.

## Changes w.r.t. Lean 3

There are some small changes in the attribute. None of them should have great effects
* The attribute will now raise an error if it tries to generate a lemma when there already exists
  a lemma with that name (in Lean 3 it would generate a different unique name)
* `transparency.none` has been replaced by `TransparencyMode.reducible`
* The `attr` configuration option has been split into `isSimp` and `attrs` (for extra attributes)
* Because Lean 4 uses bundled structures, this means that `simps` applied to anything that
  implements a notation class will almost certainly require a user-provided custom simps projection.

## Tags

structures, projections, simp, simplifier, generates declarations
-/

public meta section
open Lean Elab Parser Command
open Meta hiding Config
open Elab.Term hiding mkConst

/-- An internal representation of a name to be used for a generated lemma. -/
private structure NameStruct where
  /-- The namespace that the final name will reside in. -/
  parent : Name
  /-- A list of pieces to be joined by `toName`. -/
  components : List String

/-- Join the components with `_`, or append `_def` if there is only one component. -/
private def NameStruct.toName (n : NameStruct) : Name :=
  Name.mkStr n.parent <|
    match n.components with
    | [] => ""
    | [x] => s!"{x}_def"
    | e => "_".intercalate e

instance : Coe NameStruct Name where coe := NameStruct.toName

/-- `update nm s isPrefix` adds `s` to the last component of `nm`,
either as prefix or as suffix (specified by `isPrefix`).
Used by `simps_add_projections`. -/
private def NameStruct.update (nm : NameStruct) (s : String) (isPrefix : Bool := false) :
    NameStruct :=
  { nm with components := if isPrefix then s :: nm.components else nm.components ++ [s] }

-- move
namespace Lean.Meta
open Tactic Simp
/-- Make `MkSimpContextResult` giving data instead of Syntax. Doesn't support arguments.
Intended to be very similar to `Lean.Elab.Tactic.mkSimpContext`
Todo: support arguments. -/
def mkSimpContextResult (cfg : Meta.Simp.Config := {}) (simpOnly := false) (kind := SimpKind.simp)
    (dischargeWrapper := DischargeWrapper.default) (hasStar := false) :
    MetaM MkSimpContextResult := do
  match dischargeWrapper with
  | .default => pure ()
  | _ =>
    if kind == SimpKind.simpAll then
      throwError "'simp_all' tactic does not support 'discharger' option"
    if kind == SimpKind.dsimp then
      throwError "'dsimp' tactic does not support 'discharger' option"
  let simpTheorems ← if simpOnly then
    simpOnlyBuiltins.foldlM (·.addConst ·) ({} : SimpTheorems)
  else
    getSimpTheorems
  let simprocs := #[← if simpOnly then pure {} else Simp.getSimprocs]
  let congrTheorems ← getSimpCongrTheorems
  let ctx : Simp.Context ← Simp.mkContext cfg
    (simpTheorems := #[simpTheorems])
    (congrTheorems := congrTheorems)
  if !hasStar then
    return { ctx, simprocs, dischargeWrapper }
  else
    let mut simpTheorems := ctx.simpTheorems
    let hs ← getPropHyps
    for h in hs do
      unless simpTheorems.isErased (.fvar h) do
        simpTheorems ← simpTheorems.addTheorem (.fvar h) (← h.getDecl).toExpr
    let ctx := ctx.setSimpTheorems simpTheorems
    return { ctx, simprocs, dischargeWrapper }

/-- Make `Simp.Context` giving data instead of Syntax. Doesn't support arguments.
Intended to be very similar to `Lean.Elab.Tactic.mkSimpContext`
Todo: support arguments. -/
def mkSimpContext (cfg : Meta.Simp.Config := {}) (simpOnly := false) (kind := SimpKind.simp)
    (dischargeWrapper := DischargeWrapper.default) (hasStar := false) :
    MetaM Simp.Context := do
  let data ← mkSimpContextResult cfg simpOnly kind dischargeWrapper hasStar
  return data.ctx

end Lean.Meta

namespace Lean.Parser
namespace Attr


/-! Declare notation classes. -/
attribute [notation_class add] HAdd
attribute [notation_class mul] HMul
attribute [notation_class sub] HSub
attribute [notation_class div] HDiv
attribute [notation_class mod] HMod
attribute [notation_class append] HAppend
attribute [notation_class pow Simps.copyFirst] HPow
attribute [notation_class andThen] HAndThen
attribute [notation_class] Neg Dvd LE LT HasEquiv HasSubset HasSSubset Union Inter SDiff Insert
  Singleton Sep Membership
attribute [notation_class one Simps.findOneArgs] OfNat
attribute [notation_class zero Simps.findZeroArgs] OfNat

/-- An `(attr := ...)` option for `simps`. -/
syntax simpsOptAttrOption := atomic(" (" &"attr" " := " Parser.Term.attrInstance,* ")")?

/-- Arguments to `@[simps]` attribute.
Currently, a potential `(attr := ...)` argument has to come before other configuration options. -/
syntax simpsArgsRest := simpsOptAttrOption Tactic.optConfig (ppSpace ident)*
