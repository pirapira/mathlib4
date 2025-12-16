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

/-- The `@[simps]` attribute automatically derives lemmas specifying the projections of this
declaration.

Example:
```lean
@[simps] def foo : ℕ × ℤ := (1, 2)
```
derives two `simp` lemmas:
```lean
@[simp] lemma foo_fst : foo.fst = 1
@[simp] lemma foo_snd : foo.snd = 2
```

* It does not derive `simp` lemmas for the prop-valued projections.
* It will automatically reduce newly created beta-redexes, but will not unfold any definitions.
* If the structure has a coercion to either sorts or functions, and this is defined to be one
  of the projections, then this coercion will be used instead of the projection.
* If the structure is a class that has an instance to a notation class, like `Neg` or `Mul`,
  then this notation is used instead of the corresponding projection.
* You can specify custom projections, by giving a declaration with name
  `{StructureName}.Simps.{projectionName}`. See Note [custom simps projection].

  Example:
  ```lean
  def Equiv.Simps.invFun (e : α ≃ β) : β → α := e.symm
  @[simps] def Equiv.trans (e₁ : α ≃ β) (e₂ : β ≃ γ) : α ≃ γ :=
  ⟨e₂ ∘ e₁, e₁.symm ∘ e₂.symm⟩
  ```
  generates
  ```
  @[simp] lemma Equiv.trans_toFun : ∀ {α β γ} (e₁ e₂) (a : α), ⇑(e₁.trans e₂) a = (⇑e₂ ∘ ⇑e₁) a
  @[simp] lemma Equiv.trans_invFun : ∀ {α β γ} (e₁ e₂) (a : γ),
    ⇑((e₁.trans e₂).symm) a = (⇑(e₁.symm) ∘ ⇑(e₂.symm)) a
  ```

* You can specify custom projection names, by specifying the new projection names using
  `initialize_simps_projections`.
  Example: `initialize_simps_projections Equiv (toFun → apply, invFun → symm_apply)`.
  See `initialize_simps_projections` for more information.

* If one of the fields itself is a structure, this command will recursively create
  `simp` lemmas for all fields in that structure.
  * Exception: by default it will not recursively create `simp` lemmas for fields in the structures
    `Prod`, `PProd`, and `Opposite`. You can give explicit projection names or change the value of
    `Simps.Config.notRecursive` to override this behavior.

  Example:
  ```lean
  structure MyProd (α β : Type*) := (fst : α) (snd : β)
  @[simps] def foo : Prod ℕ ℕ × MyProd ℕ ℕ := ⟨⟨1, 2⟩, 3, 4⟩
  ```
  generates
  ```lean
  @[simp] lemma foo_fst : foo.fst = (1, 2)
  @[simp] lemma foo_snd_fst : foo.snd.fst = 3
  @[simp] lemma foo_snd_snd : foo.snd.snd = 4
  ```

* You can use `@[simps proj1 proj2 ...]` to only generate the projection lemmas for the specified
  projections.
* Recursive projection names can be specified using `proj1_proj2_proj3`.
  This will create a lemma of the form `foo.proj1.proj2.proj3 = ...`.

  Example:
  ```lean
  structure MyProd (α β : Type*) := (fst : α) (snd : β)
  @[simps fst fst_fst snd] def foo : Prod ℕ ℕ × MyProd ℕ ℕ := ⟨⟨1, 2⟩, 3, 4⟩
  ```
  generates
  ```lean
  @[simp] lemma foo_fst : foo.fst = (1, 2)
  @[simp] lemma foo_fst_fst : foo.fst.fst = 1
  @[simp] lemma foo_snd : foo.snd = {fst := 3, snd := 4}
  ```
* If one of the values is an eta-expanded structure, we will eta-reduce this structure.

  Example:
  ```lean
  structure EquivPlusData (α β) extends α ≃ β where
    data : Bool
  @[simps] def EquivPlusData.rfl {α} : EquivPlusData α α := { Equiv.refl α with data := true }
  ```
  generates the following:
  ```lean
  @[simp] lemma bar_toEquiv : ∀ {α : Sort*}, bar.toEquiv = Equiv.refl α
  @[simp] lemma bar_data : ∀ {α : Sort*}, bar.data = true
  ```
  This is true, even though Lean inserts an eta-expanded version of `Equiv.refl α` in the
  definition of `bar`.
* You can add additional attributes to all lemmas generated by `simps` using e.g.
  `@[simps (attr := grind =)]`.
* For configuration options, see the doc string of `Simps.Config`.
* The precise syntax is `simps (attr := a) config ident*`, where `a` is a list of attributes,
  `config` declares configuration options and `ident*` is a list of desired projection names.
* Configuration options can be given using `(config := e)` where `e : Simps.Config`,
  or by specifying options directly, like `-fullyApplied` or `(notRecursive := [])`.
* `@[simps]` reduces let-expressions where necessary.
* When option `trace.simps.verbose` is true, `simps` will print the projections it finds and the
  lemmas it generates. The same can be achieved by using `@[simps?]`.
* Use `@[to_additive (attr := simps)]` to apply both `to_additive` and `simps` to a definition
  This will also generate the additive versions of all `simp` lemmas.
-/
/- If one of the fields is a partially applied constructor, we will eta-expand it
  (this likely never happens, so is not included in the official doc). -/
syntax (name := simps) "simps" "!"? "?"? simpsArgsRest : attr

@[inherit_doc simps] macro "simps?"  rest:simpsArgsRest : attr => `(attr| simps   ? $rest)
@[inherit_doc simps] macro "simps!"  rest:simpsArgsRest : attr => `(attr| simps !   $rest)
@[inherit_doc simps] macro "simps!?" rest:simpsArgsRest : attr => `(attr| simps ! ? $rest)
@[inherit_doc simps] macro "simps?!" rest:simpsArgsRest : attr => `(attr| simps ! ? $rest)

end Attr

/-- Linter to check that `simps!` is used when needed -/
register_option linter.simpsNoConstructor : Bool := {
  defValue := true
  descr := "Linter to check that `simps!` is used" }

/-- Linter to check that no unused custom declarations are declared for simps. -/
register_option linter.simpsUnusedCustomDeclarations : Bool := {
  defValue := true
  descr := "Linter to check that no unused custom declarations are declared for simps" }

namespace Command

/-- Syntax for renaming a projection in `initialize_simps_projections`. -/
syntax simpsRule.rename := ident " → " ident
/-- Syntax for making a projection non-default in `initialize_simps_projections`. -/
syntax simpsRule.erase := "-" ident
/-- Syntax for making a projection default in `initialize_simps_projections`. -/
syntax simpsRule.add := "+" ident
/-- Syntax for making a projection prefix. -/
syntax simpsRule.prefix := &"as_prefix " ident
/-- Syntax for a single rule in `initialize_simps_projections`. -/
syntax simpsRule := simpsRule.prefix <|> simpsRule.rename <|> simpsRule.erase <|> simpsRule.add
/-- Syntax for `initialize_simps_projections`. -/
syntax simpsProj := ppSpace ident (" (" simpsRule,+ ")")?

/--
This command allows customisation of the lemmas generated by `simps`.

By default, tagging a definition of an element `myObj` of a structure `MyStruct` with `@[simps]`
generates one `@[simp]` lemma `myObj_myProj` for each projection `myProj` of `MyStruct`. There are a
few exceptions to this general rule:
* For algebraic structures, we will automatically use the notation (like `Mul`)
  for the projections if such an instance is available.
* By default, the projections to parent structures are not default projections,
  but all the data-carrying fields are (including those in parent structures).

This default behavior is customisable as such:
* You can disable a projection by default by running
  `initialize_simps_projections MulEquiv (-invFun)`
  This will ensure that no simp lemmas are generated for this projection,
  unless this projection is explicitly specified by the user (as in
  `@[simps invFun] def myEquiv : MulEquiv _ _ := _`).
* Conversely, you can enable a projection by default by running
  `initialize_simps_projections MulEquiv (+toEquiv)`.
* You can specify custom names by writing e.g.
  `initialize_simps_projections MulEquiv (toFun → apply, invFun → symm_apply)`.
* If you want the projection name added as a prefix in the generated lemma name, you can use
  `as_prefix fieldName`:
  `initialize_simps_projections MulEquiv (toFun → coe, as_prefix coe)`
  Note that this does not influence the parsing of projection names: if you have a declaration
  `foo` and you want to apply the projections `snd`, `coe` (which is a prefix) and `fst`, in that
  order you can run `@[simps snd_coe_fst] def foo ...` and this will generate a lemma with the
  name `coe_foo_snd_fst`.

Here are a few extra pieces of information:
  * Run `initialize_simps_projections?` (or `set_option trace.simps.verbose true`)
  to see the generated projections.
* Running `initialize_simps_projections MyStruct` without arguments is not necessary, it has the
  same effect if you just add `@[simps]` to a declaration.
* It is recommended to call `@[simps]` or `initialize_simps_projections` in the same file as the
  structure declaration. Otherwise, the projections could be generated multiple times in different
  files.

Some common uses:
* If you define a new homomorphism-like structure (like `MulHom`) you can just run
  `initialize_simps_projections` after defining the `DFunLike` instance (or instance that implies
  a `DFunLike` instance).
  ```
    instance {mM : Mul M} {mN : Mul N} : FunLike (MulHom M N) M N := ...
    initialize_simps_projections MulHom (toFun → apply)
  ```
  This will generate `foo_apply` lemmas for each declaration `foo`.
* If you prefer `coe_foo` lemmas that state equalities between functions, use
  `initialize_simps_projections MulHom (toFun → coe, as_prefix coe)`
  In this case you have to use `@[simps -fullyApplied]` whenever you call `@[simps]`.
* You can also initialize to use both, in which case you have to choose which one to use by default,
  by using either of the following
  ```
    initialize_simps_projections MulHom (toFun → apply, toFun → coe, as_prefix coe, -coe)
    initialize_simps_projections MulHom (toFun → apply, toFun → coe, as_prefix coe, -apply)
  ```
  In the first case, you can get both lemmas using `@[simps, simps -fullyApplied coe]` and in
  the second case you can get both lemmas using `@[simps -fullyApplied, simps apply]`.
* If you declare a new homomorphism-like structure (like `RelEmbedding`),
  then `initialize_simps_projections` will automatically find any `DFunLike` coercions
  that will be used as the default projection for the `toFun` field.
  ```
    initialize_simps_projections relEmbedding (toFun → apply)
  ```
* If you have an isomorphism-like structure (like `Equiv`) you often want to define a custom
  projection for the inverse:
  ```
    def Equiv.Simps.symm_apply (e : α ≃ β) : β → α := e.symm
    initialize_simps_projections Equiv (toFun → apply, invFun → symm_apply)
  ```
-/
syntax (name := initialize_simps_projections)
  "initialize_simps_projections" "?"? simpsProj : command

@[inherit_doc «initialize_simps_projections»]
macro "initialize_simps_projections?" rest:simpsProj : command =>
  `(initialize_simps_projections ? $rest)

end Command
end Lean.Parser

initialize registerTraceClass `simps.verbose
initialize registerTraceClass `simps.debug

namespace Simps

/-- Projection data for a single projection of a structure -/
structure ProjectionData where
  /-- The name used in the generated `simp` lemmas -/
  name : Name
  /-- An Expression used by simps for the projection. It must be definitionally equal to an original
  projection (or a composition of multiple projections).
  These Expressions can contain the universe parameters specified in the first argument of
  `structureExt`. -/
  expr : Expr
  /-- A list of natural numbers, which is the projection number(s) that have to be applied to the
  Expression. For example the list `[0, 1]` corresponds to applying the first projection of the
  structure, and then the second projection of the resulting structure (this assumes that the
  target of the first projection is a structure with at least two projections).
  The composition of these projections is required to be definitionally equal to the provided
  Expression. -/
  projNrs : List Nat
  /-- A Boolean specifying whether `simp` lemmas are generated for this projection by default. -/
  isDefault : Bool
  /-- A Boolean specifying whether this projection is written as prefix. -/
  isPrefix : Bool
  deriving Inhabited

instance : ToMessageData ProjectionData where toMessageData
  | ⟨a, b, c, d, e⟩ => .group <| .nest 1 <|
    "⟨" ++ .joinSep [toMessageData a, toMessageData b, toMessageData c, toMessageData d,
      toMessageData e] ("," ++ Format.line) ++ "⟩"

/--
The `Simps.structureExt` environment extension specifies the preferred projections of the given
structure, used by the `@[simps]` attribute.
- You can generate this with the command `initialize_simps_projections`.
- If not generated, the `@[simps]` attribute will generate this automatically.
- To change the default value, see Note [custom simps projection].
- The first argument is the list of names of the universe variables used in the structure
- The second argument is an array that consists of the projection data for each projection.
-/
initialize structureExt : NameMapExtension (List Name × Array ProjectionData) ←
  registerNameMapExtension (List Name × Array ProjectionData)

/-- Projection data used internally in `getRawProjections`. -/
structure ParsedProjectionData where
  /-- name for this projection used in the structure definition -/
  strName : Name
  /-- syntax that might have provided `strName` -/
  strStx : Syntax := .missing
  /-- name for this projection used in the generated `simp` lemmas -/
  newName : Name
  /-- syntax that provided `newName` -/
  newStx : Syntax := .missing
  /-- will simp lemmas be generated for with (without specifically naming this?) -/
  isDefault : Bool := true
  /-- is the projection name a prefix? -/
  isPrefix : Bool := false
  /-- projection expression -/
  expr? : Option Expr := none
  /-- the list of projection numbers this expression corresponds to -/
  projNrs : Array Nat := #[]
  /-- is this a projection that is changed by the user? -/
  isCustom : Bool := false

/-- Turn `ParsedProjectionData` into `ProjectionData`. -/
def ParsedProjectionData.toProjectionData (p : ParsedProjectionData) : ProjectionData :=
  { p with name := p.newName, expr := p.expr?.getD default, projNrs := p.projNrs.toList }

instance : ToMessageData ParsedProjectionData where toMessageData
  | ⟨x₁, x₂, x₃, x₄, x₅, x₆, x₇, x₈, x₉⟩ => .group <| .nest 1 <|
    "⟨" ++ .joinSep [toMessageData x₁, toMessageData x₂, toMessageData x₃, toMessageData x₄,
      toMessageData x₅, toMessageData x₆, toMessageData x₇, toMessageData x₈, toMessageData x₉]
    ("," ++ Format.line) ++ "⟩"

/-- The type of rules that specify how metadata for projections in changes.
See `initialize_simps_projections`. -/
inductive ProjectionRule where
  /-- A renaming rule `before→after` or
    Each name comes with the syntax used to write the rule,
    which is used to declare hover information. -/
  | rename (oldName : Name) (oldStx : Syntax) (newName : Name) (newStx : Syntax) :
      ProjectionRule
  /-- An adding rule `+fieldName` -/
  | add : Name → Syntax → ProjectionRule
  /-- A hiding rule `-fieldName` -/
  | erase : Name → Syntax → ProjectionRule
  /-- A prefix rule `prefix fieldName` -/
  | prefix : Name → Syntax → ProjectionRule

instance : ToMessageData ProjectionRule where toMessageData
  | .rename x₁ x₂ x₃ x₄ => .group <| .nest 1 <|
    "rename ⟨" ++ .joinSep [toMessageData x₁, toMessageData x₂, toMessageData x₃, toMessageData x₄]
      ("," ++ Format.line) ++ "⟩"
  | .add x₁ x₂ => .group <| .nest 1 <|
    "+⟨" ++ .joinSep [toMessageData x₁, toMessageData x₂] ("," ++ Format.line) ++ "⟩"
  | .erase x₁ x₂ => .group <| .nest 1 <|
    "-⟨" ++ .joinSep [toMessageData x₁, toMessageData x₂] ("," ++ Format.line) ++ "⟩"
  | .prefix x₁ x₂ => .group <| .nest 1 <|
    "prefix ⟨" ++ .joinSep [toMessageData x₁, toMessageData x₂] ("," ++ Format.line) ++ "⟩"

/-- Returns the projection information of a structure. -/
def projectionsInfo (l : List ProjectionData) (pref : String) (str : Name) : MessageData :=
  let ⟨defaults, nondefaults⟩ := l.partition (·.isDefault)
  let toPrint : List MessageData :=
    defaults.map fun s ↦
      let prefixStr := if s.isPrefix then "(prefix) " else ""
      m!"Projection {prefixStr}{s.name}: {s.expr}"
  let print2 : MessageData :=
    String.join <| (nondefaults.map fun nm : ProjectionData ↦ toString nm.1).intersperse ", "
  let toPrint :=
    toPrint ++
      if nondefaults.isEmpty then [] else
      [("No lemmas are generated for the projections: " : MessageData) ++ print2 ++ "."]
  let toPrint := MessageData.joinSep toPrint ("\n" : MessageData)
  m!"{pref} {str}:\n{toPrint}"

/-- Find the indices of the projections that need to be applied to elaborate `$e.$projName`.
Example: If `e : α ≃+ β` and ``projName = `invFun`` then this returns `[0, 1]`, because the first
projection of `MulEquiv` is `toEquiv` and the second projection of `Equiv` is `invFun`. -/
def findProjectionIndices (strName projName : Name) : MetaM (List Nat) := do
  let env ← getEnv
  let some baseStr := findField? env strName projName |
    throwError "{strName} has no field {projName} in parent structure"
  let some fullProjName := getProjFnForField? env baseStr projName |
    throwError "no such field {projName}"
  let some pathToField := getPathToBaseStructure? env baseStr strName |
    throwError "no such field {projName}"
  let allProjs := pathToField ++ [fullProjName]
  return allProjs.map (env.getProjectionFnInfo? · |>.get!.i)

/--
A variant of `Substring.dropPrefix?` that does not consider `toFoo` to be a prefix to `toFoo_1`.
This is checked by inspecting whether the first character of the remaining part is a digit.

We use this variant because the latter is often a different field with an auto-generated name.
-/
private def dropPrefixIfNotNumber? (s : String) (pre : String) : Option String.Slice := do
  let ret ← s.dropPrefix? pre
  -- flag is true when the remaining part is nonempty and starts with a digit.
  let flag := ret.toString.toList.head?.elim false Char.isDigit
  if flag then none else some ret

/-- A variant of `String.isPrefixOf` that does not consider `toFoo` to be a prefix to `toFoo_1`. -/
private def isPrefixOfAndNotNumber (s p : String) : Bool := (dropPrefixIfNotNumber? p s).isSome

/-- A variant of `String.splitOn` that does not split `toFoo_1` into `toFoo` and `1`. -/
private def splitOnNotNumber (s delim : String) : List String :=
  (process (s.splitOn delim).reverse "").reverse where
    process (arr : List String) (tail : String) := match arr with
      | [] => []
      | (x :: xs) =>
        -- flag is true when this segment is nonempty and starts with a digit.
        let flag := x.toList.head?.elim false Char.isDigit
        if flag then
          process xs (tail ++ delim ++ x)
        else
          List.cons (x ++ tail) (process xs "")

/-- Auxiliary function of `getCompositeOfProjections`. -/
partial def getCompositeOfProjectionsAux (proj : String) (e : Expr) (pos : Array Nat)
    (args : Array Expr) : MetaM (Expr × Array Nat) := do
  let env ← getEnv
  let .const structName _ := (← whnf (← inferType e)).getAppFn |
    throwError "{e} doesn't have a structure as type"
  let projs := getStructureFieldsFlattened env structName
  let projInfo := projs.toList.map fun p ↦ do
    ((← dropPrefixIfNotNumber? proj (p.lastComponentAsString ++ "_")).toString, p)
  let some (projRest, projName) := projInfo.reduceOption.getLast? |
    throwError "Failed to find constructor {proj.dropEnd 1} in structure {structName}."
  let newE ← mkProjection e projName
  let newPos := pos ++ (← findProjectionIndices structName projName)
  -- we do this here instead of in a recursive call in order to not get an unnecessary eta-redex
  if projRest.isEmpty then
    let newE ← mkLambdaFVars args newE
    return (newE, newPos)
  let type ← inferType newE
  forallTelescopeReducing type fun typeArgs _tgt ↦ do
    getCompositeOfProjectionsAux projRest (mkAppN newE typeArgs) newPos (args ++ typeArgs)

/-- Suppose we are given a structure `str` and a projection `proj`, that could be multiple nested
projections (separated by `_`), where each projection could be a projection of a parent structure.
This function returns an expression that is the composition of these projections and a
list of natural numbers, that are the projection numbers of the applied projections.
Note that this function is similar to elaborating dot notation, but it can do a little more.

Example: if we do
```
structure gradedFun (A : ℕ → Type*) where
  toFun := ∀ i j, A i →+ A j →+ A (i + j)
initialize_simps_projections (toFun_toFun_toFun → myMul)
```
we will be able to generate the "projection"
  `fun {A} (f : gradedFun A) (x : A i) (y : A j) ↦ ↑(↑(f.toFun i j) x) y`,
which projection notation cannot do. -/
def getCompositeOfProjections (structName : Name) (proj : String) : MetaM (Expr × Array Nat) := do
  let strExpr ← mkConstWithLevelParams structName
  let type ← inferType strExpr
  forallTelescopeReducing type fun typeArgs _ ↦
  withLocalDeclD `x (mkAppN strExpr typeArgs) fun e ↦
  getCompositeOfProjectionsAux (proj ++ "_") e #[] <| typeArgs.push e

/-- Get the default `ParsedProjectionData` for structure `str`.
It first returns the direct fields of the structure in the right order, and then
all (non-subobject fields) of all parent structures. The subobject fields are precisely the
non-default fields. -/
def mkParsedProjectionData (structName : Name) : CoreM (Array ParsedProjectionData) := do
  let env ← getEnv
  let projs := getStructureFields env structName
  if projs.size == 0 then
    throwError "Declaration {structName} is not a structure."
  let projData := projs.map fun fieldName ↦ {
    strName := fieldName, newName := fieldName,
    isDefault := isSubobjectField? env structName fieldName |>.isNone }
  let parentProjs := getStructureFieldsFlattened env structName false
  let parentProjs := parentProjs.filter (!projs.contains ·)
  let parentProjData := parentProjs.map fun nm ↦
    {strName := nm, newName := nm}
  return projData ++ parentProjData
