/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Yury Kudryashov, Floris van Doorn, Jon Eugster, Bryan Gin-ge Chen,
Jovan Gerbscheid
-/
module

public meta import Batteries.Tactic.Trans
public meta import Lean.Compiler.NoncomputableAttr
public meta import Lean.Elab.Tactic.Ext
public meta import Lean.Meta.Tactic.Rfl
public meta import Lean.Meta.Tactic.Symm
public meta import Mathlib.Data.Array.Defs
public meta import Mathlib.Data.Nat.Notation
public meta import Mathlib.Lean.Expr.ReplaceRec
public meta import Mathlib.Lean.Meta.Simp
public meta import Mathlib.Lean.Name
public meta import Mathlib.Tactic.Eqns -- just to copy the attribute
public meta import Mathlib.Tactic.Simps.Basic
public meta import Mathlib.Tactic.Translate.GuessName
public meta import Lean.Meta.CoeAttr

/-!
# The translation attribute.

Implementation of the translation attribute. This is used for `@[to_additive]` and `@[to_dual]`.
See the docstring of `to_additive` for more information
-/

public meta section

open Lean Meta Elab Command Std

namespace Mathlib.Tactic.Translate
open Translate -- currently needed to enable projection notation

/-- `(attr := ...)` applies the given attributes to the original and the translated declaration.
In the case of `to_additive`, we may want to apply it multiple times,
(such as in `a ^ n` -> `n • a` -> `n +ᵥ a`). In this case, you should use the syntax
`to_additive (attr := some_other_attr, to_additive)`, which will apply `some_other_attr` to all
three generated declarations.
 -/
syntax attrOption := &"attr" " := " Parser.Term.attrInstance,*
/--
`(reorder := ...)` reorders the arguments/hypotheses in the generated declaration.
It uses cycle notation. For example `(reorder := α β, 5 6)` swaps the arguments `α` and `β`
with each other and the fifth and the sixth argument, and `(reorder := 3 4 5)` will move
the fifth argument before the third argument. This is used in `to_dual` to swap the arguments in
`≤`, `<` and `⟶`. It is also used in `to_additive` to translate from `a ^ n` to `n • a`.

If the translated declaration already exists (i.e. when using `existing` or `self`), this is
inferred automatically using the function `guessReorder`.
-/
syntax reorderOption := &"reorder" " := " ((ident <|> num)+),*
/--
the `(relevant_arg := ...)` option tells which argument to look at to determine whether to
translate this constant. This is inferred automatically using the function `findRelevantArg`,
but it can also be overwritten using this syntax.

If there are multiple possible arguments, we typically tag the first one.
If this argument contains a fixed type, this declaration will not be translated.
See the Heuristics section of the `to_additive` doc-string for more details.

If a declaration is not tagged, it is presumed that the first argument is relevant.

Use `(relevant_arg := _)` to indicate that there is no relevant argument.

Implementation note: we only allow exactly 1 relevant argument, even though some declarations
(like `Prod.instGroup`) have multiple relevant argument.
The reason is that whether we translate a declaration is an all-or-nothing decision, and
we will not be able to translate declarations that (e.g.) talk about multiplication on `ℕ × α`
anyway.
-/
syntax relevantArgOption := &"relevant_arg" " := " hole <|> ident <|> num
/--
`(dont_translate := ...)` takes a list of type variables (separated by spaces) that should not be
considered for translation. For example in
```
lemma foo {α β : Type} [Group α] [Group β] (a : α) (b : β) : a * a⁻¹ = 1 ↔ b * b⁻¹ = 1
```
we can choose to only translate `α` by writing `to_additive (dont_translate := β)`.
-/
syntax dontTranslateOption := &"dont_translate" " := " (ident <|> num)+
syntax bracketedOption := "(" attrOption <|> reorderOption <|>
  relevantArgOption <|> dontTranslateOption ")"
/-- A hint for where to find the translated declaration (`existing` or `self`) -/
syntax existingNameHint := (ppSpace (&"existing" <|> &"self"))?
syntax attrArgs :=
  existingNameHint (ppSpace bracketedOption)* (ppSpace ident)? (ppSpace (str <|> docComment))?

-- We omit a doc-string on these syntaxes to instead show the `to_additive` or `to_dual` doc-string
attribute [nolint docBlame] attrArgs bracketedOption

/-- An attribute that stores all the declarations that deal with numeric literals on variable types.

Numeral literals occur in expressions without type information, so in order to decide whether `1`
needs to be changed to `0`, the context around the numeral is relevant.
Most numerals will be in an `OfNat.ofNat` application, though tactics can add numeral literals
inside arbitrary functions. By default we assume that we do not change numerals, unless it is
in a function application with the `translate_change_numeral` attribute.

`@[translate_change_numeral n₁ ...]` should be added to all functions that take one or more
numerals as argument that should be changed if `shouldTranslate` succeeds on the first argument,
i.e. when the numeral is only translated if the first argument is a variable
(or consists of variables).
The arguments `n₁ ...` are the positions of the numeral arguments (starting counting from 1). -/
syntax (name := translate_change_numeral) "translate_change_numeral" (ppSpace num)* : attr

initialize registerTraceClass `translate
initialize registerTraceClass `translate_detail

/-- Linter, mostly used by translate attributes, that checks that the source declaration doesn't
have certain attributes -/
register_option linter.existingAttributeWarning : Bool := {
  defValue := true
  descr := "Linter, mostly used by translate attributes, that checks that the source declaration \
    doesn't have certain attributes" }

/-- Linter used by translate attributes that checks if the given declaration name is
    equal to the automatically generated name -/
register_option linter.translateGenerateName : Bool := {
  defValue := true
  descr := "Linter used by translate attributes that checks if the given declaration name is \
    equal to the automatically generated name" }

/-- Linter to check whether the user correctly specified that the translated declaration already
exists -/
register_option linter.translateExisting : Bool := {
  defValue := true
  descr := "Linter used by translate attributes that checks whether the user correctly specified
    that the translated declaration already exists" }

/-- Linter used by translate attributes that checks if the given reorder is
    equal to the automatically generated name -/
register_option linter.translateReorder : Bool := {
  defValue := true
  descr := "Linter used by translate attributes that checks if the given reorder is \
    equal to the automatically generated one" }

end Mathlib.Tactic.Translate
