/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Yury Kudryashov, Floris van Doorn, Jon Eugster, Bryan Gin-ge Chen,
Jovan Gerbscheid
-/
module

public meta import Mathlib.Tactic.Translate.Core

/-!
# The `@[to_additive]` attribute.

The `@[to_additive]` attribute is used to translate multiplicative declarations to their
additive equivalent. See the docstrings of `to_additive` for more information.
-/

public meta section

namespace Mathlib.Tactic.ToAdditive
open Lean Elab Translate

end Mathlib.Tactic.ToAdditive
