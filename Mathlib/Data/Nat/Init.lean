/-
Copyright (c) 2014 Floris van Doorn (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Leonardo de Moura, Jeremy Avigad, Mario Carneiro
-/
module

public import Batteries.Tactic.Alias
public import Batteries.Tactic.Init
public import Mathlib.Init
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Tactic.Basic
public import Mathlib.Tactic.Lemma

/-!
# Basic operations on the natural numbers

This file contains:
* some basic lemmas about natural numbers
* extra recursors:
  * `leRecOn`, `le_induction`: recursion and induction principles starting at non-zero numbers
  * `decreasing_induction`: recursion growing downwards
  * `le_rec_on'`, `decreasing_induction'`: versions with slightly weaker assumptions
  * `strong_rec'`: recursion based on strong inequalities
* decidability instances on predicates about the natural numbers

This file should not depend on anything defined in Mathlib (except for notation), so that it can be
upstreamed to Batteries or the Lean standard library easily.

See note [foundational algebra order theory].
-/

@[expose] public section

open Function

namespace Nat
variable {a b c d e m n k : ℕ} {p : ℕ → Prop}

/-! ### `succ`, `pred` -/

lemma succ_pos' : 0 < succ n := succ_pos n

alias _root_.LT.lt.nat_succ_le := succ_le_of_lt

alias ⟨of_le_succ, _⟩ := le_succ_iff

lemma two_lt_of_ne : ∀ {n}, n ≠ 0 → n ≠ 1 → n ≠ 2 → 2 < n
  | 0, h, _, _ => (h rfl).elim
  | 1, _, h, _ => (h rfl).elim
  | 2, _, _, h => (h rfl).elim
  | n + 3, _, _, _ => le_add_left 3 n

/-! ### `add` -/

/-! ### `sub` -/

/-! ### `mul` -/

lemma mul_def : Nat.mul m n = m * n := mul_eq

lemma two_mul_ne_two_mul_add_one : 2 * n ≠ 2 * m + 1 :=
  mt (congrArg (· % 2))
    (by rw [Nat.add_comm, add_mul_mod_self_left, mul_mod_right, mod_eq_of_lt] <;> simp)

@[deprecated (since := "2025-06-05")] alias mul_right_eq_self_iff := mul_eq_left
@[deprecated (since := "2025-06-05")] alias mul_left_eq_self_iff := mul_eq_right
@[deprecated (since := "2025-06-05")] alias eq_zero_of_double_le := eq_zero_of_two_mul_le

/-! ### `div` -/

lemma le_div_two_iff_mul_two_le {n m : ℕ} : m ≤ n / 2 ↔ (m : ℤ) * 2 ≤ n := by
  rw [Nat.le_div_iff_mul_le Nat.zero_lt_two, ← Int.ofNat_le, Int.natCast_mul, Int.ofNat_two]

/-- A version of `Nat.div_lt_self` using successors, rather than additional hypotheses. -/
lemma div_lt_self' (a b : ℕ) : (a + 1) / (b + 2) < a + 1 :=
  Nat.div_lt_self (Nat.succ_pos _) (Nat.succ_lt_succ (Nat.succ_pos _))

@[deprecated (since := "2025-06-05")] alias eq_zero_of_le_half := eq_zero_of_le_div_two
@[deprecated (since := "2025-06-05")] alias le_half_of_half_lt_sub := le_div_two_of_div_two_lt_sub
@[deprecated (since := "2025-06-05")] alias half_le_of_sub_le_half := div_two_le_of_sub_le_div_two
@[deprecated (since := "2025-06-05")] protected alias div_le_of_le_mul' := Nat.div_le_of_le_mul
@[deprecated (since := "2025-06-05")] protected alias div_le_self' := Nat.div_le_self

lemma two_mul_odd_div_two (hn : n % 2 = 1) : 2 * (n / 2) = n - 1 := by
  lia

/-! ### `pow` -/

lemma one_le_pow' (n m : ℕ) : 1 ≤ (m + 1) ^ n := one_le_pow n (m + 1) (succ_pos m)

alias sq_sub_sq := pow_two_sub_pow_two

/-!
### Recursion and induction principles

This section is here due to dependencies -- the lemmas here require some of the lemmas
proved above, and some of the results in later sections depend on the definitions in this section.
-/

@[simp]
lemma rec_zero {C : ℕ → Sort*} (h0 : C 0) (h : ∀ n, C n → C (n + 1)) : Nat.rec h0 h 0 = h0 := rfl

-- Not `@[simp]` since `simp` can reduce the whole term.
lemma rec_add_one {C : ℕ → Sort*} (h0 : C 0) (h : ∀ n, C n → C (n + 1)) (n : ℕ) :
    Nat.rec h0 h (n + 1) = h n (Nat.rec h0 h n) := rfl

@[simp] lemma rec_one {C : ℕ → Sort*} (h0 : C 0) (h : ∀ n, C n → C (n + 1)) :
    Nat.rec (motive := C) h0 h 1 = h 0 h0 := rfl

/-- Recursion starting at a non-zero number: given a map `C k → C (k+1)` for each `k ≥ n`,
there is a map from `C n` to each `C m`, `n ≤ m`.

This is a version of `Nat.le.rec` that works for `Sort u`.
Similarly to `Nat.le.rec`, it can be used as
```
induction hle using Nat.leRec with
| refl => sorry
| le_succ_of_le hle ih => sorry
```
-/
@[elab_as_elim]
def leRec {n} {motive : (m : ℕ) → n ≤ m → Sort*}
    (refl : motive n (Nat.le_refl _))
    (le_succ_of_le : ∀ ⦃k⦄ (h : n ≤ k), motive k h → motive (k + 1) (le_succ_of_le h)) :
    ∀ {m} (h : n ≤ m), motive m h
  | 0, H => Nat.eq_zero_of_le_zero H ▸ refl
  | m + 1, H =>
    (le_succ_iff.1 H).by_cases
      (fun h : n ≤ m ↦ le_succ_of_le h <| leRec refl le_succ_of_le h)
      (fun h : n = m + 1 ↦ h ▸ refl)

/-- Recursion starting at a non-zero number: given a map `C k → C (k + 1)` for each `k`,
there is a map from `C n` to each `C m`, `n ≤ m`. For a version where the assumption is only made
when `k ≥ n`, see `Nat.leRec`. -/
@[elab_as_elim]
def leRecOn {C : ℕ → Sort*} {n : ℕ} : ∀ {m}, n ≤ m → (∀ {k}, C k → C (k + 1)) → C n → C m :=
  fun h of_succ self => Nat.leRec self (fun _ _ => @of_succ _) h

private abbrev strongRecAux {p : ℕ → Sort*} (H : ∀ n, (∀ m < n, p m) → p n) :
    ∀ n : ℕ, ∀ m < n, p m
  | 0, _, h => by simp at h
  | n + 1, m, hmn => H _ fun l hlm ↦
      strongRecAux H n l (Nat.lt_of_lt_of_le hlm <| le_of_lt_succ hmn)

/-- Recursion principle based on `<`. -/
@[elab_as_elim]
protected def strongRec' {p : ℕ → Sort*} (H : ∀ n, (∀ m < n, p m) → p n) (n : ℕ) : p n :=
  H n <| strongRecAux H n

private lemma strongRecAux_spec {p : ℕ → Sort*} (H : ∀ n, (∀ m < n, p m) → p n) (n : ℕ) :
    ∀ m (lt : m < n), strongRecAux H n m lt = H m (strongRecAux H m) :=
  n.strongRec' fun n ih m hmn ↦ by
    obtain _ | n := n
    · cases hmn
    refine congrArg (H _) ?_
    ext l hlm
    exact (ih _ n.lt_succ_self _ _).trans (ih _ hmn _ _).symm

lemma strongRec'_spec {p : ℕ → Sort*} (H : ∀ n, (∀ m < n, p m) → p n) :
    n.strongRec' H = H n fun m _ ↦ m.strongRec' H :=
  congrArg (H n) <| by ext m lt; apply strongRecAux_spec

/-- Recursion principle based on `<` applied to some natural number. -/
@[elab_as_elim]
def strongRecOn' {P : ℕ → Sort*} (n : ℕ) (h : ∀ n, (∀ m < n, P m) → P n) : P n :=
  Nat.strongRec' h n

lemma strongRecOn'_beta {P : ℕ → Sort*} {h} :
    (strongRecOn' n h : P n) = h n fun m _ ↦ (strongRecOn' m h : P m) :=
  strongRec'_spec _
