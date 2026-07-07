/-
Copyright (c) 2026 Akhil Mathew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Akhil Mathew
-/
module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Sym.Card
public import Mathlib.Tactic.Ring.RingNF

/-!
# Numerical growth lemmas for the dimension theorem

Purely arithmetic facts about functions `ℕ → ℕ`; no ring theory in this file.
We say `f` has *growth degree at most `d`* (`DimensionTheorem.GrowthLE f d`)
if `f n ≤ C * (n + 1) ^ d` for some constant `C`.

## Main results

* `DimensionTheorem.GrowthLE.of_le_sub` — the **telescoping lemma**: if `g` is
  monotone, `g n + f (n - c) ≤ f n` for all `n ≥ c`, and `f` has growth degree
  at most `d + 1`, then `g` has growth degree at most `d`.
* `DimensionTheorem.card_sym_le` — there are at most `(n + 1) ^ (k - 1)`
  monomials of degree `n` in `k ≥ 1` variables:
  `Fintype.card (Sym (Fin k) n) ≤ (n + 1) ^ (k - 1)`.

## Sources

The telescoping lemma has no direct textbook counterpart. Classical treatments
(e.g. Atiyah–Macdonald, *Introduction to Commutative Algebra*, Ch. 11) define
`d(R)` as the degree of the Hilbert–Samuel *polynomial*, for which "the
difference `P(n) - P(n - c)` has degree one less" is immediate. This
development defines `d(R)` by growth order alone (avoiding the Hilbert–Serre
theorem), and that step is replaced here: for monotone `g` dominated by the
`c`-step difference of `f`, summing along an arithmetic progression of step
`c` gives `n * g n ≤ f (n * (c + 1))`, which forces the degree drop. Used in
`FLT/Slop/DimensionTheorem/DimLeGrowth.lean` for the inductive step of `dim R ≤ d(R)`.

The counting bound is `Nat.multichoose k n ≤ (n + 1) ^ (k - 1)`, by induction
from the Pascal-type recurrence `Nat.multichoose_succ_succ`. Used in
`FLT/Slop/DimensionTheorem/GrowthLeDelta.lean` to bound the number of degree-`n`
monomials in the generators of an ideal of definition.
-/

@[expose] public section

namespace DimensionTheorem

/-- `f : ℕ → ℕ` grows at most like `n ^ d`. We use `(n + 1) ^ d` to avoid
degenerate behavior at `n = 0`. -/
def GrowthLE (f : ℕ → ℕ) (d : ℕ) : Prop :=
  ∃ C : ℕ, ∀ n, f n ≤ C * (n + 1) ^ d

namespace GrowthLE

lemma of_le {f g : ℕ → ℕ} {d : ℕ} (hg : GrowthLE g d) (h : ∀ n, f n ≤ g n) :
    GrowthLE f d := by
  obtain ⟨C, hC⟩ := hg
  exact ⟨C, fun n => (h n).trans (hC n)⟩

lemma mono {f : ℕ → ℕ} {d d' : ℕ} (hf : GrowthLE f d) (hd : d ≤ d') :
    GrowthLE f d' := by
  obtain ⟨C, hC⟩ := hf
  refine ⟨C, fun n => (hC n).trans ?_⟩
  exact Nat.mul_le_mul_left C (Nat.pow_le_pow_right (Nat.succ_le_succ n.zero_le) hd)

lemma of_bounded {f : ℕ → ℕ} {C : ℕ} (h : ∀ n, f n ≤ C) : GrowthLE f 0 :=
  ⟨C, fun n => by simpa using h n⟩

/-- **Telescoping lemma.** If `g` is monotone and, for `n ≥ c`, the value `g n` is
dominated by the difference `f n - f (n - c)` (stated additively as
`g n + f (n - c) ≤ f n`), and `f` has growth degree at most `d + 1`, then `g` has
growth degree at most `d`.

This is the numerical heart of the inductive step `dim ≤ d(R)` in the dimension
theorem: passing to `R/xR` drops the growth degree of the Hilbert–Samuel function. -/
private lemma telescope_aux {f g : ℕ → ℕ} {c : ℕ}
    (h : ∀ n, c ≤ n → g n + f (n - c) ≤ f n) (n : ℕ) :
    ∀ m : ℕ, f n + ∑ j ∈ Finset.range m, g (n + (j + 1) * c) ≤ f (n + m * c) := by
  intro m
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ← Nat.add_assoc]
    have hcle : c ≤ n + (m + 1) * c :=
      le_trans (Nat.le_mul_of_pos_left c (Nat.succ_pos m)) (Nat.le_add_left _ n)
    have key := h (n + (m + 1) * c) hcle
    have hsub : n + (m + 1) * c - c = n + m * c := by
      rw [Nat.succ_mul, ← Nat.add_assoc, Nat.add_sub_cancel]
    rw [hsub] at key
    have key' : f (n + m * c) + g (n + (m + 1) * c) ≤ f (n + (m + 1) * c) := by
      rw [Nat.add_comm (f (n + m * c)) (g (n + (m + 1) * c))]; exact key
    exact le_trans (Nat.add_le_add_right ih _) key'

-- `hc` is kept for interface stability but is not actually needed:
-- each application of `h` is at a point `n + (j + 1) * c ≥ c` regardless.
set_option linter.unusedVariables false in
@[nolint unusedArguments]
lemma of_le_sub {f g : ℕ → ℕ} {c d : ℕ} (hc : 0 < c) (hf : GrowthLE f (d + 1))
    (hg : Monotone g) (h : ∀ n, c ≤ n → g n + f (n - c) ≤ f n) :
    GrowthLE g d := by
  obtain ⟨C, hC⟩ := hf
  refine ⟨2 * C * (c + 1) ^ (d + 1) + g 0, fun n => ?_⟩
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  -- Step 1: telescoping gives `f n + ∑_{j<n} g (n + (j+1)c) ≤ f (n + n*c)`.
  have step1 : f n + ∑ j ∈ Finset.range n, g (n + (j + 1) * c) ≤ f (n + n * c) :=
    telescope_aux h n n
  -- Step 2: monotonicity of `g` gives `n * g n ≤ ∑_{j<n} g (n + (j+1)c)`.
  have step2 : n * g n ≤ ∑ j ∈ Finset.range n, g (n + (j + 1) * c) := by
    have := Finset.card_nsmul_le_sum (Finset.range n)
      (fun j => g (n + (j + 1) * c)) (g n)
      (fun j _ => hg (Nat.le_add_right n ((j + 1) * c)))
    simpa using this
  -- Step 3: hence `n * g n ≤ f (n * (c + 1))`.
  have step3 : n * g n ≤ f (n * (c + 1)) := by
    have hne : n + n * c = n * (c + 1) := by ring
    rw [← hne]
    calc n * g n ≤ ∑ j ∈ Finset.range n, g (n + (j + 1) * c) := step2
      _ ≤ f (n + n * c) := le_trans (Nat.le_add_left _ (f n)) step1
  -- Step 4: bound via the growth hypothesis on `f`.
  have hlin : n * (c + 1) + 1 ≤ (n + 1) * (c + 1) := by
    rw [add_mul, one_mul]
    exact Nat.add_le_add_left (Nat.succ_le_succ (Nat.zero_le c)) _
  have step4 : n * g n ≤ C * ((n + 1) * (c + 1)) ^ (d + 1) :=
    le_trans step3 (le_trans (hC _)
      (Nat.mul_le_mul_left C (Nat.pow_le_pow_left hlin (d + 1))))
  -- Step 5: cancel a factor of `n` (using `n + 1 ≤ 2 * n` for `n ≥ 1`).
  have key : n * g n ≤ n * ((2 * C * (c + 1) ^ (d + 1) + g 0) * (n + 1) ^ d) := by
    calc n * g n ≤ C * ((n + 1) * (c + 1)) ^ (d + 1) := step4
      _ = C * (c + 1) ^ (d + 1) * (n + 1) ^ d * (n + 1) := by
          rw [mul_pow, pow_succ]; ring
      _ ≤ C * (c + 1) ^ (d + 1) * (n + 1) ^ d * (2 * n) :=
          Nat.mul_le_mul le_rfl (by omega)
      _ = n * (2 * C * (c + 1) ^ (d + 1) * (n + 1) ^ d) := by ring
      _ ≤ n * ((2 * C * (c + 1) ^ (d + 1) + g 0) * (n + 1) ^ d) :=
          Nat.mul_le_mul le_rfl
            (Nat.mul_le_mul (Nat.le_add_right _ _) le_rfl)
  exact Nat.le_of_mul_le_mul_left key hn

end GrowthLE

/-- The number of monomials of degree `n` in `k` variables is at most `(n + 1) ^ (k - 1)`
(for `k ≥ 1`): a multiset of size `n` over `Fin k` is determined by the multiplicities of
the first `k - 1` elements, each of which lies in `{0, ..., n}`. -/
private lemma multichoose_le_pow (k : ℕ) :
    ∀ n : ℕ, Nat.multichoose (k + 1) n ≤ (n + 1) ^ k := by
  induction k with
  | zero => intro n; simp [Nat.multichoose_one]
  | succ k ih =>
    intro n
    induction n with
    | zero => simp [Nat.multichoose_zero_right]
    | succ n ihn =>
      rw [Nat.multichoose_succ_succ]
      have h2 : (n + 1) ^ (k + 1) ≤ (n + 1) * (n + 2) ^ k := by
        rw [pow_succ']
        exact Nat.mul_le_mul le_rfl (Nat.pow_le_pow_left (by omega) k)
      calc Nat.multichoose (k + 1) (n + 1) + Nat.multichoose (k + 2) n
          ≤ (n + 2) ^ k + (n + 1) ^ (k + 1) := Nat.add_le_add (ih (n + 1)) ihn
        _ ≤ (n + 2) ^ k + (n + 1) * (n + 2) ^ k := Nat.add_le_add_left h2 _
        _ = (n + 2) ^ (k + 1) := by ring

lemma card_sym_le (k n : ℕ) (hk : 1 ≤ k) :
    Fintype.card (Sym (Fin k) n) ≤ (n + 1) ^ (k - 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  rw [Sym.card_sym_fin_eq_multichoose]
  simpa using multichoose_le_pow m n

end DimensionTheorem
