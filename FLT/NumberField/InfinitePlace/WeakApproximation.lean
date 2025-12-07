/-
Copyright (c) 2024 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
import Mathlib.NumberTheory.NumberField.AdeleRing
import FLT.Mathlib.Algebra.Order.AbsoluteValue.Basic
import FLT.Mathlib.Analysis.Normed.Ring.WithAbs
import FLT.Mathlib.Data.Fin.Basic
import FLT.Mathlib.Topology.Algebra.Order.Field

/-!
# Weak approximation

This file contains weak approximation theorems for number fields and their completions
at infinite places. The main weak approximation theorem here states that for `(xᵥ)ᵥ` indexed by
finitely many infinite places, with each `xᵥ ∈ Kᵥ` there exists a global `y ∈ K` such that
`y` is arbitrarily close to each `xᵥ` (with respect to the topology on `Kᵥ` defined by `v`).
This can be equivalently stated by asserting that the appropriate `algebraMap` has dense range.

## Main results
- `NumberField.InfinitePlace.denseRange_algebraMap_pi` : weak approximation for `(xᵥ)ᵥ` when
  `v` ranges over all infinite places and each `xᵥ ∈ K` is rational.
- `NumberField.InfiniteAdeleRing.denseRange_algebraMap` : weak approximation for `(xᵥ)ᵥ` when
  `v` ranges over all infinite places and each `xᵥ ∈ Kᵥ` (i.e., `(xᵥ)ᵥ` is an infinite adele).
- `NumberField.InfinitePlace.Completion.denseRange_algebraMap_subtype_pi` : weak approximation
  for `(xᵥ)ᵥ` when `v` ranges over a subcollection of all infinite places and each
  `xᵥ ∈ Kᵥ` (useful for example when thinking only about infinite places `w` of `L` that extend
  some infinite place `v` of `K`).
-/

open scoped Topology

open NumberField

noncomputable section

namespace AbsoluteValue

variable {K : Type*} [Field K] {v : AbsoluteValue K ℝ}

open Filter in
/--
Let `a, b ∈ K`, and let `v₁, ..., vₖ` be absolute values with some `1 < vᵢ a` while all other
`vⱼ a < 1`. Suppose `1 < vᵢ b`. Let `w` be another absolute value on `K` such that `w a = 1`,
while `w b < 1`. Then we can find a sequence of values in `K` that tends to `∞` under `vᵢ`,
tends to `0` under `vⱼ`, and is always `< 1` under `w`.

Such a sequence is given by `a ^ n * b`.
-/
theorem exists_tendsto_zero_tendsto_atTop_tendsto_const
    {ι : Type*} {v : ι → AbsoluteValue K ℝ} {w : AbsoluteValue K ℝ} {a b : K} {i : ι}
    (ha : 1 < v i a) (haj : ∀ j ≠ i, v j a < 1) (haw : w a = 1) (hb : 1 < v i b) (hbw : w b < 1) :
    ∃ c : ℕ → K,
      Tendsto (fun n => (v i) (c n)) atTop atTop ∧
        (∀ j ≠ i, Tendsto (fun n => (v j) (c n)) atTop (𝓝 0)) ∧
          (∀ n, w (c n) < 1) := by
  refine ⟨fun n => a ^ n * b, ?_⟩; simp_rw [map_mul, map_pow, haw, one_pow, one_mul]
  refine ⟨Tendsto.atTop_mul_const (by linarith) (tendsto_pow_atTop_atTop_of_one_lt ha),
    fun j hj => ?_, fun _ => hbw⟩
  rw [← zero_mul <| v j b]
  exact Tendsto.mul_const _ <| tendsto_pow_atTop_nhds_zero_of_lt_one ((v j).nonneg _) (haj j hj)

open scoped Classical in
/--
Let `a, b ∈ K`, and let `v₁, ..., vₖ` be absolute values with some `1 < vᵢ a` while all other
`vⱼ a < 1`. Suppose `1 < vᵢ b`. Let `w` be another absolute value on `K` such that `w a = 1`,
while `w b < 1`. Then there is an element `k ∈ K` such that `1 < vᵢ k` while `vⱼ k < 1` for all
`j ≠ i` and `w k < 1`.

This is given by taking large enough values of a witness sequence to
`exists_tendsto_zero_tendsto_atTop_tendsto_const` (for example `a ^ n * b` works).
-/
theorem exists_one_lt_lt_one_lt_one_of_eq_one
    {ι : Type*} [Fintype ι] {v : ι → AbsoluteValue K ℝ} {w : AbsoluteValue K ℝ} {a b : K} {i : ι}
    (ha : 1 < v i a) (haj : ∀ j ≠ i, v j a < 1) (haw : w a = 1) (hb : 1 < v i b) (hbw : w b < 1) :
    ∃ k : K, 1 < v i k ∧ (∀ j ≠ i, v j k < 1) ∧ w k < 1 := by
  classical
  let ⟨c, hc⟩ := exists_tendsto_zero_tendsto_atTop_tendsto_const ha haj haw hb hbw
  simp_rw [Metric.tendsto_nhds, Filter.tendsto_atTop_atTop, Filter.eventually_atTop,
    dist_zero_right, ← WithAbs.norm_eq_abs, norm_norm] at hc
  choose r₁ hr₁ using hc.1 2
  choose rₙ hrₙ using fun j hj => hc.2.1 j hj 1 (by linarith)
  let r := Finset.univ.sup fun j => if h : j = i then r₁ else rₙ j h
  refine ⟨c r, lt_of_lt_of_le (by linarith) (hr₁ r ?_), fun j hj => ?_, hc.2.2 r⟩
  · exact Finset.le_sup_dite_pos (p := fun j => j = i) (f := fun _ _ => r₁) (Finset.mem_univ _) rfl
  · convert hrₙ j hj _ <| Finset.le_sup_dite_neg (fun j => j = i) (Finset.mem_univ j) _

open Filter in
/--
Let `a, b ∈ K`, and let `v₁, ..., vₖ` be absolute values with some `1 < vᵢ a` while all other
`vⱼ a < 1`. Let `w` be another absolute value on `K` such that `1 < w a`. Then there is a
sequence of elements in `K` that tendsto `vᵢ b` under `vᵢ`, tends to `0` under `vⱼ` for `j ≠ i`,
and tends to `w b` under `w`.

Such a sequence is given by `1 / (1 + a ^ (- n))`.
-/
theorem exists_tendsto_const_tendsto_zero_tendsto_const
    {ι : Type*} {v : ι → AbsoluteValue K ℝ} {w : AbsoluteValue K ℝ} {a : K} {i : ι}
    (b : K) (ha : 1 < v i a) (haj : ∀ j ≠ i, v j a < 1) (haw : 1 < w a) :
    ∃ c : ℕ → K,
      Tendsto (fun n => (v i) (c n)) atTop (𝓝 ((v i) b)) ∧
        (∀ j ≠ i, Tendsto (fun n => v j (c n)) atTop (𝓝 0)) ∧
          Tendsto (fun n => w (c n)) atTop (𝓝 (w b)) := by
  refine ⟨fun n => (1 / (1 + a⁻¹ ^ n) * b), ?_⟩; simp_rw [map_mul]
  nth_rw 2 [← one_mul (v i b), ← one_mul (w b)]
  let hai := map_inv₀ (v i) _ ▸ inv_lt_one_of_one_lt₀ ha
  replace haw := (map_inv₀ w _ ▸ inv_lt_one_of_one_lt₀ haw)
  refine ⟨Tendsto.mul_const _ (tendsto_div_one_add_pow_nhds_one hai), fun j hj => ?_,
      Tendsto.mul_const _ (tendsto_div_one_add_pow_nhds_one haw)⟩
  replace haj := map_inv₀ (v j) _ ▸ (one_lt_inv₀ (pos_of_pos (v j) (by linarith))).2 (haj j hj)
  exact zero_mul (v j b) ▸ Tendsto.mul_const _ (tendsto_div_one_add_pow_nhds_zero haj)

open scoped Classical in
/--
Let `a, b ∈ K`, and let `v₁, ..., vₖ` be absolute values with some `1 < vᵢ a` while all other
`vⱼ a < 1`. Suppose `1 < vᵢ b`. Let `w` be another absolute value on `K` such that `1 < w a`,
while `w b < 1`. Then there is an element `k ∈ K` such that `1 < vᵢ k` while `vⱼ k < 1` for all
`j ≠ i` and `w k < 1`.

This is given by taking large enough values of a witness sequence to
`exists_tendsto_const_tendsto_zero_tendsto_const` (for example `1 / (1 + a ^ (-n))` works).

Note that this is the result `exists_one_lt_lt_one_lt_one_of_eq_one` replacing the condition
that `w a = 1` with `1 < w a`.
-/
theorem exists_one_lt_lt_one_lt_one_of_one_lt
    {ι : Type*} [Fintype ι] {v : ι → AbsoluteValue K ℝ} {w : AbsoluteValue K ℝ} {a b : K} {i : ι}
    (ha : 1 < v i a) (haj : ∀ j ≠ i, v j a < 1) (haw : 1 < w a) (hb : 1 < v i b) (hbw : w b < 1) :
    ∃ k : K, 1 < v i k ∧ (∀ j ≠ i, v j k < 1) ∧ w k < 1 := by
  classical
  let ⟨c, hc⟩ := exists_tendsto_const_tendsto_zero_tendsto_const b ha haj haw
  have hₙ := fun j hj => Metric.tendsto_nhds.1 <| hc.2.1 j hj
  simp_rw [Filter.eventually_atTop, dist_zero_right] at hₙ
  choose r₁ hr₁ using Filter.eventually_atTop.1 <| Filter.Tendsto.eventually_const_lt hb hc.1
  choose rₙ hrₙ using fun j hj => hₙ j hj 1 (by linarith)
  choose rN hrN using Filter.eventually_atTop.1 <| Filter.Tendsto.eventually_lt_const hbw hc.2.2
  let r := max (Finset.univ.sup fun j => if h : j = i then r₁ else rₙ j h) rN
  refine ⟨c r, hr₁ r ?_, fun j hj => ?_, ?_⟩
  · exact le_max_iff.2 <| Or.inl <|
      Finset.le_sup_dite_pos (p := fun j => j = i) (f := fun _ _ => r₁) (Finset.mem_univ _) rfl
  · simp only [← WithAbs.norm_eq_abs, norm_norm] at hrₙ
    exact hrₙ j hj _ <| le_max_iff.2 <| Or.inl <|
      Finset.le_sup_dite_neg (fun j => j = i) (Finset.mem_univ j) _
  · exact hrN _ <| le_max_iff.2 (Or.inr le_rfl)

/--
Let `v₁, ..., vₖ` be a collection of at least two non-trivial and pairwise inequivalent
absolute values. Then there is `a ∈ K` such that `1 < v₁ a` while `vⱼ a < 1` for
all other `j ≠ 0`.
-/
theorem exists_one_lt_lt_one {n : ℕ} {v : Fin (n + 2) → AbsoluteValue K ℝ}
    (h : ∀ i, (v i).IsNontrivial)
    (hv : Pairwise fun i j => ¬∃ (t : ℝ) (_ : 0 < t), ∀ x, v i x = (v j x) ^ t) :
    ∃ (a : K), 1 < v 0 a ∧ ∀ j ≠ 0, v j a < 1 := by
  induction n using Nat.case_strong_induction_on with
  | hz =>
    let ⟨a, ha⟩ := (v 0).exists_one_lt_lt_one_of_ne_rpow (h 0) (h 1) (hv zero_ne_one)
    exact ⟨a, ha.1, by simp [Fin.forall_fin_two, ha.2]⟩
  | hi n ih =>
    -- Assume the result is true for all smaller collections of absolute values
    -- Let `a : K` be the value from the collection with the last absolute value removed
    let ⟨a, ha⟩ := ih n le_rfl (fun _ => h _) (hv.comp_of_injective <| Fin.castSucc_injective _)
    -- Let `b : K` be the value using then first and last absolute value
    let ⟨b, hb⟩ := ih 0 (by linarith) (fun _ => h _) <| Fin.pairwise_forall_two hv
    simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, Matrix.cons_val_zero, ne_eq,
      Fin.forall_fin_two, not_true_eq_false, IsEmpty.forall_iff, one_ne_zero, not_false_eq_true,
      Matrix.cons_val_one, forall_const, true_and] at hb
    -- If `v last < 1` then `a` works.
    by_cases ha₀ : v (Fin.last _) a < 1
    · refine ⟨a, ha.1, fun j hj => ?_⟩
      by_cases hj' : j = Fin.last (n + 2)
      · exact hj' ▸ ha₀
      · exact ha.2 (Fin.castPred _ (ne_eq _ _ ▸  hj')) <| Fin.castPred_ne_zero _ hj
    -- If `v last = 1` then this is given by `exists_one_lt_lt_one_lt_one_of_eq_one` with
    -- `w = v last`.
    · by_cases ha₁ : v (Fin.last _) a = 1
      · let ⟨k, hk⟩ := exists_one_lt_lt_one_lt_one_of_eq_one
          (v := fun i : Fin (n + 2) => v i.castSucc) ha.1 ha.2 ha₁ hb.1 hb.2
        refine ⟨k, hk.1, fun j hj => ?_⟩
        by_cases h : j ≠ Fin.last (n + 2)
        · exact ne_eq _ _ ▸ hk.2.1 (j.castPred h) <| Fin.castPred_ne_zero _ hj
        · exact not_ne_iff.1 h ▸ hk.2.2
      -- The last cast `1 < v last` is given by `exists_one_lt_lt_one_lt_one_of_one_lt` with
      -- `w = v last`.
      · let ⟨k, hk⟩ := exists_one_lt_lt_one_lt_one_of_one_lt
          (v := fun i : Fin (n + 2) => v i.castSucc) ha.1 ha.2
            (lt_of_le_of_ne (not_lt.1 ha₀) (ne_eq _ _ ▸ ha₁).symm) hb.1 hb.2
        refine ⟨k, hk.1, fun j hj => ?_⟩
        by_cases h : j ≠ Fin.last _
        · apply ne_eq _ _ ▸ hk.2.1 (j.castPred h)
          rwa [← Fin.castPred_zero, Fin.castPred_inj]
        · exact not_ne_iff.1 h ▸ hk.2.2

end AbsoluteValue

/-!
## Weak approximation results
-/

namespace NumberField.InfinitePlace

open AbsoluteValue

variable {K : Type*} [Field K] {v : InfinitePlace K} (w : InfinitePlace K)

theorem pos_of_pos {x : K} (hv : 0 < v x) : 0 < w x := by
  rw [coe_apply] at hv ⊢
  exact v.1.pos_of_pos _ hv

variable {w}

/--
If `v` and `w` are infinite places of `K` and `v = w ^ t` for some `t > 0` then `t = 1`.
-/
theorem rpow_eq_one_of_eq_rpow {t : ℝ} (h : ∀ x, v x = (w x) ^ t) : t = 1 := by
  let ⟨ψv, hψv⟩ := v.2
  let ⟨ψw, hψw⟩ := w.2
  simp only [coe_apply, ← hψv, ← hψw] at h
  have := congrArg (Real.logb 2) (h 2)
  simp only [place_apply, map_ofNat, RCLike.norm_ofNat, Nat.one_lt_ofNat, Real.logb_self_eq_one,
    Nat.ofNat_pos, ne_eq, OfNat.ofNat_ne_one, not_false_eq_true, Real.logb_rpow] at this
  exact this.symm

/--
If `v` and `w` are infinite places of `K` and `v = w ^ t`, then `v = w`.
-/
theorem eq_of_eq_rpow (h : ∃ (t : ℝ) (_ : 0 < t), ∀ x, v x = (w x) ^ t) : v = w := by
  let ⟨t, _, h⟩ := h
  simp only [rpow_eq_one_of_eq_rpow h, Real.rpow_one] at h
  exact Subtype.ext <| AbsoluteValue.ext h

open Filter in
/--
Let `v` be an infinite place and `c ∈ K` such that `1 < v c`. Suppose that `w c < 1` for any
other infinite place `w ≠ v`. Then we can find a sequence in `K` that tends to `1` with respect
to `v` and tends to `0` with respect to all other `w ≠ v`.

Such a sequence is given by `1 / (1 + c ^ (-n))`.
-/
theorem exists_tendsto_one_tendsto_zero {v : InfinitePlace K} {c : K} (hv : 1 < v c)
    (h : ∀ w : InfinitePlace K, w ≠ v → w c < 1) :
    ∃ a : ℕ → K,
      Tendsto (β := WithAbs v.1) a atTop (𝓝 1) ∧ (∀ w, w ≠ v →
        Tendsto (β := WithAbs w.1) a atTop (𝓝 0)) := by
  refine ⟨fun n => 1 / (1 + c⁻¹ ^ n), ?_, ?_⟩
  · have hx₁ := map_inv₀ v _ ▸ inv_lt_one_of_one_lt₀ hv
    nth_rw 3 [show (1 : WithAbs v.1) = 1 / 1 by norm_num]
    apply Filter.Tendsto.div tendsto_const_nhds _ one_ne_zero
    nth_rw 2 [← add_zero (1 : WithAbs v.1)]
    apply Filter.Tendsto.const_add
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simp_rw [norm_pow]
    apply tendsto_pow_atTop_nhds_zero_of_lt_one (AbsoluteValue.nonneg _ _) hx₁
  · intro w hwv
    simp_rw [div_eq_mul_inv, one_mul]
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simp_rw [norm_inv]
    apply Filter.Tendsto.inv_tendsto_atTop
    have (a : WithAbs w.1) (n : ℕ) : ‖a ^ n‖ - 1 ≤  ‖1 + a ^ n‖  := by
      simp_rw [add_comm, ← norm_one (α := WithAbs w.1), tsub_le_iff_right]
      exact norm_le_add_norm_add _ _
    apply Filter.tendsto_atTop_mono (this _)
    apply Filter.tendsto_atTop_add_right_of_le _ (-1) _ (fun _ => le_rfl)
    simp only [inv_pow, norm_inv, norm_pow]
    refine tendsto_atTop_of_geom_le (c := w c⁻¹) ?_ ?_ (fun n => ?_)
    · simp only [pow_zero, inv_one, zero_lt_one]
    · exact map_inv₀ w _ ▸ (one_lt_inv₀ (pos_of_pos w (by linarith))).2 (h w hwv)
    · rw [map_inv₀, ← inv_pow, ← inv_pow, pow_add, pow_one, mul_comm]
      exact le_rfl

/--
Suppose that there are at least two infinite places of `K`. Let `v` be one of them.
Then we can find an `x ∈ K` such that `1 < v x`, while `w x < 1` for all other `w ≠ v`.

This element is obtained by applying the analogous result for collections of non-equivalent
and non-trivial absolute values `AbsoluteValue.exists_one_lt_lt_one`.
-/
theorem exists_one_lt_lt_one [NumberField K] (h : 1 < Fintype.card (InfinitePlace K)) :
    ∃ (x : K), 1 < v x ∧ ∀ w ≠ v, w x < 1 := by
  let ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin (InfinitePlace K)
  have : 1 < n := by linarith [Fintype.card_fin n ▸ Fintype.card_eq.2 ⟨e⟩]
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' this
  let ⟨m, hm⟩ := e.symm.surjective v
  let e₀ := e.trans (Equiv.swap 0 m)
  let ⟨x, hx⟩ := AbsoluteValue.exists_one_lt_lt_one (fun i => (e₀.symm i).isNontrivial)
      (fun i j hj => mt eq_of_eq_rpow <| e₀.symm.injective.ne hj)
  refine ⟨x, hm ▸ hx.1, fun w hw => ?_⟩
  have he₀ : e₀ v = 0 := by simp [e₀, e.symm_apply_eq.1 hm]
  exact e₀.symm_apply_apply _ ▸ hx.2 (e₀ w) <| he₀ ▸ e₀.injective.ne hw

end InfinitePlace

namespace InfinitePlace.Completion

variable (K : Type*) [Field K] {v w : InfinitePlace K}

/--
*Weak approximation for subcollections*: this is the result that `K` is dense in any subcollection
`Π v ∈ S, Kᵥ` of completions at infinite places.
-/
theorem denseRange_algebraMap_subtype_pi (p : InfinitePlace K → Prop) [NumberField K] :
    DenseRange <| algebraMap K ((v : Subtype p) → v.1.Completion) := by
  apply DenseRange.comp (g := Subtype.restrict p)
    (f := algebraMap K ((v : InfinitePlace K) → v.1.Completion))
  · exact Subtype.surjective_restrict (β := fun v => v.1.Completion) p |>.denseRange
  · exact InfiniteAdeleRing.denseRange_algebraMap K
  · exact continuous_pi (fun _ => continuous_apply _)

end NumberField.InfinitePlace.Completion
