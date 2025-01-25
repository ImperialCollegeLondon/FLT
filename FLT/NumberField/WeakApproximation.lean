/-
Copyright (c) 2024 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
import Mathlib.NumberTheory.NumberField.Embeddings
import Mathlib.NumberTheory.NumberField.AdeleRing
import Mathlib.Tactic
import FLT.Mathlib.Analysis.Normed.Ring.WithAbs
import FLT.Mathlib.Topology.Constructions

open scoped Topology Classical

open NumberField

noncomputable section

namespace AbsoluteValue

variable (K : Type*) [Field K] {v : AbsoluteValue K ℝ} {w : AbsoluteValue K ℝ}

variable {K}

/-!
## Results about equivalent absolute values

We consider two absolute values `v` and `w` on `K` to be "equivalent" if `v x < 1` if and only
if `w x < 1`. We show that this is the case if and only if there is some real `t > 0` such that
`v = w ^ t`.
-/

abbrev norm : (v : AbsoluteValue K ℝ) → (WithAbs v → ℝ) := fun v => Norm.norm (E := WithAbs v)

theorem norm_def : v.norm = Norm.norm (E := WithAbs v) := rfl

theorem norm_apply_eq (x : K) : v.norm x = v x := rfl

theorem inv_pos {x : K} (h : 0 < v x) : 0 < v x⁻¹ := by
  rwa [map_inv₀, _root_.inv_pos]

theorem exists_lt_one_of_exists_one_lt
    (h : ∃ x, 1 < v x) :
    ∃ x, 0 < v x ∧ v x < 1 :=
  let ⟨x, hx⟩ := h
  ⟨x⁻¹, inv_pos (by linarith), map_inv₀ v _ ▸ inv_lt_one_iff₀.2 <| Or.inr hx⟩

theorem ne_zero_of_lt_one {x : K} (hv : 1 < v x) :
    x ≠ 0 := by
  intro hx
  rw [hx, map_zero] at hv
  linarith

theorem nonpos_iff (x : K) : v x ≤ 0 ↔ v x = 0 := by
  simp only [le_antisymm_iff, v.nonneg _, and_true]

theorem inv_lt_one_iff {x : K} : v x⁻¹ < 1 ↔ x = 0 ∨ 1 < v x := by
  simp only [map_inv₀, inv_lt_one_iff₀, nonpos_iff, map_eq_zero]

theorem one_div_le_one {x : K} (hv : 1 ≤ v x) : v (1 / x) ≤ 1 := by
  rw [one_div, map_inv₀]
  exact inv_le_one_of_one_le₀ hv

theorem one_div_pow_le_one {x : K} (hv : 1 ≤ v x) (n : ℕ) : v (1 / x ^ n) ≤ 1 :=
  one_div_le_one (map_pow v _ _ ▸ one_le_pow₀ hv)

theorem mul_one_div_lt_iff {y : K} (x : K) (h : 0 < v y) : v (x * (1 / y)) < 1 ↔ v x < v y := by
  rw [map_mul, one_div, map_inv₀, mul_inv_lt_iff₀ h, one_mul]

theorem mul_one_div_pow_lt_iff {n : ℕ} {y : K} (x : K) (h : 0 < v y) :
    v (x * (1 / y ^ n)) < 1 ↔ v x < v y ^ n :=
  map_pow v _ _ ▸ mul_one_div_lt_iff x (map_pow v _ _ ▸ pow_pos h n)

theorem one_lt_of_lt_one {v w : AbsoluteValue K ℝ}
    (h : ∀ x, v x < 1 → w x < 1) {x : K} (hv : 1 < v x) : 1 < w x :=
  (inv_lt_one_iff.1 <| h _ <| map_inv₀ v _ ▸ inv_lt_one_of_one_lt₀ hv).resolve_left <|
    ne_zero_of_lt_one hv

theorem one_lt_iff_of_lt_one_iff {v w : AbsoluteValue K ℝ}
    (h : ∀ x, v x < 1 ↔ w x < 1) (x : K) : 1 < v x ↔ 1 < w x :=
  ⟨fun hv => one_lt_of_lt_one (fun _ => (h _).1) hv,
    fun hw => one_lt_of_lt_one (fun _ => (h _).2) hw⟩

theorem eq_one_of_lt_one_iff {v w : AbsoluteValue K ℝ}
    (h : ∀ x, v x < 1 ↔ w x < 1) {x : K} (hv : v x = 1) : w x = 1 := by
  cases eq_or_lt_of_le (not_lt.1 <| (h x).not.1 hv.not_lt) with
  | inl hl => rw [← hl]
  | inr hr => rw [← one_lt_iff_of_lt_one_iff h] at hr; linarith

theorem eq_one_iff_of_lt_one_iff {v w : AbsoluteValue K ℝ}
    (h : ∀ x, v x < 1 ↔ w x < 1) (x : K) : v x = 1 ↔ w x = 1 :=
  ⟨fun hv => eq_one_of_lt_one_iff h hv, fun hw => eq_one_of_lt_one_iff (fun _ => (h _).symm) hw⟩

theorem pos_of_pos {v : AbsoluteValue K ℝ} {a : K} (w : AbsoluteValue K ℝ) (hv : 0 < v a) :
    0 < w a := by
  rwa [AbsoluteValue.pos_iff] at hv ⊢

theorem lt_one_iff_of_lt_one_imp (hv : ∃ x, 1 < v x) (h : ∀ x, v x < 1 → w x < 1) {a : K} :
    v a < 1 ↔ w a < 1:= by
  let ⟨x₀, hx₀⟩ := exists_lt_one_of_exists_one_lt hv
  refine ⟨h a, fun hw => ?_⟩
  by_contra! hv
  have (n : ℕ) : w x₀ < w a ^ n := by
    have : v (x₀ * (1 / a ^ n)) < 1 := by
      rw [mul_one_div_pow_lt_iff _ (by linarith)]
      exact lt_of_lt_of_le hx₀.2 <| one_le_pow₀ hv
    exact mul_one_div_pow_lt_iff _ (pos_of_pos w (by linarith)) |>.1 <| h _ this
  have hcontr : Filter.Tendsto (fun (_ : ℕ) => w x₀) Filter.atTop (𝓝 0) := by
    have hwn : Filter.Tendsto (fun n => w.norm a ^ n) Filter.atTop (𝓝 0) := by
      simp only [tendsto_pow_atTop_nhds_zero_iff, abs_norm]
      exact hw
    have hwn' : ∀ᶠ n in Filter.atTop, w (x₀) ≤ w.norm a ^ n := by
      simp only [Filter.eventually_atTop, ge_iff_le]
      exact ⟨1, fun n _ => le_of_lt (this n)⟩
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      hwn (Filter.Eventually.of_forall fun (_ : ℕ) => w.nonneg x₀) hwn'
  linarith [tendsto_nhds_unique hcontr tendsto_const_nhds, pos_of_pos w hx₀.1]

theorem log_div_image_eq_singleton_of_le_one_iff {v w : AbsoluteValue K ℝ}
    (hv : ∃ x, 1 < v x)
    (h : ∀ x, v x < 1 ↔ w x < 1) :
    let f : K → ℝ := fun a => Real.log (v a) / Real.log (w a)
    ∃ (a : K) (_ : 1 < v a), ∀ (b : K) (_ : 1 < v b), f b = f a := by
  obtain ⟨a, ha⟩ := hv
  refine ⟨a, ha, fun b hb₁ => ?_⟩
  by_contra! hb₂
  wlog hwlog : Real.log (v b) / Real.log (w b) < Real.log (v a) / Real.log (w a) generalizing a b
  · exact this b hb₁ a ha hb₂.symm <| lt_of_le_of_ne (not_lt.1 hwlog) hb₂.symm
  have : Real.log (v b) / Real.log (v a) < Real.log (w b) / Real.log (w a) := by
    have hwa := (one_lt_iff_of_lt_one_iff h _).1 ha
    have hwb := (one_lt_iff_of_lt_one_iff h _).1 hb₁
    rw [div_lt_div_iff₀ (Real.log_pos ha) (Real.log_pos hwa)]
    nth_rw 2 [mul_comm]
    rwa [← div_lt_div_iff₀ (Real.log_pos hwb) (Real.log_pos hwa)]
  let ⟨q, hq⟩ := exists_rat_btwn this
  rw [← Rat.num_div_den q, Rat.cast_div, Rat.cast_intCast, Rat.cast_natCast] at hq
  have h₀ : v (b ^ q.den / a ^ q.num) < 1 := by
    have := hq.1
    rwa [div_lt_div_iff₀ (Real.log_pos ha) (by simp only [Nat.cast_pos, q.den_pos]), mul_comm,
      ← Real.log_pow, ← Real.log_zpow, Real.log_lt_log_iff (pow_pos (by linarith) _)
      (zpow_pos (by linarith) _), ← div_lt_one (zpow_pos (by linarith) _),
      ← map_pow, ← map_zpow₀, ← map_div₀] at this
  have h₁ : 1 < w (b ^ q.den / a ^ q.num) := by
    have hwa := (one_lt_iff_of_lt_one_iff h _).1 ha
    letI := (one_lt_iff_of_lt_one_iff h _).1 hb₁
    have := hq.2
    rw [div_lt_div_iff₀ (by simp only [Nat.cast_pos, q.den_pos]) (Real.log_pos hwa)] at this
    nth_rw 2 [mul_comm] at this
    rwa [← Real.log_pow, ← Real.log_zpow,
      Real.log_lt_log_iff (zpow_pos (by linarith) _) (pow_pos (by linarith) _),
      ← one_lt_div (zpow_pos (by linarith) _), ← map_pow, ← map_zpow₀, ← map_div₀] at this
  exact not_lt_of_lt ((h _).1 h₀) h₁

theorem exists_rpow_of_one_lt {v w : AbsoluteValue K ℝ} (hv : ∃ x, 1 < v x)
    (h : ∀ x, v x < 1 ↔ w x < 1) :
    ∃ (t : ℝ) (_ : 0 < t), ∀ x, 1 < v x → v x = w x ^ t := by
  obtain ⟨a, ha, hlog⟩ := log_div_image_eq_singleton_of_le_one_iff hv h
  refine ⟨Real.log (v a) / Real.log (w a),
    div_pos (Real.log_pos ha) (Real.log_pos ((one_lt_iff_of_lt_one_iff h a).1 ha)), fun b hb => ?_⟩
  simp_rw [← hlog b hb]
  letI := (one_lt_iff_of_lt_one_iff h b).1 hb
  rw [div_eq_inv_mul, Real.rpow_mul (w.nonneg _), Real.rpow_inv_log (by linarith) (by linarith),
    Real.exp_one_rpow, Real.exp_log (by linarith)]

open Real in
theorem eq_rpow_iff_lt_one_iff (v w : AbsoluteValue K ℝ) (hv : ∃ x, 1 < v x) :
    (∃ (t : ℝ) (_ : 0 < t), ∀ x, v x = (w x) ^ t) ↔ (∀ x, v x < 1 ↔ w x < 1) := by
  refine ⟨fun ⟨t, ht, h⟩ x => h x ▸ Real.rpow_lt_one_iff' (w.nonneg _) ht, fun h => ?_⟩
  suffices : ∃ (t : ℝ) (_ : t > 0), ∀ x, 1 < v x → v x = w x ^ t
  · obtain ⟨t, ht, hsuff⟩ := this
    refine ⟨t, ht, fun x => ?_⟩
    by_cases h₀ : v x = 0
    · rw [(map_eq_zero v).1 h₀, map_zero, map_zero, zero_rpow (by linarith)]
    · by_cases h₁ : v x = 1
      · rw [h₁, (eq_one_iff_of_lt_one_iff h x).1 h₁, one_rpow]
      · by_cases h₂ : 0 < v x ∧ v x < 1
        · rw [← inv_inj, ← map_inv₀ v, hsuff _ (map_inv₀ v _ ▸ one_lt_inv_iff₀.2 h₂), map_inv₀,
            Real.inv_rpow (w.nonneg _)]
        · rw [← one_lt_inv_iff₀, ← map_inv₀, not_lt] at h₂
          rw [← ne_eq, ← inv_ne_one, ← map_inv₀] at h₁
          exact hsuff _ <| (inv_lt_one_iff.1 <| lt_of_le_of_ne h₂ h₁).resolve_left
            ((map_ne_zero v).1 h₀)
  exact exists_rpow_of_one_lt hv h

theorem exists_lt_one_one_le_of_ne_rpow (hv : ∃ x, 1 < v x)
    (h : ¬∃ (t : ℝ) (_ : 0 < t), ∀ x, v x = (w x) ^ t) :
    ∃ a : K, v a < 1 ∧ 1 ≤ w a := by
  contrapose! h
  exact eq_rpow_iff_lt_one_iff _ _ hv |>.2 <| fun  _ => lt_one_iff_of_lt_one_imp hv h

theorem ne_pow_symm (h : ¬∃ (t : ℝ) (_ : 0 < t), ∀ x, v x = (w x) ^ t) :
    ¬∃ (t : ℝ) (_ : 0 < t), ∀ x, w x = (v x) ^ t := by
  simp only [exists_prop, not_exists, not_and, not_forall] at h ⊢
  refine fun t ht => let ⟨x, hx⟩ := h t⁻¹ (_root_.inv_pos.2 ht); ⟨x, ?_⟩
  contrapose! hx
  exact Real.eq_rpow_inv (v.nonneg _) (w.nonneg _) (by linarith) |>.2 hx.symm

theorem exists_lt_one_one_lt_of_ne_rpow
    (hv : ∃ x, 1 < v x)
    (hw : ∃ x, 1 < w x)
    (h : ¬∃ (t : ℝ) (_ : 0 < t), ∀ x, v x = (w x) ^ t) :
    ∃ a : K, 1 < v a ∧ w a < 1 := by
  let ⟨a, ha⟩ := exists_lt_one_one_le_of_ne_rpow hv h
  let ⟨b, hb⟩ := exists_lt_one_one_le_of_ne_rpow hw (ne_pow_symm h)
  refine ⟨b / a, ?_⟩
  simp only [map_div₀]
  exact ⟨one_lt_div (pos_of_pos v (by linarith)) |>.2 (by linarith),
    div_lt_one (by linarith) |>.2 (by linarith)⟩

/-!
## Results about limits of absolute values
-/

theorem one_add_ne_zero_of_abs_ne_one {a : K} (ha : v a ≠ 1) :
    1 + a ≠ 0 := by
  contrapose! ha
  rw [eq_neg_add_of_add_eq ha, add_zero, v.map_neg, v.map_one]

theorem one_add_pow_ne_zero_of_abs_ne_one {n : ℕ} [CharZero K] {a : K} (ha : v a ≠ 1) :
    1 + a ^ n ≠ 0 := by
  by_cases h₀ : n = 0
  · rw [h₀, pow_zero, ne_eq, add_self_eq_zero]; exact one_ne_zero
  · have : v (a ^ n) ≠ 1 := by
      rwa [ne_eq, map_pow, pow_eq_one_iff_of_nonneg (AbsoluteValue.nonneg _ _) h₀]
    exact one_add_ne_zero_of_abs_ne_one this

theorem apply_one_add_pow_le (a : K) (n : ℕ) : v (1 + a ^ n) ≤ 1 + v a ^ n :=
  le_trans (v.add_le _ _) (by rw [map_one, map_pow])

theorem one_sub_pow_le (a : K) (n : ℕ) : 1 - v a ^ n ≤ v (1 + a ^ n) :=
  le_trans (by rw [map_one, map_pow]) (v.le_add _ _)

theorem tendsto_pow_mul_atTop {a b : K} (ha : 1 < v a) (hb : 0 < v b) :
    Filter.Tendsto (fun (n : ℕ) => v (a ^ n * b)) Filter.atTop Filter.atTop := by
  simp_rw [map_mul v, map_pow]
  exact Filter.Tendsto.atTop_mul_const hb (tendsto_pow_atTop_atTop_of_one_lt ha)

theorem tendsto_pow_mul_zero {a : K} (ha : v a < 1) (b : K) :
    Filter.Tendsto (fun (n : ℕ) => v (a ^ n * b)) Filter.atTop (𝓝 0) := by
  simp_rw [map_mul, map_pow]
  rw [← zero_mul (v b)]
  exact Filter.Tendsto.mul_const _ <| tendsto_pow_atTop_nhds_zero_of_lt_one (v.nonneg _) ha

theorem tendsto_one_add_pow {a : K} (ha : v a < 1) :
    Filter.Tendsto (fun n => 1 + (v a ^ n)) Filter.atTop (𝓝 1) := by
  nth_rw 2 [← add_zero 1]
  apply Filter.Tendsto.const_add
  apply tendsto_pow_atTop_nhds_zero_of_lt_one (v.nonneg _) ha

theorem tendsto_one_sub_pow {a : K} (ha : v a < 1) :
    Filter.Tendsto (fun n => 1 - (v a ^ n)) Filter.atTop (𝓝 1) := by
  nth_rw 2 [← sub_zero 1]
  apply Filter.Tendsto.const_sub
  apply tendsto_pow_atTop_nhds_zero_of_lt_one (v.nonneg _) ha

theorem tendsto_div_one_add_pow_nhds_one {a : K} (ha : v a < 1) :
    Filter.Tendsto (fun (n : ℕ) => v (1 / (1 + a ^ n))) Filter.atTop (𝓝 1) := by
  simp_rw [v.isAbsoluteValue.abv_div, v.map_one]
  nth_rw 2 [show (1 : ℝ) = 1 / 1 by norm_num]
  apply Filter.Tendsto.div tendsto_const_nhds _ one_ne_zero
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le (tendsto_one_sub_pow ha) (tendsto_one_add_pow ha)
    (one_sub_pow_le _) (apply_one_add_pow_le _)

theorem tendsto_pow_mul_div_one_add_pow_one {a : K}
    (ha : v a < 1) (b : K) :
    Filter.Tendsto (fun (n : ℕ) => v (1 / (1 + a ^ n) * b)) Filter.atTop (𝓝 (v b)) := by
  simp_rw [map_mul]
  nth_rw 2 [← one_mul (v b)]
  apply Filter.Tendsto.mul_const _ (tendsto_div_one_add_pow_nhds_one ha)

theorem tendsto_pow_div_one_add_pow_zero {a : K}
    (ha : 1 < v a) :
    Filter.Tendsto (fun (n : ℕ) => v (1 / (1 + a ^ n))) Filter.atTop (𝓝 0) := by
  simp_rw [div_eq_mul_inv, one_mul, map_inv₀, fun n => add_comm 1 (a ^ n)]
  apply Filter.Tendsto.inv_tendsto_atTop
  apply Filter.tendsto_atTop_mono (fun n => v.le_add _ _)
  simp_rw [map_one, map_pow v]
  apply Filter.tendsto_atTop_add_right_of_le _ _ _ (fun _ => le_rfl)
  refine tendsto_atTop_of_geom_le (by simp only [pow_zero, inv_one, zero_lt_one]) ha fun n => ?_
  rw [← map_pow, ← map_pow, ← map_mul, pow_succ']

theorem tendsto_pow_mul_div_one_add_pow_zero {a : K}
    (ha : 1 < v a) (b : K) :
    Filter.Tendsto (fun (n : ℕ) => v ((1 / (1 + a ^ n)) * b)) Filter.atTop (𝓝 0) := by
  simp_rw [map_mul]
  rw [← zero_mul (v b)]
  apply Filter.Tendsto.mul_const _ (tendsto_pow_div_one_add_pow_zero ha)

open Filter in
theorem exists_tendsto_zero_tendsto_atTop_tendsto_const
    {ι : Type*} {v : ι → AbsoluteValue K ℝ} {w : AbsoluteValue K ℝ} {a b : K} {i : ι}
    (ha : 1 < v i a) (haj : ∀ j ≠ i, v j a < 1) (haw : w a = 1) (hb : 1 < v i b) (hbw : w b < 1) :
    ∃ c : ℕ → K,
      Tendsto (fun n => (v i).norm (c n)) atTop atTop ∧
        (∀ j ≠ i, Tendsto (fun n => (v j).norm (c n)) atTop (𝓝 0)) ∧
          (∀ n, w (c n) < 1) := by
  refine ⟨fun n => a ^ n * b, tendsto_pow_mul_atTop ha (show 0 < v i b by linarith),
    fun j hj => tendsto_pow_mul_zero (haj j hj) b, fun _ => ?_⟩
  simp only [map_mul, map_pow, haw, one_pow, one_mul]
  exact hbw

  theorem Finset.le_sup_dite_pos {α β : Type*} [SemilatticeSup α] [OrderBot α] {s : Finset β}
    (p : β → Prop) [DecidablePred p] {f : (b : β) → p b → α} {g : (b : β) → ¬p b → α} {b : β}
    (h₀ : b ∈ s) (h₁ : p b) :
    f b h₁ ≤ s.sup fun i => if h : p i then f i h else g i h := by
  have : f b h₁ = (fun i => if h : p i then f i h else g i h) b := by simp [h₁]
  rw [this]
  apply Finset.le_sup h₀

  theorem Finset.le_sup_dite_neg {α β : Type*} [SemilatticeSup α] [OrderBot α] {s : Finset β}
    (p : β → Prop) [DecidablePred p] {f : (b : β) → p b → α} {g : (b : β) → ¬p b → α} {b : β}
    (h₀ : b ∈ s) (h₁ : ¬p b) :
    g b h₁ ≤ s.sup fun i => if h : p i then f i h else g i h := by
  have : g b h₁ = (fun i => if h : p i then f i h else g i h) b := by simp [h₁]
  rw [this]
  apply Finset.le_sup h₀

theorem exists_le_one_one_lt_of_eq_one
    {ι : Type*} [Fintype ι] {v : ι → AbsoluteValue K ℝ} {w : AbsoluteValue K ℝ} {a b : K} {i : ι}
    (ha : 1 < v i a) (haj : ∀ j ≠ i, v j a < 1) (haw : w a = 1) (hb : 1 < v i b) (hbw : w b < 1) :
    ∃ k : K, 1 < v i k ∧ (∀ j ≠ i, v j k < 1) ∧ w k < 1 := by
  let ⟨c, hc⟩ := exists_tendsto_zero_tendsto_atTop_tendsto_const ha haj haw hb hbw
  simp_rw [Metric.tendsto_nhds, Filter.tendsto_atTop_atTop, Filter.eventually_atTop,
    dist_zero_right, norm_norm] at hc
  choose r₁ hr₁ using hc.1 2
  choose rₙ hrₙ using fun j hj => hc.2.1 j hj 1 (by linarith)
  let r := Finset.univ.sup fun j => if h : j = i then r₁ else rₙ j h
  refine ⟨c r, lt_of_lt_of_le (by linarith) (hr₁ r ?_), fun j hj => ?_, hc.2.2 r⟩
  · exact Finset.le_sup_dite_pos (p := fun j => j = i) (f := fun _ _ => r₁) (Finset.mem_univ _) rfl
  · exact hrₙ j hj _ <| Finset.le_sup_dite_neg (fun j => j = i) (Finset.mem_univ j) _

open Filter in
theorem exists_tendsto_const_tendsto_zero_tendsto_const
    {ι : Type*} {v : ι → AbsoluteValue K ℝ} {w : AbsoluteValue K ℝ} {a : K} {i : ι}
    (b : K) (ha : 1 < v i a) (haj : ∀ j ≠ i, v j a < 1) (haw : 1 < w a) :
    ∃ c : ℕ → K,
      Tendsto (fun n => (v i).norm (c n)) atTop (𝓝 ((v i).norm b)) ∧
        (∀ j ≠ i, Tendsto (fun n => (v j).norm (c n)) atTop (𝓝 0)) ∧
          Tendsto (fun n => w.norm (c n)) atTop (𝓝 (w.norm b)) :=
  ⟨fun n => (1 / (1 + a⁻¹ ^ n) * b),
    tendsto_pow_mul_div_one_add_pow_one (map_inv₀ (v i) _ ▸ inv_lt_one_of_one_lt₀ ha) b,
      fun j hj => tendsto_pow_mul_div_one_add_pow_zero
        (map_inv₀ (v j) _ ▸ (one_lt_inv₀ (pos_of_pos (v j) (by linarith))).2 (haj j hj)) b,
          tendsto_pow_mul_div_one_add_pow_one (map_inv₀ w _ ▸ inv_lt_one_of_one_lt₀ haw) b⟩

open Filter in
theorem exists_one_lt_of_tendsto_const {v : AbsoluteValue K ℝ} {b : K} {c : ℕ → K}
    (hb : 1 < v b) (hc : Tendsto (fun n => v.norm (c n)) atTop (𝓝 (v.norm b))) :
    ∃ N, ∀ r ≥ N, 1 < v (c r) := by
  rw [Metric.tendsto_atTop] at hc
  let ⟨N, hN⟩ := hc (dist 1 (v b) / 2) (div_pos (dist_pos.2 (by linarith)) (by norm_num))
  refine ⟨N, fun r hr => ?_⟩
  simp_rw [Real.dist_eq, abs_eq_neg_self.2 (show 1 - v b ≤ 0 by linarith), neg_sub] at hN
  specialize hN r hr
  by_cases h : v b < v (c r)
  · exact lt_trans hb h
  · rw [abs_eq_neg_self.2 (by exact tsub_nonpos.2 (not_lt.1 h))] at hN
    exact (sub_lt_sub_iff_left _).1 <| neg_sub _ (v.norm b) ▸ lt_trans hN <|
      div_two_lt_of_pos (by linarith)

open Filter in
theorem exists_lt_one_of_tendsto_const {v : AbsoluteValue K ℝ} {b : K} {c : ℕ → K}
    (hb : v b < 1)
    (hc : Tendsto (fun n => v.norm (c n)) atTop (𝓝 (v.norm b))) :
    ∃ N, ∀ r ≥ N, v (c r) < 1 := by
  rw [Metric.tendsto_atTop] at hc
  let ⟨N, hN⟩ := hc (dist 1 (v b) / 2) (div_pos (dist_pos.2 (by linarith)) (by norm_num))
  refine ⟨N, fun r hr => ?_⟩
  specialize hN r hr
  simp_rw [Real.dist_eq, abs_eq_self.2 (show 0 ≤ 1 - v b by linarith)] at hN
  by_cases h : v b ≤ v (c r)
  · rw [abs_eq_self.2 (by exact sub_nonneg_of_le h)] at hN
    exact (sub_lt_sub_iff_right _).1 <| lt_trans hN <| div_two_lt_of_pos (by linarith)
  · exact lt_trans (not_le.1 h) hb

theorem exists_lt_one_one_lt_of_one_lt
    {ι : Type*} [Fintype ι] {v : ι → AbsoluteValue K ℝ} {w : AbsoluteValue K ℝ} {a b : K} {i : ι}
    (ha : 1 < v i a) (haj : ∀ j ≠ i, v j a < 1) (haw : 1 < w a) (hb : 1 < v i b) (hbw : w b < 1) :
    ∃ k : K, 1 < v i k ∧ (∀ j ≠ i, v j k < 1) ∧ w k < 1 := by
  let ⟨c, hc⟩ := exists_tendsto_const_tendsto_zero_tendsto_const b ha haj haw
  have hₙ := fun j hj => Metric.tendsto_nhds.1 <| hc.2.1 j hj
  simp_rw [Filter.eventually_atTop, dist_zero_right] at hₙ
  choose r₁ hr₁ using exists_one_lt_of_tendsto_const hb hc.1
  choose rₙ hrₙ using fun j hj => hₙ j hj 1 (by linarith)
  choose rN hrN using exists_lt_one_of_tendsto_const hbw hc.2.2
  let r := max (Finset.univ.sup fun j => if h : j = i then r₁ else rₙ j h) rN
  refine ⟨c r, hr₁ r ?_, fun j hj => ?_, ?_⟩
  · exact le_max_iff.2 <| Or.inl <|
      Finset.le_sup_dite_pos (p := fun j => j = i) (f := fun _ _ => r₁) (Finset.mem_univ _) rfl
  · simp only [norm_norm] at hrₙ
    exact hrₙ j hj _ <| le_max_iff.2 <| Or.inl <|
      Finset.le_sup_dite_neg (fun j => j = i) (Finset.mem_univ j) _
  · exact hrN _ <| le_max_iff.2 (Or.inr le_rfl)

theorem Fin.castPred_ne_zero {n : ℕ} {j : Fin (n + 2)} (h₁ : j ≠ Fin.last (n + 1)) (h₂ : j ≠ 0) :
    Fin.castPred j h₁ ≠ 0 := by
  contrapose! h₂
  rwa [← Fin.castPred_zero, Fin.castPred_inj] at h₂

theorem Fin.pairwise_forall_two {n : ℕ} {r : Fin (n + 2) → Fin (n + 2) → Prop} (h : Pairwise r) :
    Pairwise (r.onFun ![0, Fin.last _]) := by
  apply Pairwise.comp_of_injective h
  simp [Function.Injective, Fin.forall_fin_two]

theorem exists_one_lt_lt_one_pi {n : ℕ} {v : Fin (n + 2) → AbsoluteValue K ℝ}
    (h : ∀ i, ∃ x, 1 < v i x)
    (hv : Pairwise fun i j => ¬∃ (t : ℝ) (_ : 0 < t), ∀ x, v i x = (v j x) ^ t) :
    ∃ (a : K), 1 < v 0 a ∧ ∀ j ≠ 0, v j a < 1 := by
  induction n using Nat.case_strong_induction_on with
  | hz =>
    let ⟨a, ha⟩ := (v 0).exists_lt_one_one_lt_of_ne_rpow (h 0) (h 1) (hv zero_ne_one)
    exact ⟨a, ha.1, by simp [Fin.forall_fin_two]; exact ha.2⟩
  | hi n ih =>
    let ⟨a, ha⟩ := ih n le_rfl (fun _ => h _) (hv.comp_of_injective <| Fin.castSucc_injective _)
    let ⟨b, hb⟩ := ih 0 (by linarith) (fun _ => h _) <| Fin.pairwise_forall_two hv
    simp [Fin.forall_fin_two] at hb
    by_cases ha₀ : v (Fin.last _) a < 1
    · refine ⟨a, ha.1, fun j hj => ?_⟩
      by_cases hj' : j = Fin.last (n + 2)
      · exact hj' ▸ ha₀
      · exact ha.2 (Fin.castPred _ (ne_eq _ _ ▸  hj')) <| Fin.castPred_ne_zero _ hj
    · by_cases ha₁ : v (Fin.last _) a = 1
      · let ⟨k, hk⟩ := exists_le_one_one_lt_of_eq_one (v := fun i : Fin (n + 2) => v i.castSucc)
          ha.1 ha.2 ha₁ hb.1 hb.2
        refine ⟨k, hk.1, fun j hj => ?_⟩
        by_cases h : j ≠ Fin.last (n + 2)
        · exact ne_eq _ _ ▸ hk.2.1 (j.castPred h) <| Fin.castPred_ne_zero _ hj
        · exact not_ne_iff.1 h ▸ hk.2.2
      · let ⟨k, hk⟩ := exists_lt_one_one_lt_of_one_lt (v := fun i : Fin (n + 2) => v i.castSucc)
          ha.1 ha.2 (lt_of_le_of_ne (not_lt.1 ha₀) (ne_eq _ _ ▸ ha₁).symm) hb.1 hb.2
        refine ⟨k, hk.1, fun j hj => ?_⟩
        by_cases h : j ≠ Fin.last _
        · apply ne_eq _ _ ▸ hk.2.1 (j.castPred h)
          rwa [← Fin.castPred_zero, Fin.castPred_inj]
        · exact not_ne_iff.1 h ▸ hk.2.2

end AbsoluteValue

namespace NumberField.InfinitePlace

open AbsoluteValue

variable {K : Type*} [Field K] {v w : InfinitePlace K}

variable (w)

theorem pos_of_pos {x : K} (hv : 0 < v x) : 0 < w x := by
  rw [coe_apply] at hv ⊢
  exact v.1.pos_of_pos _ hv

variable {w}

theorem rpow_eq_one_of_eq_rpow {t : ℝ} (h : ∀ x, v x = (w x) ^ t) : t = 1 := by
  let ⟨ψv, hψv⟩ := v.2
  let ⟨ψw, hψw⟩ := w.2
  simp only [coe_apply, ← hψv, ← hψw] at h
  have := congrArg (Real.logb 2) (h 2)
  simp only [place_apply, map_ofNat, RCLike.norm_ofNat, Nat.one_lt_ofNat, Real.logb_self_eq_one,
    Nat.ofNat_pos, ne_eq, OfNat.ofNat_ne_one, not_false_eq_true, Real.logb_rpow] at this
  exact this.symm

theorem eq_of_eq_rpow (h : ∃ (t : ℝ) (_ : 0 < t), ∀ x, v x = (w x) ^ t) : v = w := by
  let ⟨t, _, h⟩ := h
  simp only [rpow_eq_one_of_eq_rpow h, Real.rpow_one] at h
  exact Subtype.ext <| AbsoluteValue.ext h

theorem eq_rpow_of_eq (h : v = w) : ∃ (t : ℝ) (_ : 0 < t), ∀ x, v x = (w x) ^ t :=
  ⟨1, by linarith, fun x => by rw [h, Real.rpow_one]⟩

variable (v)

theorem exists_one_lt : ∃ x, 1 < v x := by
  refine ⟨2, let ⟨φ, hφ⟩ := v.2; ?_⟩
  simp only [coe_apply, ← hφ, place_apply, map_ofNat, RCLike.norm_ofNat, Nat.one_lt_ofNat]

variable {v}

open Filter in
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

theorem exists_one_lt_lt_one [NumberField K] (h : 1 < Fintype.card (InfinitePlace K)) :
    ∃ (x : K), 1 < v x ∧ ∀ w ≠ v, w x < 1 := by
  let ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin (InfinitePlace K)
  have : 1 < n := by linarith [Fintype.card_fin n ▸ Fintype.card_eq.2 ⟨e⟩]
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' this
  let ⟨m, hm⟩ := e.symm.surjective v
  let e₀ := e.trans (Equiv.swap 0 m)
  let ⟨x, hx⟩ := AbsoluteValue.exists_one_lt_lt_one_pi (fun i => (e₀.symm i).exists_one_lt)
      (fun i j hj => mt eq_of_eq_rpow <| e₀.symm.injective.ne hj)
  refine ⟨x, hm ▸ hx.1, fun w hw => ?_⟩
  have he₀ : e₀ v = 0 := by simp [e₀, e.symm_apply_eq.1 hm]
  exact e₀.symm_apply_apply _ ▸ hx.2 (e₀ w) <| he₀ ▸ e₀.injective.ne hw

variable (K)

open Filter in
theorem denseRange_algebraMap_pi [NumberField K] :
    DenseRange <| algebraMap K ((v : InfinitePlace K) → WithAbs v.1) := by
  by_cases hcard : Fintype.card (InfinitePlace K) = 1
  · -- If there is only one infinite place this is the identity map
    letI := Fintype.equivFinOfCardEq hcard |>.unique
    let f := Homeomorph.funUnique (InfinitePlace K) (WithAbs this.default.1)
    convert DenseRange.comp f.symm.surjective.denseRange denseRange_id f.continuous_invFun <;>
    exact this.uniq _
  -- We have to show that for some `(zᵥ)ᵥ` there is a `y` in `K` that is arbitrarily close to `z`
  -- under the embedding `y ↦ (y)ᵥ`
  refine Metric.denseRange_iff.2 fun z r hr => ?_
  -- For some `v`, by previous results we can select a sequence `xᵥ → 1` in `v`'s topology
  -- and `→ 0` in any other infinite place topology
  have (v : InfinitePlace K) : ∃ (x : ℕ → WithAbs v.1),
      Tendsto (fun n => x n) atTop (𝓝 1) ∧ ∀ w ≠ v,
        Tendsto (β := WithAbs w.1) (fun n => x n) atTop (𝓝 0) := by
    haveI : 0 < Fintype.card (InfinitePlace K) := Fintype.card_pos
    let ⟨_, hx⟩ := v.exists_one_lt_lt_one (by omega)
    exact exists_tendsto_one_tendsto_zero hx.1 hx.2
  choose x h using this
  -- Define the sequence `y = ∑ v, xᵥ * zᵥ` in `K`
  let y := fun n => ∑ v, x v n * z v
  -- At each place `w` the limit of `y` with respect to `w`'s topology is `z w`.
  have : Tendsto (fun n w => ((∑ v, x v n * z v) : WithAbs w.1)) atTop (𝓝 z) := by
    refine tendsto_pi_nhds.2 fun w => ?_
    simp_rw [← Finset.sum_ite_eq_of_mem _ _ _ (Finset.mem_univ w)]
    -- In `w`'s topology we have that `x v n * z v → z v`  if `v = w` else `→ 0`
    refine tendsto_finset_sum _ fun v _ => ?_
    by_cases hw : w = v
    · -- because `x w → 1` in `w`'s topology
      simp only [hw, if_true, ← congrArg (β := ℕ → K) x hw, ← congrArg z hw]
      nth_rw 2 [← one_mul (z w)]
      exact Tendsto.mul_const _ (h w).1
    · -- while `x v → 0` in `w`'s topology (v ≠ w)
      simp only [hw, if_false]
      rw [← zero_mul (z v)]
      exact Filter.Tendsto.mul_const _ <| (h v).2 w hw
  simp_rw [Metric.tendsto_atTop] at this
  let ⟨N, h⟩ := this r hr
  exact ⟨y N, dist_comm z (algebraMap K _ (y N)) ▸ h N le_rfl⟩

namespace Completion

variable (K : Type*) [Field K] {v w : InfinitePlace K}

theorem denseRange_algebraMap_pi [NumberField K] :
    DenseRange <| algebraMap K (InfiniteAdeleRing K) := by
  apply DenseRange.comp (DenseRange.piMap (fun _ => UniformSpace.Completion.denseRange_coe))
    (InfinitePlace.denseRange_algebraMap_pi K)
    <| Continuous.piMap (fun _ => UniformSpace.Completion.continuous_coe _)

theorem denseRange_algebraMap_subtype_pi (p : InfinitePlace K → Prop) [NumberField K] :
    DenseRange <| algebraMap K ((v : Subtype p) → v.1.Completion) := by
  apply DenseRange.comp (g := Subtype.restrict p)
    (f := algebraMap K ((v : InfinitePlace K) → v.1.Completion))
  · exact Subtype.surjective_restrict (β := fun v => v.1.Completion) p |>.denseRange
  · exact denseRange_algebraMap_pi K
  · exact continuous_pi (fun _ => continuous_apply _)

end NumberField.InfinitePlace.Completion
