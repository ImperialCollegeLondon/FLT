import Mathlib.Algebra.Order.AbsoluteValue.Basic
import FLT.Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.Algebra.EuclideanDomain.Field
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open scoped Topology

namespace AbsoluteValue

variable {F S : Type*} [Field F] [Field S] [LinearOrder S] [IsStrictOrderedRing S]
  {v w : AbsoluteValue F S}

/--
If `v` is a nontrivial absolute value, and `w` is another absolute value such that `w x < 1`
if `v x < 1`, then we must also have `v x < 1` if `w x < 1`.
-/
theorem lt_one_iff_of_lt_one_imp [Archimedean S] [TopologicalSpace S] [OrderTopology S]
      (hv : v.IsNontrivial) (h : ∀ x, v x < 1 → w x < 1) {a : F} :
    v a < 1 ↔ w a < 1:= by
  let ⟨x₀, hx₀⟩ := hv.exists_abv_lt_one
  refine ⟨h a, fun hw => ?_⟩
  by_contra! hv
  have (n : ℕ) : w x₀ < w a ^ n := by
    have : v (x₀ * (1 / a ^ n)) < 1 := by
      rw [mul_one_div_pow_lt_iff _ (by linarith)]
      exact lt_of_lt_of_le hx₀.2 <| one_le_pow₀ hv
    exact mul_one_div_pow_lt_iff _ (pos_of_pos w (by linarith)) |>.1 <| h _ this
  have hcontr : Filter.Tendsto (fun (_ : ℕ) => w x₀) Filter.atTop (𝓝 0) := by
    have hwn : Filter.Tendsto (fun n => w a ^ n) Filter.atTop (𝓝 0) := by
      have := abs_eq_self.2 (w.nonneg _) ▸ hw
      exact tendsto_pow_atTop_nhds_zero_iff.2 this
    have hwn' : ∀ᶠ n in Filter.atTop, w x₀ ≤ w a ^ n := by
      simp only [Filter.eventually_atTop, ge_iff_le]
      exact ⟨1, fun n _ => le_of_lt (this n)⟩
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      hwn (Filter.Eventually.of_forall fun (_ : ℕ) => w.nonneg x₀) hwn'
  linarith [tendsto_nhds_unique hcontr tendsto_const_nhds, w.pos hx₀.1]

/--
If `v` and `w` are two real absolute values on `F`, `v` is non-trivial, and `v x < 1` if and
only if `w x < 1`, then `log (v a) / log (w a)` is constant for all `a ∈ K`.
-/
theorem log_div_image_eq_singleton_of_le_one_iff {v w : AbsoluteValue F ℝ}
    (hv : v.IsNontrivial)
    (h : ∀ x, v x < 1 ↔ w x < 1) :
    let f : F → ℝ := fun a => Real.log (v a) / Real.log (w a)
    ∃ (a : F) (_ : 1 < v a), ∀ (b : F) (_ : 1 < v b), f b = f a := by
  obtain ⟨a, ha⟩ := hv.exists_abv_gt_one
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
  exact not_lt_of_gt ((h _).1 h₀) h₁

theorem exists_rpow_of_one_lt {v w : AbsoluteValue F ℝ} (hv : v.IsNontrivial)
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
/--
Let `v` and `w` be two real absolute values on `F`, where `v` is non-trivial. The condition that
`v x < 1` if and only if `w x < 1` is equivalent to the condition that `v = w ^ t` for some
real `t > 0`.
-/
theorem eq_rpow_iff_lt_one_iff {v : AbsoluteValue F ℝ} (w : AbsoluteValue F ℝ)
    (hv : v.IsNontrivial) :
    (∃ (t : ℝ) (_ : 0 < t), ∀ x, v x = (w x) ^ t) ↔ (∀ x, v x < 1 ↔ w x < 1) := by
  refine ⟨fun ⟨t, ht, h⟩ x => h x ▸ Real.rpow_lt_one_iff' (w.nonneg _) ht, fun h => ?_⟩
  suffices ∃ (t : ℝ) (_ : t > 0), ∀ x, 1 < v x → v x = w x ^ t by
    obtain ⟨t, ht, hsuff⟩ := this
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

/--
If `v` is non-trivial and `v = w ^ t` for some `t > 0`, then we can find an `a ∈ F` such that
`v a < 1` while `1 ≤ w a`.
-/
theorem exists_lt_one_one_le_of_ne_rpow {v w : AbsoluteValue F ℝ}
    (hv : v.IsNontrivial)
    (h : ¬∃ (t : ℝ) (_ : 0 < t), ∀ x, v x = (w x) ^ t) :
    ∃ a : F, v a < 1 ∧ 1 ≤ w a := by
  contrapose! h
  exact eq_rpow_iff_lt_one_iff _ hv |>.2 <| fun  _ => lt_one_iff_of_lt_one_imp hv h

theorem ne_pow_symm {v w : AbsoluteValue F ℝ} (h : ¬∃ (t : ℝ) (_ : 0 < t), ∀ x, v x = (w x) ^ t) :
    ¬∃ (t : ℝ) (_ : 0 < t), ∀ x, w x = (v x) ^ t := by
  simp only [exists_prop, not_exists, not_and, not_forall] at h ⊢
  refine fun t ht => let ⟨x, hx⟩ := h t⁻¹ (_root_.inv_pos.2 ht); ⟨x, ?_⟩
  contrapose! hx
  exact Real.eq_rpow_inv (v.nonneg _) (w.nonneg _) (by linarith) |>.2 hx.symm

/--
If `v` and `w` are two non-trivial absolute values such that `v = w ^ t` for some `t > 0`, then
we can find an `a ∈ K` such that `1 < v a` while `w a  < 1`.
-/
theorem exists_one_lt_lt_one_of_ne_rpow {v w : AbsoluteValue F ℝ}
    (hv : v.IsNontrivial)
    (hw : w.IsNontrivial)
    (h : ¬∃ (t : ℝ) (_ : 0 < t), ∀ x, v x = (w x) ^ t) :
    ∃ a : F, 1 < v a ∧ w a < 1 := by
  let ⟨a, ha⟩ := exists_lt_one_one_le_of_ne_rpow hv h
  let ⟨b, hb⟩ := exists_lt_one_one_le_of_ne_rpow hw (ne_pow_symm h)
  refine ⟨b / a, ?_⟩
  simp only [map_div₀]
  exact ⟨one_lt_div (pos_of_pos v (by linarith)) |>.2 (by linarith),
    div_lt_one (by linarith) |>.2 (by linarith)⟩

end AbsoluteValue
