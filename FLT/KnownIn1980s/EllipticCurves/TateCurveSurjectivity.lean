/-
Copyright (c) 2026 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, William Coram, Samuel Yin
-/
module

import Mathlib.NumberTheory.TsumDivisorsAntidiagonal
import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean

public import FLT.KnownIn1980s.EllipticCurves.TateCurveGroupLaw
import FLT.Slop.NumberTheory.TsumDivisorsAntidiagonal

/-!
# The Tate curve `E_q`: surjectivity of the uniformisation

`WeierstrassCurve.exists_tateCurvePoint_eq` — every point of `E_q(k)` is `φ(u)` for some
`u ∈ kˣ` (Silverman, ATAEC V.4). Following Silverman's filtration proof, the argument climbs a
ladder of three "pieces", each an elementary valuation computation:

* *the formal-group piece* (`exists_tateCurvePoint_eq_of_one_lt`): points with `|x| > 1` are
  hit by parameters `u = 1 + t`, `0 < |t| < 1`; the parameter is produced by an ultrametric
  fixed-point argument on the annulus expansions of `X`, `Y` at `1 + t`, and identified by the
  unique-large-root lemma `tateCurve_eq_of_ratio_eq`;
* *the unit piece* (`exists_tateCurvePoint_eq_of_eq_one`): points with `|x| = 1` are hit by
  `u₀·(1 + t)` with `|u₀| = 1`: the explicit lift `u₀ = y²/x³` approximates the point to
  `O(q)` (`exists_tateCurve_unit_approx`), the difference lands in `|x| > 1`
  (`tateCurve_sub_of_close`), and the formal piece finishes;
* *the component piece* (`exists_tateCurvePoint_sub_component_zero`): points with `|x| < 1` fall
  into `ord q - 1` classes cut out by the valuations of `y` and `x + y` (Silverman's
  Lemmas 4.1.1–4.1.4: `tateCurve_component_trichotomy` and the coset lemmas
  `tateCurve_sub_of_same_U`/`_V`/`_W`); translating by `φ(ϖᵐ)` for `0 ≤ m < ord q` and
  applying the pigeonhole principle to these classes moves any point into `|x| ≥ 1`.

Fifth of the files split out of `TateCurveUniformisation`.
-/

@[expose] public section

open scoped WeierstrassCurve.Affine -- `(E⁄k).Point` notation for the group of `k`-points
open scoped PowerSeries -- `ℤ⟦X⟧` notation for `PowerSeries ℤ`
open scoped Topology -- `𝓝` notation for neighbourhood filters
open ValuativeRel -- `𝒪[k]` notation for the ring of integers of `k`, and `valuation`

-- Can be deleted when mathlib#41391 lands
set_option linter.overlappingInstances false

section Generic

/-- In a discretely valued semiring of rank at most one, every nonzero element of the value group
is an integer power of the maximal element `< 1`. (For the Tate curve: the classes `Uₙ`, `Vₙ`
of Silverman ATAEC V.4 Lemma 4.1.2 are indexed by powers of the uniformizer.) -/
theorem ValuativeRel.exists_zpow_uniformizer_eq {R : Type*} [Semiring R] [ValuativeRel R]
    [IsDiscrete R] [IsRankLeOne R] [IsNontrivial R] {γ : ValueGroupWithZero R} (hγ : γ ≠ 0) :
    ∃ n : ℤ, uniformizer R ^ n = γ := by
  obtain ⟨s⟩ := IsRankLeOne.nonempty (R := R)
  have hβ0 : 0 < s.emb (uniformizer R) := by simpa using s.strictMono uniformizer_pos
  have hβ1 : s.emb (uniformizer R) < 1 := by simpa using s.strictMono uniformizer_lt_one
  have hα0 : 0 < s.emb γ := by simpa using s.strictMono (zero_lt_iff.mpr hγ)
  obtain ⟨n, hn⟩ := exists_mem_Ioc_zpow hα0 ((one_lt_inv₀ hβ0).mpr hβ1)
  have h_lower : uniformizer R ^ (-n) < γ := s.strictMono.lt_iff_lt.mp (by simpa using hn.1)
  have h_upper : γ ≤ uniformizer R ^ (-(n + 1)) :=
    s.strictMono.le_iff_le.mp (by simpa using hn.2)
  have hδ_le : γ * uniformizer R ^ (n + 1) ≤ 1 :=
    (mul_le_mul_left h_upper _).trans_eq (zpow_neg_mul_zpow_self _ uniformizer_ne_zero)
  have hδ_lt : uniformizer R < γ * uniformizer R ^ (n + 1) := by
    simpa only [← zpow_add₀ uniformizer_ne_zero, neg_add_cancel_left, zpow_one] using
      mul_lt_mul_of_pos_right h_lower (zpow_pos uniformizer_pos (n + 1))
  refine ⟨-(n + 1), ?_⟩
  rw [zpow_neg]
  exact inv_eq_of_mul_eq_one_left <| hδ_le.lt_or_eq.resolve_left fun h ↦
    hδ_lt.not_ge (le_uniformizer_iff.mpr h)

/-- A division ring with a discrete, nontrivial valuation has a uniformizer: a unit whose
valuation is the maximal value-group element `< 1`. -/
theorem ValuativeRel.exists_unit_valuation_uniformizer (K : Type*) [DivisionRing K] [ValuativeRel K]
    [IsDiscrete K] [IsNontrivial K] : ∃ ϖ : Kˣ, valuation K (ϖ : K) = uniformizer K :=
  let ⟨π, hπ⟩ := valuation_surjective (uniformizer K)
  ⟨Units.mk0 π ((valuation K).ne_zero_iff.mp (hπ.trans_ne uniformizer_ne_zero)), hπ⟩

end Generic

variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k]

private theorem TateCurve.valuation_tsum_sub_le {T : ℕ → k} {c v : ValueGroupWithZero k}
    (hT0 : T 0 = 0) (hv : v ≠ 0) (hc : c < 1)
    (hd : ∀ n, valuation k (T (n + 1) - T n) ≤ c ^ n * v) (n : ℕ) :
    valuation k ((∑' i, (T (i + 1) - T i)) - T n) ≤ c ^ n * v := by
  have hsum : Summable fun i ↦ T (i + 1) - T i :=
    summable_of_valuation_le_const_mul_pow hv hc _ fun i ↦ (hd i).trans_eq (mul_comm _ _)
  have hsplit : (∑' i, (T (i + 1) - T i)) - T n = ∑' i, (T (i + n + 1) - T (i + n)) := by
    rw [sub_eq_iff_eq_add', show T n = ∑ i ∈ Finset.range n, (T (i + 1) - T i) by
      rw [Finset.sum_range_sub, hT0, sub_zero]]
    exact (Summable.sum_add_tsum_nat_add n hsum).symm
  rw [hsplit]
  exact valuation_tsum_le ((summable_nat_add_iff n).mpr hsum) fun i ↦ (hd _).trans
    (mul_le_mul' (pow_le_pow_right_of_le_one' hc.le (Nat.le_add_left n i)) le_rfl)

private theorem TateCurve.eq_zero_of_valuation_le_pow_mul {x : k} {c v : ValueGroupWithZero k}
    (hc : c < 1) (hv : v ≠ 0) (h : ∀ n, valuation k x ≤ c ^ (n + 1) * v) : x = 0 := by
  by_contra hx
  obtain ⟨N, hN⟩ := exists_pow_lt hc
    (Units.mk0 _ (mul_ne_zero ((valuation k).ne_zero_iff.mpr hx) (inv_ne_zero hv)))
  rw [Units.val_mk0] at hN
  have h1 : c ^ N * v < valuation k x * v⁻¹ * v :=
    (mul_lt_mul_iff_left₀ (zero_lt_iff.mpr hv)).mpr hN
  rw [mul_assoc, inv_mul_cancel₀ hv, mul_one] at h1
  exact absurd (h N) (not_le.mpr ((mul_le_mul'
    (pow_le_pow_right_of_le_one' hc.le N.le_succ) le_rfl).trans_lt h1))

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
private theorem TateCurve.valuation_iterate_le_aux (G : k → k) {r : ValueGroupWithZero k}
    (hmaps : ∀ t, valuation k t ≤ r → valuation k (G t) ≤ r) (n : ℕ) :
    valuation k (G^[n] 0) ≤ r :=
  Set.MapsTo.iterate (s := {t | valuation k t ≤ r}) hmaps n (by simp)

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
private theorem TateCurve.valuation_iterate_sub_iterate_le_aux (G : k → k)
    {r c : ValueGroupWithZero k} (hmaps : ∀ t, valuation k t ≤ r → valuation k (G t) ≤ r)
    (hlip : ∀ t t', valuation k t ≤ r → valuation k t' ≤ r →
      valuation k (G t - G t') ≤ c * valuation k (t - t')) (n : ℕ) :
    valuation k (G^[n + 1] 0 - G^[n] 0) ≤ c ^ n * valuation k (G 0) := by
  induction n with
  | zero => simp
  | succ n ih =>
    simpa only [Function.iterate_succ_apply', pow_succ', mul_assoc] using
      (hlip _ _ (valuation_iterate_le_aux G hmaps _) (valuation_iterate_le_aux G hmaps _)).trans
        (mul_le_mul' le_rfl ih)

private theorem TateCurve.valuation_tsum_iterate_sub_le_aux (G : k → k)
    {r c : ValueGroupWithZero k} (hc : c < 1) (hG0 : G 0 ≠ 0)
    (hmaps : ∀ t, valuation k t ≤ r → valuation k (G t) ≤ r)
    (hlip : ∀ t t', valuation k t ≤ r → valuation k t' ≤ r →
      valuation k (G t - G t') ≤ c * valuation k (t - t')) :
    valuation k (∑' n, (G^[n + 1] 0 - G^[n] 0)) ≤ r := by
  let T : ℕ → k := fun n ↦ G^[n] 0
  have hd : ∀ n, valuation k (T (n + 1) - T n) ≤ c ^ n * valuation k (G 0) :=
    fun n ↦ by simpa [T] using valuation_iterate_sub_iterate_le_aux G hmaps hlip n
  have hsum : valuation k (∑' n, (G^[n + 1] 0 - G^[n] 0)) ≤ valuation k (G 0) := by
    simpa [T] using
      valuation_tsum_sub_le (T := T) (by simp [T]) ((valuation k).ne_zero_iff.mpr hG0) hc hd 0
  exact hsum.trans (hmaps 0 (by simp))

private theorem TateCurve.isFixedPt_tsum_iterate_sub_aux (G : k → k)
    {r c : ValueGroupWithZero k} (hc : c < 1) (hG0 : G 0 ≠ 0)
    (hmaps : ∀ t, valuation k t ≤ r → valuation k (G t) ≤ r)
    (hlip : ∀ t t', valuation k t ≤ r → valuation k t' ≤ r →
      valuation k (G t - G t') ≤ c * valuation k (t - t')) :
    Function.IsFixedPt G (∑' n, (G^[n + 1] 0 - G^[n] 0)) := by
  let T : ℕ → k := fun n ↦ G^[n] 0
  let t : k := ∑' n, (T (n + 1) - T n)
  have hT : ∀ n, valuation k (T n) ≤ r :=
    fun n ↦ by simpa [T] using valuation_iterate_le_aux G hmaps n
  have hd : ∀ n, valuation k (T (n + 1) - T n) ≤ c ^ n * valuation k (G 0) :=
    fun n ↦ by simpa [T] using valuation_iterate_sub_iterate_le_aux G hmaps hlip n
  have hvG0 : valuation k (G 0) ≠ 0 := (valuation k).ne_zero_iff.mpr hG0
  have htail : ∀ n, valuation k (t - T n) ≤ c ^ n * valuation k (G 0) := by
    intro n
    change valuation k ((∑' i, (T (i + 1) - T i)) - T n) ≤ c ^ n * valuation k (G 0)
    exact valuation_tsum_sub_le (by simp [T]) hvG0 hc hd n
  have htr : valuation k t ≤ r := by
    simpa [t, T] using valuation_tsum_iterate_sub_le_aux G hc hG0 hmaps hlip
  refine sub_eq_zero.mp <| eq_zero_of_valuation_le_pow_mul hc hvG0 fun n ↦ ?_
  rw [show G t - t = (G t - G (T n)) + (T (n + 1) - t) by
    rw [show T (n + 1) = G (T n) by simp [T, Function.iterate_succ_apply']]
    ring]
  refine ((valuation k).map_add _ _).trans (max_le ?_ ?_)
  · exact (hlip _ _ htr (hT _)).trans <| (mul_le_mul' le_rfl (htail n)).trans_eq <| by
      rw [← mul_assoc, ← pow_succ']
  · simpa [Valuation.map_sub_swap] using htail (n + 1)

/-- A valuation-valued strict contraction preserving a closed ball over a nonarchimedean local
field has a fixed point in that ball. -/
theorem TateCurve.exists_fixedPoint (G : k → k) {r c : ValueGroupWithZero k} (hc : c < 1)
    (hmaps : ∀ t, valuation k t ≤ r → valuation k (G t) ≤ r)
    (hlip : ∀ t t', valuation k t ≤ r → valuation k t' ≤ r →
      valuation k (G t - G t') ≤ c * valuation k (t - t')) :
    ∃ t, valuation k t ≤ r ∧ G t = t := by
  classical
  by_cases hG0 : G 0 = 0
  · exact ⟨0, by simp, hG0⟩
  exact ⟨_, valuation_tsum_iterate_sub_le_aux G hc hG0 hmaps hlip,
    isFixedPt_tsum_iterate_sub_aux G hc hG0 hmaps hlip⟩

/-- `|a₄(q)| ≤ |q|`: the series `a₄(q) = -5q - 45q² - ⋯` has no constant term. -/
theorem WeierstrassCurve.valuation_tateA₄_le (q : k) (hq : valuation k q < 1) :
    valuation k (tateA₄ q) ≤ valuation k q := by
  simpa [tateA₄_eq_evalInt q hq] using
    TateCurve.valuation_evalInt_le_pow q hq (M := 1) fun m hm ↦ by
    simp [Nat.lt_one_iff.mp hm, TateCurve.coeff_a₄Formal]

/-- `|a₆(q)| = |q|`: the series `a₆(q) = -q - 23q² - ⋯` has unit linear coefficient
(Silverman, ATAEC V.4, proof of Lemma 4.1.2). -/
theorem WeierstrassCurve.valuation_tateA₆ (q : k) (hq0 : q ≠ 0) (hq : valuation k q < 1) :
    valuation k (tateA₆ q) = valuation k q := by
  rw [tateA₆_eq_evalInt q hq, ← (valuation k).map_neg,
    ← show TateCurve.evalInt q (-TateCurve.a₆Formal) =
        -TateCurve.evalInt q TateCurve.a₆Formal by
      simpa using TateCurve.evalInt_C_mul q (-1) TateCurve.a₆Formal]
  apply TateCurve.valuation_evalInt_eq q hq0 hq <;>
    simp [← PowerSeries.coeff_zero_eq_constantCoeff]

/-- The estimate `|a₆(q) + q| ≤ |q|²` expresses that `a₆(q) = -q + O(q²)`. -/
theorem WeierstrassCurve.valuation_tateA₆_add (q : k) (hq : valuation k q < 1) :
    valuation k (tateA₆ q + q) ≤ valuation k q ^ 2 := by
  rw [show tateA₆ q + q = TateCurve.evalInt q (TateCurve.a₆Formal + PowerSeries.X) by
    rw [tateA₆_eq_evalInt q hq, TateCurve.evalInt_add (TateCurve.summable_evalInt q hq _)
      (TateCurve.summable_evalInt q hq _), TateCurve.evalInt_X]]
  exact TateCurve.valuation_evalInt_le_pow q hq (M := 2) fun m hm ↦ by
    interval_cases m <;> simp [-PowerSeries.coeff_zero_eq_constantCoeff]

/-- `|a₆(q)| ≤ |q|`: the `≤` form of `valuation_tateA₆`, available without `q ≠ 0`. -/
theorem WeierstrassCurve.valuation_tateA₆_le (q : k) (hq : valuation k q < 1) :
    valuation k (tateA₆ q) ≤ valuation k q := by
  simpa [tateA₆_eq_evalInt q hq] using
    TateCurve.valuation_evalInt_le_pow q hq (M := 1) fun m hm ↦ by
    simp [Nat.lt_one_iff.mp hm, -PowerSeries.coeff_zero_eq_constantCoeff]

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] in
private theorem WeierstrassCurve.tateCurve_equation_iff {q x y : k} :
    ((tateCurve q)⁄k).Equation x y ↔ y ^ 2 + x * y = x ^ 3 + tateA₄ q * x + tateA₆ q := by
  simp [Affine.equation_iff, tateCurve]

/-- On `E_q`, a point with `|x| > 1` satisfies `|y|² = |x|³`, hence `|y| > |x|` and
`|x / y| < 1`. -/
theorem WeierstrassCurve.tateCurve_valuation_y_sq {q x y : k} (hq : valuation k q < 1)
    (h : ((tateCurve q)⁄k).Equation x y) (hx : 1 < valuation k x) :
    valuation k y ^ 2 = valuation k x ^ 3 := by
  rw [tateCurve_equation_iff, add_assoc] at h
  have hx0 : (0 : ValueGroupWithZero k) < valuation k x := zero_lt_one.trans hx
  have hx3 : valuation k x ≤ valuation k x ^ 3 := le_self_pow hx.le three_ne_zero
  have h46 : valuation k (tateA₄ q * x + tateA₆ q) < valuation k x ^ 3 := by
    refine ((valuation k).map_add _ _).trans_lt (max_lt ?_ ?_)
    · rw [map_mul]
      exact ((mul_le_mul' (valuation_tateA₄_le q hq) le_rfl).trans_lt
        (mul_lt_of_lt_one_left hx0 hq)).trans_le hx3
    · exact ((valuation_tateA₆_le q hq).trans_lt hq).trans (hx.trans_le hx3)
  have hL : valuation k (y ^ 2 + x * y) = valuation k x ^ 3 := by
    rw [h, (valuation k).map_add_eq_of_lt_left (by rw [map_pow]; exact h46), map_pow]
  rcases le_or_gt (valuation k y) (valuation k x) with hyx | hyx
  · have hle : valuation k (y ^ 2 + x * y) ≤ valuation k x ^ 2 :=
      ((valuation k).map_add _ _).trans (max_le (by rw [map_pow]; exact pow_le_pow_left' hyx 2)
        (by rw [map_mul, pow_two]; exact mul_le_mul' le_rfl hyx))
    exact absurd (hL ▸ hle) (pow_lt_pow_right₀ hx (by norm_num)).not_ge
  · have hlt : valuation k (x * y) < valuation k (y ^ 2) := by
      rw [map_pow, map_mul, pow_two]
      exact (mul_lt_mul_iff_left₀ (hx0.trans hyx)).mpr hyx
    rwa [(valuation k).map_add_eq_of_lt_left hlt, map_pow] at hL

private theorem valuation_eq_one_of_sq_add_mul_eq_one {R : Type*} [Field R] [ValuativeRel R]
    {x y : R} (hx : valuation R x = 1) (hxy : valuation R (y ^ 2 + x * y) = 1) :
    valuation R y = 1 := by
  by_cases hy : y = 0
  · simp [hy] at hxy
  have hy0 : (0 : ValueGroupWithZero R) < valuation R y :=
    zero_lt_iff.mpr ((valuation R).ne_zero_iff.mpr hy)
  rcases lt_trichotomy (valuation R y) 1 with hy1 | hy1 | hy1
  · have hlt : valuation R (y ^ 2) < valuation R (x * y) := by
      rw [map_pow, map_mul, hx, one_mul, pow_two]
      simpa using (mul_lt_mul_iff_left₀ hy0).mpr hy1
    rwa [(valuation R).map_add_eq_of_lt_right hlt, map_mul, hx, one_mul] at hxy
  · exact hy1
  · have hlt : valuation R (x * y) < valuation R (y ^ 2) := by
      rw [map_pow, map_mul, hx, one_mul, pow_two]
      simpa using (mul_lt_mul_iff_left₀ hy0).mpr hy1
    rw [(valuation R).map_add_eq_of_lt_left hlt, map_pow] at hxy
    exact ((one_lt_pow₀ hy1 two_ne_zero).ne hxy.symm).elim

/-- On `E_q`, a point with `|x| = 1` has `|y| = 1` (Silverman ATAEC V.4, Lemma 4.1.1). -/
theorem WeierstrassCurve.tateCurve_valuation_y_eq_one {q x y : k} (hq : valuation k q < 1)
    (h : ((tateCurve q)⁄k).Equation x y) (hx : valuation k x = 1) : valuation k y = 1 := by
  rw [tateCurve_equation_iff, add_assoc] at h
  apply valuation_eq_one_of_sq_add_mul_eq_one hx
  rw [h, (valuation k).map_add_eq_of_lt_left (by
    rw [map_pow, hx, one_pow]
    refine ((valuation k).map_add _ _).trans_lt (max_lt ?_ ?_)
    · rw [map_mul, hx, mul_one]
      exact (valuation_tateA₄_le q hq).trans_lt hq
    · exact (valuation_tateA₆_le q hq).trans_lt hq), map_pow, hx, one_pow]

private theorem valuation_pow_add_mul_add_lt_one_aux {R : Type*} [Ring R] [ValuativeRel R]
    {x a b : R} {n : ℕ} (hn : n ≠ 0) (hx : valuation R x < 1) (ha : valuation R a ≤ 1)
    (hb : valuation R b < 1) : valuation R (x ^ n + a * x + b) < 1 := by
  refine (valuation R).map_add_lt ((valuation R).map_add_lt ?_ ?_) hb
  · rw [map_pow]
    exact (pow_lt_one_iff_of_nonneg (zero_le (a := valuation R x)) hn).mpr hx
  · rw [map_mul]
    exact mul_lt_one_of_nonneg_of_lt_one_right ha (zero_le (a := valuation R x)) hx

private theorem one_le_valuation_sq_add_mul_of_lt_one_of_one_le_aux {R : Type*} [Field R]
    [ValuativeRel R] {x y : R} (hx : valuation R x < 1) (hy : 1 ≤ valuation R y) :
    1 ≤ valuation R (y ^ 2 + x * y) := by
  have hy0 : (0 : ValueGroupWithZero R) < valuation R y := zero_lt_one.trans_le hy
  have hlt : valuation R (x * y) < valuation R (y ^ 2) := by
    rw [map_pow, map_mul, pow_two]
    exact (mul_lt_mul_iff_left₀ hy0).mpr (hx.trans_le hy)
  rw [(valuation R).map_add_eq_of_lt_left hlt, map_pow, pow_two]
  exact one_le_mul hy hy

/-- On `E_q`, a point with `|x| < 1` has `|y| < 1` (Silverman ATAEC V.4, Lemma 4.1.1). -/
theorem WeierstrassCurve.tateCurve_valuation_y_lt_one {q x y : k} (hq : valuation k q < 1)
    (h : ((tateCurve q)⁄k).Equation x y) (hx : valuation k x < 1) :
    valuation k y < 1 := by
  by_contra! hy
  rw [tateCurve_equation_iff] at h
  have hRHS := valuation_pow_add_mul_add_lt_one_aux three_ne_zero hx
    ((valuation_tateA₄_le q hq).trans hq.le) ((valuation_tateA₆_le q hq).trans_lt hq)
  rw [← h] at hRHS
  exact (not_le_of_gt hRHS) (one_le_valuation_sq_add_mul_of_lt_one_of_one_le_aux hx hy)

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
private theorem valuation_XField_tail_coeff_le_one {u : k} (hu : valuation k u = 1) (n : ℕ) :
    valuation k (∑ d ∈ n.divisors,
      ((d : k) * u ^ d + (d : k) * (u⁻¹) ^ d - 2 * (d : k))) ≤ 1 := by
  refine (valuation k).map_sum_le fun d _ ↦ ?_
  refine le_trans ((valuation k).map_sub _ _) (max_le (le_trans
    ((valuation k).map_add _ _) (max_le ?_ ?_)) ?_)
  · rw [map_mul, map_pow, hu, one_pow, mul_one]
    exact valuation_natCast_le_one d
  · rw [map_mul, map_pow, map_inv₀, hu, inv_one, one_pow, mul_one]
    exact valuation_natCast_le_one d
  · rw [show ((2 : k) * (d : k)) = ((2 * d : ℕ) : k) by push_cast; ring]
    exact valuation_natCast_le_one _

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
private theorem valuation_XField_tail_term_le {q u : k} (hq : valuation k q < 1)
    (hu : valuation k u = 1) (n : ℕ) : valuation k ((∑ d ∈ n.divisors,
      ((d : k) * u ^ d + (d : k) * (u⁻¹) ^ d - 2 * (d : k))) * q ^ n) ≤ valuation k q := by
  rcases n with - | n
  · simp
  · rw [map_mul, map_pow]
    exact (mul_le_mul' (valuation_XField_tail_coeff_le_one hu _) le_rfl).trans <| by
      simpa using pow_le_pow_right_of_le_one' hq.le (show 1 ≤ n + 1 by omega)

/-- If `|u| = 1`, then `|X(u, q) - u/(1-u)²| ≤ |q|`. -/
theorem WeierstrassCurve.valuation_tateX_sub_leading (q : kˣ) (hq : valuation k (q : k) < 1)
    {u : k} (hu : valuation k u = 1) :
    valuation k (tateX u (q : k) - u / (1 - u) ^ 2) ≤ valuation k (q : k) := by
  let U : kˣ := Units.mk0 u <| (valuation k).ne_zero_iff.mp (hu.trans_ne one_ne_zero)
  have htails : Summable fun N : ℕ ↦ (∑ d ∈ N.divisors,
      ((d : k) * (U : k) ^ d + (d : k) * ((U : k)⁻¹) ^ d - 2 * (d : k))) * (q : k) ^ N :=
    ((TateCurve.evalBounded_XField_tail q U (by simp [U, hu])).summable
      (by simpa [U, hu] using hq)).congr fun n ↦ by rw [PowerSeries.coeff_mk]
  have hann := tateX_eq_annulus q U hq (by simpa [U, hu] using hq) (by simp [U, hu])
  simp only [U, Units.val_mk0] at hann htails
  rw [hann, add_sub_cancel_left]
  exact valuation_tsum_le htails (valuation_XField_tail_term_le hq hu)

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
private theorem TateCurve.valuation_YField_tail_coeff_le_one {u : k}
    (hu : valuation k u = 1) (n : ℕ) :
    valuation k (∑ d ∈ n.divisors, (((d.choose 2 : ℕ) : k) * u ^ d
      - (((d + 1).choose 2 : ℕ) : k) * (u⁻¹) ^ d + (d : k))) ≤ 1 := by
  refine (valuation k).map_sum_le fun d _ ↦ ?_
  refine le_trans ((valuation k).map_add _ _) (max_le (le_trans
    ((valuation k).map_sub _ _) (max_le ?_ ?_)) ?_)
  · rw [map_mul, map_pow, hu, one_pow, mul_one]
    exact valuation_natCast_le_one _
  · rw [map_mul, map_pow, map_inv₀, hu, inv_one, one_pow, mul_one]
    exact valuation_natCast_le_one _
  · exact valuation_natCast_le_one _

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
private theorem TateCurve.valuation_YField_tail_term_le (q : k) (hq : valuation k q < 1)
    {u : k} (hu : valuation k u = 1) (n : ℕ) :
    valuation k ((∑ d ∈ n.divisors, (((d.choose 2 : ℕ) : k) * u ^ d
      - (((d + 1).choose 2 : ℕ) : k) * (u⁻¹) ^ d + (d : k))) * q ^ n) ≤ valuation k q := by
  rcases n with - | n
  · simp
  · rw [map_mul, map_pow]
    exact (mul_le_mul' (valuation_YField_tail_coeff_le_one hu _) le_rfl).trans <| by
      simpa using pow_le_pow_right_of_le_one' hq.le (show 1 ≤ n + 1 by omega)

/-- `|Y(u, q) - u²/(1-u)³| ≤ |q|` for `|u| = 1`. -/
theorem WeierstrassCurve.valuation_tateY_sub_leading (q : kˣ) (hq : valuation k (q : k) < 1)
    {u : k} (hu : valuation k u = 1) :
    valuation k (tateY u (q : k) - u ^ 2 / (1 - u) ^ 3) ≤ valuation k (q : k) := by
  have hu0 : u ≠ 0 := (valuation k).ne_zero_iff.mp (hu.trans_ne one_ne_zero)
  have htails : Summable fun N : ℕ ↦ (∑ d ∈ N.divisors,
      (((d.choose 2 : ℕ) : k) * ((Units.mk0 u hu0 : kˣ) : k) ^ d
        - (((d + 1).choose 2 : ℕ) : k) * (((Units.mk0 u hu0 : kˣ) : k)⁻¹) ^ d
        + (d : k))) * (q : k) ^ N :=
    ((TateCurve.evalBounded_YField_tail q (Units.mk0 u hu0) (by simp [hu])).summable
      (by simpa [hu] using hq)).congr fun n ↦ by rw [PowerSeries.coeff_mk]
  have hann := tateY_eq_annulus q (Units.mk0 u hu0) hq (by simpa [hu] using hq) (by simp [hu])
  simp only [Units.val_mk0] at hann htails
  rw [hann, add_sub_cancel_left]
  exact valuation_tsum_le htails fun N ↦ TateCurve.valuation_YField_tail_term_le _ hq hu N

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
/-- `|uᵈ - u'ᵈ| ≤ |u - u'|` on the closed unit disc: factor out `u - u'` by the
geometric sum, whose value is integral. -/
private theorem WeierstrassCurve.valuation_pow_sub_pow_le {u u' : k}
    (hu : valuation k u ≤ 1) (hu' : valuation k u' ≤ 1) (d : ℕ) :
    valuation k (u ^ d - u' ^ d) ≤ valuation k (u - u') := by
  rw [← geom_sum₂_mul, map_mul]
  calc valuation k (∑ i ∈ Finset.range d, u ^ i * u' ^ (d - 1 - i)) * valuation k (u - u')
      ≤ 1 * valuation k (u - u') := by
        refine mul_le_mul' ((valuation k).map_sum_le fun i _ ↦ ?_) le_rfl
        rw [map_mul, map_pow, map_pow]
        exact (mul_le_mul' (pow_le_one' hu i) (pow_le_one' hu' _)).trans_eq (one_mul 1)
    _ = valuation k (u - u') := one_mul _

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
/-- `|u⁻ᵈ - u'⁻ᵈ| ≤ |u - u'|` on the unit circle: the difference is `(u'ᵈ - uᵈ)`
divided by the unit `uᵈu'ᵈ`. -/
private theorem WeierstrassCurve.valuation_inv_pow_sub_inv_pow_le {u u' : k}
    (hu : valuation k u = 1) (hu' : valuation k u' = 1) (d : ℕ) :
    valuation k ((u⁻¹) ^ d - (u'⁻¹) ^ d) ≤ valuation k (u - u') := by
  have hu0 : u ≠ 0 := fun h ↦ by rw [h, map_zero] at hu; exact zero_ne_one hu
  have hu'0 : u' ≠ 0 := fun h ↦ by rw [h, map_zero] at hu'; exact zero_ne_one hu'
  have hd : (u⁻¹) ^ d - (u'⁻¹) ^ d = (u' ^ d - u ^ d) * (u ^ d)⁻¹ * (u' ^ d)⁻¹ := by
    have h1 : u ^ d ≠ 0 := pow_ne_zero d hu0
    have h2 : u' ^ d ≠ 0 := pow_ne_zero d hu'0
    rw [inv_pow, inv_pow]
    field_simp
  rw [hd, map_mul, map_mul, map_inv₀, map_inv₀, map_pow, map_pow, hu, hu', one_pow,
    inv_one, mul_one, mul_one, Valuation.map_sub_swap]
  exact valuation_pow_sub_pow_le hu.le hu'.le d

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
private theorem TateCurve.valuation_XField_tail_coeff_sub_le {u u' : k}
    (hu : valuation k u = 1) (hu' : valuation k u' = 1) (n : ℕ) :
    valuation k (∑ d ∈ n.divisors,
      (((d : k) * u ^ d + (d : k) * (u⁻¹) ^ d - 2 * (d : k))
        - ((d : k) * u' ^ d + (d : k) * (u'⁻¹) ^ d - 2 * (d : k))))
      ≤ valuation k (u - u') := by
  refine (valuation k).map_sum_le fun d _ ↦ ?_
  rw [show ((d : k) * u ^ d + (d : k) * (u⁻¹) ^ d - 2 * (d : k))
        - ((d : k) * u' ^ d + (d : k) * (u'⁻¹) ^ d - 2 * (d : k)) =
      (d : k) * (u ^ d - u' ^ d) + (d : k) * ((u⁻¹) ^ d - (u'⁻¹) ^ d) by ring]
  refine ((valuation k).map_add _ _).trans (max_le ?_ ?_)
  · rw [map_mul]
    exact (mul_le_mul' (valuation_natCast_le_one d)
      (WeierstrassCurve.valuation_pow_sub_pow_le hu.le hu'.le d)).trans_eq (one_mul _)
  · rw [map_mul]
    exact (mul_le_mul' (valuation_natCast_le_one d)
      (WeierstrassCurve.valuation_inv_pow_sub_inv_pow_le hu hu' d)).trans_eq (one_mul _)

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
private theorem TateCurve.valuation_XField_tail_term_sub_le (q : k)
    (hq : valuation k q < 1) {u u' : k} (hu : valuation k u = 1)
    (hu' : valuation k u' = 1) (n : ℕ) :
    valuation k (((∑ d ∈ n.divisors,
      ((d : k) * u ^ d + (d : k) * (u⁻¹) ^ d - 2 * (d : k))) * q ^ n)
        - ((∑ d ∈ n.divisors,
          ((d : k) * u' ^ d + (d : k) * (u'⁻¹) ^ d - 2 * (d : k))) * q ^ n))
      ≤ valuation k q * valuation k (u - u') := by
  rcases n with - | n
  · simp
  · rw [← sub_mul, ← Finset.sum_sub_distrib, map_mul, map_pow]
    calc
      valuation k (∑ d ∈ (n + 1).divisors,
          (((d : k) * u ^ d + (d : k) * (u⁻¹) ^ d - 2 * (d : k))
            - ((d : k) * u' ^ d + (d : k) * (u'⁻¹) ^ d - 2 * (d : k)))) *
            valuation k q ^ (n + 1)
          ≤ valuation k (u - u') * valuation k q ^ (n + 1) :=
        mul_le_mul' (valuation_XField_tail_coeff_sub_le hu hu' _) le_rfl
      _ ≤ valuation k (u - u') * valuation k q := mul_le_mul' le_rfl <| by
        simpa only [pow_one] using
          pow_le_pow_right_of_le_one' hq.le (show 1 ≤ n + 1 by omega)
      _ = valuation k q * valuation k (u - u') := mul_comm _ _

private theorem TateCurve.hasSum_XField_tail (q : kˣ) (hq : valuation k (q : k) < 1)
    {u : k} (hu : valuation k u = 1) :
    HasSum (fun N : ℕ ↦ (∑ d ∈ N.divisors,
      ((d : k) * u ^ d + (d : k) * (u⁻¹) ^ d - 2 * (d : k))) * (q : k) ^ N)
      (WeierstrassCurve.tateX u (q : k) - u / (1 - u) ^ 2) := by
  let U : kˣ := Units.mk0 u fun h ↦ by rw [h, map_zero] at hu; exact zero_ne_one hu
  have htails : Summable fun N : ℕ ↦ (∑ d ∈ N.divisors,
      ((d : k) * (U : k) ^ d + (d : k) * ((U : k)⁻¹) ^ d - 2 * (d : k))) * (q : k) ^ N :=
    ((evalBounded_XField_tail q U (by simp [U, hu])).summable
      (by simpa [U, hu] using hq)).congr fun n ↦ by rw [PowerSeries.coeff_mk]
  have hann := WeierstrassCurve.tateX_eq_annulus q U hq (by simpa [U, hu] using hq)
    (by simp [U, hu])
  simp only [U, Units.val_mk0] at hann htails
  rw [hann, add_sub_cancel_left]
  exact htails.hasSum

/-- On `|u| = 1`, the annulus tail `Rx(u) = X(u, q) - u/(1-u)²` is `|q|`-Lipschitz:
`|Rx(u) - Rx(u')| ≤ |q|·|u - u'|`. -/
theorem WeierstrassCurve.valuation_tateX_tail_sub (q : kˣ) (hq : valuation k (q : k) < 1)
    {u u' : k} (hu : valuation k u = 1) (hu' : valuation k u' = 1) :
    valuation k ((tateX u (q : k) - u / (1 - u) ^ 2)
        - (tateX u' (q : k) - u' / (1 - u') ^ 2))
      ≤ valuation k (q : k) * valuation k (u - u') := by
  have hsum := TateCurve.hasSum_XField_tail q hq hu
  have hsum' := TateCurve.hasSum_XField_tail q hq hu'
  rw [← hsum.tsum_eq, ← hsum'.tsum_eq,
    ← hsum.summable.tsum_sub hsum'.summable]
  exact valuation_tsum_le (hsum.summable.sub hsum'.summable) fun n ↦
    TateCurve.valuation_XField_tail_term_sub_le (q : k) hq hu hu' n

private theorem WeierstrassCurve.hasSum_YField_tail (q : kˣ)
    (hq : valuation k (q : k) < 1) {u : k} (hu : valuation k u = 1) :
    HasSum (fun n : ℕ ↦ (∑ d ∈ n.divisors, (((d.choose 2 : ℕ) : k) * u ^ d
      - (((d + 1).choose 2 : ℕ) : k) * (u⁻¹) ^ d + (d : k))) * (q : k) ^ n)
      (tateY u (q : k) - u ^ 2 / (1 - u) ^ 3) := by
  have hu0 : u ≠ 0 := fun h ↦ by rw [h, map_zero] at hu; exact zero_ne_one hu
  have htails : Summable fun n : ℕ ↦ (∑ d ∈ n.divisors,
      (((d.choose 2 : ℕ) : k) * ((Units.mk0 u hu0 : kˣ) : k) ^ d
        - (((d + 1).choose 2 : ℕ) : k) * (((Units.mk0 u hu0 : kˣ) : k)⁻¹) ^ d
        + (d : k))) * (q : k) ^ n :=
    ((TateCurve.evalBounded_YField_tail q (Units.mk0 u hu0) (by simp [hu])).summable
      (by simpa [hu] using hq)).congr fun n ↦ by rw [PowerSeries.coeff_mk]
  have hann := tateY_eq_annulus q (Units.mk0 u hu0) hq (by simpa [hu] using hq) (by simp [hu])
  simp only [Units.val_mk0] at hann htails
  rw [hann, add_sub_cancel_left]
  exact htails.hasSum

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
private theorem WeierstrassCurve.valuation_YField_tail_coeff_sub_le {u u' : k}
    (hu : valuation k u = 1) (hu' : valuation k u' = 1) (n : ℕ) :
    valuation k (∑ d ∈ n.divisors,
      ((((d.choose 2 : ℕ) : k) * u ^ d
          - (((d + 1).choose 2 : ℕ) : k) * (u⁻¹) ^ d + (d : k))
        - (((d.choose 2 : ℕ) : k) * u' ^ d
          - (((d + 1).choose 2 : ℕ) : k) * (u'⁻¹) ^ d + (d : k))))
      ≤ valuation k (u - u') := by
  refine (valuation k).map_sum_le fun d _ ↦ ?_
  rw [show ((((d.choose 2 : ℕ) : k) * u ^ d
        - (((d + 1).choose 2 : ℕ) : k) * (u⁻¹) ^ d + (d : k))
      - (((d.choose 2 : ℕ) : k) * u' ^ d
        - (((d + 1).choose 2 : ℕ) : k) * (u'⁻¹) ^ d + (d : k)))
      = ((d.choose 2 : ℕ) : k) * (u ^ d - u' ^ d)
        - (((d + 1).choose 2 : ℕ) : k) * ((u⁻¹) ^ d - (u'⁻¹) ^ d) by ring]
  refine ((valuation k).map_sub _ _).trans (max_le ?_ ?_)
  · rw [map_mul]
    exact (mul_le_mul' (valuation_natCast_le_one _)
      (valuation_pow_sub_pow_le hu.le hu'.le d)).trans_eq (one_mul _)
  · rw [map_mul]
    exact (mul_le_mul' (valuation_natCast_le_one _)
      (valuation_inv_pow_sub_inv_pow_le hu hu' d)).trans_eq (one_mul _)

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
private theorem WeierstrassCurve.valuation_YField_tail_term_sub_le {q u u' : k}
    (hq : valuation k q < 1) (hu : valuation k u = 1) (hu' : valuation k u' = 1) (n : ℕ) :
    valuation k (((∑ d ∈ n.divisors, (((d.choose 2 : ℕ) : k) * u ^ d
        - (((d + 1).choose 2 : ℕ) : k) * (u⁻¹) ^ d + (d : k))) * q ^ n)
      - ((∑ d ∈ n.divisors, (((d.choose 2 : ℕ) : k) * u' ^ d
        - (((d + 1).choose 2 : ℕ) : k) * (u'⁻¹) ^ d + (d : k))) * q ^ n))
      ≤ valuation k q * valuation k (u - u') := by
  rcases n with - | n
  · simp
  · rw [← sub_mul, ← Finset.sum_sub_distrib, map_mul, map_pow]
    calc
      valuation k (∑ d ∈ (n + 1).divisors,
          ((((d.choose 2 : ℕ) : k) * u ^ d
              - (((d + 1).choose 2 : ℕ) : k) * (u⁻¹) ^ d + (d : k))
            - (((d.choose 2 : ℕ) : k) * u' ^ d
              - (((d + 1).choose 2 : ℕ) : k) * (u'⁻¹) ^ d + (d : k))))
          * valuation k q ^ (n + 1)
          ≤ valuation k (u - u') * valuation k q ^ (n + 1) :=
        mul_le_mul' (valuation_YField_tail_coeff_sub_le hu hu' _) le_rfl
      _ ≤ valuation k (u - u') * valuation k q := mul_le_mul' le_rfl <| by
        simpa using pow_le_pow_right_of_le_one' hq.le (show 1 ≤ n + 1 by omega)
      _ = valuation k q * valuation k (u - u') := mul_comm _ _

/-- The annulus tail of `Y` is `O(q)`-Lipschitz on `|u| = 1`. -/
theorem WeierstrassCurve.valuation_tateY_tail_sub (q : kˣ) (hq : valuation k (q : k) < 1)
    {u u' : k} (hu : valuation k u = 1) (hu' : valuation k u' = 1) :
    valuation k ((tateY u (q : k) - u ^ 2 / (1 - u) ^ 3)
        - (tateY u' (q : k) - u' ^ 2 / (1 - u') ^ 3))
      ≤ valuation k (q : k) * valuation k (u - u') := by
  have h := hasSum_YField_tail q hq hu
  have h' := hasSum_YField_tail q hq hu'
  rw [← h.tsum_eq, ← h'.tsum_eq, ← h.summable.tsum_sub h'.summable]
  exact valuation_tsum_le (h.summable.sub h'.summable)
    (valuation_YField_tail_term_sub_le hq hu hu')

/-- `|Y(1 + t, q)| = |t|⁻³` for `0 < |t| < 1`: the leading term `u²/(1-u)³ = -(1+t)²/t³`
dominates the `O(q)` tail. Companion to `valuation_tateX_one_add` (Silverman ATAEC V.4,
p. 432). -/
theorem WeierstrassCurve.valuation_tateY_one_add (q : kˣ) (hq : valuation k (q : k) < 1)
    {t : k} (ht0 : t ≠ 0) (ht : valuation k t < 1) :
    valuation k (tateY (1 + t) (q : k)) = ((valuation k t)⁻¹) ^ 3 := by
  have hv1 : valuation k (1 + t) = 1 := by
    simpa using (valuation k).map_add_eq_of_lt_left (x := (1 : k)) (by simpa using ht)
  have hvt : valuation k t ≠ 0 := (valuation k).ne_zero_iff.mpr ht0
  have hlead : valuation k ((1 + t) ^ 2 / (1 - (1 + t)) ^ 3) = ((valuation k t)⁻¹) ^ 3 := by
    rw [show (1 : k) - (1 + t) = -t by ring, map_div₀, map_pow, map_pow, Valuation.map_neg,
      hv1, one_pow, one_div, inv_pow]
  have hone_le : (1 : ValueGroupWithZero k) ≤ ((valuation k t)⁻¹) ^ 3 := by
    have h1 : (1 : ValueGroupWithZero k) ≤ (valuation k t)⁻¹ :=
      ((one_lt_inv₀ (zero_lt_iff.mpr hvt)).mpr ht).le
    calc (1 : ValueGroupWithZero k) = 1 ^ 3 := (one_pow 3).symm
      _ ≤ ((valuation k t)⁻¹) ^ 3 := pow_le_pow_left' h1 3
  have hlt : valuation k (tateY (1 + t) (q : k) - (1 + t) ^ 2 / (1 - (1 + t)) ^ 3)
      < valuation k ((1 + t) ^ 2 / (1 - (1 + t)) ^ 3) := by
    rw [hlead]
    exact lt_of_le_of_lt (valuation_tateY_sub_leading q hq hv1) (lt_of_lt_of_le hq hone_le)
  rw [show tateY (1 + t) (q : k) = (1 + t) ^ 2 / (1 - (1 + t)) ^ 3
      + (tateY (1 + t) (q : k) - (1 + t) ^ 2 / (1 - (1 + t)) ^ 3) by ring,
    (valuation k).map_add_eq_of_lt_left hlt, hlead]

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] in
private theorem WeierstrassCurve.tateCurve_ratio_elimination {q x y x' y' : k}
    (h : ((tateCurve q)⁄k).Equation x y) (h' : ((tateCurve q)⁄k).Equation x' y')
    (hr : x * y' = x' * y) :
    (x - x') * (x ^ 3 * x' ^ 2 - tateA₆ q * x ^ 2 - tateA₄ q * x ^ 2 * x'
      - tateA₆ q * x * x') = 0 := by
  rw [tateCurve_equation_iff] at h h'
  linear_combination (-(x * x' ^ 2)) * h + x ^ 3 * h'
    - (x * (x * y' + x' * y + x * x')) * hr

private theorem WeierstrassCurve.valuation_tateCurve_ratio_remainder_le {q x x' : k}
    (hq : valuation k q < 1) (hx : 1 < valuation k x) (hx' : 1 < valuation k x') :
    valuation k (tateA₆ q * x ^ 2 + tateA₄ q * x ^ 2 * x' + tateA₆ q * x * x')
      ≤ valuation k (q * (x ^ 2 * x')) := by
  have ht1 : valuation k (tateA₆ q * x ^ 2) ≤ valuation k (q * (x ^ 2 * x')) := by
    have h1 : valuation k (tateA₆ q * x ^ 2) = valuation k (tateA₆ q) * valuation k (x ^ 2) :=
      map_mul _ _ _
    have h2 : valuation k (q * (x ^ 2 * x')) =
        valuation k q * valuation k (x ^ 2) * valuation k x' := by
      rw [map_mul, map_mul, ← mul_assoc]
    rw [h1, h2]
    exact (mul_le_mul' (valuation_tateA₆_le q hq) le_rfl).trans
      (le_mul_of_one_le_right' hx'.le)
  have ht2 : valuation k (tateA₄ q * x ^ 2 * x') ≤ valuation k (q * (x ^ 2 * x')) := by
    have h1 : valuation k (tateA₄ q * x ^ 2 * x') =
        valuation k (tateA₄ q) * valuation k (x ^ 2 * x') := by
      rw [← map_mul]
      congr 1
      ring
    have h2 : valuation k (q * (x ^ 2 * x')) = valuation k q * valuation k (x ^ 2 * x') :=
      map_mul _ _ _
    rw [h1, h2]
    exact mul_le_mul' (valuation_tateA₄_le q hq) le_rfl
  have ht3 : valuation k (tateA₆ q * x * x') ≤ valuation k (q * (x ^ 2 * x')) := by
    have h1 : valuation k (tateA₆ q * x * x') =
        valuation k (tateA₆ q) * valuation k (x * x') := by
      rw [← map_mul]
      congr 1
      ring
    have h2 : valuation k (q * (x ^ 2 * x')) =
        valuation k q * (valuation k x * valuation k (x * x')) := by
      rw [show q * (x ^ 2 * x') = q * (x * (x * x')) by ring, map_mul, map_mul]
    rw [h1, h2]
    exact (mul_le_mul' (valuation_tateA₆_le q hq) le_rfl).trans
      (mul_le_mul' le_rfl (le_mul_of_one_le_left' hx.le))
  exact ((valuation k).map_add _ _).trans <| max_le
    (((valuation k).map_add _ _).trans (max_le ht1 ht2)) ht3

private theorem WeierstrassCurve.tateCurve_x_eq_of_ratio_eq {q x y x' y' : k}
    (hq : valuation k q < 1) (h : ((tateCurve q)⁄k).Equation x y)
    (h' : ((tateCurve q)⁄k).Equation x' y') (hx : 1 < valuation k x)
    (hx' : 1 < valuation k x') (hr : x * y' = x' * y) : x = x' := by
  by_contra hxx
  have hx0 : x ≠ 0 := (valuation k).ne_zero_iff.mp <| ne_of_gt (zero_lt_one.trans hx)
  have hx'0 : x' ≠ 0 := (valuation k).ne_zero_iff.mp <| ne_of_gt (zero_lt_one.trans hx')
  have hkey : x ^ 3 * x' ^ 2 =
      tateA₆ q * x ^ 2 + tateA₄ q * x ^ 2 * x' + tateA₆ q * x * x' := by
    rcases mul_eq_zero.mp (tateCurve_ratio_elimination h h' hr) with h1 | h1
    · exact absurd (sub_eq_zero.mp h1) hxx
    · linear_combination h1
  have hw0 : (0 : ValueGroupWithZero k) < valuation k (x ^ 2 * x') :=
    zero_lt_iff.mpr ((valuation k).ne_zero_iff.mpr (mul_ne_zero (pow_ne_zero 2 hx0) hx'0))
  have hcof : valuation k q < valuation k (x * x') := by
    refine hq.trans_le ?_
    rw [map_mul]
    exact one_le_mul hx.le hx'.le
  have hmain : valuation k (q * (x ^ 2 * x')) < valuation k (x ^ 3 * x' ^ 2) := by
    rw [map_mul, show valuation k (x ^ 3 * x' ^ 2) =
      valuation k (x * x') * valuation k (x ^ 2 * x') by
        rw [← map_mul]
        congr 1
        ring]
    exact (mul_lt_mul_iff_left₀ hw0).mpr hcof
  rw [hkey] at hmain
  exact (not_lt_of_ge (valuation_tateCurve_ratio_remainder_le hq hx hx')) hmain

/-- **Unique large root**: two points of `E_q(k)` with `|x|, |x'| > 1` and the same ratio
`x/y = x'/y'` coincide. (Replaces Silverman's appeal to the formal group `Ê_q` [AEC VII.2.2]:
on the line `y = cx` the Weierstrass cubic has exactly one root with `|·| > 1`, by Vieta.) -/
theorem WeierstrassCurve.tateCurve_eq_of_ratio_eq {q x y x' y' : k}
    (hq : valuation k q < 1) (h : ((tateCurve q)⁄k).Equation x y)
    (h' : ((tateCurve q)⁄k).Equation x' y') (hx : 1 < valuation k x)
    (hx' : 1 < valuation k x') (hr : x * y' = x' * y) : x = x' ∧ y = y' := by
  have hxx := tateCurve_x_eq_of_ratio_eq hq h h' hx hx' hr
  subst x'
  have hx0 : x ≠ 0 := (valuation k).ne_zero_iff.mp <| ne_of_gt (zero_lt_one.trans hx)
  exact ⟨rfl, (mul_left_cancel₀ hx0 hr).symm⟩

private noncomputable def WeierstrassCurve.tateCurveFormalError (q w s : k) : k :=
  (tateX (1 + s) q - (1 + s) / (1 - (1 + s)) ^ 2)
    + w * (tateY (1 + s) q - (1 + s) ^ 2 / (1 - (1 + s)) ^ 3)

private noncomputable def WeierstrassCurve.tateCurveFormalCorrection (q w s : k) : k :=
  w * (1 + s) - s ^ 3 * tateCurveFormalError q w s / (1 + s)

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
private theorem WeierstrassCurve.tateCurve_ratio_ne_zero {x y : k}
    (hx : 1 < valuation k x) (hy2 : valuation k y ^ 2 = valuation k x ^ 3) : -x / y ≠ 0 := by
  have hx0 : x ≠ 0 := (valuation k).ne_zero_iff.mp <| ne_of_gt (zero_lt_one.trans hx)
  have hy0 : y ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hy2
    exact pow_ne_zero 3 (zero_lt_one.trans hx).ne' (by simpa using hy2.symm)
  exact div_ne_zero (neg_ne_zero.mpr hx0) hy0

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
private theorem WeierstrassCurve.valuation_tateCurve_ratio_sq_mul {x y : k}
    (hx : 1 < valuation k x) (hy2 : valuation k y ^ 2 = valuation k x ^ 3) :
    valuation k (-x / y) ^ 2 * valuation k x = 1 := by
  have hvx0 : (0 : ValueGroupWithZero k) < valuation k x := zero_lt_one.trans hx
  rw [map_div₀, Valuation.map_neg, div_pow, hy2,
    show valuation k x ^ 3 = valuation k x ^ 2 * valuation k x from pow_succ _ 2,
    div_mul_eq_div_div, div_self (pow_ne_zero 2 hvx0.ne'), one_div, inv_mul_cancel₀ hvx0.ne']

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
private theorem WeierstrassCurve.valuation_tateCurve_ratio_lt_one {w x : k}
    (hx : 1 < valuation k x) (hw2 : valuation k w ^ 2 * valuation k x = 1) :
    valuation k w < 1 := by
  by_contra hw
  rw [not_lt] at hw
  have hx_le : valuation k x ≤ valuation k w ^ 2 * valuation k x := by
    conv_lhs => rw [← one_mul (valuation k x)]
    refine mul_le_mul' ?_ le_rfl
    calc
      (1 : ValueGroupWithZero k) = 1 ^ 2 := (one_pow 2).symm
      _ ≤ valuation k w ^ 2 := pow_le_pow_left' hw 2
  rw [hw2] at hx_le
  exact (lt_of_lt_of_le hx hx_le).false

private theorem WeierstrassCurve.valuation_tateCurveFormalError_le (q : kˣ)
    (hq : valuation k (q : k) < 1) {w s : k} (hw : valuation k w < 1)
    (hs : valuation k s ≤ valuation k w) :
    valuation k (tateCurveFormalError (q : k) w s) ≤ valuation k (q : k) := by
  have h1s : valuation k (1 + s) = 1 := by
    simpa using (valuation k).map_add_eq_of_lt_left (x := (1 : k))
      (by simpa using hs.trans_lt hw)
  rw [tateCurveFormalError]
  refine ((valuation k).map_add _ _).trans (max_le ?_ ?_)
  · exact valuation_tateX_sub_leading q hq h1s
  · rw [map_mul]
    exact (mul_le_mul' hw.le (valuation_tateY_sub_leading q hq h1s)).trans_eq
      (one_mul _)

private theorem WeierstrassCurve.valuation_tateCurveFormalError_sub_le (q : kˣ)
    (hq : valuation k (q : k) < 1) {w s s' : k} (hw : valuation k w < 1)
    (hs : valuation k s ≤ valuation k w) (hs' : valuation k s' ≤ valuation k w) :
    valuation k (tateCurveFormalError (q : k) w s - tateCurveFormalError (q : k) w s') ≤
      valuation k (q : k) * valuation k (s - s') := by
  have h1s : valuation k (1 + s) = 1 := by
    simpa using (valuation k).map_add_eq_of_lt_left (x := (1 : k))
      (by simpa using hs.trans_lt hw)
  have h1s' : valuation k (1 + s') = 1 := by
    simpa using (valuation k).map_add_eq_of_lt_left (x := (1 : k))
      (by simpa using hs'.trans_lt hw)
  have hX := valuation_tateX_tail_sub q hq h1s h1s'
  have hY := valuation_tateY_tail_sub q hq h1s h1s'
  rw [show (1 + s) - (1 + s') = s - s' by ring] at hX hY
  simp only [tateCurveFormalError]
  rw [show
    ((tateX (1 + s) (q : k) - (1 + s) / (1 - (1 + s)) ^ 2)
        + w * (tateY (1 + s) (q : k) - (1 + s) ^ 2 / (1 - (1 + s)) ^ 3))
      - ((tateX (1 + s') (q : k) - (1 + s') / (1 - (1 + s')) ^ 2)
        + w * (tateY (1 + s') (q : k) - (1 + s') ^ 2 / (1 - (1 + s')) ^ 3)) =
      ((tateX (1 + s) (q : k) - (1 + s) / (1 - (1 + s)) ^ 2)
        - (tateX (1 + s') (q : k) - (1 + s') / (1 - (1 + s')) ^ 2))
      + w * ((tateY (1 + s) (q : k) - (1 + s) ^ 2 / (1 - (1 + s)) ^ 3)
        - (tateY (1 + s') (q : k) - (1 + s') ^ 2 / (1 - (1 + s')) ^ 3)) by ring]
  refine ((valuation k).map_add _ _).trans (max_le hX ?_)
  rw [map_mul]
  exact (mul_le_mul' hw.le hY).trans_eq (one_mul _)

private theorem WeierstrassCurve.valuation_tateCurveFormalCorrection_le (q : kˣ)
    (hq : valuation k (q : k) < 1) {w s : k} (hw : valuation k w < 1)
    (hs : valuation k s ≤ valuation k w) :
    valuation k (tateCurveFormalCorrection (q : k) w s) ≤ valuation k w := by
  have h1s : valuation k (1 + s) = 1 := by
    simpa using (valuation k).map_add_eq_of_lt_left (x := (1 : k))
      (by simpa using hs.trans_lt hw)
  rw [tateCurveFormalCorrection]
  refine ((valuation k).map_sub _ _).trans (max_le ?_ ?_)
  · rw [map_mul, h1s, mul_one]
  · rw [map_div₀, map_mul, map_pow, h1s, div_one]
    calc
      valuation k s ^ 3 * valuation k (tateCurveFormalError (q : k) w s) ≤
          valuation k w ^ 3 * valuation k (q : k) :=
        mul_le_mul' (pow_le_pow_left' hs 3) (valuation_tateCurveFormalError_le q hq hw hs)
      _ ≤ valuation k w * 1 := by
        rw [pow_succ', mul_assoc]
        refine mul_le_mul' le_rfl ?_
        calc
          valuation k w ^ 2 * valuation k (q : k) ≤ 1 ^ 2 * 1 :=
            mul_le_mul' (pow_le_pow_left' hw.le 2) hq.le
          _ = 1 := by simp
      _ = valuation k w := mul_one _

private theorem WeierstrassCurve.valuation_tateCurveFormalError_combination_le (q : kˣ)
    (hq : valuation k (q : k) < 1) {w s s' : k} (hw : valuation k w < 1)
    (hs : valuation k s ≤ valuation k w) (hs' : valuation k s' ≤ valuation k w) :
    valuation k ((tateCurveFormalError (q : k) w s - tateCurveFormalError (q : k) w s') *
        (1 + s') + tateCurveFormalError (q : k) w s' * (s' - s)) ≤
      valuation k (q : k) * valuation k (s - s') := by
  have h1s' : valuation k (1 + s') = 1 := by
    simpa using (valuation k).map_add_eq_of_lt_left (x := (1 : k))
      (by simpa using hs'.trans_lt hw)
  refine ((valuation k).map_add _ _).trans (max_le ?_ ?_)
  · rw [map_mul, h1s', mul_one]
    exact valuation_tateCurveFormalError_sub_le q hq hw hs hs'
  · rw [map_mul, Valuation.map_sub_swap]
    exact mul_le_mul' (valuation_tateCurveFormalError_le q hq hw hs') le_rfl

private theorem WeierstrassCurve.valuation_tateCurveFormalCorrection_numerator_le (q : kˣ)
    (hq : valuation k (q : k) < 1) {w s s' : k} (hw : valuation k w < 1)
    (hs : valuation k s ≤ valuation k w) (hs' : valuation k s' ≤ valuation k w) :
    valuation k (s ^ 3 * tateCurveFormalError (q : k) w s * (1 + s')
        - s' ^ 3 * tateCurveFormalError (q : k) w s' * (1 + s)) ≤
      valuation k (q : k) * valuation k (s - s') := by
  have h1s' : valuation k (1 + s') = 1 := by
    simpa using (valuation k).map_add_eq_of_lt_left (x := (1 : k))
      (by simpa using hs'.trans_lt hw)
  rw [show s ^ 3 * tateCurveFormalError (q : k) w s * (1 + s')
      - s' ^ 3 * tateCurveFormalError (q : k) w s' * (1 + s) =
    (s ^ 3 - s' ^ 3) * tateCurveFormalError (q : k) w s * (1 + s')
      + s' ^ 3 * ((tateCurveFormalError (q : k) w s
        - tateCurveFormalError (q : k) w s') * (1 + s')
        + tateCurveFormalError (q : k) w s' * (s' - s)) by ring]
  refine ((valuation k).map_add _ _).trans (max_le ?_ ?_)
  · rw [map_mul, map_mul, h1s', mul_one]
    calc
      valuation k (s ^ 3 - s' ^ 3) * valuation k (tateCurveFormalError (q : k) w s) ≤
          valuation k (s - s') * valuation k (q : k) := by
        exact mul_le_mul' (valuation_pow_sub_pow_le (hs.trans hw.le) (hs'.trans hw.le) 3)
          (valuation_tateCurveFormalError_le q hq hw hs)
      _ = valuation k (q : k) * valuation k (s - s') := mul_comm _ _
  · rw [map_mul, map_pow]
    calc
      valuation k s' ^ 3 * valuation k
          ((tateCurveFormalError (q : k) w s - tateCurveFormalError (q : k) w s') *
            (1 + s') + tateCurveFormalError (q : k) w s' * (s' - s)) ≤
          1 * (valuation k (q : k) * valuation k (s - s')) :=
        mul_le_mul' ((pow_le_pow_left' (hs'.trans hw.le) 3).trans_eq (one_pow 3))
          (valuation_tateCurveFormalError_combination_le q hq hw hs hs')
      _ = valuation k (q : k) * valuation k (s - s') := one_mul _

private theorem WeierstrassCurve.valuation_tateCurveFormalCorrection_sub_le (q : kˣ)
    (hq : valuation k (q : k) < 1) {w s s' : k} (hw : valuation k w < 1)
    (hs : valuation k s ≤ valuation k w) (hs' : valuation k s' ≤ valuation k w) :
    valuation k (tateCurveFormalCorrection (q : k) w s
        - tateCurveFormalCorrection (q : k) w s') ≤
      max (valuation k w) (valuation k (q : k)) * valuation k (s - s') := by
  have h1s : valuation k (1 + s) = 1 := by
    simpa using (valuation k).map_add_eq_of_lt_left (x := (1 : k))
      (by simpa using hs.trans_lt hw)
  have h1s' : valuation k (1 + s') = 1 := by
    simpa using (valuation k).map_add_eq_of_lt_left (x := (1 : k))
      (by simpa using hs'.trans_lt hw)
  have h1s0 : (1 : k) + s ≠ 0 := fun h ↦ by rw [h, map_zero] at h1s; exact zero_ne_one h1s
  have h1s'0 : (1 : k) + s' ≠ 0 := fun h ↦ by rw [h, map_zero] at h1s'; exact zero_ne_one h1s'
  have hsplit : tateCurveFormalCorrection (q : k) w s
      - tateCurveFormalCorrection (q : k) w s' = w * (s - s')
        - ((s ^ 3 * tateCurveFormalError (q : k) w s * (1 + s')
          - s' ^ 3 * tateCurveFormalError (q : k) w s' * (1 + s)) /
            ((1 + s) * (1 + s'))) := by
    simp only [tateCurveFormalCorrection]
    field_simp
    ring
  rw [hsplit]
  refine ((valuation k).map_sub _ _).trans (max_le ?_ ?_)
  · rw [map_mul]
    exact mul_le_mul' (le_max_left _ _) le_rfl
  · rw [map_div₀, map_mul, h1s, h1s', one_mul, div_one]
    exact (valuation_tateCurveFormalCorrection_numerator_le q hq hw hs hs').trans
      (mul_le_mul' (le_max_right _ _) le_rfl)

private theorem WeierstrassCurve.exists_tateCurveFormalCorrection_fixedPoint (q : kˣ)
    (hq : valuation k (q : k) < 1) {w : k} (hw0 : w ≠ 0) (hw : valuation k w < 1) :
    ∃ t, valuation k t ≤ valuation k w ∧ t ≠ 0 ∧
      tateCurveFormalCorrection (q : k) w t = t := by
  obtain ⟨t, ht, hfix⟩ := TateCurve.exists_fixedPoint (tateCurveFormalCorrection (q : k) w)
    (r := valuation k w) (c := max (valuation k w) (valuation k (q : k))) (max_lt hw hq)
    (fun s hs ↦ valuation_tateCurveFormalCorrection_le q hq hw hs)
    (fun s s' hs hs' ↦ valuation_tateCurveFormalCorrection_sub_le q hq hw hs hs')
  refine ⟨t, ht, ?_, hfix⟩
  intro ht0
  rw [ht0] at hfix
  have hzero : tateCurveFormalCorrection (q : k) w 0 = w := by
    simp [tateCurveFormalCorrection]
  exact hw0 (hzero.symm.trans hfix)

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] in
private theorem WeierstrassCurve.tateCurve_ratio_eq_of_formalCorrection_fixedPoint
    {q w x y t : k} (hw : w = -x / y) (hw0 : w ≠ 0) (ht0 : t ≠ 0)
    (hfix : tateCurveFormalCorrection q w t = t) :
    tateX (1 + t) q * y = x * tateY (1 + t) q := by
  have h1t : (1 : k) + t ≠ 0 := by
    intro h
    have ht : t = -1 := by linear_combination h
    subst t
    simp [tateCurveFormalCorrection] at hfix
  have hy0 : y ≠ 0 := by
    intro hy
    apply hw0
    rw [hw, hy]
    simp
  have hC : w * (1 + t) ^ 2 - t ^ 3 * tateCurveFormalError q w t = t * (1 + t) := by
    have h := congrArg (fun z ↦ z * (1 + t)) hfix
    simp only [tateCurveFormalCorrection, sub_mul] at h
    rw [div_mul_cancel₀ _ h1t] at h
    linear_combination h
  have hXwY : tateX (1 + t) q + w * tateY (1 + t) q = 0 := by
    simp only [tateCurveFormalError] at hC
    have hmt : (1 : k) - (1 + t) ≠ 0 := by
      intro h
      exact ht0 (by linear_combination -h)
    have hpow : t ^ 6 * (tateX (1 + t) q + w * tateY (1 + t) q) = 0 := by
      field_simp at hC
      linear_combination hC
    rcases mul_eq_zero.mp hpow with h | h
    · exact absurd (pow_eq_zero_iff (by omega : (6 : ℕ) ≠ 0) |>.mp h) ht0
    · exact h
  have hxy := congrArg (fun z ↦ z * y) hXwY
  simp only [zero_mul, add_mul] at hxy
  rw [hw] at hxy
  have hdiv : -x / y * tateY (1 + t) q * y = -x * tateY (1 + t) q := by
    field_simp
  rw [hdiv] at hxy
  linear_combination hxy

private theorem WeierstrassCurve.tateCurvePoint_eq_of_formal_parameter (q : kˣ)
    (hq : valuation k (q : k) < 1) {x y t : k}
    (h : ((tateCurve (q : k))⁄k).Nonsingular x y) (hx : 1 < valuation k x) (ht0 : t ≠ 0)
    (ht : valuation k t < 1)
    (hr : tateX (1 + t) (q : k) * y = x * tateY (1 + t) (q : k)) :
    ∃ u : kˣ, tateCurvePoint q hq u = .some x y h := by
  have h1t1 : valuation k (1 + t) = 1 := by
    simpa using (valuation k).map_add_eq_of_lt_left (x := (1 : k)) (by simpa using ht)
  have h1t : (1 : k) + t ≠ 0 := fun h ↦ by rw [h, map_zero] at h1t1; exact zero_ne_one h1t1
  have hne1 : (1 : k) + t ≠ 1 := fun h ↦ ht0 (by linear_combination h)
  let u : kˣ := Units.mk0 (1 + t) h1t
  have hu_not : u ∉ Subgroup.zpowers q := by
    refine TateCurve.notMem_zpowers_of_annulus q u hq ?_ ?_ ?_
    · simpa only [u, Units.val_mk0, h1t1] using hq
    · simp only [u, Units.val_mk0, h1t1]
      exact le_rfl
    · simpa only [u, Units.val_mk0] using hne1
  have hEt : ((tateCurve (q : k))⁄k).Equation (tateX (1 + t) (q : k))
      (tateY (1 + t) (q : k)) := by
    simpa only [u, Units.val_mk0] using tateCurve_equation q hq u hu_not
  have hXt : 1 < valuation k (tateX (1 + t) (q : k)) := by
    rw [valuation_tateX_one_add q hq ht0 ht]
    exact one_lt_pow₀
      ((one_lt_inv₀ (zero_lt_iff.mpr ((valuation k).ne_zero_iff.mpr ht0))).mpr ht) two_ne_zero
  obtain ⟨hXx, hYy⟩ := tateCurve_eq_of_ratio_eq hq hEt h.1 hXt hx hr
  refine ⟨u, ?_⟩
  rw [tateCurvePoint, dif_neg hu_not]
  simp only [u, Units.val_mk0, hXx, hYy]

/-- **The formal-group piece of Tate surjectivity**: every point of `E_q(k)` with `|x| > 1`
is `φ(1 + t)` for some `0 < |t| < 1`; in particular it is in the image of `φ`
(Silverman ATAEC V.4, pp. 431–432). -/
theorem WeierstrassCurve.exists_tateCurvePoint_eq_of_one_lt (q : kˣ)
    (hq : valuation k (q : k) < 1) {x y : k}
    (h : ((tateCurve (q : k))⁄k).Nonsingular x y) (hx : 1 < valuation k x) :
    ∃ u : kˣ, tateCurvePoint q hq u = .some x y h := by
  have hy2 := tateCurve_valuation_y_sq hq h.1 hx
  let w : k := -x / y
  have hw0 : w ≠ 0 := by simpa only [w] using tateCurve_ratio_ne_zero hx hy2
  have hw2 := valuation_tateCurve_ratio_sq_mul hx hy2
  have hw : valuation k w < 1 := valuation_tateCurve_ratio_lt_one hx (by simpa only [w] using hw2)
  obtain ⟨t, ht, ht0, hfix⟩ := exists_tateCurveFormalCorrection_fixedPoint q hq hw0 hw
  refine tateCurvePoint_eq_of_formal_parameter q hq h hx ht0 (ht.trans_lt hw) ?_
  exact tateCurve_ratio_eq_of_formalCorrection_fixedPoint rfl hw0 ht0 hfix

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
private theorem WeierstrassCurve.tateCurve_two_mul_y_add_x_not_lt_one_aux {x y : k}
    (hx : valuation k x = 1) (hy : valuation k y = 1)
    (h2 : valuation k (2 : k) < 1) : ¬valuation k (2 * y + x) < 1 := by
  have h2y : valuation k (2 * y) < valuation k x := by
    rw [map_mul, hy, mul_one, hx]
    exact h2
  rw [(valuation k).map_add_eq_of_lt_right h2y, hx]
  exact lt_irrefl 1

private theorem WeierstrassCurve.tateCurve_xDeriv_eq_one_of_three_lt_one_aux {q x y : k}
    (hq : valuation k q < 1) (hx : valuation k x = 1) (hy : valuation k y = 1)
    (h3 : valuation k (3 : k) < 1) :
    valuation k (3 * x ^ 2 - y + tateA₄ q) = 1 := by
  have hA4 : valuation k (tateA₄ q) < 1 :=
    lt_of_le_of_lt (valuation_tateA₄_le q hq) hq
  have hsmall : valuation k (3 * x ^ 2 + tateA₄ q) < 1 := by
    refine lt_of_le_of_lt ((valuation k).map_add _ _) (max_lt ?_ hA4)
    rw [map_mul, map_pow, hx, one_pow, mul_one]
    exact h3
  rw [show 3 * x ^ 2 - y + tateA₄ q = (3 * x ^ 2 + tateA₄ q) + -y by ring,
    (valuation k).map_add_eq_of_lt_right (by rw [Valuation.map_neg, hy]; exact hsmall),
    Valuation.map_neg, hy]

private theorem WeierstrassCurve.tateCurve_one_add_six_mul_x_lt_one_aux {q x y : k}
    (hq : valuation k q < 1) (hx : valuation k x = 1)
    (h2 : valuation k (2 * y + x) < 1)
    (hD : valuation k (3 * x ^ 2 - y + tateA₄ q) < 1)
    (hv2 : valuation k (2 : k) ≤ 1) : valuation k (1 + 6 * x) < 1 := by
  have hid : x * (1 + 6 * x) =
      (2 * y + x) + 2 * (3 * x ^ 2 - y + tateA₄ q) - 2 * tateA₄ q := by
    ring
  have hb : valuation k (x * (1 + 6 * x)) < 1 := by
    rw [hid]
    refine lt_of_le_of_lt ((valuation k).map_sub _ _) (max_lt (lt_of_le_of_lt
      ((valuation k).map_add _ _) (max_lt h2 ?_)) ?_)
    · rw [map_mul]
      exact (mul_le_mul' hv2 le_rfl).trans_lt (by simpa using hD)
    · rw [map_mul]
      exact (mul_le_mul' hv2 le_rfl).trans_lt (by
        simpa using lt_of_le_of_lt (valuation_tateA₄_le q hq) hq)
  rwa [map_mul, hx, one_mul] at hb

private theorem WeierstrassCurve.tateCurve_xDeriv_left_factor_le_one_aux {q x y : k}
    (hq : valuation k q < 1) (hx : valuation k x = 1)
    (hD : valuation k (3 * x ^ 2 - y + tateA₄ q) ≤ 1)
    (hv2 : valuation k (2 : k) ≤ 1) (hv6 : valuation k (6 : k) ≤ 1) :
    valuation k (tateA₄ q + 6 * x ^ 2 - 2 * (3 * x ^ 2 - y + tateA₄ q) + x) ≤ 1 := by
  have hx2 : valuation k (6 * x ^ 2) ≤ 1 := by
    rw [map_mul, map_pow, hx, one_pow, mul_one]
    exact hv6
  refine le_trans ((valuation k).map_add _ _) (max_le (le_trans
    ((valuation k).map_sub _ _) (max_le (le_trans ((valuation k).map_add _ _)
    (max_le ((valuation_tateA₄_le q hq).trans hq.le) hx2)) ?_)) hx.le)
  rw [map_mul]
  simpa using mul_le_mul' hv2 hD

omit [IsNonarchimedeanLocalField k] in
private theorem WeierstrassCurve.tateCurve_xDeriv_right_factor_le_one_aux {q x y : k}
    (hx : valuation k x = 1) (hD : valuation k (3 * x ^ 2 - y + tateA₄ q) ≤ 1)
    (hv6 : valuation k (6 : k) ≤ 1) :
    valuation k ((3 * x ^ 2 - y + tateA₄ q) - 6 * x ^ 2 - x) ≤ 1 := by
  have hx2 : valuation k (6 * x ^ 2) ≤ 1 := by
    rw [map_mul, map_pow, hx, one_pow, mul_one]
    exact hv6
  exact le_trans ((valuation k).map_sub _ _)
    (max_le (le_trans ((valuation k).map_sub _ _) (max_le hD hx2)) hx.le)

private theorem WeierstrassCurve.tateCurve_nine_mul_x_add_two_lt_one_aux {q x y : k}
    (hq : valuation k q < 1)
    (h : y ^ 2 + x * y = x ^ 3 + tateA₄ q * x + tateA₆ q)
    (hx : valuation k x = 1) (hD : valuation k (3 * x ^ 2 - y + tateA₄ q) < 1)
    (hv2 : valuation k (2 : k) ≤ 1) (hv6 : valuation k (6 : k) ≤ 1) :
    valuation k (9 * x + 2) < 1 := by
  have hid : x ^ 3 * (9 * x + 2) =
      (y ^ 2 + x * y - (x ^ 3 + tateA₄ q * x + tateA₆ q)) +
        (tateA₄ q * x + tateA₆ q) -
      (tateA₄ q * (tateA₄ q + 6 * x ^ 2 - 2 * (3 * x ^ 2 - y + tateA₄ q) + x) +
        (3 * x ^ 2 - y + tateA₄ q) *
          ((3 * x ^ 2 - y + tateA₄ q) - 6 * x ^ 2 - x)) := by
    ring
  have hA4 : valuation k (tateA₄ q) < 1 :=
    lt_of_le_of_lt (valuation_tateA₄_le q hq) hq
  have hA6 : valuation k (tateA₆ q) < 1 :=
    lt_of_le_of_lt (valuation_tateA₆_le q hq) hq
  have hU := tateCurve_xDeriv_left_factor_le_one_aux hq hx hD.le hv2 hv6
  have hV := tateCurve_xDeriv_right_factor_le_one_aux hx hD.le hv6
  have hb : valuation k (x ^ 3 * (9 * x + 2)) < 1 := by
    rw [hid, show y ^ 2 + x * y - (x ^ 3 + tateA₄ q * x + tateA₆ q) = 0 by rw [h, sub_self],
      zero_add]
    refine lt_of_le_of_lt ((valuation k).map_sub _ _) (max_lt (lt_of_le_of_lt
      ((valuation k).map_add _ _) (max_lt ?_ hA6)) (lt_of_le_of_lt
      ((valuation k).map_add _ _) (max_lt ?_ ?_)))
    · rw [map_mul, hx, mul_one]
      exact hA4
    · rw [map_mul]
      exact (mul_le_mul' le_rfl hU).trans_lt (by simpa using hA4)
    · rw [map_mul]
      exact (mul_le_mul' le_rfl hV).trans_lt (by simpa using hD)
  rwa [map_mul, map_pow, hx, one_pow, one_mul] at hb

private theorem WeierstrassCurve.tateCurve_xDeriv_not_lt_one_of_two_three_eq_one_aux
    {q x y : k} (hq : valuation k q < 1)
    (h : y ^ 2 + x * y = x ^ 3 + tateA₄ q * x + tateA₆ q)
    (hx : valuation k x = 1) (h2 : valuation k (2 * y + x) < 1)
    (hv2 : valuation k (2 : k) = 1) (hv3 : valuation k (3 : k) = 1) :
    ¬valuation k (3 * x ^ 2 - y + tateA₄ q) < 1 := by
  intro hD
  have hv6 : valuation k (6 : k) ≤ 1 := valuation_natCast_le_one 6
  have hstep1 := tateCurve_one_add_six_mul_x_lt_one_aux hq hx h2 hD hv2.le
  have hstep2 := tateCurve_nine_mul_x_add_two_lt_one_aux hq h hx hD hv2.le hv6
  have hid : (-1 : k) = 3 * (1 + 6 * x) - 2 * (9 * x + 2) := by ring
  have : valuation k (-1 : k) < 1 := by
    rw [hid]
    refine lt_of_le_of_lt ((valuation k).map_sub _ _) (max_lt ?_ ?_)
    · rw [map_mul, hv3, one_mul]
      exact hstep1
    · rw [map_mul, hv2, one_mul]
      exact hstep2
  simp at this

private theorem WeierstrassCurve.tateCurve_xDeriv_eq_one_of_two_three_eq_one_aux
    {q x y : k} (hq : valuation k q < 1)
    (h : y ^ 2 + x * y = x ^ 3 + tateA₄ q * x + tateA₆ q)
    (hx : valuation k x = 1) (hy : valuation k y = 1)
    (h2 : valuation k (2 * y + x) < 1) (hv2 : valuation k (2 : k) = 1)
    (hv3 : valuation k (3 : k) = 1) :
    valuation k (3 * x ^ 2 - y + tateA₄ q) = 1 := by
  have hle : valuation k (3 * x ^ 2 - y + tateA₄ q) ≤ 1 := by
    refine le_trans ((valuation k).map_add _ _) (max_le (le_trans ((valuation k).map_sub _ _)
      (max_le ?_ hy.le)) ((valuation_tateA₄_le q hq).trans hq.le))
    rw [map_mul, map_pow, hx, one_pow, mul_one]
    exact hv3.le
  exact hle.lt_or_eq.resolve_left <|
    tateCurve_xDeriv_not_lt_one_of_two_three_eq_one_aux hq h hx h2 hv2 hv3

/-- Nonsingularity of the reduction, made elementary: a point of `E_q` with `|x| = |y| = 1`
and `|2y + x| < 1` has `|3x² - y + a₄| = 1`. (The reduced point is a smooth point of the
nodal cubic, so not both partial derivatives vanish; the three cases `|2| < 1`, `|3| < 1`,
`|2| = |3| = 1` are handled by explicit congruences.) -/
theorem WeierstrassCurve.tateCurve_valuation_xDeriv_eq_one {q x y : k}
    (hq : valuation k q < 1) (h : ((tateCurve q)⁄k).Equation x y)
    (hx : valuation k x = 1) (hy : valuation k y = 1)
    (h2 : valuation k (2 * y + x) < 1) :
    valuation k (3 * x ^ 2 - y + tateA₄ q) = 1 := by
  rw [tateCurve_equation_iff] at h
  rcases lt_or_eq_of_le (valuation_natCast_le_one (R := k) 2) with hv2 | hv2
  · exact (tateCurve_two_mul_y_add_x_not_lt_one_aux hx hy hv2 h2).elim
  rcases lt_or_eq_of_le (valuation_natCast_le_one (R := k) 3) with hv3 | hv3
  · exact tateCurve_xDeriv_eq_one_of_three_lt_one_aux hq hx hy hv3
  · exact tateCurve_xDeriv_eq_one_of_two_three_eq_one_aux hq h hx hy h2 hv2 hv3

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] in
/-- `negY` of the Tate curve: `-y - x`. -/
private theorem WeierstrassCurve.tateCurve_negY (q x y : k) :
    ((tateCurve q)⁄k).negY x y = -y - x := by
  rw [show (tateCurve q)⁄k = tateCurve q by
    simp only [WeierstrassCurve.baseChange, Algebra.algebraMap_self, WeierstrassCurve.map_id]]
  rw [Affine.negY, show (tateCurve q).a₁ = 1 from rfl, show (tateCurve q).a₃ = 0 from rfl]
  ring

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] in
/-- `addX` of the Tate curve: `ℓ² + ℓ - x₁ - x₂`. -/
private theorem WeierstrassCurve.tateCurve_addX (q x₁ x₂ ℓ : k) :
    ((tateCurve q)⁄k).addX x₁ x₂ ℓ = ℓ ^ 2 + ℓ - x₁ - x₂ := by
  rw [show (tateCurve q)⁄k = tateCurve q by
    simp only [WeierstrassCurve.baseChange, Algebra.algebraMap_self, WeierstrassCurve.map_id]]
  rw [Affine.addX, show (tateCurve q).a₁ = 1 from rfl, show (tateCurve q).a₂ = 0 from rfl]
  ring

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] in
open scoped Classical in
/-- The doubling slope of the Tate curve: `(3x² + a₄ - y)/(2y + x)`. -/
private theorem WeierstrassCurve.tateCurve_slope_self {q x y : k}
    (h2 : y ≠ ((tateCurve q)⁄k).negY x y) :
    ((tateCurve q)⁄k).slope x x y y = (3 * x ^ 2 + tateA₄ q - y) / (2 * y + x) := by
  have hcollapse : (tateCurve q)⁄k = tateCurve q := by
    simp only [WeierstrassCurve.baseChange, Algebra.algebraMap_self, WeierstrassCurve.map_id]
  rw [Affine.slope_of_Y_ne rfl h2, tateCurve_negY,
    show ((tateCurve q)⁄k).a₂ = 0 by rw [hcollapse]; exact rfl,
    show ((tateCurve q)⁄k).a₄ = tateA₄ q by rw [hcollapse]; exact rfl,
    show ((tateCurve q)⁄k).a₁ = 1 by rw [hcollapse]; exact rfl]
  congr 1 <;> ring

omit [IsNonarchimedeanLocalField k] in
/-- The `x`-coordinate of a chord sum with slope of valuation `> 1` is large: in
`addX = ℓ² + ℓ - x₁ - x₂` the `ℓ²` term dominates. -/
private theorem WeierstrassCurve.tateCurve_valuation_addX_of_one_lt {q x₁ x₂ ℓ : k}
    (hx₁ : valuation k x₁ ≤ 1) (hx₂ : valuation k x₂ ≤ 1) (hℓ : 1 < valuation k ℓ) :
    1 < valuation k (((tateCurve q)⁄k).addX x₁ x₂ ℓ) := by
  have hℓ0 : (0 : ValueGroupWithZero k) < valuation k ℓ := lt_trans zero_lt_one hℓ
  have htail : valuation k (ℓ - x₁ - x₂) = valuation k ℓ := by
    rw [show ℓ - x₁ - x₂ = ℓ + (-x₁ - x₂) by ring]
    refine (valuation k).map_add_eq_of_lt_left ?_
    refine lt_of_le_of_lt (le_trans ((valuation k).map_sub _ _) (max_le ?_ hx₂)) hℓ
    rw [Valuation.map_neg]
    exact hx₁
  have hsq : valuation k ℓ < valuation k (ℓ ^ 2) := by
    rw [map_pow, pow_two]
    calc valuation k ℓ = 1 * valuation k ℓ := (one_mul _).symm
      _ < valuation k ℓ * valuation k ℓ := (mul_lt_mul_iff_left₀ hℓ0).mpr hℓ
  rw [tateCurve_addX, show ℓ ^ 2 + ℓ - x₁ - x₂ = ℓ ^ 2 + (ℓ - x₁ - x₂) by ring,
    (valuation k).map_add_eq_of_lt_left (by rw [htail]; exact hsq), map_pow]
  calc (1 : ValueGroupWithZero k) < valuation k ℓ := hℓ
    _ ≤ valuation k ℓ ^ 2 := by
        calc valuation k ℓ = valuation k ℓ ^ 1 := (pow_one _).symm
          _ ≤ valuation k ℓ ^ 2 := pow_le_pow_right' hℓ.le (by omega)

open scoped Classical in
private theorem WeierstrassCurve.tateCurve_sub_of_close_of_x_eq_of_not_two_torsion_aux
    {q x y y' : k} (hq : valuation k q < 1) (h : ((tateCurve q)⁄k).Nonsingular x y)
    (h' : ((tateCurve q)⁄k).Nonsingular x y') (hx : valuation k x = 1)
    (hy : valuation k y = 1) (h2yx : valuation k (2 * y + x) < 1)
    (hyneg : y = -y' - x) (h2tor : y ≠ ((tateCurve q)⁄k).negY x y) :
    ∃ (x'' y'' : k) (h'' : ((tateCurve q)⁄k).Nonsingular x'' y''),
      Affine.Point.some x y h - Affine.Point.some x y' h' = .some x'' y'' h'' ∧
        1 < valuation k x'' := by
  have hnegY' : ((tateCurve q)⁄k).negY x y' = y := by
    rw [tateCurve_negY]
    exact hyneg.symm
  have hyne : y ≠ ((tateCurve q)⁄k).negY x (((tateCurve q)⁄k).negY x y') := by
    rw [Affine.negY_negY]
    intro hyy'eq
    rw [tateCurve_negY] at h2tor
    exact h2tor (by linear_combination hyneg + hyy'eq)
  rw [sub_eq_add_neg, Affine.Point.neg_some]
  refine ⟨_, _, _, Affine.Point.add_of_Y_ne hyne, ?_⟩
  rw [hnegY', tateCurve_slope_self h2tor]
  have hden0 : (2 : k) * y + x ≠ 0 := by
    intro h0
    rw [tateCurve_negY] at h2tor
    exact h2tor (by linear_combination h0)
  have hnum : valuation k (3 * x ^ 2 + tateA₄ q - y) = 1 := by
    rw [show (3 : k) * x ^ 2 + tateA₄ q - y = 3 * x ^ 2 - y + tateA₄ q by ring]
    exact tateCurve_valuation_xDeriv_eq_one hq h.1 hx hy h2yx
  refine tateCurve_valuation_addX_of_one_lt hx.le hx.le ?_
  rw [map_div₀, hnum, one_div]
  exact (one_lt_inv₀ (zero_lt_iff.mpr ((valuation k).ne_zero_iff.mpr hden0))).mpr h2yx

open scoped Classical in
private theorem WeierstrassCurve.tateCurve_sub_of_close_of_negY_eq_aux {q x y y' : k}
    (hq : valuation k q < 1) (h : ((tateCurve q)⁄k).Nonsingular x y)
    (h' : ((tateCurve q)⁄k).Nonsingular x y') (hx : valuation k x = 1)
    (hy : valuation k y = 1) (hyy : valuation k (y - y') < 1) (hyneg : y = -y' - x) :
    Affine.Point.some x y h - Affine.Point.some x y' h' = 0 ∨
      ∃ (x'' y'' : k) (h'' : ((tateCurve q)⁄k).Nonsingular x'' y''),
        Affine.Point.some x y h - Affine.Point.some x y' h' = .some x'' y'' h'' ∧
          1 < valuation k x'' := by
  have h2yx : valuation k (2 * y + x) < 1 := by
    rw [show (2 : k) * y + x = y - y' + (y - (-y' - x)) by ring, ← hyneg, sub_self,
      add_zero]
    exact hyy
  have hnegY' : ((tateCurve q)⁄k).negY x y' = y := by
    rw [tateCurve_negY]
    exact hyneg.symm
  by_cases h2tor : y = ((tateCurve q)⁄k).negY x y
  · left
    rw [sub_eq_add_neg, Affine.Point.neg_some]
    refine Affine.Point.add_of_Y_eq rfl ?_
    rw [hnegY']
    exact h2tor
  · right
    exact tateCurve_sub_of_close_of_x_eq_of_not_two_torsion_aux hq h h' hx hy h2yx hyneg h2tor

open scoped Classical in
private theorem WeierstrassCurve.tateCurve_sub_of_close_of_x_eq_aux {q x y x' y' : k}
    (hq : valuation k q < 1) (h : ((tateCurve q)⁄k).Nonsingular x y)
    (h' : ((tateCurve q)⁄k).Nonsingular x' y') (hx : valuation k x = 1)
    (hy : valuation k y = 1) (hyy : valuation k (y - y') < 1) (hxx' : x = x') :
    Affine.Point.some x y h - Affine.Point.some x' y' h' = 0 ∨
      ∃ (x'' y'' : k) (h'' : ((tateCurve q)⁄k).Nonsingular x'' y''),
        Affine.Point.some x y h - Affine.Point.some x' y' h' = .some x'' y'' h'' ∧
          1 < valuation k x'' := by
  subst x'
  rcases Affine.Y_eq_of_X_eq h.1 h'.1 rfl with hyy' | hyneg
  · left
    subst y'
    rw [sub_eq_add_neg, Affine.Point.neg_some]
    exact Affine.Point.add_of_Y_eq rfl (Affine.negY_negY _ _).symm
  · rw [tateCurve_negY] at hyneg
    exact tateCurve_sub_of_close_of_negY_eq_aux hq h h' hx hy hyy hyneg

omit [IsNonarchimedeanLocalField k] in
private theorem WeierstrassCurve.valuation_tateCurve_chord_companion_eq_one_aux {q x y x' y' : k}
    (hD : valuation k (3 * x ^ 2 - y + tateA₄ q) = 1) (hx : valuation k x = 1)
    (hx' : valuation k x' = 1) (hxx : valuation k (x - x') < 1)
    (hyy : valuation k (y - y') < 1) :
    valuation k (x ^ 2 + x * x' + x' ^ 2 + tateA₄ q - y') = 1 := by
  rw [show x ^ 2 + x * x' + x' ^ 2 + tateA₄ q - y' =
      (3 * x ^ 2 - y + tateA₄ q) +
        (x * (x' - x) + (x' - x) * (x' + x) + (y - y')) by ring]
  rw [(valuation k).map_add_eq_of_lt_left (by
    rw [hD]
    refine lt_of_le_of_lt ((valuation k).map_add _ _) (max_lt (lt_of_le_of_lt
      ((valuation k).map_add _ _) (max_lt ?_ ?_)) hyy)
    · rw [map_mul, hx, one_mul, Valuation.map_sub_swap]
      exact hxx
    · rw [map_mul]
      calc valuation k (x' - x) * valuation k (x' + x)
          ≤ valuation k (x' - x) * 1 := by
            refine mul_le_mul' le_rfl ?_
            exact le_trans ((valuation k).map_add _ _) (max_le hx'.le hx.le)
        _ = valuation k (x' - x) := mul_one _
        _ < 1 := by rw [Valuation.map_sub_swap]; exact hxx), hD]

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
private theorem valuation_lt_right_of_mul_eq_mul_of_right_eq_one_aux {a b c d : k}
    (ha0 : a ≠ 0) (hb : valuation k b < 1) (hc : valuation k c = 1)
    (h : b * d = a * c) : valuation k a < valuation k d := by
  have hc0 : c ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hc
    exact zero_ne_one hc
  have hb0 : b ≠ 0 := by
    intro h0
    have hac : a * c = 0 := by rw [← h, h0, zero_mul]
    exact ha0 ((mul_eq_zero.mp hac).resolve_right hc0)
  have hva0 : valuation k a ≠ 0 := (valuation k).ne_zero_iff.mpr ha0
  have hv : valuation k d * valuation k b = valuation k a := by
    have heq := congrArg (valuation k) h
    rw [map_mul, map_mul, hc, mul_one] at heq
    rw [mul_comm]
    exact heq
  by_contra hle
  rw [not_lt] at hle
  have hcontra : valuation k a < valuation k a := by
    calc valuation k a = valuation k d * valuation k b := hv.symm
      _ ≤ valuation k a * valuation k b := mul_le_mul' hle le_rfl
      _ = valuation k b * valuation k a := mul_comm _ _
      _ < 1 * valuation k a :=
        (mul_lt_mul_iff_left₀ (zero_lt_iff.mpr hva0)).mpr hb
      _ = valuation k a := one_mul _
  exact (lt_irrefl _) hcontra

private theorem WeierstrassCurve.valuation_tateCurve_chord_slope_gt_one_of_deriv_lt_aux
    {q x y x' y' : k} (hq : valuation k q < 1) (h : ((tateCurve q)⁄k).Equation x y)
    (h' : ((tateCurve q)⁄k).Equation x' y') (hx : valuation k x = 1)
    (hx' : valuation k x' = 1) (hy : valuation k y = 1)
    (hxx : valuation k (x - x') < 1) (hyy : valuation k (y - y') < 1)
    (hxx' : x ≠ x') (hd : valuation k (2 * y + x) < 1) :
    1 < valuation k ((y + y' + x') / (x - x')) := by
  have hD : valuation k (3 * x ^ 2 - y + tateA₄ q) = 1 :=
    tateCurve_valuation_xDeriv_eq_one hq h hx hy hd
  have hC1 := valuation_tateCurve_chord_companion_eq_one_aux hD hx hx' hxx hyy
  rw [tateCurve_equation_iff] at h h'
  have hBC : (y - y') * (y + x + y') =
      (x - x') * (x ^ 2 + x * x' + x' ^ 2 + tateA₄ q - y') := by
    linear_combination h - h'
  have hBgt : valuation k (x - x') < valuation k (y + x + y') :=
    valuation_lt_right_of_mul_eq_mul_of_right_eq_one_aux (sub_ne_zero.mpr hxx') hyy hC1 hBC
  have hAB : valuation k (y + y' + x') = valuation k (y + x + y') := by
    rw [show y + y' + x' = (y + x + y') + (x' - x) by ring]
    exact (valuation k).map_add_eq_of_lt_left
      (by rw [Valuation.map_sub_swap]; exact hBgt)
  have hvsub0 : valuation k (x - x') ≠ 0 := (valuation k).ne_zero_iff.mpr (sub_ne_zero.mpr hxx')
  rw [map_div₀, hAB, div_eq_mul_inv]
  calc (1 : ValueGroupWithZero k)
      = valuation k (x - x') * (valuation k (x - x'))⁻¹ :=
        (mul_inv_cancel₀ hvsub0).symm
    _ < valuation k (y + x + y') * (valuation k (x - x'))⁻¹ :=
      (mul_lt_mul_iff_left₀ (zero_lt_iff.mpr (inv_ne_zero hvsub0))).mpr hBgt

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
private theorem WeierstrassCurve.valuation_tateCurve_chord_slope_gt_one_of_deriv_eq_one_aux
    {x y x' y' : k} (hxx : valuation k (x - x') < 1)
    (hyy : valuation k (y - y') < 1) (hxx' : x ≠ x')
    (hd : valuation k (2 * y + x) = 1) :
    1 < valuation k ((y + y' + x') / (x - x')) := by
  have hA1 : valuation k (y + y' + x') = 1 := by
    rw [show y + y' + x' = (2 * y + x) + ((y' - y) + (x' - x)) by ring]
    rw [(valuation k).map_add_eq_of_lt_left (by
      rw [hd]
      refine lt_of_le_of_lt ((valuation k).map_add _ _) (max_lt ?_ ?_)
      · rw [Valuation.map_sub_swap]
        exact hyy
      · rw [Valuation.map_sub_swap]
        exact hxx), hd]
  have hvsub0 : valuation k (x - x') ≠ 0 :=
    (valuation k).ne_zero_iff.mpr (sub_ne_zero.mpr hxx')
  rw [map_div₀, hA1, one_div]
  exact (one_lt_inv₀ (zero_lt_iff.mpr hvsub0)).mpr hxx

private theorem WeierstrassCurve.valuation_tateCurve_chord_slope_gt_one_aux {q x y x' y' : k}
    (hq : valuation k q < 1) (h : ((tateCurve q)⁄k).Equation x y)
    (h' : ((tateCurve q)⁄k).Equation x' y') (hx : valuation k x = 1)
    (hx' : valuation k x' = 1) (hy : valuation k y = 1)
    (hxx : valuation k (x - x') < 1) (hyy : valuation k (y - y') < 1)
    (hxx' : x ≠ x') : 1 < valuation k ((y + y' + x') / (x - x')) := by
  have hva : valuation k (2 * y + x) ≤ 1 := by
    refine le_trans ((valuation k).map_add _ _) (max_le ?_ hx.le)
    rw [map_mul, hy, mul_one]
    simpa using valuation_natCast_le_one (R := k) 2
  rcases lt_or_eq_of_le hva with hd | hd
  · exact valuation_tateCurve_chord_slope_gt_one_of_deriv_lt_aux hq h h' hx hx' hy hxx hyy hxx' hd
  · exact valuation_tateCurve_chord_slope_gt_one_of_deriv_eq_one_aux hxx hyy hxx' hd

open scoped Classical in
private theorem WeierstrassCurve.tateCurve_sub_of_close_of_x_ne_aux {q x y x' y' : k}
    (hq : valuation k q < 1) (h : ((tateCurve q)⁄k).Nonsingular x y)
    (h' : ((tateCurve q)⁄k).Nonsingular x' y') (hx : valuation k x = 1)
    (hx' : valuation k x' = 1) (hy : valuation k y = 1)
    (hxx : valuation k (x - x') < 1) (hyy : valuation k (y - y') < 1) (hxx' : x ≠ x') :
    Affine.Point.some x y h - Affine.Point.some x' y' h' = 0 ∨
      ∃ (x'' y'' : k) (h'' : ((tateCurve q)⁄k).Nonsingular x'' y''),
        Affine.Point.some x y h - Affine.Point.some x' y' h' = .some x'' y'' h'' ∧
          1 < valuation k x'' := by
  right
  rw [sub_eq_add_neg, Affine.Point.neg_some]
  refine ⟨_, _, _, Affine.Point.add_of_X_ne hxx', ?_⟩
  rw [tateCurve_negY, Affine.slope_of_X_ne hxx',
    show y - (-y' - x') = y + y' + x' by ring]
  exact tateCurve_valuation_addX_of_one_lt hx.le hx'.le <|
    valuation_tateCurve_chord_slope_gt_one_aux hq h.1 h'.1 hx hx' hy hxx hyy hxx'

open scoped Classical in
/-- **Same reduction ⟹ difference in the formal-group piece**: two `𝒪ˣ`-coordinate points
of `E_q(k)` that are congruent mod `𝔪` differ by a point with `|x| > 1` (or are equal).
Replaces Silverman's appeal to reduction theory [AEC VII.2.1] by a direct estimate on the
subtraction formula, using `tateCurve_valuation_xDeriv_eq_one` when the chord degenerates
at a `2`-torsion reduction. -/
theorem WeierstrassCurve.tateCurve_sub_of_close {q : k}
    (hq : valuation k q < 1) {x y x' y' : k} (h : ((tateCurve q)⁄k).Nonsingular x y)
    (h' : ((tateCurve q)⁄k).Nonsingular x' y') (hx : valuation k x = 1)
    (hy : valuation k y = 1) (hxx : valuation k (x - x') < 1)
    (hyy : valuation k (y - y') < 1) :
    Affine.Point.some x y h - Affine.Point.some x' y' h' = 0 ∨
      ∃ (x'' y'' : k) (h'' : ((tateCurve q)⁄k).Nonsingular x'' y''),
        Affine.Point.some x y h - Affine.Point.some x' y' h' = .some x'' y'' h'' ∧
          1 < valuation k x'' := by
  have hx' : valuation k x' = 1 := by
    rw [show x' = x + -(x - x') by ring,
      (valuation k).map_add_eq_of_lt_left (by rw [Valuation.map_neg, hx]; exact hxx), hx]
  by_cases hxx' : x = x'
  · exact tateCurve_sub_of_close_of_x_eq_aux hq h h' hx hy hyy hxx'
  · exact tateCurve_sub_of_close_of_x_ne_aux hq h h' hx hx' hy hxx hyy hxx'

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
private theorem WeierstrassCurve.valuation_nodal_parameter_eq_one_aux {x y : k}
    (hx : valuation k x = 1) (hy : valuation k y = 1) :
    valuation k (y ^ 2 / x ^ 3) = 1 := by
  rw [map_div₀, map_pow, map_pow, hx, hy, one_pow, one_pow, div_one]

private theorem WeierstrassCurve.nodal_parameter_denominator_facts_aux {q x y : k}
    (hq : valuation k q < 1) (h : ((tateCurve q)⁄k).Equation x y)
    (hx : valuation k x = 1) (hy : valuation k y = 1) :
    x * y - tateA₄ q * x - tateA₆ q ≠ 0 ∧
      valuation k (x * y - tateA₄ q * x - tateA₆ q) = 1 ∧
      1 - y ^ 2 / x ^ 3 = (x * y - tateA₄ q * x - tateA₆ q) / x ^ 3 ∧
      valuation k (1 - y ^ 2 / x ^ 3) = 1 := by
  rw [tateCurve_equation_iff] at h
  have hx0 : x ≠ 0 := fun h0 ↦ by rw [h0, map_zero] at hx; exact zero_ne_one hx
  have hve : valuation k (x * y - tateA₄ q * x - tateA₆ q) = 1 := by
    rw [show x * y - tateA₄ q * x - tateA₆ q =
        x * y + (-(tateA₄ q * x) - tateA₆ q) by ring,
      (valuation k).map_add_eq_of_lt_left ?_, map_mul, hx, hy, one_mul]
    rw [map_mul, hx, hy, one_mul]
    refine lt_of_le_of_lt (le_trans ((valuation k).map_sub _ _) (max_le ?_
      (valuation_tateA₆_le q hq))) hq
    rw [Valuation.map_neg, map_mul]
    calc valuation k (tateA₄ q) * valuation k x ≤ valuation k q * 1 :=
          mul_le_mul' (valuation_tateA₄_le q hq) hx.le
      _ = valuation k q := mul_one _
  have he0 : x * y - tateA₄ q * x - tateA₆ q ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hve
    exact zero_ne_one hve
  have hcube : x ^ 3 - y ^ 2 = x * y - tateA₄ q * x - tateA₆ q := by
    linear_combination -h
  have h1mu : 1 - y ^ 2 / x ^ 3 = (x * y - tateA₄ q * x - tateA₆ q) / x ^ 3 := by
    rw [← hcube]
    field_simp
  have hv1mu : valuation k (1 - y ^ 2 / x ^ 3) = 1 := by
    rw [h1mu, map_div₀, hve, map_pow, hx, one_pow, div_one]
  exact ⟨he0, hve, h1mu, hv1mu⟩

private theorem WeierstrassCurve.valuation_nodal_coefficient_error_le_aux {q x : k}
    (hq : valuation k q < 1) (hx : valuation k x = 1) :
    valuation k (tateA₄ q * x + tateA₆ q) ≤ valuation k q := by
  refine le_trans ((valuation k).map_add _ _) (max_le ?_ (valuation_tateA₆_le _ hq))
  rw [map_mul]
  calc valuation k (tateA₄ q) * valuation k x ≤ valuation k q * 1 :=
        mul_le_mul' (valuation_tateA₄_le _ hq) hx.le
    _ = valuation k q := mul_one _

private theorem WeierstrassCurve.valuation_nodal_X_sub_le_aux {q x y : k}
    (hq : valuation k q < 1) (hx : valuation k x = 1) (hy : valuation k y = 1)
    (hx0 : x ≠ 0) (he0 : x * y - tateA₄ q * x - tateA₆ q ≠ 0)
    (hve : valuation k (x * y - tateA₄ q * x - tateA₆ q) = 1)
    (h1mu : 1 - y ^ 2 / x ^ 3 = (x * y - tateA₄ q * x - tateA₆ q) / x ^ 3)
    (hb1 : valuation k (tateA₄ q * x + tateA₆ q) ≤ valuation k q) :
    valuation k ((y ^ 2 / x ^ 3) / (1 - y ^ 2 / x ^ 3) ^ 2 - x) ≤ valuation k q := by
  have hid : (y ^ 2 / x ^ 3) / (1 - y ^ 2 / x ^ 3) ^ 2 - x =
      x * ((tateA₄ q * x + tateA₆ q) * (2 * x * y - tateA₄ q * x - tateA₆ q)) /
        (x * y - tateA₄ q * x - tateA₆ q) ^ 2 := by
    obtain ⟨e, he⟩ : ∃ e, e = x * y - tateA₄ q * x - tateA₆ q := ⟨_, rfl⟩
    have he0' : e ≠ 0 := by rw [he]; exact he0
    have hx3 : x ^ 3 ≠ 0 := pow_ne_zero 3 hx0
    rw [h1mu, ← he, show tateA₄ q * x + tateA₆ q = x * y - e by rw [he]; ring,
      show 2 * x * y - tateA₄ q * x - tateA₆ q = x * y + e by rw [he]; ring]
    field_simp
    ring
  rw [hid, map_div₀, map_pow, hve, one_pow, div_one, map_mul, hx, one_mul, map_mul]
  have hb2 : valuation k (2 * x * y - tateA₄ q * x - tateA₆ q) ≤ 1 := by
    refine le_trans ((valuation k).map_sub _ _) (max_le (le_trans
      ((valuation k).map_sub _ _) (max_le ?_ ?_)) ?_)
    · rw [map_mul, map_mul, hx, hy, mul_one, mul_one]
      simpa using (valuation_natCast_le_one (R := k) 2)
    · rw [map_mul]
      calc valuation k (tateA₄ q) * valuation k x ≤ 1 * 1 :=
            mul_le_mul' (le_trans (valuation_tateA₄_le _ hq) hq.le) hx.le
        _ = 1 := one_mul 1
    · exact le_trans (valuation_tateA₆_le _ hq) hq.le
  calc valuation k (tateA₄ q * x + tateA₆ q) *
        valuation k (2 * x * y - tateA₄ q * x - tateA₆ q) ≤ valuation k q * 1 :=
        mul_le_mul' hb1 hb2
    _ = valuation k q := mul_one _

omit [IsNonarchimedeanLocalField k] in
private theorem WeierstrassCurve.valuation_nodal_Y_sub_le_aux {q x y : k}
    (hx : valuation k x = 1) (hy : valuation k y = 1)
    (hx0 : x ≠ 0) (he0 : x * y - tateA₄ q * x - tateA₆ q ≠ 0)
    (hve : valuation k (x * y - tateA₄ q * x - tateA₆ q) = 1)
    (h1mu : 1 - y ^ 2 / x ^ 3 = (x * y - tateA₄ q * x - tateA₆ q) / x ^ 3)
    (hb1 : valuation k (tateA₄ q * x + tateA₆ q) ≤ valuation k q) :
    valuation k ((y ^ 2 / x ^ 3) ^ 2 / (1 - y ^ 2 / x ^ 3) ^ 3 - y) ≤ valuation k q := by
  have hid : (y ^ 2 / x ^ 3) ^ 2 / (1 - y ^ 2 / x ^ 3) ^ 3 - y =
      y * ((tateA₄ q * x + tateA₆ q) * ((x * y) ^ 2 +
        x * y * (x * y - tateA₄ q * x - tateA₆ q) +
        (x * y - tateA₄ q * x - tateA₆ q) ^ 2)) /
        (x * y - tateA₄ q * x - tateA₆ q) ^ 3 := by
    obtain ⟨e, he⟩ : ∃ e, e = x * y - tateA₄ q * x - tateA₆ q := ⟨_, rfl⟩
    have he0' : e ≠ 0 := by rw [he]; exact he0
    have hx3 : x ^ 3 ≠ 0 := pow_ne_zero 3 hx0
    rw [h1mu, ← he, show tateA₄ q * x + tateA₆ q = x * y - e by rw [he]; ring]
    field_simp
    ring
  rw [hid, map_div₀, map_pow, hve, one_pow, div_one, map_mul, hy, one_mul, map_mul]
  have hxy1 : valuation k (x * y) ≤ 1 := by
    rw [map_mul, hx, hy, one_mul]
  have hb2 : valuation k ((x * y) ^ 2 +
      x * y * (x * y - tateA₄ q * x - tateA₆ q) +
      (x * y - tateA₄ q * x - tateA₆ q) ^ 2) ≤ 1 := by
    refine le_trans ((valuation k).map_add _ _) (max_le (le_trans
      ((valuation k).map_add _ _) (max_le ?_ ?_)) ?_)
    · rw [map_pow]
      exact pow_le_one' hxy1 2
    · rw [map_mul, hve, mul_one]
      exact hxy1
    · rw [map_pow, hve, one_pow]
  calc valuation k (tateA₄ q * x + tateA₆ q) * valuation k ((x * y) ^ 2 +
        x * y * (x * y - tateA₄ q * x - tateA₆ q) +
        (x * y - tateA₄ q * x - tateA₆ q) ^ 2) ≤ valuation k q * 1 :=
        mul_le_mul' hb1 hb2
    _ = valuation k q := mul_one _

private theorem WeierstrassCurve.valuation_tateX_nodal_sub_le_aux (q : kˣ)
    (hq : valuation k (q : k) < 1) {u x : k} (hvu : valuation k u = 1)
    (hXc : valuation k (u / (1 - u) ^ 2 - x) ≤ valuation k (q : k)) :
    valuation k (tateX u (q : k) - x) ≤ valuation k (q : k) := by
  rw [show tateX u (q : k) - x =
    (tateX u (q : k) - u / (1 - u) ^ 2) + (u / (1 - u) ^ 2 - x) by ring]
  exact le_trans ((valuation k).map_add _ _)
    (max_le (valuation_tateX_sub_leading q hq hvu) hXc)

private theorem WeierstrassCurve.valuation_tateY_nodal_sub_le_aux (q : kˣ)
    (hq : valuation k (q : k) < 1) {u y : k} (hvu : valuation k u = 1)
    (hYc : valuation k (u ^ 2 / (1 - u) ^ 3 - y) ≤ valuation k (q : k)) :
    valuation k (tateY u (q : k) - y) ≤ valuation k (q : k) := by
  rw [show tateY u (q : k) - y =
    (tateY u (q : k) - u ^ 2 / (1 - u) ^ 3) + (u ^ 2 / (1 - u) ^ 3 - y) by ring]
  exact le_trans ((valuation k).map_add _ _)
    (max_le (valuation_tateY_sub_leading q hq hvu) hYc)

private theorem WeierstrassCurve.exists_nodal_approximation_data_aux (q : kˣ)
    (hq : valuation k (q : k) < 1) {x y : k}
    (h : ((tateCurve (q : k))⁄k).Equation x y) (hx : valuation k x = 1)
    (hy : valuation k y = 1) : ∃ u : k, u ≠ 0 ∧ valuation k u = 1 ∧ u ≠ 1 ∧
      valuation k (tateX u (q : k) - x) ≤ valuation k (q : k) ∧
      valuation k (tateY u (q : k) - y) ≤ valuation k (q : k) := by
  have hx0 : x ≠ 0 := fun h0 ↦ by rw [h0, map_zero] at hx; exact zero_ne_one hx
  have hy0 : y ≠ 0 := fun h0 ↦ by rw [h0, map_zero] at hy; exact zero_ne_one hy
  have hu0 : y ^ 2 / x ^ 3 ≠ 0 := div_ne_zero (pow_ne_zero 2 hy0) (pow_ne_zero 3 hx0)
  have hvu := valuation_nodal_parameter_eq_one_aux hx hy
  obtain ⟨he0, hve, h1mu, hv1mu⟩ := nodal_parameter_denominator_facts_aux hq h hx hy
  have hune : y ^ 2 / x ^ 3 ≠ 1 := by
    intro h1
    rw [h1, sub_self, map_zero] at hv1mu
    exact zero_ne_one hv1mu
  have hb1 := valuation_nodal_coefficient_error_le_aux hq hx
  have hXc := valuation_nodal_X_sub_le_aux hq hx hy hx0 he0 hve h1mu hb1
  have hYc := valuation_nodal_Y_sub_le_aux hx hy hx0 he0 hve h1mu hb1
  exact ⟨y ^ 2 / x ^ 3, hu0, hvu, hune,
    valuation_tateX_nodal_sub_le_aux q hq hvu hXc,
    valuation_tateY_nodal_sub_le_aux q hq hvu hYc⟩

/-- **The approximating unit**: for a point of `E_q(k)` with `|x| = |y| = 1`, the unit
`u₀ = y²/x³` satisfies `|X(u₀, q) - x| ≤ |q|` and `|Y(u₀, q) - y| ≤ |q|`
(and `|u₀| = 1`, `u₀ ≠ 1`). This is the explicit inverse of the parametrisation of the
smooth locus of the nodal cubic (Silverman ATAEC V.4, p. 432: "the inverse being
`(x, y) ↦ y²/x³`"). -/
theorem WeierstrassCurve.exists_tateCurve_unit_approx (q : kˣ)
    (hq : valuation k (q : k) < 1) {x y : k}
    (h : ((tateCurve (q : k))⁄k).Equation x y) (hx : valuation k x = 1)
    (hy : valuation k y = 1) :
    ∃ u₀ : kˣ, valuation k (u₀ : k) = 1 ∧ (u₀ : k) ≠ 1 ∧
      valuation k (tateX (u₀ : k) (q : k) - x) ≤ valuation k (q : k) ∧
      valuation k (tateY (u₀ : k) (q : k) - y) ≤ valuation k (q : k) := by
  obtain ⟨u, hu0, hvu, hune, hX, hY⟩ := exists_nodal_approximation_data_aux q hq h hx hy
  exact ⟨Units.mk0 u hu0, by simpa only [Units.val_mk0] using hvu,
    by simpa only [Units.val_mk0] using hune,
    by simpa only [Units.val_mk0] using hX,
    by simpa only [Units.val_mk0] using hY⟩

/-- **The unit piece of Tate surjectivity**: every point of `E_q(k)` with `|x| = 1` is in the
image of `φ` (Silverman ATAEC V.4, p. 432). -/
theorem WeierstrassCurve.exists_tateCurvePoint_eq_of_eq_one (q : kˣ)
    (hq : valuation k (q : k) < 1) {x y : k}
    (h : ((tateCurve (q : k))⁄k).Nonsingular x y) (hx : valuation k x = 1) :
    ∃ u : kˣ, tateCurvePoint q hq u = .some x y h := by
  classical
  have hy : valuation k y = 1 := tateCurve_valuation_y_eq_one hq h.1 hx
  obtain ⟨u₀, hvu₀, hu₀ne1, hXa, hYa⟩ := exists_tateCurve_unit_approx q hq h.1 hx hy
  have hu₀mem : u₀ ∉ Subgroup.zpowers q := by
    refine TateCurve.notMem_zpowers_of_annulus q u₀ hq ?_ ?_ hu₀ne1
    · rw [hvu₀]
      exact hq
    · rw [hvu₀]
  have hns := tateCurve_nonsingular q hq u₀ hu₀mem
  have hXX : valuation k (x - tateX (u₀ : k) (q : k)) < 1 := by
    rw [Valuation.map_sub_swap]
    exact lt_of_le_of_lt hXa hq
  have hYY : valuation k (y - tateY (u₀ : k) (q : k)) < 1 := by
    rw [Valuation.map_sub_swap]
    exact lt_of_le_of_lt hYa hq
  rcases tateCurve_sub_of_close hq h hns hx hy hXX hYY with h0 | ⟨x'', y'', h'', hdiff, hbig⟩
  · refine ⟨u₀, ?_⟩
    rw [tateCurvePoint, dif_neg hu₀mem]
    rw [sub_eq_zero] at h0
    exact h0.symm
  · obtain ⟨v, hv⟩ := exists_tateCurvePoint_eq_of_one_lt q hq h'' hbig
    refine ⟨u₀ * v, ?_⟩
    rw [tateCurvePoint_mul q hq u₀ v, hv, ← hdiff, tateCurvePoint, dif_neg hu₀mem]
    abel

private theorem max_valuation_y_add_eq_max_valuation_x_y_aux {R Γ₀ : Type*} [Ring R]
    [LinearOrderedCommMonoidWithZero Γ₀] (v : Valuation R Γ₀) (x y : R) :
    max (v y) (v (x + y)) = max (v x) (v y) := by
  rcases lt_trichotomy (v x) (v y) with h | h | h
  · rw [v.map_add_eq_of_lt_right h, max_self, max_eq_right h.le]
  · have hxy : v (x + y) ≤ v y := by simpa [h] using v.map_add x y
    rw [max_eq_left hxy, h, max_self]
  · rw [v.map_add_eq_of_lt_left h, max_eq_right h.le, max_eq_left h.le]

private theorem WeierstrassCurve.max_valuation_x_y_pos_of_tateCurve_equation_aux {q x y : k}
    (hq0 : q ≠ 0) (hq : valuation k q < 1) (h : ((tateCurve q)⁄k).Equation x y) :
    0 < max (valuation k x) (valuation k y) := by
  rw [tateCurve_equation_iff] at h
  have hva6 := valuation_tateA₆ q hq0 hq
  rcases (zero_le (a := max (valuation k x) (valuation k y))).lt_or_eq with h0 | h0
  · exact h0
  · exfalso
    have hx0 : valuation k x = 0 := le_antisymm (h0 ▸ le_max_left _ _) zero_le
    have hy0 : valuation k y = 0 := le_antisymm (h0 ▸ le_max_right _ _) zero_le
    have hx0' : x = 0 := by
      by_contra hne
      exact (valuation k).ne_zero_iff.mpr hne hx0
    have hy0' : y = 0 := by
      by_contra hne
      exact (valuation k).ne_zero_iff.mpr hne hy0
    rw [hx0', hy0'] at h
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, zero_add,
      add_zero] at h
    rw [← h, map_zero] at hva6
    exact (valuation k).ne_zero_iff.mpr hq0 hva6.symm

private theorem WeierstrassCurve.valuation_tateA4_mul_lt_q_of_max_lt_one_aux {q x y : k}
    (hq0 : q ≠ 0) (hq : valuation k q < 1)
    (hμ1 : max (valuation k x) (valuation k y) < 1) :
    valuation k (tateA₄ q * x) < valuation k q := by
  have hvq0 : valuation k q ≠ 0 := (valuation k).ne_zero_iff.mpr hq0
  rcases eq_or_ne (valuation k x) 0 with h0 | h0
  · rw [map_mul, h0, mul_zero]
    exact zero_lt_iff.mpr hvq0
  · rw [map_mul, mul_comm]
    calc valuation k x * valuation k (tateA₄ q)
        ≤ valuation k x * valuation k q := mul_le_mul' le_rfl (valuation_tateA₄_le q hq)
      _ < 1 * valuation k q := (mul_lt_mul_iff_left₀ (zero_lt_iff.mpr hvq0)).mpr
        (lt_of_le_of_lt (le_max_left _ (valuation k y)) hμ1)
      _ = valuation k q := one_mul _

private theorem WeierstrassCurve.valuation_tateCurve_rhs_eq_q_of_max_sq_le_aux {q x y : k}
    (hq0 : q ≠ 0) (hq : valuation k q < 1)
    (hμ0 : 0 < max (valuation k x) (valuation k y))
    (hμ1 : max (valuation k x) (valuation k y) < 1)
    (hsq : max (valuation k x) (valuation k y) ^ 2 ≤ valuation k q) :
    valuation k (x ^ 3 + tateA₄ q * x + tateA₆ q) = valuation k q := by
  have hx3_le : valuation k (x ^ 3) ≤ max (valuation k x) (valuation k y) ^ 3 := by
    rw [map_pow]
    exact pow_le_pow_left' (le_max_left _ _) 3
  have hμ3lt : max (valuation k x) (valuation k y) ^ 3 <
      max (valuation k x) (valuation k y) ^ 2 := by
    rw [pow_succ]
    exact (mul_lt_mul_of_pos_left hμ1 (pow_pos hμ0 2)).trans_eq (mul_one _)
  rw [show x ^ 3 + tateA₄ q * x + tateA₆ q = tateA₆ q + (x ^ 3 + tateA₄ q * x) by
    ring, (valuation k).map_add_eq_of_lt_left ?_, valuation_tateA₆ q hq0 hq]
  rw [valuation_tateA₆ q hq0 hq]
  refine lt_of_le_of_lt ((valuation k).map_add _ _) (max_lt ?_
    (valuation_tateA4_mul_lt_q_of_max_lt_one_aux hq0 hq hμ1))
  exact hx3_le.trans_lt (hμ3lt.trans_le hsq)

private theorem WeierstrassCurve.valuation_tateCurve_q_le_max_sq_aux {q x y : k}
    (hq0 : q ≠ 0) (hq : valuation k q < 1) (h : ((tateCurve q)⁄k).Equation x y)
    (hx : valuation k x < 1) (hy : valuation k y < 1) :
    valuation k q ≤ max (valuation k x) (valuation k y) ^ 2 := by
  have hμ0 := max_valuation_x_y_pos_of_tateCurve_equation_aux hq0 hq h
  have hμ1 : max (valuation k x) (valuation k y) < 1 := max_lt hx hy
  rw [tateCurve_equation_iff] at h
  have hkey : y * (y + x) = x ^ 3 + tateA₄ q * x + tateA₆ q := by linear_combination h
  by_contra hlt
  rw [not_le] at hlt
  have hRHS := valuation_tateCurve_rhs_eq_q_of_max_sq_le_aux hq0 hq hμ0 hμ1 hlt.le
  have hxy_le : valuation k (x + y) ≤ max (valuation k x) (valuation k y) :=
    ((valuation k).map_add _ _).trans (max_le (le_max_left _ _) (le_max_right _ _))
  have hle2 : valuation k y * valuation k (x + y) ≤
      max (valuation k x) (valuation k y) ^ 2 := by
    rw [pow_two]
    exact mul_le_mul' (le_max_right _ _) hxy_le
  rw [← hkey, map_mul, add_comm y x] at hRHS
  rw [hRHS] at hle2
  exact (not_lt_of_ge hle2) hlt

private theorem WeierstrassCurve.tateCurve_component_of_q_lt_max_sq_aux {q x y : k}
    (hq0 : q ≠ 0) (hq : valuation k q < 1) (h : ((tateCurve q)⁄k).Equation x y)
    (hx : valuation k x < 1) (hy : valuation k y < 1)
    (hqlt : valuation k q < max (valuation k x) (valuation k y) ^ 2) :
    (valuation k (x + y) < valuation k y ∧ valuation k q < valuation k y ^ 2) ∨
      valuation k y < valuation k (x + y) ∧ valuation k q < valuation k (x + y) ^ 2 := by
  have hμ0 := max_valuation_x_y_pos_of_tateCurve_equation_aux hq0 hq h
  have hμ1 : max (valuation k x) (valuation k y) < 1 := max_lt hx hy
  rw [tateCurve_equation_iff] at h
  have hkey : y * (y + x) = x ^ 3 + tateA₄ q * x + tateA₆ q := by linear_combination h
  have hprod : valuation k y * valuation k (x + y) =
      valuation k (x ^ 3 + tateA₄ q * x + tateA₆ q) := by
    rw [← hkey, map_mul, add_comm x y]
  have hμmax := max_valuation_y_add_eq_max_valuation_x_y_aux (valuation k) x y
  have hx3_le : valuation k (x ^ 3) ≤ max (valuation k x) (valuation k y) ^ 3 := by
    rw [map_pow]
    exact pow_le_pow_left' (le_max_left _ _) 3
  have hμ3lt : max (valuation k x) (valuation k y) ^ 3 <
      max (valuation k x) (valuation k y) ^ 2 := by
    rw [pow_succ]
    exact (mul_lt_mul_of_pos_left hμ1 (pow_pos hμ0 2)).trans_eq (mul_one _)
  have hRHSlt : valuation k y * valuation k (x + y) <
      max (valuation k x) (valuation k y) ^ 2 := by
    rw [hprod]
    refine lt_of_le_of_lt ((valuation k).map_add _ _) (max_lt (lt_of_le_of_lt
      ((valuation k).map_add _ _) (max_lt (hx3_le.trans_lt hμ3lt)
        ((valuation_tateA4_mul_lt_q_of_max_lt_one_aux hq0 hq hμ1).trans hqlt))) ?_)
    exact (valuation_tateA₆_le q hq).trans_lt hqlt
  rcases lt_trichotomy (valuation k y) (valuation k (x + y)) with hc | hc | hc
  · have hxyμ : valuation k (x + y) = max (valuation k x) (valuation k y) := by
      have h1 := hμmax
      rw [max_eq_right hc.le] at h1
      exact h1
    exact Or.inr ⟨hc, hqlt.trans_eq (congrArg (fun z ↦ z ^ 2) hxyμ.symm)⟩
  · have hyμ : valuation k y = max (valuation k x) (valuation k y) := by
      have h1 := hμmax
      rw [← hc, max_self] at h1
      exact h1
    have hxyμ : valuation k (x + y) = max (valuation k x) (valuation k y) :=
      hc.symm.trans hyμ
    have heq : valuation k y * valuation k (x + y) =
        max (valuation k x) (valuation k y) ^ 2 := by
      calc valuation k y * valuation k (x + y) =
            max (valuation k x) (valuation k y) * valuation k (x + y) :=
          congrArg (fun z ↦ z * valuation k (x + y)) hyμ
        _ = max (valuation k x) (valuation k y) * max (valuation k x) (valuation k y) :=
          congrArg (fun z ↦ max (valuation k x) (valuation k y) * z) hxyμ
        _ = max (valuation k x) (valuation k y) ^ 2 := (pow_two _).symm
    exact (lt_irrefl _ (heq ▸ hRHSlt)).elim
  · have hyμ : valuation k y = max (valuation k x) (valuation k y) := by
      have h1 := hμmax
      rw [max_eq_left hc.le] at h1
      exact h1
    exact Or.inl ⟨hc, hqlt.trans_eq (congrArg (fun z ↦ z ^ 2) hyμ.symm)⟩

private theorem WeierstrassCurve.tateCurve_component_of_q_eq_max_sq_aux {q x y : k}
    (hq0 : q ≠ 0) (hq : valuation k q < 1) (h : ((tateCurve q)⁄k).Equation x y)
    (hx : valuation k x < 1) (hy : valuation k y < 1)
    (hqeq : valuation k q = max (valuation k x) (valuation k y) ^ 2) :
    valuation k y = valuation k (x + y) ∧ valuation k y ^ 2 = valuation k q := by
  have hμ0 := max_valuation_x_y_pos_of_tateCurve_equation_aux hq0 hq h
  have hμ1 : max (valuation k x) (valuation k y) < 1 := max_lt hx hy
  have hRHSeq := valuation_tateCurve_rhs_eq_q_of_max_sq_le_aux hq0 hq hμ0 hμ1 hqeq.ge
  rw [tateCurve_equation_iff] at h
  have hkey : y * (y + x) = x ^ 3 + tateA₄ q * x + tateA₆ q := by linear_combination h
  have hprodμ : valuation k y * valuation k (x + y) =
      max (valuation k x) (valuation k y) ^ 2 := by
    calc valuation k y * valuation k (x + y) =
          valuation k (x ^ 3 + tateA₄ q * x + tateA₆ q) := by
            rw [← hkey, map_mul, add_comm y x]
      _ = valuation k q := hRHSeq
      _ = max (valuation k x) (valuation k y) ^ 2 := hqeq
  have hxy_le : valuation k (x + y) ≤ max (valuation k x) (valuation k y) :=
    ((valuation k).map_add _ _).trans (max_le (le_max_left _ _) (le_max_right _ _))
  have hyμ : valuation k y = max (valuation k x) (valuation k y) := by
    by_contra hne
    have hylt := lt_of_le_of_ne (le_max_right (valuation k x) (valuation k y)) hne
    have hlt2 : valuation k y * valuation k (x + y) <
        max (valuation k x) (valuation k y) ^ 2 := by
      calc valuation k y * valuation k (x + y)
          ≤ valuation k y * max (valuation k x) (valuation k y) := mul_le_mul' le_rfl hxy_le
        _ = max (valuation k x) (valuation k y) * valuation k y := mul_comm _ _
        _ < max (valuation k x) (valuation k y) * max (valuation k x) (valuation k y) :=
          mul_lt_mul_of_pos_left hylt hμ0
        _ = max (valuation k x) (valuation k y) ^ 2 := (pow_two _).symm
    rw [hprodμ] at hlt2
    exact lt_irrefl _ hlt2
  have hxyμ : valuation k (x + y) = max (valuation k x) (valuation k y) := by
    have hcancel : max (valuation k x) (valuation k y) * valuation k (x + y) =
        max (valuation k x) (valuation k y) * max (valuation k x) (valuation k y) := by
      calc max (valuation k x) (valuation k y) * valuation k (x + y) =
            valuation k y * valuation k (x + y) :=
          congrArg (fun z ↦ z * valuation k (x + y)) hyμ.symm
        _ = max (valuation k x) (valuation k y) ^ 2 := hprodμ
        _ = max (valuation k x) (valuation k y) * max (valuation k x) (valuation k y) :=
          pow_two _
    exact mul_left_cancel₀ hμ0.ne' hcancel
  exact ⟨hyμ.trans hxyμ.symm, by rw [hyμ, hqeq]⟩

/-- **Silverman's Lemma 4.1.2** (trichotomy): a point of `E_q(k)` with `|x| < 1` satisfies
exactly one of: `|x + y| < |y|` with `|q| < |y|²` (class `U`); `|y| < |x + y|` with
`|q| < |x + y|²` (class `V`); or `|y| = |x + y|` with `|y|² = |q|` (class `W`). -/
theorem WeierstrassCurve.tateCurve_component_trichotomy {q x y : k} (hq0 : q ≠ 0)
    (hq : valuation k q < 1) (h : ((tateCurve q)⁄k).Equation x y)
    (hx : valuation k x < 1) :
    (valuation k (x + y) < valuation k y ∧ valuation k q < valuation k y ^ 2) ∨
    (valuation k y < valuation k (x + y) ∧ valuation k q < valuation k (x + y) ^ 2) ∨
    (valuation k y = valuation k (x + y) ∧ valuation k y ^ 2 = valuation k q) := by
  have hy : valuation k y < 1 := tateCurve_valuation_y_lt_one hq h hx
  have hq_le := valuation_tateCurve_q_le_max_sq_aux hq0 hq h hx hy
  rcases lt_or_eq_of_le hq_le with hqlt | hqeq
  · exact (tateCurve_component_of_q_lt_max_sq_aux hq0 hq h hx hy hqlt).imp id Or.inl
  · exact Or.inr <| Or.inr <| tateCurve_component_of_q_eq_max_sq_aux hq0 hq h hx hy hqeq

omit [IsNonarchimedeanLocalField k] in
/-- The `x`-coordinate of a chord sum is integral as soon as `|ℓ² + ℓ| ≥ 1` and the inputs
are small: in `addX = (ℓ² + ℓ) - x₁ - x₂` the first group dominates. -/
private theorem WeierstrassCurve.tateCurve_valuation_addX_of_one_le {q x₁ x₂ ℓ : k}
    (hx₁ : valuation k x₁ < 1) (hx₂ : valuation k x₂ < 1)
    (hℓ : 1 ≤ valuation k (ℓ ^ 2 + ℓ)) :
    1 ≤ valuation k (((tateCurve q)⁄k).addX x₁ x₂ ℓ) := by
  rw [tateCurve_addX, show ℓ ^ 2 + ℓ - x₁ - x₂ = (ℓ ^ 2 + ℓ) + (-x₁ - x₂) by ring,
    (valuation k).map_add_eq_of_lt_left ?_]
  · exact hℓ
  · refine lt_of_lt_of_le ?_ hℓ
    refine lt_of_le_of_lt ((valuation k).map_sub _ _) (max_lt ?_ hx₂)
    rw [Valuation.map_neg]
    exact hx₁

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
private theorem valuation_x_eq_y_of_mem_tateCurve_U_aux {x y : k}
    (hU : valuation k (x + y) < valuation k y) : valuation k x = valuation k y := by
  rw [show x = (x + y) + -y by ring,
    (valuation k).map_add_eq_of_lt_right (by rw [Valuation.map_neg]; exact hU),
    Valuation.map_neg]

omit [IsNonarchimedeanLocalField k] in
open scoped Classical in
private theorem WeierstrassCurve.tateCurve_sub_of_same_U_of_x_eq_aux {q x y x' y' : k}
    (h : ((tateCurve q)⁄k).Nonsingular x y) (h' : ((tateCurve q)⁄k).Nonsingular x' y')
    (hU' : valuation k (x' + y') < valuation k y) (hxx' : x = x') :
    Affine.Point.some x y h - Affine.Point.some x' y' h' = 0 := by
  have hnegY : ((tateCurve q)⁄k).negY x' y' = -y' - x' := tateCurve_negY q x' y'
  rw [sub_eq_add_neg, Affine.Point.neg_some]
  rcases Affine.Y_eq_of_X_eq h.1 h'.1 hxx' with hyy' | hyneg
  · subst x'
    subst y'
    exact Affine.Point.add_of_Y_eq rfl (Affine.negY_negY _ _).symm
  · exfalso
    rw [hnegY] at hyneg
    have hxy' : x' + y' = -y := by linear_combination hyneg
    have h1 : valuation k (x' + y') = valuation k y := by rw [hxy', Valuation.map_neg]
    exact (ne_of_lt hU') h1

omit [IsNonarchimedeanLocalField k] in
open scoped Classical in
private theorem WeierstrassCurve.tateCurve_sub_of_same_U_of_x_ne_aux {q x y x' y' : k}
    (h : ((tateCurve q)⁄k).Nonsingular x y) (h' : ((tateCurve q)⁄k).Nonsingular x' y')
    (hyy : valuation k y = valuation k y') (hU : valuation k (x + y) < valuation k y)
    (hU' : valuation k (x' + y') < valuation k y') (hy1 : valuation k y < 1)
    (hxx' : x ≠ x') :
    ∃ (x'' y'' : k) (h'' : ((tateCurve q)⁄k).Nonsingular x'' y''),
      Affine.Point.some x y h - Affine.Point.some x' y' h' = .some x'' y'' h'' ∧
        1 ≤ valuation k x'' := by
  have hy1' : valuation k y' < 1 := by rw [← hyy]; exact hy1
  have hvx := valuation_x_eq_y_of_mem_tateCurve_U_aux hU
  have hvx' := valuation_x_eq_y_of_mem_tateCurve_U_aux hU'
  have hsub0 : x - x' ≠ 0 := sub_ne_zero.mpr hxx'
  have hvsub0 : valuation k (x - x') ≠ 0 := (valuation k).ne_zero_iff.mpr hsub0
  rw [sub_eq_add_neg, Affine.Point.neg_some]
  refine ⟨_, _, _, Affine.Point.add_of_X_ne hxx', ?_⟩
  rw [tateCurve_negY, Affine.slope_of_X_ne hxx',
    show y - (-y' - x') = y + y' + x' by ring]
  refine tateCurve_valuation_addX_of_one_le (by rw [hvx]; exact hy1)
    (by rw [hvx']; exact hy1') ?_
  have hid : ((y + y' + x') / (x - x')) ^ 2 + (y + y' + x') / (x - x') =
      ((y + y' + x') * (y + x + y')) / (x - x') ^ 2 := by
    field_simp
    ring
  have hA : valuation k (y + y' + x') = valuation k y := by
    rw [show y + y' + x' = y + (x' + y') by ring]
    refine (valuation k).map_add_eq_of_lt_left ?_
    rw [← hyy] at hU'
    exact hU'
  have hB : valuation k (y + x + y') = valuation k y := by
    rw [show y + x + y' = y' + (x + y) by ring,
      (valuation k).map_add_eq_of_lt_left (by rw [← hyy]; exact hU), ← hyy]
  have hd_le : valuation k (x - x') ≤ valuation k y := by
    refine le_trans ((valuation k).map_sub _ _) (max_le (le_of_eq hvx) ?_)
    rw [hvx', ← hyy]
  rw [hid, map_div₀, map_mul, hA, hB, map_pow]
  refine (one_le_div₀ (pow_pos (zero_lt_iff.mpr hvsub0) 2)).mpr ?_
  rw [pow_two]
  exact mul_le_mul' hd_le hd_le

omit [IsNonarchimedeanLocalField k] in
open scoped Classical in
/-- **Silverman's Lemma 4.1.4(i)**: two points of `E_q(k)` in the same class `Uₙ`
(`|y| = |y'| = |ϖ|ⁿ > |x + y|, |x' + y'|`, with `|q| < |y|² `) differ by a point with
`|x| ≥ 1` (or are equal). -/
theorem WeierstrassCurve.tateCurve_sub_of_same_U {q : k} {x y x' y' : k}
    (h : ((tateCurve q)⁄k).Nonsingular x y)
    (h' : ((tateCurve q)⁄k).Nonsingular x' y') (hyy : valuation k y = valuation k y')
    (hU : valuation k (x + y) < valuation k y) (hU' : valuation k (x' + y') < valuation k y')
    (hy1 : valuation k y < 1) :
    Affine.Point.some x y h - Affine.Point.some x' y' h' = 0 ∨
      ∃ (x'' y'' : k) (h'' : ((tateCurve q)⁄k).Nonsingular x'' y''),
        Affine.Point.some x y h - Affine.Point.some x' y' h' = .some x'' y'' h'' ∧
          1 ≤ valuation k x'' := by
  by_cases hxx' : x = x'
  · left
    exact tateCurve_sub_of_same_U_of_x_eq_aux h h' (by rw [hyy]; exact hU') hxx'
  · right
    exact tateCurve_sub_of_same_U_of_x_ne_aux h h' hyy hU hU' hy1 hxx'

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
private theorem valuation_add_neg_sub_lt_neg_sub_aux {x y : k}
    (h : valuation k y < valuation k (x + y)) :
    valuation k (x + (-y - x)) < valuation k (-y - x) := by
  rw [show x + (-y - x) = -y by ring, Valuation.map_neg,
    show -y - x = -(x + y) by ring, Valuation.map_neg]
  exact h

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] in
private theorem WeierstrassCurve.tateCurve_neg_point_eq_aux {q x y : k}
    (h : ((tateCurve q)⁄k).Nonsingular x y)
    (hn : ((tateCurve q)⁄k).Nonsingular x (-y - x)) :
    Affine.Point.some x (-y - x) hn = -Affine.Point.some x y h := by
  rw [Affine.Point.neg_some]
  simp only [tateCurve_negY]

omit [IsNonarchimedeanLocalField k] in
open scoped Classical in
/-- **Silverman's Lemma 4.1.4(ii)**: two points of `E_q(k)` in the same class `Vₙ` differ
by a point with `|x| ≥ 1` (or are equal). Follows from the `U` case via
`P ∈ Uₙ ⟺ -P ∈ Vₙ`. -/
theorem WeierstrassCurve.tateCurve_sub_of_same_V {q : k} {x y x' y' : k}
    (h : ((tateCurve q)⁄k).Nonsingular x y)
    (h' : ((tateCurve q)⁄k).Nonsingular x' y')
    (hyy : valuation k (x + y) = valuation k (x' + y'))
    (hV : valuation k y < valuation k (x + y)) (hV' : valuation k y' < valuation k (x' + y'))
    (hy1 : valuation k (x + y) < 1) :
    Affine.Point.some x y h - Affine.Point.some x' y' h' = 0 ∨
      ∃ (x'' y'' : k) (h'' : ((tateCurve q)⁄k).Nonsingular x'' y''),
        Affine.Point.some x y h - Affine.Point.some x' y' h' = .some x'' y'' h'' ∧
          1 ≤ valuation k x'' := by
  have hn : ((tateCurve q)⁄k).Nonsingular x (-y - x) := by
    simpa only [tateCurve_negY] using (Affine.nonsingular_neg _ _).mpr h
  have hn' : ((tateCurve q)⁄k).Nonsingular x' (-y' - x') := by
    simpa only [tateCurve_negY] using (Affine.nonsingular_neg _ _).mpr h'
  have hUU := tateCurve_sub_of_same_U hn' hn
      (by simpa only [show -y' - x' = -(x' + y') by ring,
          show -y - x = -(x + y) by ring, Valuation.map_neg] using hyy.symm)
      (valuation_add_neg_sub_lt_neg_sub_aux hV') (valuation_add_neg_sub_lt_neg_sub_aux hV)
      (by simpa only [show -y' - x' = -(x' + y') by ring, Valuation.map_neg] using
        hyy ▸ hy1)
  rw [tateCurve_neg_point_eq_aux h' hn', tateCurve_neg_point_eq_aux h hn, neg_sub_neg] at hUU
  exact hUU

private noncomputable def WeierstrassCurve.tateCurveDoublePhi (q x : k) : k :=
  x ^ 4 - 2 * tateA₄ q * x ^ 2 - 8 * tateA₆ q * x + tateA₄ q ^ 2 - tateA₆ q

private noncomputable def WeierstrassCurve.tateCurveDoubleF (q x : k) : k :=
  48 * x ^ 2 + 8 * x + 64 * tateA₄ q - 1

private noncomputable def WeierstrassCurve.tateCurveDoubleG (q x : k) : k :=
  12 * x ^ 3 - x ^ 2 - 20 * tateA₄ q * x + 2 * tateA₄ q - 108 * tateA₆ q

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] in
private theorem WeierstrassCurve.tateCurve_double_x_mul_denominator_sq_aux {q x y : k}
    (hEq : y ^ 2 + x * y = x ^ 3 + tateA₄ q * x + tateA₆ q)
    (hd0 : (2 : k) * y + x ≠ 0) :
    ((tateCurve q)⁄k).addX x x ((3 * x ^ 2 + tateA₄ q - y) / (2 * y + x)) *
        (2 * y + x) ^ 2 = tateCurveDoublePhi q x := by
  rw [tateCurve_addX,
    show (((3 * x ^ 2 + tateA₄ q - y) / (2 * y + x)) ^ 2 +
        (3 * x ^ 2 + tateA₄ q - y) / (2 * y + x) - x - x) * (2 * y + x) ^ 2 =
      (((3 * x ^ 2 + tateA₄ q - y) / (2 * y + x)) * (2 * y + x)) ^ 2 +
        ((3 * x ^ 2 + tateA₄ q - y) / (2 * y + x)) * (2 * y + x) * (2 * y + x) -
          2 * x * (2 * y + x) ^ 2 by ring,
    div_mul_cancel₀ _ hd0, tateCurveDoublePhi]
  linear_combination (-8 * x - 1) * hEq

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] in
private theorem WeierstrassCurve.tateCurve_double_resultant_aux {q x y : k}
    (hEq : y ^ 2 + x * y = x ^ 3 + tateA₄ q * x + tateA₆ q)
    (hd0 : (2 : k) * y + x ≠ 0) :
    (2 * y + x) ^ 2 *
        (tateCurveDoubleG q x -
          ((tateCurve q)⁄k).addX x x ((3 * x ^ 2 + tateA₄ q - y) / (2 * y + x)) *
            tateCurveDoubleF q x) =
      tateA₄ q ^ 2 - tateA₆ q - 64 * tateA₄ q ^ 3 - 432 * tateA₆ q ^ 2 +
        72 * tateA₄ q * tateA₆ q := by
  have hx2d := tateCurve_double_x_mul_denominator_sq_aux hEq hd0
  rw [show (2 * y + x) ^ 2 *
      (tateCurveDoubleG q x -
        ((tateCurve q)⁄k).addX x x ((3 * x ^ 2 + tateA₄ q - y) / (2 * y + x)) *
          tateCurveDoubleF q x) =
      (2 * y + x) ^ 2 * tateCurveDoubleG q x -
        (((tateCurve q)⁄k).addX x x ((3 * x ^ 2 + tateA₄ q - y) / (2 * y + x)) *
          (2 * y + x) ^ 2) * tateCurveDoubleF q x by ring,
    hx2d, tateCurveDoublePhi, tateCurveDoubleG, tateCurveDoubleF]
  linear_combination
    (4 * (12 * x ^ 3 - x ^ 2 - 20 * tateA₄ q * x + 2 * tateA₄ q - 108 * tateA₆ q)) * hEq

private theorem WeierstrassCurve.valuation_tateCurve_double_discriminant_aux (q : k)
    (hq0 : q ≠ 0) (hq : valuation k q < 1) :
    valuation k (tateA₄ q ^ 2 - tateA₆ q - 64 * tateA₄ q ^ 3 - 432 * tateA₆ q ^ 2 +
      72 * tateA₄ q * tateA₆ q) = valuation k q := by
  have hΔeq : (tateCurve q).Δ = tateA₄ q ^ 2 - tateA₆ q - 64 * tateA₄ q ^ 3 -
      432 * tateA₆ q ^ 2 + 72 * tateA₄ q * tateA₆ q := by
    rw [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
      WeierstrassCurve.b₈, show (tateCurve q).a₁ = 1 from rfl,
      show (tateCurve q).a₂ = 0 from rfl, show (tateCurve q).a₃ = 0 from rfl,
      show (tateCurve q).a₄ = tateA₄ q from rfl, show (tateCurve q).a₆ = tateA₆ q from rfl]
    ring
  rw [← hΔeq]
  exact valuation_tateCurve_Δ q hq0 hq

private theorem WeierstrassCurve.valuation_tateCurve_double_G_lt_one_aux {q x : k}
    (hq : valuation k q < 1) (hx1 : valuation k x ≤ 1)
    (hx2q : valuation k (x ^ 2) ≤ valuation k q) :
    valuation k (tateCurveDoubleG q x) < 1 := by
  rw [tateCurveDoubleG]
  refine lt_of_le_of_lt (le_trans ((valuation k).map_sub _ _) (max_le (le_trans
    ((valuation k).map_add _ _) (max_le (le_trans ((valuation k).map_sub _ _)
    (max_le (le_trans ((valuation k).map_sub _ _) (max_le ?_ ?_)) ?_)) ?_)) ?_)) hq
  · rw [show (12 : k) * x ^ 3 = (12 : k) * x * x ^ 2 by ring, map_mul]
    calc valuation k ((12 : k) * x) * valuation k (x ^ 2) ≤ 1 * valuation k q := by
          refine mul_le_mul' ?_ hx2q
          rw [map_mul]
          exact (mul_le_mul' (valuation_natCast_le_one 12) hx1).trans_eq (one_mul 1)
      _ = valuation k q := one_mul _
  · exact hx2q
  · rw [show (20 : k) * tateA₄ q * x = (20 : k) * x * tateA₄ q by ring, map_mul]
    calc valuation k ((20 : k) * x) * valuation k (tateA₄ q) ≤ 1 * valuation k q := by
          refine mul_le_mul' ?_ (valuation_tateA₄_le q hq)
          rw [map_mul]
          exact (mul_le_mul' (valuation_natCast_le_one 20) hx1).trans_eq (one_mul 1)
      _ = valuation k q := one_mul _
  · rw [map_mul]
    exact (mul_le_mul' (valuation_natCast_le_one 2) (valuation_tateA₄_le q hq)).trans_eq
      (one_mul _)
  · rw [map_mul]
    exact (mul_le_mul' (valuation_natCast_le_one 108) (valuation_tateA₆_le q hq)).trans_eq
      (one_mul _)

private theorem WeierstrassCurve.valuation_tateCurve_double_F_le_one_aux {q x : k}
    (hq : valuation k q < 1) (hx1 : valuation k x ≤ 1)
    (hx2q : valuation k (x ^ 2) ≤ valuation k q) :
    valuation k (tateCurveDoubleF q x) ≤ 1 := by
  rw [tateCurveDoubleF]
  refine le_trans ((valuation k).map_sub _ _) (max_le (le_trans
    ((valuation k).map_add _ _) (max_le (le_trans ((valuation k).map_add _ _)
    (max_le ?_ ?_)) ?_)) ?_)
  · rw [map_mul]
    exact (mul_le_mul' (valuation_natCast_le_one 48) (hx2q.trans hq.le)).trans_eq (one_mul 1)
  · rw [map_mul]
    exact (mul_le_mul' (valuation_natCast_le_one 8) hx1).trans_eq (one_mul 1)
  · rw [map_mul]
    exact (mul_le_mul' (valuation_natCast_le_one 64)
      ((valuation_tateA₄_le q hq).trans hq.le)).trans_eq (one_mul 1)
  · rw [Valuation.map_one]

private theorem WeierstrassCurve.valuation_tateCurve_double_resultant_term_one_le_aux
    {q x y : k} (hq0 : q ≠ 0) (hq : valuation k q < 1)
    (hEq : y ^ 2 + x * y = x ^ 3 + tateA₄ q * x + tateA₆ q)
    (hW : valuation k y ^ 2 = valuation k q)
    (hxy : valuation k (x + y) = valuation k y) (hd0 : (2 : k) * y + x ≠ 0) :
    1 ≤ valuation k (tateCurveDoubleG q x -
      ((tateCurve q)⁄k).addX x x ((3 * x ^ 2 + tateA₄ q - y) / (2 * y + x)) *
        tateCurveDoubleF q x) := by
  have hd_le : valuation k (2 * y + x) ≤ valuation k y := by
    rw [show (2 : k) * y + x = (x + y) + y by ring]
    exact ((valuation k).map_add _ _).trans (max_le hxy.le le_rfl)
  have hd2_le : valuation k ((2 * y + x) ^ 2) ≤ valuation k q := by
    rw [map_pow, ← hW]
    exact pow_le_pow_left' hd_le 2
  have hd2_0 : valuation k ((2 * y + x) ^ 2) ≠ 0 :=
    (valuation k).ne_zero_iff.mpr (pow_ne_zero 2 hd0)
  have hkey := tateCurve_double_resultant_aux hEq hd0
  have hΔ := valuation_tateCurve_double_discriminant_aux q hq0 hq
  by_contra hlt
  rw [not_le] at hlt
  have hcontr : valuation k ((2 * y + x) ^ 2 *
      (tateCurveDoubleG q x -
        ((tateCurve q)⁄k).addX x x ((3 * x ^ 2 + tateA₄ q - y) / (2 * y + x)) *
          tateCurveDoubleF q x)) < valuation k q := by
    rw [map_mul]
    calc valuation k ((2 * y + x) ^ 2) * valuation k
          (tateCurveDoubleG q x -
            ((tateCurve q)⁄k).addX x x ((3 * x ^ 2 + tateA₄ q - y) / (2 * y + x)) *
              tateCurveDoubleF q x)
        < valuation k ((2 * y + x) ^ 2) * 1 :=
          by
            calc valuation k ((2 * y + x) ^ 2) * valuation k
                  (tateCurveDoubleG q x -
                    ((tateCurve q)⁄k).addX x x
                      ((3 * x ^ 2 + tateA₄ q - y) / (2 * y + x)) * tateCurveDoubleF q x) =
                valuation k (tateCurveDoubleG q x -
                    ((tateCurve q)⁄k).addX x x
                      ((3 * x ^ 2 + tateA₄ q - y) / (2 * y + x)) * tateCurveDoubleF q x) *
                  valuation k ((2 * y + x) ^ 2) := mul_comm _ _
              _ < 1 * valuation k ((2 * y + x) ^ 2) :=
                (mul_lt_mul_iff_left₀ (zero_lt_iff.mpr hd2_0)).mpr hlt
              _ = valuation k ((2 * y + x) ^ 2) * 1 := mul_comm _ _
      _ = valuation k ((2 * y + x) ^ 2) := mul_one _
      _ ≤ valuation k q := hd2_le
  rw [hkey, hΔ] at hcontr
  exact (lt_irrefl _) hcontr

private theorem WeierstrassCurve.valuation_tateCurve_double_addX_one_le_aux {q x y : k}
    (hq0 : q ≠ 0) (hq : valuation k q < 1)
    (hEq : y ^ 2 + x * y = x ^ 3 + tateA₄ q * x + tateA₆ q)
    (hW : valuation k y ^ 2 = valuation k q)
    (hxy : valuation k (x + y) = valuation k y) (hx_le : valuation k x ≤ valuation k y)
    (hy1 : valuation k y < 1) (hd0 : (2 : k) * y + x ≠ 0) :
    1 ≤ valuation k (((tateCurve q)⁄k).addX x x
      ((3 * x ^ 2 + tateA₄ q - y) / (2 * y + x))) := by
  have hx1 : valuation k x ≤ 1 := hx_le.trans hy1.le
  have hx2q : valuation k (x ^ 2) ≤ valuation k q := by
    rw [map_pow, ← hW]
    exact pow_le_pow_left' hx_le 2
  have hG_lt := valuation_tateCurve_double_G_lt_one_aux hq hx1 hx2q
  have hF_le := valuation_tateCurve_double_F_le_one_aux hq hx1 hx2q
  have h1le := valuation_tateCurve_double_resultant_term_one_le_aux hq0 hq hEq hW hxy hd0
  have h1le' : 1 ≤ valuation k (((tateCurve q)⁄k).addX x x
      ((3 * x ^ 2 + tateA₄ q - y) / (2 * y + x)) * tateCurveDoubleF q x) := by
    rcases le_or_gt 1 (valuation k (((tateCurve q)⁄k).addX x x
      ((3 * x ^ 2 + tateA₄ q - y) / (2 * y + x)) * tateCurveDoubleF q x)) with hle | hlt
    · exact hle
    · exfalso
      have : valuation k (tateCurveDoubleG q x -
          ((tateCurve q)⁄k).addX x x ((3 * x ^ 2 + tateA₄ q - y) / (2 * y + x)) *
            tateCurveDoubleF q x) < 1 :=
        lt_of_le_of_lt ((valuation k).map_sub _ _) (max_lt hG_lt hlt)
      exact (not_lt_of_ge h1le) this
  calc 1 ≤ valuation k (((tateCurve q)⁄k).addX x x
        ((3 * x ^ 2 + tateA₄ q - y) / (2 * y + x)) * tateCurveDoubleF q x) := h1le'
    _ = valuation k (((tateCurve q)⁄k).addX x x
        ((3 * x ^ 2 + tateA₄ q - y) / (2 * y + x))) * valuation k (tateCurveDoubleF q x) :=
      map_mul _ _ _
    _ ≤ valuation k (((tateCurve q)⁄k).addX x x
        ((3 * x ^ 2 + tateA₄ q - y) / (2 * y + x))) * 1 := mul_le_mul' le_rfl hF_le
    _ = valuation k (((tateCurve q)⁄k).addX x x
        ((3 * x ^ 2 + tateA₄ q - y) / (2 * y + x))) := mul_one _

open scoped Classical in
private theorem WeierstrassCurve.tateCurve_sub_of_same_W_of_inverse_not_two_torsion_aux
    {q x y y' : k} (hq0 : q ≠ 0) (hq : valuation k q < 1)
    (h : ((tateCurve q)⁄k).Nonsingular x y) (h' : ((tateCurve q)⁄k).Nonsingular x y')
    (hW : valuation k y ^ 2 = valuation k q) (hxy : valuation k (x + y) = valuation k y)
    (hx_le : valuation k x ≤ valuation k y) (hy1 : valuation k y < 1)
    (hyneg : y = -y' - x) (h2tor : y ≠ ((tateCurve q)⁄k).negY x y) :
    ∃ (x'' y'' : k) (h'' : ((tateCurve q)⁄k).Nonsingular x'' y''),
      Affine.Point.some x y h - Affine.Point.some x y' h' = .some x'' y'' h'' ∧
        1 ≤ valuation k x'' := by
  have hnegY' : ((tateCurve q)⁄k).negY x y' = y := by
    rw [tateCurve_negY]
    exact hyneg.symm
  have hyne : y ≠ ((tateCurve q)⁄k).negY x (((tateCurve q)⁄k).negY x y') := by
    rw [Affine.negY_negY]
    intro hyy'eq
    rw [tateCurve_negY] at h2tor
    exact h2tor (by linear_combination hyneg + hyy'eq)
  rw [sub_eq_add_neg, Affine.Point.neg_some]
  refine ⟨_, _, _, Affine.Point.add_of_Y_ne hyne, ?_⟩
  rw [hnegY', tateCurve_slope_self h2tor]
  have hEq := h.1
  rw [tateCurve_equation_iff] at hEq
  have hd0 : (2 : k) * y + x ≠ 0 := by
    intro h0
    rw [tateCurve_negY] at h2tor
    exact h2tor (by linear_combination h0)
  exact valuation_tateCurve_double_addX_one_le_aux hq0 hq hEq hW hxy hx_le hy1 hd0

open scoped Classical in
private theorem WeierstrassCurve.tateCurve_sub_of_same_W_of_x_eq_aux {q x y x' y' : k}
    (hq0 : q ≠ 0) (hq : valuation k q < 1)
    (h : ((tateCurve q)⁄k).Nonsingular x y) (h' : ((tateCurve q)⁄k).Nonsingular x' y')
    (hW : valuation k y ^ 2 = valuation k q) (hxy : valuation k (x + y) = valuation k y)
    (hx_le : valuation k x ≤ valuation k y) (hy1 : valuation k y < 1) (hxx' : x = x') :
    Affine.Point.some x y h - Affine.Point.some x' y' h' = 0 ∨
      ∃ (x'' y'' : k) (h'' : ((tateCurve q)⁄k).Nonsingular x'' y''),
        Affine.Point.some x y h - Affine.Point.some x' y' h' = .some x'' y'' h'' ∧
          1 ≤ valuation k x'' := by
  subst x'
  rcases Affine.Y_eq_of_X_eq h.1 h'.1 rfl with hyy' | hyneg
  · left
    subst y'
    rw [sub_eq_add_neg, Affine.Point.neg_some]
    exact Affine.Point.add_of_Y_eq rfl (Affine.negY_negY _ _).symm
  · rw [tateCurve_negY] at hyneg
    have hnegY' : ((tateCurve q)⁄k).negY x y' = y := by
      rw [tateCurve_negY]
      exact hyneg.symm
    by_cases h2tor : y = ((tateCurve q)⁄k).negY x y
    · left
      rw [sub_eq_add_neg, Affine.Point.neg_some]
      refine Affine.Point.add_of_Y_eq rfl ?_
      rw [hnegY']
      exact h2tor
    · right
      exact tateCurve_sub_of_same_W_of_inverse_not_two_torsion_aux hq0 hq h h' hW hxy hx_le
        hy1 hyneg h2tor

private theorem WeierstrassCurve.valuation_tateCurve_exchange_difference_le_aux
    {q x y x' y' : k} (hq : valuation k q < 1)
    (hEq : y ^ 2 + x * y = x ^ 3 + tateA₄ q * x + tateA₆ q)
    (hEq' : y' ^ 2 + x' * y' = x' ^ 3 + tateA₄ q * x' + tateA₆ q)
    (hW : valuation k y ^ 2 = valuation k q) (hW' : valuation k y' ^ 2 = valuation k q)
    (hyy : valuation k y = valuation k y') (hx_le : valuation k x ≤ valuation k y)
    (hx'_le : valuation k x' ≤ valuation k y') :
    valuation k ((y + x + y') * y - (y + y' + x') * y') ≤
      valuation k (x - x') * valuation k q := by
  have hByAy : (y + x + y') * y - (y + y' + x') * y' =
      (x - x') * (x ^ 2 + x * x' + x' ^ 2 + tateA₄ q) := by
    linear_combination hEq - hEq'
  rw [hByAy, map_mul]
  refine mul_le_mul' le_rfl <| le_trans ((valuation k).map_add _ _) (max_le (le_trans
    ((valuation k).map_add _ _) (max_le (le_trans ((valuation k).map_add _ _)
    (max_le ?_ ?_)) ?_)) (valuation_tateA₄_le q hq))
  · rw [map_pow, ← hW]
    exact pow_le_pow_left' hx_le 2
  · rw [map_mul, ← hW, pow_two]
    exact mul_le_mul' hx_le (hyy ▸ hx'_le)
  · rw [map_pow, ← hW']
    exact pow_le_pow_left' hx'_le 2

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
private theorem valuation_tateCurve_chord_factor_max_pos_aux {x y x' y' : k} (hxx' : x ≠ x') :
    0 < max (valuation k (y + x + y')) (valuation k (y + y' + x')) := by
  rcases (zero_le (a := max (valuation k (y + x + y'))
    (valuation k (y + y' + x')))).lt_or_eq with h0 | h0
  · exact h0
  · exfalso
    have hB0 : valuation k (y + x + y') = 0 :=
      le_antisymm (h0 ▸ le_max_left _ _) zero_le
    have hA0 : valuation k (y + y' + x') = 0 :=
      le_antisymm (h0 ▸ le_max_right _ _) zero_le
    have hB0' : y + x + y' = 0 := by
      by_contra hne
      exact (valuation k).ne_zero_iff.mpr hne hB0
    have hA0' : y + y' + x' = 0 := by
      by_contra hne
      exact (valuation k).ne_zero_iff.mpr hne hA0
    exact hxx' (by linear_combination hB0' - hA0')

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
private theorem valuation_tateCurve_chord_factors_eq_aux {q x y x' y' : k}
    (hvy0 : valuation k y ≠ 0) (hW : valuation k y ^ 2 = valuation k q)
    (hyy : valuation k y = valuation k y') (hy1 : valuation k y < 1) (hxx' : x ≠ x')
    (hsub_le : valuation k ((y + x + y') * y - (y + y' + x') * y') ≤
      valuation k (x - x') * valuation k q) :
    valuation k (y + y' + x') = valuation k (y + x + y') := by
  have hxsub_le : valuation k (x - x') ≤
      max (valuation k (y + x + y')) (valuation k (y + y' + x')) := by
    rw [show x - x' = (y + x + y') + -(y + y' + x') by ring]
    refine ((valuation k).map_add _ _).trans (max_le (le_max_left _ _) ?_)
    rw [Valuation.map_neg]
    exact le_max_right _ _
  have hmax0 := valuation_tateCurve_chord_factor_max_pos_aux (y := y) (y' := y') hxx'
  have hABval : valuation k ((y + x + y') * y) =
      valuation k ((y + y' + x') * y') := by
    by_contra hne
    have hmaxmul : max (valuation k ((y + x + y') * y))
        (valuation k ((y + y' + x') * y')) =
        max (valuation k (y + x + y')) (valuation k (y + y' + x')) * valuation k y := by
      rw [map_mul, map_mul, ← hyy]
      have hmono : Monotone (· * valuation k y) := fun _ _ hab ↦ mul_le_mul' hab le_rfl
      exact (hmono.map_max).symm
    have hchain : valuation k ((y + x + y') * y - (y + y' + x') * y') <
        max (valuation k ((y + x + y') * y))
          (valuation k ((y + y' + x') * y')) := by
      calc valuation k ((y + x + y') * y - (y + y' + x') * y')
          ≤ valuation k (x - x') * valuation k q := hsub_le
        _ ≤ max (valuation k (y + x + y')) (valuation k (y + y' + x')) *
            valuation k q := mul_le_mul' hxsub_le le_rfl
        _ = max (valuation k (y + x + y')) (valuation k (y + y' + x')) *
            valuation k y * valuation k y := by rw [← hW, pow_two, mul_assoc]
        _ < max (valuation k (y + x + y')) (valuation k (y + y' + x')) *
            valuation k y * 1 := by
          rw [mul_comm _ (valuation k y), mul_comm _ (1 : ValueGroupWithZero k)]
          exact (mul_lt_mul_iff_left₀ (mul_pos hmax0 (zero_lt_iff.mpr hvy0))).mpr hy1
        _ = max (valuation k (y + x + y')) (valuation k (y + y' + x')) *
            valuation k y := mul_one _
        _ = max (valuation k ((y + x + y') * y))
            (valuation k ((y + y' + x') * y')) := hmaxmul.symm
    have hsubeq : valuation k ((y + x + y') * y - (y + y' + x') * y') =
        max (valuation k ((y + x + y') * y)) (valuation k ((y + y' + x') * y')) := by
      rw [sub_eq_add_neg, (valuation k).map_add_of_distinct_val]
      · rw [Valuation.map_neg]
      · simpa only [Valuation.map_neg] using hne
    rw [hsubeq] at hchain
    exact (lt_irrefl _) hchain
  have h1 := hABval
  rw [map_mul, map_mul, ← hyy] at h1
  exact (mul_right_cancel₀ hvy0 h1).symm

private theorem WeierstrassCurve.valuation_tateCurve_same_W_chord_slope_one_le_aux
    {q x y x' y' : k} (hq0 : q ≠ 0) (hq : valuation k q < 1)
    (hEq : y ^ 2 + x * y = x ^ 3 + tateA₄ q * x + tateA₆ q)
    (hEq' : y' ^ 2 + x' * y' = x' ^ 3 + tateA₄ q * x' + tateA₆ q)
    (hW : valuation k y ^ 2 = valuation k q) (hW' : valuation k y' ^ 2 = valuation k q)
    (hyy : valuation k y = valuation k y') (hy1 : valuation k y < 1)
    (hx_le : valuation k x ≤ valuation k y) (hx'_le : valuation k x' ≤ valuation k y')
    (hxx' : x ≠ x') :
    1 ≤ valuation k (((y + y' + x') / (x - x')) ^ 2 + (y + y' + x') / (x - x')) := by
  have hvq0 : valuation k q ≠ 0 := (valuation k).ne_zero_iff.mpr hq0
  have hvy0 : valuation k y ≠ 0 := by
    intro h0
    rw [h0] at hW
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at hW
    exact hvq0 hW.symm
  have hsub_le := valuation_tateCurve_exchange_difference_le_aux hq hEq hEq' hW hW' hyy
    hx_le hx'_le
  have hAB := valuation_tateCurve_chord_factors_eq_aux hvy0 hW hyy hy1 hxx' hsub_le
  have hxsub_le : valuation k (x - x') ≤
      max (valuation k (y + x + y')) (valuation k (y + y' + x')) := by
    rw [show x - x' = (y + x + y') + -(y + y' + x') by ring]
    refine ((valuation k).map_add _ _).trans (max_le (le_max_left _ _) ?_)
    rw [Valuation.map_neg]
    exact le_max_right _ _
  have hd_le : valuation k (x - x') ≤ valuation k (y + y' + x') := by
    rwa [← hAB, max_self] at hxsub_le
  have hvsub0 : valuation k (x - x') ≠ 0 :=
    (valuation k).ne_zero_iff.mpr (sub_ne_zero.mpr hxx')
  have hid : ((y + y' + x') / (x - x')) ^ 2 + (y + y' + x') / (x - x') =
      ((y + y' + x') * (y + x + y')) / (x - x') ^ 2 := by
    field_simp
    ring
  rw [hid, map_div₀, map_mul, map_pow]
  calc (1 : ValueGroupWithZero k)
      = valuation k (x - x') ^ 2 * (valuation k (x - x') ^ 2)⁻¹ :=
        (mul_inv_cancel₀ (pow_ne_zero 2 hvsub0)).symm
    _ ≤ valuation k (y + y' + x') * valuation k (y + x + y') *
        (valuation k (x - x') ^ 2)⁻¹ := by
      refine mul_le_mul' ?_ le_rfl
      rw [pow_two]
      exact mul_le_mul' hd_le (hd_le.trans hAB.le)
    _ = valuation k (y + y' + x') * valuation k (y + x + y') /
        valuation k (x - x') ^ 2 := (div_eq_mul_inv _ _).symm

open scoped Classical in
private theorem WeierstrassCurve.tateCurve_sub_of_same_W_of_x_ne_aux {q x y x' y' : k}
    (hq0 : q ≠ 0) (hq : valuation k q < 1)
    (h : ((tateCurve q)⁄k).Nonsingular x y) (h' : ((tateCurve q)⁄k).Nonsingular x' y')
    (hW : valuation k y ^ 2 = valuation k q) (hW' : valuation k y' ^ 2 = valuation k q)
    (hyy : valuation k y = valuation k y') (hy1 : valuation k y < 1)
    (hx_le : valuation k x ≤ valuation k y) (hx'_le : valuation k x' ≤ valuation k y')
    (hxx' : x ≠ x') :
    Affine.Point.some x y h - Affine.Point.some x' y' h' = 0 ∨
      ∃ (x'' y'' : k) (h'' : ((tateCurve q)⁄k).Nonsingular x'' y''),
        Affine.Point.some x y h - Affine.Point.some x' y' h' = .some x'' y'' h'' ∧
          1 ≤ valuation k x'' := by
  right
  rw [sub_eq_add_neg, Affine.Point.neg_some]
  refine ⟨_, _, _, Affine.Point.add_of_X_ne hxx', ?_⟩
  rw [tateCurve_negY, Affine.slope_of_X_ne hxx',
    show y - (-y' - x') = y + y' + x' by ring]
  have hEq := h.1
  have hEq' := h'.1
  rw [tateCurve_equation_iff] at hEq hEq'
  refine tateCurve_valuation_addX_of_one_le (hx_le.trans_lt hy1) ?_ ?_
  · exact hx'_le.trans_lt (hyy ▸ hy1)
  · exact valuation_tateCurve_same_W_chord_slope_one_le_aux hq0 hq hEq hEq' hW hW' hyy
      hy1 hx_le hx'_le hxx'

open scoped Classical in
/-- **Silverman's Lemma 4.1.4(iii)**: two points of `E_q(k)` in the class `W`
(`|y| = |x + y| = |q|^{1/2}`, stated squared) differ by a point with `|x| ≥ 1` (or are
equal). The case `P' = -P` uses the duplication formula and the resultant identity
`g·G - f·F = Δ` together with `|Δ| = |q|` (`valuation_tateCurve_Δ`). -/
theorem WeierstrassCurve.tateCurve_sub_of_same_W {q : k} (hq0 : q ≠ 0)
    (hq : valuation k q < 1) {x y x' y' : k} (h : ((tateCurve q)⁄k).Nonsingular x y)
    (h' : ((tateCurve q)⁄k).Nonsingular x' y')
    (hW : valuation k y ^ 2 = valuation k q) (hxy : valuation k (x + y) = valuation k y)
    (hW' : valuation k y' ^ 2 = valuation k q)
    (hxy' : valuation k (x' + y') = valuation k y') :
    Affine.Point.some x y h - Affine.Point.some x' y' h' = 0 ∨
      ∃ (x'' y'' : k) (h'' : ((tateCurve q)⁄k).Nonsingular x'' y''),
        Affine.Point.some x y h - Affine.Point.some x' y' h' = .some x'' y'' h'' ∧
          1 ≤ valuation k x'' := by
  have hyy := (sq_eq_sq₀ zero_le zero_le).mp (hW.trans hW'.symm)
  have hy1 := (sq_lt_one_iff₀ zero_le).mp (hW.trans_lt hq)
  have hx_le : valuation k x ≤ valuation k y := by
    rw [show x = (x + y) + -y by ring]
    refine ((valuation k).map_add _ _).trans (max_le hxy.le ?_)
    rw [Valuation.map_neg]
  have hx'_le : valuation k x' ≤ valuation k y' := by
    rw [show x' = (x' + y') + -y' by ring]
    refine ((valuation k).map_add _ _).trans (max_le hxy'.le ?_)
    rw [Valuation.map_neg]
  by_cases hxx' : x = x'
  · exact tateCurve_sub_of_same_W_of_x_eq_aux hq0 hq h h' hW hxy hx_le hy1 hxx'
  · exact tateCurve_sub_of_same_W_of_x_ne_aux hq0 hq h h' hW hW' hyy hy1 hx_le hx'_le hxx'

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
private theorem WeierstrassCurve.valuation_annulus_X_leading_lt_one_aux {c : k}
    (hc : valuation k c < 1) : valuation k (c / (1 - c) ^ 2) < 1 := by
  have h1c : valuation k (1 - c) = 1 := by
    rw [show (1 : k) - c = 1 + -c by ring]
    simpa using (valuation k).map_add_eq_of_lt_left (x := (1 : k)) (by simpa using hc)
  rwa [map_div₀, map_pow, h1c, one_pow, div_one]

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
private theorem TateCurve.valuation_XField_tail_divisor_le_max_aux (q c : k)
    (hq : valuation k q ≤ 1) (hc : valuation k c ≤ 1)
    (hqc : valuation k q * (valuation k c)⁻¹ ≤ 1) {d N : ℕ} (hd1 : 1 ≤ d) (hdN : d ≤ N) :
    valuation k (((d : k) * c ^ d + (d : k) * (c⁻¹) ^ d - 2 * (d : k)) * q ^ N)
      ≤ max (valuation k q * (valuation k c)⁻¹) (valuation k q) := by
  have hqN_le : valuation k (q ^ N) ≤ valuation k q := by
    rw [map_pow]
    simpa only [pow_one] using pow_le_pow_right_of_le_one' hq (hd1.trans hdN)
  rw [show ((d : k) * c ^ d + (d : k) * (c⁻¹) ^ d - 2 * (d : k)) * q ^ N =
      (d : k) * c ^ d * q ^ N + (d : k) * (c⁻¹) ^ d * q ^ N
        - 2 * (d : k) * q ^ N by ring]
  refine ((valuation k).map_sub _ _).trans (max_le (((valuation k).map_add _ _).trans
    (max_le ?_ ?_)) ?_)
  · refine le_max_of_le_right ?_
    rw [map_mul]
    calc valuation k ((d : k) * c ^ d) * valuation k (q ^ N)
        ≤ 1 * valuation k q := by
          refine mul_le_mul' ?_ hqN_le
          rw [map_mul, map_pow]
          exact (mul_le_mul' (valuation_natCast_le_one d) (pow_le_one' hc d)).trans_eq
            (one_mul 1)
      _ = valuation k q := one_mul _
  · refine le_max_of_le_left ?_
    rw [map_mul, map_mul, map_pow, map_pow, map_inv₀]
    have hsplit : valuation k q ^ N = valuation k q ^ d * valuation k q ^ (N - d) := by
      rw [← pow_add]
      congr 1
      omega
    calc valuation k ((d : ℕ) : k) * (valuation k c)⁻¹ ^ d * valuation k q ^ N
        ≤ 1 * (valuation k c)⁻¹ ^ d * valuation k q ^ N :=
          mul_le_mul' (mul_le_mul' (valuation_natCast_le_one d) le_rfl) le_rfl
      _ = (valuation k q * (valuation k c)⁻¹) ^ d * valuation k q ^ (N - d) := by
        rw [one_mul, hsplit, mul_pow]
        exact (mul_left_comm _ _ _).trans (mul_assoc _ _ _).symm
      _ ≤ (valuation k q * (valuation k c)⁻¹) ^ d * 1 :=
        mul_le_mul' le_rfl (pow_le_one' hq _)
      _ = (valuation k q * (valuation k c)⁻¹) ^ d := mul_one _
      _ ≤ (valuation k q * (valuation k c)⁻¹) ^ 1 :=
        pow_le_pow_right_of_le_one' hqc hd1
      _ = valuation k q * (valuation k c)⁻¹ := pow_one _
  · refine le_max_of_le_right ?_
    rw [map_mul]
    calc valuation k (2 * (d : k)) * valuation k (q ^ N) ≤ 1 * valuation k q := by
          refine mul_le_mul' ?_ hqN_le
          rw [show ((2 : k) * (d : k)) = ((2 * d : ℕ) : k) by push_cast; ring]
          exact valuation_natCast_le_one _
      _ = valuation k q := one_mul _

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
private theorem TateCurve.valuation_XField_tail_term_le_max_aux (q c : k)
    (hq : valuation k q ≤ 1) (hc : valuation k c ≤ 1)
    (hqc : valuation k q * (valuation k c)⁻¹ ≤ 1) (N : ℕ) :
    valuation k ((∑ d ∈ N.divisors,
      ((d : k) * c ^ d + (d : k) * (c⁻¹) ^ d - 2 * (d : k))) * q ^ N)
      ≤ max (valuation k q * (valuation k c)⁻¹) (valuation k q) := by
  rcases N with - | N
  · simp
  · rw [Finset.sum_mul]
    refine (valuation k).map_sum_le fun d hd ↦
      valuation_XField_tail_divisor_le_max_aux q c hq hc hqc
        (Nat.one_le_iff_ne_zero.mpr (Nat.pos_of_mem_divisors hd).ne')
        (Nat.le_of_dvd (Nat.succ_pos N) (Nat.mem_divisors.mp hd).1)

private theorem TateCurve.valuation_XField_tail_lt_one_aux (q : kˣ)
    {c : k} (hc1 : valuation k (q : k) < valuation k c) (hc2 : valuation k c < 1) :
    valuation k (∑' N : ℕ, (∑ d ∈ N.divisors,
      ((d : k) * c ^ d + (d : k) * (c⁻¹) ^ d - 2 * (d : k))) * (q : k) ^ N) < 1 := by
  have hvc0 : valuation k c ≠ 0 := fun h0 ↦
    (valuation k).ne_zero_iff.mpr q.ne_zero (le_antisymm (h0 ▸ hc1.le) zero_le)
  have hc0 : c ≠ 0 := (valuation k).ne_zero_iff.mp hvc0
  have hqc : valuation k (q : k) * (valuation k c)⁻¹ < 1 := by
    exact (mul_lt_mul_iff_left₀ (zero_lt_iff.mpr (inv_ne_zero hvc0))).mpr hc1 |>.trans_eq
      (mul_inv_cancel₀ hvc0)
  have htails : Summable fun N : ℕ ↦ (∑ d ∈ N.divisors,
      ((d : k) * c ^ d + (d : k) * (c⁻¹) ^ d - 2 * (d : k))) * (q : k) ^ N :=
    ((evalBounded_XField_tail q (Units.mk0 c hc0) hc2.le).summable (by simpa using hqc)).congr
      fun n ↦ by rw [PowerSeries.coeff_mk, Units.val_mk0]
  exact (valuation_tsum_le htails fun N ↦
    valuation_XField_tail_term_le_max_aux (q : k) c (hc1.trans hc2).le hc2.le hqc.le N).trans_lt
      (max_lt hqc (hc1.trans hc2))

/-- `|X(c, q)| < 1` for `|q| < |c| < 1`: the images `φ(ϖᵐ)`, `0 < m < ord q`, of proper
uniformizer powers lie outside `E_{q,0}(k)` (all terms of the annulus expansion are small).
Feeds the pigeonhole contradiction in `exists_tateCurvePoint_sub_component_zero`. -/
theorem WeierstrassCurve.valuation_tateX_lt_one (q : kˣ) (hq : valuation k (q : k) < 1)
    {c : k} (hc1 : valuation k (q : k) < valuation k c) (hc2 : valuation k c < 1) :
    valuation k (tateX c (q : k)) < 1 := by
  have hc0 : c ≠ 0 := by
    intro h
    rw [h, map_zero] at hc1
    exact (not_lt_of_ge (show (0 : ValueGroupWithZero k) ≤ valuation k (q : k) from zero_le)) hc1
  have hann := tateX_eq_annulus q (Units.mk0 c hc0) hq (by simpa using hc1)
    (by simpa using hc2.le)
  simp only [Units.val_mk0] at hann
  rw [hann]
  exact ((valuation k).map_add _ _).trans_lt <| max_lt
    (valuation_annulus_X_leading_lt_one_aux hc2)
    (TateCurve.valuation_XField_tail_lt_one_aux q hc1 hc2)

private inductive WeierstrassCurve.TateCurveComponentData (q x y : k)
    (π₀ : ValueGroupWithZero k) (N : ℕ)
  | U (j : ℕ) (hj1 : 1 ≤ j) (hjN : 2 * j < N)
      (hlt : valuation k (x + y) < valuation k y)
      (hval : valuation k y = π₀ ^ (j : ℤ))
  | V (j : ℕ) (hj1 : 1 ≤ j) (hjN : 2 * j < N)
      (hlt : valuation k y < valuation k (x + y))
      (hval : valuation k (x + y) = π₀ ^ (j : ℤ))
  | W (heq : valuation k y = valuation k (x + y))
      (hsq : valuation k y ^ 2 = valuation k q)

private def WeierstrassCurve.TateCurveComponentData.code {q x y : k}
    {π₀ : ValueGroupWithZero k} {N : ℕ} : TateCurveComponentData q x y π₀ N → ℕ
  | .U j _ _ _ _ => 2 * j - 1
  | .V j _ _ _ _ => 2 * j
  | .W _ _ => N - 1

private theorem ValuativeRel.exists_unit_uniformizer_order_aux {K : Type*} [Field K]
    [ValuativeRel K] [IsDiscrete K] [IsRankLeOne K] [IsNontrivial K] (q : Kˣ)
    (hq : valuation K (q : K) < 1) :
    ∃ (ϖ : Kˣ) (N : ℕ), 1 ≤ N ∧ valuation K (ϖ : K) = uniformizer K ∧
      valuation K (q : K) = uniformizer K ^ (N : ℤ) := by
  have hvq0 : valuation K (q : K) ≠ 0 := (valuation K).ne_zero_iff.mpr q.ne_zero
  obtain ⟨ϖ, hϖ⟩ := exists_unit_valuation_uniformizer K
  obtain ⟨n, hn⟩ := exists_zpow_uniformizer_eq (R := K) hvq0
  have hn1 : 1 ≤ n := by
    by_contra hnpos
    have hn0 : n ≤ 0 := by omega
    have hone : (1 : ValueGroupWithZero K) ≤ uniformizer K ^ n := by
      rw [← zpow_zero (uniformizer K)]
      exact (zpow_right_strictAnti₀ uniformizer_pos uniformizer_lt_one).antitone hn0
    rw [hn] at hone
    exact (not_le_of_gt hq) hone
  refine ⟨ϖ, n.toNat, by omega, hϖ, ?_⟩
  rw [← hn]
  congr 1
  omega

private theorem ValuativeRel.exists_pos_nat_uniformizer_pow_eq_aux {K : Type*} [CommRing K]
    [ValuativeRel K] [IsDiscrete K] [IsRankLeOne K] [IsNontrivial K]
    {γ : ValueGroupWithZero K} (hγ0 : γ ≠ 0) (hγ1 : γ < 1) :
    ∃ j : ℕ, 1 ≤ j ∧ γ = uniformizer K ^ (j : ℤ) := by
  obtain ⟨n, hn⟩ := exists_zpow_uniformizer_eq (R := K) hγ0
  have hn1 : 1 ≤ n := by
    by_contra hnpos
    have hn0 : n ≤ 0 := by omega
    have hone : (1 : ValueGroupWithZero K) ≤ uniformizer K ^ n := by
      rw [← zpow_zero (uniformizer K)]
      exact (zpow_right_strictAnti₀ uniformizer_pos uniformizer_lt_one).antitone hn0
    rw [hn] at hone
    exact (not_le_of_gt hγ1) hone
  refine ⟨n.toNat, by omega, ?_⟩
  rw [← hn]
  congr 1
  omega

open scoped Classical in
private theorem WeierstrassCurve.exists_tateCurve_translate_data_aux (q : kˣ)
    (hq : valuation k (q : k) < 1) (P : ((tateCurve (q : k))⁄k).Point) (ϖ : kˣ)
    (hnotIntegral : ∀ c : kˣ,
      P - tateCurvePoint q hq c ≠ 0 ∧
        ∀ (x y : k) (h : ((tateCurve (q : k))⁄k).Nonsingular x y),
          P - tateCurvePoint q hq c = .some x y h → valuation k x < 1) :
    ∃ (X Y : ℕ → k) (Hns : ∀ m, ((tateCurve (q : k))⁄k).Nonsingular (X m) (Y m)),
      (∀ m, P - tateCurvePoint q hq (ϖ ^ m) = .some (X m) (Y m) (Hns m)) ∧
        ∀ m, valuation k (X m) < 1 := by
  have hdata : ∀ m : ℕ, ∃ (x y : k) (h : ((tateCurve (q : k))⁄k).Nonsingular x y),
      P - tateCurvePoint q hq (ϖ ^ m) = .some x y h ∧ valuation k x < 1 := by
    intro m
    rcases hQ : P - tateCurvePoint q hq (ϖ ^ m) with - | ⟨x, y, h⟩
    · exact False.elim ((hnotIntegral (ϖ ^ m)).1 hQ)
    · exact ⟨x, y, h, rfl, (hnotIntegral (ϖ ^ m)).2 x y h hQ⟩
  choose X Y Hns HQ HX using hdata
  exact ⟨X, Y, Hns, HQ, HX⟩

private theorem WeierstrassCurve.exists_tateCurveComponentData_of_small_aux (q : kˣ)
    (hq : valuation k (q : k) < 1) {x y : k} {N : ℕ}
    (hqN : valuation k (q : k) = uniformizer k ^ (N : ℤ))
    (h : ((tateCurve (q : k))⁄k).Nonsingular x y) (hx : valuation k x < 1) :
    ∃ C : TateCurveComponentData (q : k) x y (uniformizer k) N,
      C.code ∈ Finset.Icc 1 (N - 1) := by
  have hvq0 : valuation k (q : k) ≠ 0 := (valuation k).ne_zero_iff.mpr q.ne_zero
  have hy : valuation k y < 1 := tateCurve_valuation_y_lt_one hq h.1 hx
  rcases tateCurve_component_trichotomy q.ne_zero hq h.1 hx with hU | hV | hW
  · have hy0 : valuation k y ≠ 0 := by
      intro hy0
      rw [hy0] at hU
      exact (not_lt_of_ge (show (0 : ValueGroupWithZero k) ≤ valuation k (q : k) from zero_le))
        (by simpa using hU.2)
    obtain ⟨j, hj1, hj⟩ := ValuativeRel.exists_pos_nat_uniformizer_pow_eq_aux hy0 hy
    have hjN : 2 * j < N := by
      rw [hqN, hj, ← zpow_natCast (uniformizer k ^ (j : ℤ)) 2, ← zpow_mul] at hU
      have hjN' := (zpow_lt_zpow_iff_right_of_lt_one₀ uniformizer_pos uniformizer_lt_one).mp hU.2
      omega
    refine ⟨.U j hj1 hjN hU.1 hj, ?_⟩
    change 2 * j - 1 ∈ Finset.Icc 1 (N - 1)
    exact Finset.mem_Icc.mpr (by omega)
  · have hxy : valuation k (x + y) < 1 :=
      lt_of_le_of_lt ((valuation k).map_add _ _) (max_lt hx hy)
    have hxy0 : valuation k (x + y) ≠ 0 := by
      intro hxy0
      rw [hxy0] at hV
      exact (not_lt_of_ge (show (0 : ValueGroupWithZero k) ≤ valuation k (q : k) from zero_le))
        (by simpa using hV.2)
    obtain ⟨j, hj1, hj⟩ := ValuativeRel.exists_pos_nat_uniformizer_pow_eq_aux hxy0 hxy
    have hjN : 2 * j < N := by
      rw [hqN, hj, ← zpow_natCast (uniformizer k ^ (j : ℤ)) 2, ← zpow_mul] at hV
      have hjN' := (zpow_lt_zpow_iff_right_of_lt_one₀ uniformizer_pos uniformizer_lt_one).mp hV.2
      omega
    refine ⟨.V j hj1 hjN hV.1 hj, ?_⟩
    change 2 * j ∈ Finset.Icc 1 (N - 1)
    exact Finset.mem_Icc.mpr (by omega)
  · have hy0 : valuation k y ≠ 0 := by
      intro hy0
      rw [hy0] at hW
      exact hvq0 (by simpa using hW.2.symm)
    obtain ⟨j, hj1, hj⟩ := ValuativeRel.exists_pos_nat_uniformizer_pow_eq_aux hy0 hy
    have hNj : N = 2 * j := by
      have hNj' : (N : ℤ) = 2 * (j : ℤ) := by
        refine (zpow_right_injective₀
          (show (0 : ValueGroupWithZero k) < uniformizer k from uniformizer_pos)
          (show uniformizer k ≠ (1 : ValueGroupWithZero k) from uniformizer_lt_one.ne)) ?_
        change uniformizer k ^ (N : ℤ) = uniformizer k ^ (2 * (j : ℤ))
        rw [← hqN, ← hW.2, hj, ← zpow_natCast (uniformizer k ^ (j : ℤ)) 2, ← zpow_mul]
        congr 1
        omega
      omega
    refine ⟨.W hW.1 hW.2, ?_⟩
    change N - 1 ∈ Finset.Icc 1 (N - 1)
    exact Finset.mem_Icc.mpr (by omega)

open scoped Classical in
private theorem WeierstrassCurve.tateCurve_translate_pow_sub_aux (q : kˣ)
    (hq : valuation k (q : k) < 1) (P : ((tateCurve (q : k))⁄k).Point) (ϖ : kˣ)
    {a b : ℕ} {x y x' y' : k} (h : ((tateCurve (q : k))⁄k).Nonsingular x y)
    (h' : ((tateCurve (q : k))⁄k).Nonsingular x' y') (hab : a < b)
    (hQa : P - tateCurvePoint q hq (ϖ ^ a) = .some x y h)
    (hQb : P - tateCurvePoint q hq (ϖ ^ b) = .some x' y' h') :
    Affine.Point.some x y h - Affine.Point.some x' y' h' =
      tateCurvePoint q hq (ϖ ^ (b - a)) := by
  rw [← hQa, ← hQb]
  have hsplit : ϖ ^ b = ϖ ^ (b - a) * ϖ ^ a := by
    rw [← pow_add]
    congr 1
    omega
  simp only [hsplit, tateCurvePoint_mul]
  abel

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
private theorem valuation_uniformizer_pow_sub_aux {ϖ : kˣ} {π₀ : ValueGroupWithZero k}
    {a b : ℕ} (hϖ : valuation k (ϖ : k) = π₀) (hab : a ≤ b) :
    valuation k (((ϖ ^ (b - a) : kˣ) : k)) = π₀ ^ ((b : ℤ) - a) := by
  rw [Units.val_pow_eq_pow_val, map_pow, hϖ, ← zpow_natCast]
  congr 1
  omega

private theorem not_mem_zpowers_uniformizer_pow_sub_aux (q ϖ : kˣ) {N a b : ℕ}
    (hN1 : 1 ≤ N) (hqN : valuation k (q : k) = uniformizer k ^ (N : ℤ))
    (hϖ : valuation k (ϖ : k) = uniformizer k) (hab : a < b) (hbN : b < N) :
    ϖ ^ (b - a) ∉ Subgroup.zpowers q := by
  rintro ⟨z, hz⟩
  have hval := congrArg (fun u : kˣ ↦ valuation k (u : k)) hz
  simp only [Units.val_zpow_eq_zpow_val, map_zpow₀] at hval
  rw [hqN, ← zpow_mul, valuation_uniformizer_pow_sub_aux hϖ hab.le] at hval
  have hNz : (N : ℤ) * z = (b : ℤ) - a := by
    refine (zpow_right_injective₀
      (show (0 : ValueGroupWithZero k) < uniformizer k from uniformizer_pos)
      (show uniformizer k ≠ (1 : ValueGroupWithZero k) from uniformizer_lt_one.ne)) ?_
    change uniformizer k ^ ((N : ℤ) * z) = uniformizer k ^ ((b : ℤ) - a)
    exact hval
  rcases lt_trichotomy z 0 with hz0 | hz0 | hz0
  · have : (N : ℤ) * z < 0 := mul_neg_of_pos_of_neg (by omega) hz0
    omega
  · rw [hz0, mul_zero] at hNz
    omega
  · have : (N : ℤ) ≤ (N : ℤ) * z := le_mul_of_one_le_right (by omega) (by omega)
    omega

open scoped Classical in
private theorem WeierstrassCurve.tateCurvePoint_uniformizer_pow_not_integral_aux (q ϖ : kˣ)
    (hq : valuation k (q : k) < 1) {N a b : ℕ} (hN1 : 1 ≤ N)
    (hqN : valuation k (q : k) = uniformizer k ^ (N : ℤ))
    (hϖ : valuation k (ϖ : k) = uniformizer k) (hab : a < b) (hbN : b < N) :
    ¬(tateCurvePoint q hq (ϖ ^ (b - a)) = 0 ∨
      ∃ (x y : k) (h : ((tateCurve (q : k))⁄k).Nonsingular x y),
        tateCurvePoint q hq (ϖ ^ (b - a)) = .some x y h ∧ 1 ≤ valuation k x) := by
  intro hdisj
  have hnotmem := not_mem_zpowers_uniformizer_pow_sub_aux q ϖ hN1 hqN hϖ hab hbN
  have hvpow := valuation_uniformizer_pow_sub_aux (a := a) (b := b) hϖ hab.le
  rcases hdisj with hzero | ⟨x, y, h, heq, hx⟩
  · exact hnotmem ((tateCurvePoint_eq_zero_iff q hq).mp hzero)
  · rw [tateCurvePoint, dif_neg hnotmem, Affine.Point.some.injEq] at heq
    have hsmall : valuation k (tateX ((ϖ ^ (b - a) : kˣ) : k) (q : k)) < 1 := by
      refine valuation_tateX_lt_one q hq ?_ ?_
      · rw [hvpow, hqN]
        exact (zpow_right_strictAnti₀ uniformizer_pos uniformizer_lt_one) (by omega)
      · rw [hvpow, ← zpow_zero (uniformizer k)]
        exact (zpow_right_strictAnti₀ uniformizer_pos uniformizer_lt_one) (by omega)
    rw [heq.1] at hsmall
    exact (not_le_of_gt hsmall) hx

private theorem WeierstrassCurve.even_order_of_tateCurveComponent_W_aux (q : kˣ) {y : k}
    {N : ℕ} (hqN : valuation k (q : k) = uniformizer k ^ (N : ℤ))
    (hy : valuation k y < 1) (hWq : valuation k y ^ 2 = valuation k (q : k)) :
    ∃ j : ℕ, N = 2 * j := by
  have hvq0 : valuation k (q : k) ≠ 0 := (valuation k).ne_zero_iff.mpr q.ne_zero
  have hy0 : valuation k y ≠ 0 := by
    intro hy0
    rw [hy0] at hWq
    exact hvq0 (by simpa using hWq.symm)
  obtain ⟨j, _, hj⟩ := ValuativeRel.exists_pos_nat_uniformizer_pow_eq_aux hy0 hy
  refine ⟨j, ?_⟩
  have hNj : (N : ℤ) = 2 * (j : ℤ) := by
    refine (zpow_right_injective₀
      (show (0 : ValueGroupWithZero k) < uniformizer k from uniformizer_pos)
      (show uniformizer k ≠ (1 : ValueGroupWithZero k) from uniformizer_lt_one.ne)) ?_
    change uniformizer k ^ (N : ℤ) = uniformizer k ^ (2 * (j : ℤ))
    rw [← hqN, ← hWq, hj, ← zpow_natCast (uniformizer k ^ (j : ℤ)) 2, ← zpow_mul]
    congr 1
    omega
  omega

open scoped Classical in
private theorem WeierstrassCurve.same_tateCurveComponentData_sub_integral_aux (q : kˣ)
    (hq : valuation k (q : k) < 1) {N : ℕ}
    (hqN : valuation k (q : k) = uniformizer k ^ (N : ℤ)) {x y x' y' : k}
    (h : ((tateCurve (q : k))⁄k).Nonsingular x y)
    (h' : ((tateCurve (q : k))⁄k).Nonsingular x' y')
    (hx : valuation k x < 1) (hx' : valuation k x' < 1)
    (C : TateCurveComponentData (q : k) x y (uniformizer k) N)
    (C' : TateCurveComponentData (q : k) x' y' (uniformizer k) N)
    (hcode : C.code = C'.code) :
    Affine.Point.some x y h - Affine.Point.some x' y' h' = 0 ∨
      ∃ (x'' y'' : k) (h'' : ((tateCurve (q : k))⁄k).Nonsingular x'' y''),
        Affine.Point.some x y h - Affine.Point.some x' y' h' = .some x'' y'' h'' ∧
          1 ≤ valuation k x'' := by
  rcases C with ⟨ja, hja1, hjaN, hUa, hva⟩ | ⟨ja, hja1, hjaN, hVa, hva⟩
    | ⟨hWa, hWqa⟩ <;>
    rcases C' with ⟨jb, hjb1, hjbN, hUb, hvb⟩ | ⟨jb, hjb1, hjbN, hVb, hvb⟩
      | ⟨hWb, hWqb⟩
  · have hjj : ja = jb := by
      change 2 * ja - 1 = 2 * jb - 1 at hcode
      omega
    refine tateCurve_sub_of_same_U h h' (by rw [hva, hvb, hjj]) hUa hUb ?_
    rw [hva, ← zpow_zero (uniformizer k)]
    exact (zpow_right_strictAnti₀ uniformizer_pos uniformizer_lt_one) (by omega)
  · change 2 * ja - 1 = 2 * jb at hcode
    omega
  · change 2 * ja - 1 = N - 1 at hcode
    omega
  · change 2 * ja = 2 * jb - 1 at hcode
    omega
  · have hjj : ja = jb := by
      change 2 * ja = 2 * jb at hcode
      omega
    refine tateCurve_sub_of_same_V h h' (by rw [hva, hvb, hjj]) hVa hVb ?_
    rw [hva, ← zpow_zero (uniformizer k)]
    exact (zpow_right_strictAnti₀ uniformizer_pos uniformizer_lt_one) (by omega)
  · change 2 * ja = N - 1 at hcode
    obtain ⟨jw, hN⟩ := even_order_of_tateCurveComponent_W_aux q hqN
      (tateCurve_valuation_y_lt_one hq h'.1 hx') hWqb
    omega
  · change N - 1 = 2 * jb - 1 at hcode
    omega
  · change N - 1 = 2 * jb at hcode
    obtain ⟨jw, hN⟩ := even_order_of_tateCurveComponent_W_aux q hqN
      (tateCurve_valuation_y_lt_one hq h.1 hx) hWqa
    omega
  · exact tateCurve_sub_of_same_W q.ne_zero hq h h' hWqa hWa.symm hWqb hWb.symm

open scoped Classical in
private theorem WeierstrassCurve.no_tateCurveComponentData_collision_aux (q : kˣ)
    (hq : valuation k (q : k) < 1) (P : ((tateCurve (q : k))⁄k).Point) (ϖ : kˣ)
    {N a b : ℕ} (hN1 : 1 ≤ N)
    (hqN : valuation k (q : k) = uniformizer k ^ (N : ℤ))
    (hϖ : valuation k (ϖ : k) = uniformizer k) {X Y : ℕ → k}
    (Hns : ∀ m, ((tateCurve (q : k))⁄k).Nonsingular (X m) (Y m))
    (HQ : ∀ m, P - tateCurvePoint q hq (ϖ ^ m) = .some (X m) (Y m) (Hns m))
    (HX : ∀ m, valuation k (X m) < 1) (hab : a < b) (hbN : b < N)
    (Ca : TateCurveComponentData (q : k) (X a) (Y a) (uniformizer k) N)
    (Cb : TateCurveComponentData (q : k) (X b) (Y b) (uniformizer k) N)
    (hcode : Ca.code = Cb.code) : False := by
  have hdiff := tateCurve_translate_pow_sub_aux q hq P ϖ (Hns a) (Hns b) hab (HQ a) (HQ b)
  have hdisj := same_tateCurveComponentData_sub_integral_aux q hq hqN (Hns a) (Hns b)
    (HX a) (HX b) Ca Cb hcode
  rw [hdiff] at hdisj
  exact tateCurvePoint_uniformizer_pow_not_integral_aux q ϖ hq hN1 hqN hϖ hab hbN hdisj

open scoped Classical in
private theorem WeierstrassCurve.tateCurve_component_pigeonhole_aux (q : kˣ)
    (hq : valuation k (q : k) < 1) (P : ((tateCurve (q : k))⁄k).Point) (ϖ : kˣ)
    {N : ℕ} (hN1 : 1 ≤ N) (hqN : valuation k (q : k) = uniformizer k ^ (N : ℤ))
    (hϖ : valuation k (ϖ : k) = uniformizer k) {X Y : ℕ → k}
    (Hns : ∀ m, ((tateCurve (q : k))⁄k).Nonsingular (X m) (Y m))
    (HQ : ∀ m, P - tateCurvePoint q hq (ϖ ^ m) = .some (X m) (Y m) (Hns m))
    (HX : ∀ m, valuation k (X m) < 1) : False := by
  have hdata : ∀ m, ∃ C : TateCurveComponentData (q : k) (X m) (Y m) (uniformizer k) N,
      C.code ∈ Finset.Icc 1 (N - 1) := fun m ↦
    exists_tateCurveComponentData_of_small_aux q hq hqN (Hns m) (HX m)
  choose C hmem using hdata
  have hcard : (Finset.Icc 1 (N - 1)).card < (Finset.range N).card := by
    rw [Nat.card_Icc, Finset.card_range]
    omega
  obtain ⟨m, hmN, m', hm'N, hne, hcodes⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcard (fun a _ ↦ hmem a)
  rw [Finset.mem_range] at hmN hm'N
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact no_tateCurveComponentData_collision_aux q hq P ϖ hN1 hqN hϖ Hns HQ HX hlt hm'N
      (C m) (C m') hcodes
  · exact no_tateCurveComponentData_collision_aux q hq P ϖ hN1 hqN hϖ Hns HQ HX hgt hmN
      (C m') (C m) hcodes.symm


open scoped Classical in
/-- **The component piece of Tate surjectivity** (Silverman ATAEC V.4, Proposition 4.1):
every point of `E_q(k)` can be translated by some `φ(c)` into the subgroup
`E_{q,0}(k) = {O} ∪ {|x| ≥ 1}`. Internally `c = ϖᵐ` for a uniformizer `ϖ` and `0 ≤ m < N`
where `|q| = |ϖ|ᴺ`: if no translate lands in `E_{q,0}(k)`, the `N` translates fall into the
`N - 1` classes of `tateCurve_component_trichotomy` (coded by the value `|y|`, `|x+y|` or
`W`-membership), so two translates share a class; their difference `φ(ϖᵐ'⁻ᵐ)` would have
`|x| ≥ 1` by Lemma 4.1.4, contradicting `valuation_tateX_lt_one`. -/
theorem WeierstrassCurve.exists_tateCurvePoint_sub_component_zero (q : kˣ)
    (hq : valuation k (q : k) < 1) (P : ((tateCurve (q : k))⁄k).Point) :
    ∃ c : kˣ, P - tateCurvePoint q hq c = 0 ∨
      ∃ (x y : k) (h : ((tateCurve (q : k))⁄k).Nonsingular x y),
        P - tateCurvePoint q hq c = .some x y h ∧ 1 ≤ valuation k x := by
  obtain ⟨ϖ, N, hN1, hϖ, hqN⟩ := ValuativeRel.exists_unit_uniformizer_order_aux q hq
  by_contra hnotIntegral
  push Not at hnotIntegral
  obtain ⟨X, Y, Hns, HQ, HX⟩ :=
    exists_tateCurve_translate_data_aux q hq P ϖ hnotIntegral
  exact tateCurve_component_pigeonhole_aux q hq P ϖ hN1 hqN hϖ Hns HQ HX

/-- **Surjectivity of Tate's uniformisation** (Silverman, ATAEC V.4): every point of
`E_q(k)` is `φ(u)` for some `u ∈ kˣ`.

Assembles the three pieces: `exists_tateCurvePoint_sub_component_zero` translates `P` into
`{O} ∪ {|x| ≥ 1}` by some `φ(c)`; on `|x| = 1` the unit piece
(`exists_tateCurvePoint_eq_of_eq_one`) applies; on `|x| > 1` the formal-group piece
(`exists_tateCurvePoint_eq_of_one_lt`) applies; additivity `tateCurvePoint_mul` combines the
parameters. -/
theorem WeierstrassCurve.exists_tateCurvePoint_eq (q : kˣ)
    (hq : valuation k (q : k) < 1) (P : ((tateCurve (q : k))⁄k).Point) :
    ∃ u : kˣ, tateCurvePoint q hq u = P := by
  classical
  obtain ⟨c, hc⟩ := exists_tateCurvePoint_sub_component_zero q hq P
  rcases hc with h0 | ⟨x, y, h, hdiff, hbig⟩
  · exact ⟨c, (sub_eq_zero.mp h0).symm⟩
  · rcases lt_or_eq_of_le hbig with hgt | heq1
    · obtain ⟨v, hv⟩ := exists_tateCurvePoint_eq_of_one_lt q hq h hgt
      refine ⟨c * v, ?_⟩
      rw [tateCurvePoint_mul, hv, ← hdiff]
      abel
    · obtain ⟨v, hv⟩ := exists_tateCurvePoint_eq_of_eq_one q hq h heq1.symm
      refine ⟨c * v, ?_⟩
      rw [tateCurvePoint_mul, hv, ← hdiff]
      abel
