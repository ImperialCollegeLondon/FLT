/-
Copyright (c) 2026 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Reduction
public import Mathlib.NumberTheory.LocalField.Basic
public import FLT.KnownIn1980s.EllipticCurves.WeilPairing
public import FLT.KnownIn1980s.EllipticCurves.TateParameter
public import FLT.KnownIn1980s.EllipticCurves.TateCurveDescent

public import Mathlib.NumberTheory.ModularForms.Discriminant
public import Mathlib.NumberTheory.ModularForms.NormTrace

import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean

/-!

# The Tate curve

Let `k` be a nonarchimedean local field and let `E/k` be an elliptic curve, given by a
minimal Weierstrass equation, with split multiplicative reduction. Tate's theory attaches
to `E` a canonical *Tate parameter*, an element `q = q(E)` of `k` with `0 < |q| < 1`, and
an isomorphism of groups `E(k) ≅ kˣ/qᶻ` (Tate's uniformisation). The construction is
functorial: if `k → l` is a valuation-compatible morphism of nonarchimedean local fields
then the base change of `E` to `l` again has split multiplicative reduction, the Tate
parameter of the base change is the image of `q`, and the uniformisations over `k` and `l`
fit into a commutative diagram — in general only up to an unremovable sign, but on the nose
when the morphism is `k`-linear (see `tateEquiv_baseChange` and `tateEquiv_galois`). The
`k`-linear case gives the Galois-equivariance needed to compute the Galois representations
attached to `E`.

These results are due to Tate, in a manuscript which
circulated from the early 1960s and was eventually published in 1995 as *A review of
non-Archimedean elliptic curves*. See also Roquette, *Analytic theory of elliptic
functions over local fields* (1970), and Silverman, *Advanced topics in the arithmetic
of elliptic curves*, V.3 and V.5, for textbook accounts.

## TODO

* **Rank 1 generality.** Tate's theory works over any field complete with respect to a
  nontrivial rank 1 (i.e. real-valued) nonarchimedean valuation, for example `ℂ_p` or the
  completion of the maximal unramified extension of `ℚ_p`: completeness and `|q| < 1` are
  all that is needed for the relevant power series to converge. But right now we can't
  talk about an elliptic curve over `ℂ_p` having split multiplicative reduction, so we
  stick to nonarchimedean local fields: mathlib's
  `WeierstrassCurve.HasSplitMultiplicativeReduction` is defined via minimal Weierstrass
  equations, and mathlib's `WeierstrassCurve.IsMinimal` requires
  `IsDiscreteValuationRing` (its existence theorem `exists_isMinimal` is proved by
  well-foundedness of the value group, which fails for dense value groups).

  Mathematics question: is there a theory of minimal models for elliptic curves
  with multiplicative reduction over fields complete wrt an arbitrary rank 1 valuation?
  For additive reduction you have no chance (consider `y² = x³ + p` over `ℂₚ`).

* **Topology.** `tateEquiv` below should be an isomorphism of *topological* groups, where
  `kˣ/qᶻ` carries the quotient topology and `E(k)` the topology coming from `k`. This
  cannot currently be stated: mathlib has no topology on `WeierstrassCurve.Affine.Point`
  (nor on `Projectivization`, from which it could be induced).

* **Signs.** There is a choice of sign for the Tate uniformisation. I propose that we
  simply use the definition in e.g. Silverman. One could say explicitly what the sign
  is by asking what the pullback of the invariant differential `dx/(2y + a₁x + a₃)` to
  `kˣ` is; it will be some constant times `du/u` (for the Tate curve `E_q` itself, with
  Silverman's series, it is exactly `du/u`).
-/

@[expose] public section

open scoped WeierstrassCurve.Affine -- `(E⁄k).Point` notation for the group of `k`-points
open scoped PowerSeries -- `ℤ⟦X⟧` notation for `PowerSeries ℤ`
open scoped Topology -- `𝓝` notation for neighbourhood filters
open ValuativeRel -- `𝒪[k]` notation for the ring of integers of `k`, and `valuation`

-- Can be deleted when mathlib#41391 lands
set_option linter.overlappingInstances false

/-! ### The Tate curve `E_q`

For `q` with `0 < |q| < 1` there is an explicit Weierstrass curve `E_q`, whose coefficients
are power series in `q` with integer coefficients, together with a uniformisation
`kˣ/qᶻ ≅ E_q(k)` given by explicit power series `X(u, q)`, `Y(u, q)` — all of it involving
no choices whatsoever, and commuting on the nose with every valuative morphism of fields.
The uniformisation of a general `E` with split multiplicative reduction is obtained by
transporting this one along an isomorphism `E_{q(E)} ≅ E` of Weierstrass curves
(`exists_variableChange_tateCurve` below), and *that* is the only choice in the theory:
there are exactly two such isomorphisms, differing by negation.
-/

section TateCurve

-- For the defining series we only need a topology on the field: this section makes sense
-- (and the series converge) over any field complete with respect to a rank 1
-- nonarchimedean valuation, cf. the TODO above.
variable {k : Type*} [Field k] [TopologicalSpace k]

/-- The coefficient `a₄(q) = -5s₃(q)` of the Tate curve, where
`sₖ(q) = ∑_{n≥1} nᵏqⁿ/(1-qⁿ)` (Silverman, ATAEC V.3). -/
noncomputable def WeierstrassCurve.tateA₄ (q : k) : k :=
  -5 * ∑' n : ℕ, ((n + 1 : ℕ) : k) ^ 3 * q ^ (n + 1) / (1 - q ^ (n + 1))

/-- The coefficient `a₆(q) = -(5s₃(q) + 7s₅(q))/12` of the Tate curve, where
`sₖ(q) = ∑_{n≥1} nᵏqⁿ/(1-qⁿ)`; the integrality `12 ∣ 5n³ + 7n⁵` makes sense of the
division by `12` in every characteristic (Silverman, ATAEC V.3). -/
noncomputable def WeierstrassCurve.tateA₆ (q : k) : k :=
  ∑' n : ℕ, -(((5 * (n + 1) ^ 3 + 7 * (n + 1) ^ 5) / 12 : ℤ) : k) * q ^ (n + 1) /
    (1 - q ^ (n + 1))

/-- The Tate curve `E_q : y² + xy = x³ + a₄(q)x + a₆(q)` (Silverman, ATAEC V.3). -/
noncomputable def WeierstrassCurve.tateCurve (q : k) : WeierstrassCurve k :=
  ⟨1, 0, 0, tateA₄ q, tateA₆ q⟩

/-- The `j`-invariant `j(q) = c₄(q)³/Δ(q) = q⁻¹ + 744 + 196884q + ⋯` of the Tate curve
(Silverman, ATAEC V.1.1(b)), defined via the usual `c₄` and `Δ` of the Weierstrass
equation of `E_q` (concretely `c₄(q) = 1 - 48a₄(q) = 1 + 240s₃(q)`). For `0 < |q| < 1`
we have `|j(q)| = |q|⁻¹ > 1`: the Tate curve has non-integral `j`-invariant. -/
noncomputable def WeierstrassCurve.tateJ (q : k) : k :=
  (tateCurve q).c₄ ^ 3 / (tateCurve q).Δ

/-- The `x`-coordinate `X(u, q) = ∑_{n ∈ ℤ} qⁿu/(1 - qⁿu)² - 2s₁(q)` of Tate's
uniformisation, where `s₁(q) = ∑_{n ≥ 1} nqⁿ/(1 - qⁿ)`. This is the function `X(u, q)` of
Silverman, ATAEC V.1.1; for `0 < |q| < 1` and `u ∉ qᶻ` the sums converge (junk value
otherwise). -/
noncomputable def WeierstrassCurve.tateX (u q : k) : k :=
  (∑' n : ℤ, q ^ n * u / (1 - q ^ n * u) ^ 2) -
    2 * ∑' n : ℕ, ((n + 1 : ℕ) : k) * q ^ (n + 1) / (1 - q ^ (n + 1))

/-- The `y`-coordinate `Y(u, q) = ∑_{n ∈ ℤ} (qⁿu)²/(1 - qⁿu)³ + s₁(q)` of Tate's
uniformisation, where `s₁(q) = ∑_{n ≥ 1} nqⁿ/(1 - qⁿ)`. This is the function `Y(u, q)` of
Silverman, ATAEC V.1.1. -/
noncomputable def WeierstrassCurve.tateY (u q : k) : k :=
  (∑' n : ℤ, (q ^ n * u) ^ 2 / (1 - q ^ n * u) ^ 3) +
    ∑' n : ℕ, ((n + 1 : ℕ) : k) * q ^ (n + 1) / (1 - q ^ (n + 1))

end TateCurve

-- let k be a nonarchimedean local field
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k]

-- A field with a valuative topology is Hausdorff: `{y : |y| < |x|}` is a neighbourhood of
-- `0` not containing `x`. (Mathlib has this for `Valued` fields, `ValuedRing.separated`,
-- but not for `IsValuativeTopology`; this should move to a Mathlib fixup file or mathlib.)
instance : T2Space k := by
  apply IsTopologicalAddGroup.t2Space_of_zero_sep
  intro x hx
  refine ⟨{y | valuation k y < valuation k x}, ?_,
    fun h ↦ lt_irrefl _ (show valuation k x < valuation k x from h)⟩
  rw [IsValuativeTopology.mem_nhds_zero_iff]
  exact ⟨Units.mk0 (valuation k x) ((valuation k).ne_zero_iff.mpr hx), fun y hy ↦ hy⟩

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
/-- Integers have valuation at most `1`: they lie in the valuation subring `𝒪[k]`. -/
theorem TateCurve.valuation_intCast_le_one (m : ℤ) : valuation k (m : k) ≤ 1 :=
  (Valuation.mem_integer_iff _ _).mp (intCast_mem 𝒪[k] m)

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
/-- Natural numbers have valuation at most `1`. -/
theorem TateCurve.valuation_natCast_le_one (n : ℕ) : valuation k (n : k) ≤ 1 := by
  rw [show ((n : k)) = ((n : ℤ) : k) by push_cast; ring]
  exact valuation_intCast_le_one _

/-- Powers of an element of the open unit disc become arbitrarily small. This is where the
rank-one hypothesis on the value group enters (via mathlib's strictly monotone embedding
into `ℝ≥0`, where the statement is the usual archimedean one): an abstract value group of
higher rank need not be archimedean, and the statement would be false. -/
theorem TateCurve.exists_pow_valuation_lt (q : k) (hq : valuation k q < 1)
    (γ : (ValueGroupWithZero k)ˣ) : ∃ N : ℕ, valuation k q ^ N < γ := by
  rcases eq_or_ne (valuation k q) 0 with h0 | h0
  · exact ⟨1, by rw [h0, pow_one]; exact zero_lt_iff.mpr γ.ne_zero⟩
  · obtain ⟨s⟩ := ValuativeRel.IsRankLeOne.nonempty (R := k)
    obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one
      (show 0 < s.emb γ from by simpa using s.strictMono (zero_lt_iff.mpr γ.ne_zero))
      (show s.emb (valuation k q) < 1 from by simpa using s.strictMono hq)
    exact ⟨N, s.strictMono.lt_iff_lt.mp (by rwa [map_pow])⟩

/-- Any unit of `k` can be moved into the annulus `|q| < |·| ≤ 1` by a power of `q`:
a fundamental domain for the action of `qᶻ` on `kˣ`. As with
`exists_pow_valuation_lt`, this is where the rank-one hypothesis enters, through the
strictly monotone embedding of the value group into `ℝ≥0` and the archimedean property
`exists_mem_Ioc_zpow` there. -/
theorem TateCurve.exists_zpow_mul_mem_annulus (q : kˣ) (hq : valuation k (q : k) < 1)
    (u : kˣ) : ∃ m : ℤ, valuation k (q : k) < valuation k ((q : k) ^ m * (u : k)) ∧
      valuation k ((q : k) ^ m * (u : k)) ≤ 1 := by
  obtain ⟨s⟩ := ValuativeRel.IsRankLeOne.nonempty (R := k)
  set β := s.emb (valuation k (q : k)) with hβ
  set α := s.emb (valuation k (u : k)) with hα
  have hβ0 : 0 < β := by
    have h : valuation k (q : k) ≠ 0 := (valuation k).ne_zero_iff.mpr (Units.ne_zero q)
    simpa [hβ] using s.strictMono (zero_lt_iff.mpr h)
  have hβ1 : β < 1 := by simpa [hβ] using s.strictMono hq
  have hα0 : 0 < α := by
    have h : valuation k (u : k) ≠ 0 := (valuation k).ne_zero_iff.mpr (Units.ne_zero u)
    simpa [hα] using s.strictMono (zero_lt_iff.mpr h)
  obtain ⟨n, hn⟩ := exists_mem_Ioc_zpow hα0 ((one_lt_inv₀ hβ0).mpr hβ1)
  have hn1 : β ^ (-n) < α := by
    have := hn.1
    rwa [inv_zpow, ← zpow_neg] at this
  have hn2 : α ≤ β ^ (-(n + 1)) := by
    have := hn.2
    rwa [inv_zpow, ← zpow_neg] at this
  refine ⟨n + 1, ?_, ?_⟩
  · rw [map_mul, map_zpow₀]
    refine s.strictMono.lt_iff_lt.mp ?_
    rw [map_mul, map_zpow₀]
    calc β = β ^ (n + 1) * β ^ (-n) := by
          rw [← zpow_add₀ hβ0.ne', show n + 1 + -n = 1 by ring, zpow_one]
      _ < β ^ (n + 1) * α := mul_lt_mul_of_pos_left hn1 (zpow_pos hβ0 _)
  · rw [map_mul, map_zpow₀]
    refine s.strictMono.le_iff_le.mp ?_
    rw [map_mul, map_zpow₀, map_one]
    calc β ^ (n + 1) * α ≤ β ^ (n + 1) * β ^ (-(n + 1)) :=
          mul_le_mul_of_nonneg_left hn2 (zpow_pos hβ0 _).le
      _ = 1 := by rw [← zpow_add₀ hβ0.ne', show n + 1 + -(n + 1) = 0 by ring, zpow_zero]

/-- The convergence criterion for series over a nonarchimedean local field: if each term
of `f` is bounded by `|q|^(e i)` for an exponent function `e` with finite sublevel sets,
then `f` is summable — its terms tend to zero cofinitely, which suffices by completeness
and the nonarchimedean property (no absolute convergence is needed — contrast the
archimedean case). -/
theorem TateCurve.summable_of_valuation_le_pow {ι : Type*} {q : k} (hq : valuation k q < 1)
    {f : ι → k} (e : ι → ℕ) (he : ∀ N, {i | e i < N}.Finite)
    (hf : ∀ i, valuation k (f i) ≤ valuation k q ^ e i) : Summable f := by
  -- `Summable` only sees the topology, but the completeness criterion below is stated for
  -- uniform spaces: equip `k` with its canonical uniformity
  letI : UniformSpace k := IsTopologicalAddGroup.rightUniformSpace k
  haveI : IsUniformAddGroup k := isUniformAddGroup_of_addCommGroup
  haveI : NonarchimedeanRing k := by
    convert! ValuativeRel.nonarchimedeanRing k
    exact Valuation.toTopologicalSpace_eq _
  apply NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
  rw [(IsValuativeTopology.hasBasis_nhds (0 : k)).tendsto_right_iff]
  intro γ _
  obtain ⟨N, hN⟩ := exists_pow_valuation_lt q hq γ
  rw [Filter.eventually_cofinite]
  refine (he N).subset fun i hi ↦ ?_
  simp only [Set.mem_setOf_eq, sub_zero] at hi
  exact lt_of_not_ge fun hge ↦
    hi (lt_of_le_of_lt ((hf i).trans (pow_le_pow_right_of_le_one' hq.le hge)) hN)

/-- Every integral power series is evaluable on the open unit disc of a nonarchimedean
local field: integers have valuation at most `1`, so the terms have valuation at most
`|q|ⁿ → 0`, and a series whose terms tend to zero converges, by completeness and the
nonarchimedean property (no absolute convergence is needed — contrast the archimedean
case). -/
theorem TateCurve.summable_evalInt (q : k) (hq : valuation k q < 1) (F : ℤ⟦X⟧) :
    Summable fun n ↦ ((PowerSeries.coeff n F : ℤ) : k) * q ^ n := by
  -- `Summable` only sees the topology, but the completeness criterion below is stated for
  -- uniform spaces: equip `k` with its canonical uniformity
  letI : UniformSpace k := IsTopologicalAddGroup.rightUniformSpace k
  haveI : IsUniformAddGroup k := isUniformAddGroup_of_addCommGroup
  haveI : NonarchimedeanRing k := by
    convert! ValuativeRel.nonarchimedeanRing k
    exact Valuation.toTopologicalSpace_eq _
  -- in a complete nonarchimedean group, it suffices that the terms tend to zero
  apply NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
  rw [Nat.cofinite_eq_atTop, (IsValuativeTopology.hasBasis_nhds (0 : k)).tendsto_right_iff]
  intro γ _
  obtain ⟨N, hN⟩ := exists_pow_valuation_lt q hq γ
  -- from `n ≥ N` on, the terms have valuation `≤ |q|ⁿ ≤ |q|^N < γ`
  filter_upwards [Filter.eventually_ge_atTop N] with n hn
  simp only [sub_zero, map_mul, map_pow]
  calc valuation k ((PowerSeries.coeff n F : ℤ) : k) * valuation k q ^ n
      ≤ 1 * valuation k q ^ n := mul_le_mul_left (valuation_intCast_le_one _) _
    _ = valuation k q ^ n := one_mul _
    _ ≤ valuation k q ^ N := pow_le_pow_right_of_le_one' hq.le hn
    _ < γ := hN

/-- Evaluation of integral power series at a point of the open unit disc is
multiplicative: the nonarchimedean Mertens theorem (the Cauchy product of two convergent
series converges to the product — over a nonarchimedean field this needs only that the
terms tend to zero, not absolute convergence). Together with `TateCurve.evalInt_add` this
makes `evalInt q` a ring homomorphism `ℤ⟦X⟧ → k` for each `|q| < 1`. -/
theorem TateCurve.evalInt_mul (q : k) (hq : valuation k q < 1) (F G : ℤ⟦X⟧) :
    evalInt q (F * G) = evalInt q F * evalInt q G := by
  have hf := summable_evalInt q hq F
  have hg := summable_evalInt q hq G
  -- summability of the doubly-indexed product series: as in `summable_evalInt`, but over
  -- `ℕ × ℕ`, where "the terms tend to zero cofinitely" is witnessed by the finiteness of
  -- the set of `(i, j)` with `i + j < N`
  have hfg : Summable fun x : ℕ × ℕ ↦
      (((PowerSeries.coeff x.1 F : ℤ) : k) * q ^ x.1) *
        (((PowerSeries.coeff x.2 G : ℤ) : k) * q ^ x.2) := by
    letI : UniformSpace k := IsTopologicalAddGroup.rightUniformSpace k
    haveI : IsUniformAddGroup k := isUniformAddGroup_of_addCommGroup
    haveI : NonarchimedeanRing k := by
      convert! ValuativeRel.nonarchimedeanRing k
      exact Valuation.toTopologicalSpace_eq _
    apply NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
    rw [(IsValuativeTopology.hasBasis_nhds (0 : k)).tendsto_right_iff]
    intro γ _
    obtain ⟨N, hN⟩ := exists_pow_valuation_lt q hq γ
    rw [Filter.eventually_cofinite]
    refine Set.Finite.subset ((Set.finite_Iio N).prod (Set.finite_Iio N)) fun x hx ↦ ?_
    simp only [Set.mem_setOf_eq, sub_zero] at hx
    -- the term at `(i, j)` has valuation `≤ |q|^(i+j)`
    have hbound : valuation k ((((PowerSeries.coeff x.1 F : ℤ) : k) * q ^ x.1) *
        (((PowerSeries.coeff x.2 G : ℤ) : k) * q ^ x.2)) ≤ valuation k q ^ (x.1 + x.2) :=
      calc valuation k ((((PowerSeries.coeff x.1 F : ℤ) : k) * q ^ x.1) *
            (((PowerSeries.coeff x.2 G : ℤ) : k) * q ^ x.2))
          = valuation k ((PowerSeries.coeff x.1 F : ℤ) : k) * valuation k q ^ x.1 *
              (valuation k ((PowerSeries.coeff x.2 G : ℤ) : k) * valuation k q ^ x.2) := by
            rw [map_mul, map_mul, map_mul, map_pow, map_pow]
        _ ≤ 1 * valuation k q ^ x.1 * (1 * valuation k q ^ x.2) :=
            mul_le_mul' (mul_le_mul_left (valuation_intCast_le_one _) _)
              (mul_le_mul_left (valuation_intCast_le_one _) _)
        _ = valuation k q ^ (x.1 + x.2) := by rw [one_mul, one_mul, pow_add]
    -- so a term of valuation `≥ γ` must have `i + j < N`
    have hlt : x.1 + x.2 < N := lt_of_not_ge fun hge ↦
      hx (lt_of_le_of_lt (hbound.trans (pow_le_pow_right_of_le_one' hq.le hge)) hN)
    exact Set.mem_prod.mpr ⟨Set.mem_Iio.mpr (lt_of_le_of_lt (Nat.le_add_right _ _) hlt),
      Set.mem_Iio.mpr (lt_of_le_of_lt (Nat.le_add_left _ _) hlt)⟩
  -- the antidiagonal regrouping of the double sum (in the ambient topology, which is T3
  -- since `k` is a Hausdorff topological additive group)
  simp only [evalInt]
  rw [hf.tsum_mul_tsum_eq_tsum_sum_antidiagonal hg hfg]
  -- identify the `n`-th antidiagonal sum with the `n`-th coefficient of `F * G`
  refine tsum_congr fun n ↦ ?_
  rw [PowerSeries.coeff_mul, Int.cast_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun kl hkl ↦ ?_
  rw [Finset.mem_antidiagonal] at hkl
  rw [Int.cast_mul, ← hkl, pow_add]
  ring

theorem TateCurve.evalInt_pow (q : k) (hq : valuation k q < 1) (F : ℤ⟦X⟧) (m : ℕ) :
    evalInt q (F ^ m) = evalInt q F ^ m := by
  induction m with
  | zero => simp
  | succ m ih => rw [pow_succ, pow_succ, evalInt_mul q hq, ih]

/-- Evaluation of integral power series is compatible with formal substitution: for
`|q| < 1` and `G` with zero constant term, `(F ∘ G)(q) = F(G(q))`. Together with
`evalInt_mul` this makes evaluation fully functorial; it is the bridge taking the formal
compositional identities of `TateCurve.jInvReverse` to the `j`/`q` round-trips of
Silverman, ATAEC V.5.2. The proof is a Fubini argument on the double series
`∑_{m,n} FₘGᵐₙqⁿ`: summing rows first gives `∑ₘ Fₘ·G(q)ᵐ = F(G(q))`, summing columns
first gives `∑ₙ (F∘G)ₙqⁿ` — the columns being *finite* sums, since `ord(Gᵐ) ≥ m`. -/
theorem TateCurve.evalInt_subst (q : k) (hq : valuation k q < 1) {G : ℤ⟦X⟧}
    (hG0 : PowerSeries.constantCoeff G = 0) (F : ℤ⟦X⟧) :
    evalInt q (PowerSeries.subst G F) = evalInt (evalInt q G) F := by
  -- low coefficients of powers vanish: `ord(Gᵐ) ≥ m`
  have hvanish : ∀ m n : ℕ, n < m → PowerSeries.coeff n (G ^ m) = (0 : ℤ) := by
    intro m n hnm
    obtain ⟨G', hG'⟩ := PowerSeries.X_dvd_iff.mpr hG0
    rw [hG', mul_pow, mul_comm ((PowerSeries.X : ℤ⟦X⟧) ^ m), PowerSeries.coeff_mul_X_pow',
      if_neg (by omega)]
  -- the double series is summable: the `(m, n)` term vanishes for `n < m` and is
  -- bounded by `|q|ⁿ` otherwise, so it is bounded by `|q|^(max m n)` throughout
  obtain ⟨S, hS⟩ : Summable fun p : ℕ × ℕ ↦ ((PowerSeries.coeff p.1 F : ℤ) : k) *
      (((PowerSeries.coeff p.2 (G ^ p.1) : ℤ) : k) * q ^ p.2) := by
    refine summable_of_valuation_le_pow hq (fun p ↦ max p.1 p.2) (fun N ↦ ?_) fun p ↦ ?_
    · refine ((Set.finite_Iio N).prod (Set.finite_Iio N)).subset fun p hp ↦ ?_
      exact Set.mem_prod.mpr ⟨Set.mem_Iio.mpr (lt_of_le_of_lt (le_max_left _ _) hp),
        Set.mem_Iio.mpr (lt_of_le_of_lt (le_max_right _ _) hp)⟩
    · rcases lt_or_ge p.2 p.1 with h | h
      · rw [hvanish p.1 p.2 h]
        simp
      · rw [map_mul (valuation k), map_mul (valuation k), map_pow (valuation k)]
        calc valuation k ((PowerSeries.coeff p.1 F : ℤ) : k) *
              (valuation k ((PowerSeries.coeff p.2 (G ^ p.1) : ℤ) : k) *
                valuation k q ^ p.2)
            ≤ 1 * (1 * valuation k q ^ p.2) :=
              mul_le_mul' (valuation_intCast_le_one _)
                (mul_le_mul_left (valuation_intCast_le_one _) _)
          _ = valuation k q ^ p.2 := by rw [one_mul, one_mul]
          _ = valuation k q ^ max p.1 p.2 := by rw [max_eq_right h]
  -- rows: summing over `n` first gives `Fₘ·G(q)ᵐ`
  have hrow : ∀ m : ℕ, HasSum (fun n : ℕ ↦ ((PowerSeries.coeff m F : ℤ) : k) *
      (((PowerSeries.coeff n (G ^ m) : ℤ) : k) * q ^ n))
      (((PowerSeries.coeff m F : ℤ) : k) * evalInt q (G ^ m)) := fun m ↦
    ((summable_evalInt q hq (G ^ m)).hasSum).mul_left _
  -- columns: summing over `m` first gives the coefficients of the composite,
  -- and these sums are finite since `ord(Gᵐ) ≥ m`
  have hcol : ∀ n : ℕ, HasSum (fun m : ℕ ↦ ((PowerSeries.coeff m F : ℤ) : k) *
      (((PowerSeries.coeff n (G ^ m) : ℤ) : k) * q ^ n))
      (((PowerSeries.coeff n (PowerSeries.subst G F) : ℤ) : k) * q ^ n) := by
    intro n
    have hcoeff : PowerSeries.coeff n (PowerSeries.subst G F) =
        ∑ m ∈ Finset.range (n + 1),
          PowerSeries.coeff m F * PowerSeries.coeff n (G ^ m) := by
      have hsupp : (Function.support fun d ↦
          PowerSeries.coeff d F • PowerSeries.coeff n (G ^ d)) ⊆
            ↑(Finset.range (n + 1)) := by
        intro m hm
        simp only [Function.mem_support] at hm
        simp only [Finset.coe_range, Set.mem_Iio]
        by_contra hc
        exact hm (by
          change PowerSeries.coeff m F • PowerSeries.coeff n (G ^ m) = 0
          rw [hvanish m n (by omega), smul_zero])
      rw [PowerSeries.coeff_subst' (PowerSeries.HasSubst.of_constantCoeff_zero' hG0),
        finsum_eq_finsetSum_of_support_subset _ hsupp]
      exact Finset.sum_congr rfl fun m _ ↦ smul_eq_mul _ _
    have hval : ((PowerSeries.coeff n (PowerSeries.subst G F) : ℤ) : k) * q ^ n =
        ∑ m ∈ Finset.range (n + 1), ((PowerSeries.coeff m F : ℤ) : k) *
          (((PowerSeries.coeff n (G ^ m) : ℤ) : k) * q ^ n) := by
      rw [hcoeff]
      push_cast
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun m _ ↦ by ring
    refine hval.symm ▸ hasSum_sum_of_ne_finset_zero fun m hm ↦ ?_
    rw [hvanish m n (by simp only [Finset.mem_range] at hm; omega)]
    simp
  -- assemble: both iterated sums equal the double sum
  have hLHS : HasSum (fun n : ℕ ↦
      ((PowerSeries.coeff n (PowerSeries.subst G F) : ℤ) : k) * q ^ n) S :=
    HasSum.prod_fiberwise ((Equiv.prodComm ℕ ℕ).hasSum_iff.mpr hS) hcol
  have hRHS : HasSum (fun m : ℕ ↦
      ((PowerSeries.coeff m F : ℤ) : k) * evalInt q G ^ m) S := by
    have h := hS.prod_fiberwise hrow
    simpa only [evalInt_pow q hq] using h
  rw [show evalInt q (PowerSeries.subst G F) = S from hLHS.tsum_eq,
    show evalInt (evalInt q G) F = S from hRHS.tsum_eq]

/-- Powers of an element of the open unit disc tend to zero. -/
theorem TateCurve.tendsto_pow_nhds_zero {x : k} (hx : valuation k x < 1) :
    Filter.Tendsto (fun n : ℕ ↦ x ^ n) Filter.atTop (𝓝 0) := by
  rw [(IsValuativeTopology.hasBasis_nhds (0 : k)).tendsto_right_iff]
  intro γ _
  obtain ⟨N, hN⟩ := exists_pow_valuation_lt x hx γ
  filter_upwards [Filter.eventually_ge_atTop N] with n hn
  simp only [sub_zero, map_pow]
  exact lt_of_le_of_lt (pow_le_pow_right_of_le_one' hx.le hn) hN

/-- The geometric series over a nonarchimedean local field: for `|x| < 1`,
`x + x² + x³ + ⋯ = x/(1 - x)`. (Summability is by the nonarchimedean criterion — the
terms tend to zero — and the value is identified through the partial sums
`x(xⁿ - 1)/(x - 1)`.) -/
theorem TateCurve.hasSum_geometric_succ {x : k} (hx : valuation k x < 1) :
    HasSum (fun j : ℕ ↦ x ^ (j + 1)) (x / (1 - x)) := by
  have hx1 : x ≠ 1 := by
    rintro rfl
    simp at hx
  have hx1' : x - 1 ≠ 0 := sub_ne_zero.mpr hx1
  have h1x : (1 : k) - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hx1)
  obtain ⟨S, hS⟩ : Summable fun j : ℕ ↦ x ^ (j + 1) :=
    summable_of_valuation_le_pow hx (fun j ↦ j + 1)
      (fun N ↦ (Set.finite_Iio N).subset fun j hj ↦ Set.mem_Iio.mpr (Nat.lt_of_succ_lt hj))
      fun j ↦ le_of_eq (map_pow _ _ _)
  suffices hlim : Filter.Tendsto (fun n : ℕ ↦ ∑ j ∈ Finset.range n, x ^ (j + 1))
      Filter.atTop (𝓝 (x / (1 - x))) from
    tendsto_nhds_unique hS.tendsto_sum_nat hlim ▸ hS
  have hps : ∀ n : ℕ, ∑ j ∈ Finset.range n, x ^ (j + 1) = x * ((x ^ n - 1) / (x - 1)) := by
    intro n
    rw [← geom_sum_eq hx1 n, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ ↦ by ring
  simp only [hps]
  have h := (((tendsto_pow_nhds_zero hx).sub_const 1).div_const (x - 1)).const_mul x
  convert h using 2
  rw [zero_sub]
  field_simp
  ring

/-- The derived geometric series over a nonarchimedean local field: for `|x| < 1`,
`∑_{j≥1} j·xʲ = x/(1-x)²`. Obtained as the Cauchy product of the geometric series with
itself: the `N`-th antidiagonal has `N + 1` terms, all equal to `x^(N+1)`. -/
theorem TateCurve.hasSum_geometric_deriv {x : k} (hx : valuation k x < 1) :
    HasSum (fun j : ℕ ↦ ((j + 1 : ℕ) : k) * x ^ (j + 1)) (x / (1 - x) ^ 2) := by
  have hx1 : x ≠ 1 := by
    rintro rfl
    simp at hx
  have h1x : (1 : k) - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hx1)
  have hgeo₁ := hasSum_geometric_succ hx
  have hgeo₀ : HasSum (fun j : ℕ ↦ x ^ j) (x / (1 - x) + 1) := by
    simpa using (hasSum_nat_add_iff (f := fun j : ℕ ↦ x ^ j) 1).mp hgeo₁
  have hdouble : Summable fun p : ℕ × ℕ ↦ x ^ (p.1 + 1) * x ^ p.2 := by
    refine summable_of_valuation_le_pow hx (fun p ↦ p.1 + p.2) (fun N ↦ ?_) fun p ↦ ?_
    · exact ((Set.finite_Iio N).prod (Set.finite_Iio N)).subset fun p hp ↦
        Set.mem_prod.mpr ⟨Set.mem_Iio.mpr (lt_of_le_of_lt (Nat.le_add_right _ _) hp),
          Set.mem_Iio.mpr (lt_of_le_of_lt (Nat.le_add_left _ _) hp)⟩
    · rw [← pow_add, map_pow]
      exact pow_le_pow_right_of_le_one' hx.le (by omega)
  have key := hgeo₁.summable.tsum_mul_tsum_eq_tsum_sum_antidiagonal hgeo₀.summable hdouble
  rw [hgeo₁.tsum_eq, hgeo₀.tsum_eq] at key
  have hsummable : Summable fun j : ℕ ↦ ((j + 1 : ℕ) : k) * x ^ (j + 1) := by
    refine summable_of_valuation_le_pow hx (fun j ↦ j) (fun N ↦ Set.finite_Iio N) fun j ↦ ?_
    rw [map_mul, map_pow, show (((j + 1 : ℕ)) : k) = (((j + 1 : ℕ) : ℤ) : k) by push_cast; ring]
    calc valuation k (((j + 1 : ℕ) : ℤ) : k) * valuation k x ^ (j + 1)
        ≤ 1 * valuation k x ^ (j + 1) := mul_le_mul_left (valuation_intCast_le_one _) _
      _ = valuation k x ^ (j + 1) := one_mul _
      _ ≤ valuation k x ^ j := pow_le_pow_right_of_le_one' hx.le (Nat.le_succ j)
  have hinner : ∀ N : ℕ, (∑ kl ∈ Finset.antidiagonal N, x ^ (kl.1 + 1) * x ^ kl.2)
      = ((N + 1 : ℕ) : k) * x ^ (N + 1) := fun N ↦ by
    have h1 : ∀ kl ∈ Finset.antidiagonal N, x ^ (kl.1 + 1) * x ^ kl.2 = x ^ (N + 1) := by
      intro kl hkl
      rw [Finset.mem_antidiagonal] at hkl
      rw [← pow_add]
      congr 1
      omega
    rw [Finset.sum_congr rfl h1, Finset.sum_const, Finset.Nat.card_antidiagonal, nsmul_eq_mul]
  refine hsummable.hasSum_iff.mpr ?_
  calc ∑' j : ℕ, ((j + 1 : ℕ) : k) * x ^ (j + 1)
      = ∑' N : ℕ, ∑ kl ∈ Finset.antidiagonal N, x ^ (kl.1 + 1) * x ^ kl.2 :=
        tsum_congr fun N ↦ (hinner N).symm
    _ = x / (1 - x) * (x / (1 - x) + 1) := key.symm
    _ = x / (1 - x) ^ 2 := by
        field_simp
        ring

private theorem TateCurve.sum_range_succ_choose_two (n : ℕ) :
    ∑ i ∈ Finset.range (n + 1), (i + 1) = (n + 2).choose 2 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      have h := Nat.choose_succ_succ (n + 2) 1
      simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Nat.choose_one_right] at h
      rw [show n + 1 + 2 = n + 2 + 1 from by omega]
      omega

/-- The twice-derived geometric series `∑_{d≥1} (d+1 choose 2)·xᵈ = x/(1-x)³`: the Cauchy
product of `hasSum_geometric_deriv` with the geometric series. These are the coefficients
of the `u⁻ᵈ`-half of the `y`-coordinate of Tate's uniformisation. -/
theorem TateCurve.hasSum_geometric_div_cube {x : k} (hx : valuation k x < 1) :
    HasSum (fun j : ℕ ↦ (((j + 2).choose 2 : ℕ) : k) * x ^ (j + 1)) (x / (1 - x) ^ 3) := by
  have hx1 : x ≠ 1 := by
    rintro rfl
    simp at hx
  have h1x : (1 : k) - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hx1)
  have hderiv := hasSum_geometric_deriv hx
  have hgeo₀ : HasSum (fun j : ℕ ↦ x ^ j) (x / (1 - x) + 1) := by
    simpa using (hasSum_nat_add_iff (f := fun j : ℕ ↦ x ^ j) 1).mp (hasSum_geometric_succ hx)
  have hdouble : Summable fun p : ℕ × ℕ ↦ ((p.1 + 1 : ℕ) : k) * x ^ (p.1 + 1) * x ^ p.2 := by
    refine summable_of_valuation_le_pow hx (fun p ↦ p.1 + p.2) (fun N ↦ ?_) fun p ↦ ?_
    · exact ((Set.finite_Iio N).prod (Set.finite_Iio N)).subset fun p hp ↦
        Set.mem_prod.mpr ⟨Set.mem_Iio.mpr (lt_of_le_of_lt (Nat.le_add_right _ _) hp),
          Set.mem_Iio.mpr (lt_of_le_of_lt (Nat.le_add_left _ _) hp)⟩
    · rw [map_mul, map_mul, map_pow, map_pow]
      calc valuation k ((p.1 + 1 : ℕ) : k) * valuation k x ^ (p.1 + 1) * valuation k x ^ p.2
          ≤ 1 * valuation k x ^ (p.1 + 1) * valuation k x ^ p.2 :=
            mul_le_mul_left (mul_le_mul_left (valuation_natCast_le_one _) _) _
        _ = valuation k x ^ (p.1 + 1 + p.2) := by rw [one_mul, ← pow_add]
        _ ≤ valuation k x ^ (p.1 + p.2) :=
            pow_le_pow_right_of_le_one' hx.le (by omega)
  have key := hderiv.summable.tsum_mul_tsum_eq_tsum_sum_antidiagonal hgeo₀.summable hdouble
  rw [hderiv.tsum_eq, hgeo₀.tsum_eq] at key
  have hinner : ∀ N : ℕ,
      (∑ kl ∈ Finset.antidiagonal N, ((kl.1 + 1 : ℕ) : k) * x ^ (kl.1 + 1) * x ^ kl.2)
      = (((N + 2).choose 2 : ℕ) : k) * x ^ (N + 1) := fun N ↦ by
    have h1 : ∀ kl ∈ Finset.antidiagonal N, ((kl.1 + 1 : ℕ) : k) * x ^ (kl.1 + 1) * x ^ kl.2
        = ((kl.1 + 1 : ℕ) : k) * x ^ (N + 1) := by
      intro kl hkl
      rw [Finset.mem_antidiagonal] at hkl
      rw [mul_assoc, ← pow_add]
      congr 2
      omega
    rw [Finset.sum_congr rfl h1, ← Finset.sum_mul, ← Nat.cast_sum,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, sum_range_succ_choose_two]
  have hsummable : Summable fun j : ℕ ↦ (((j + 2).choose 2 : ℕ) : k) * x ^ (j + 1) := by
    refine summable_of_valuation_le_pow hx (fun j ↦ j) (fun N ↦ Set.finite_Iio N) fun j ↦ ?_
    rw [map_mul, map_pow]
    calc valuation k (((j + 2).choose 2 : ℕ) : k) * valuation k x ^ (j + 1)
        ≤ 1 * valuation k x ^ (j + 1) := mul_le_mul_left (valuation_natCast_le_one _) _
      _ = valuation k x ^ (j + 1) := one_mul _
      _ ≤ valuation k x ^ j := pow_le_pow_right_of_le_one' hx.le (Nat.le_succ j)
  refine hsummable.hasSum_iff.mpr ?_
  calc ∑' j : ℕ, (((j + 2).choose 2 : ℕ) : k) * x ^ (j + 1)
      = ∑' N : ℕ, ∑ kl ∈ Finset.antidiagonal N, ((kl.1 + 1 : ℕ) : k) * x ^ (kl.1 + 1) * x ^ kl.2 :=
        tsum_congr fun N ↦ (hinner N).symm
    _ = x / (1 - x) ^ 2 * (x / (1 - x) + 1) := key.symm
    _ = x / (1 - x) ^ 3 := by
        field_simp
        ring

/-- The series `∑_{d≥1} (d choose 2)·xᵈ = x²/(1-x)³`: the Cauchy product of the geometric
series with `hasSum_geometric_deriv`. These are the coefficients of the `uᵈ`-half of the
`y`-coordinate of Tate's uniformisation. -/
theorem TateCurve.hasSum_geometric_sq_div_cube {x : k} (hx : valuation k x < 1) :
    HasSum (fun j : ℕ ↦ (((j + 1).choose 2 : ℕ) : k) * x ^ (j + 1)) (x ^ 2 / (1 - x) ^ 3) := by
  have hx1 : x ≠ 1 := by
    rintro rfl
    simp at hx
  have h1x : (1 : k) - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hx1)
  have hgeo₁ := hasSum_geometric_succ hx
  have hderiv := hasSum_geometric_deriv hx
  have hdouble : Summable fun p : ℕ × ℕ ↦
      x ^ (p.1 + 1) * (((p.2 + 1 : ℕ) : k) * x ^ (p.2 + 1)) := by
    refine summable_of_valuation_le_pow hx (fun p ↦ p.1 + p.2) (fun N ↦ ?_) fun p ↦ ?_
    · exact ((Set.finite_Iio N).prod (Set.finite_Iio N)).subset fun p hp ↦
        Set.mem_prod.mpr ⟨Set.mem_Iio.mpr (lt_of_le_of_lt (Nat.le_add_right _ _) hp),
          Set.mem_Iio.mpr (lt_of_le_of_lt (Nat.le_add_left _ _) hp)⟩
    · rw [map_mul, map_mul, map_pow, map_pow]
      calc valuation k x ^ (p.1 + 1) * (valuation k ((p.2 + 1 : ℕ) : k) *
            valuation k x ^ (p.2 + 1))
          ≤ valuation k x ^ (p.1 + 1) * (1 * valuation k x ^ (p.2 + 1)) :=
            mul_le_mul' le_rfl (mul_le_mul_left (valuation_natCast_le_one _) _)
        _ = valuation k x ^ (p.1 + 1 + (p.2 + 1)) := by rw [one_mul, ← pow_add]
        _ ≤ valuation k x ^ (p.1 + p.2) :=
            pow_le_pow_right_of_le_one' hx.le (by omega)
  have key := hgeo₁.summable.tsum_mul_tsum_eq_tsum_sum_antidiagonal hderiv.summable hdouble
  rw [hgeo₁.tsum_eq, hderiv.tsum_eq] at key
  have hinner : ∀ N : ℕ,
      (∑ kl ∈ Finset.antidiagonal N, x ^ (kl.1 + 1) * (((kl.2 + 1 : ℕ) : k) * x ^ (kl.2 + 1)))
      = (((N + 2).choose 2 : ℕ) : k) * x ^ (N + 2) := fun N ↦ by
    have h1 : ∀ kl ∈ Finset.antidiagonal N,
        x ^ (kl.1 + 1) * (((kl.2 + 1 : ℕ) : k) * x ^ (kl.2 + 1))
        = ((kl.2 + 1 : ℕ) : k) * x ^ (N + 2) := by
      intro kl hkl
      rw [Finset.mem_antidiagonal] at hkl
      rw [mul_left_comm, ← pow_add]
      congr 2
      omega
    rw [Finset.sum_congr rfl h1, ← Finset.sum_mul, ← Nat.cast_sum,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    congr 2
    calc ∑ i ∈ Finset.range (N + 1), (N - i + 1)
        = ∑ i ∈ Finset.range (N + 1), (i + 1) := Finset.sum_range_reflect (fun j ↦ j + 1) (N + 1)
      _ = (N + 2).choose 2 := sum_range_succ_choose_two N
  have h2 : HasSum (fun N : ℕ ↦ (((N + 2).choose 2 : ℕ) : k) * x ^ (N + 2))
      (x / (1 - x) * (x / (1 - x) ^ 2)) := by
    have hsummable : Summable fun N : ℕ ↦ (((N + 2).choose 2 : ℕ) : k) * x ^ (N + 2) := by
      refine summable_of_valuation_le_pow hx (fun j ↦ j) (fun N ↦ Set.finite_Iio N) fun j ↦ ?_
      rw [map_mul, map_pow]
      calc valuation k (((j + 2).choose 2 : ℕ) : k) * valuation k x ^ (j + 2)
          ≤ 1 * valuation k x ^ (j + 2) := mul_le_mul_left (valuation_natCast_le_one _) _
        _ = valuation k x ^ (j + 2) := one_mul _
        _ ≤ valuation k x ^ j := pow_le_pow_right_of_le_one' hx.le (by omega)
    refine hsummable.hasSum_iff.mpr ?_
    calc ∑' N : ℕ, (((N + 2).choose 2 : ℕ) : k) * x ^ (N + 2)
        = ∑' N : ℕ, ∑ kl ∈ Finset.antidiagonal N,
            x ^ (kl.1 + 1) * (((kl.2 + 1 : ℕ) : k) * x ^ (kl.2 + 1)) :=
          tsum_congr fun N ↦ (hinner N).symm
      _ = x / (1 - x) * (x / (1 - x) ^ 2) := key.symm
  have h3 := (hasSum_nat_add_iff
    (f := fun j : ℕ ↦ (((j + 1).choose 2 : ℕ) : k) * x ^ (j + 1)) 1).mp h2
  have hval : x / (1 - x) * (x / (1 - x) ^ 2) +
      ∑ i ∈ Finset.range 1, (((i + 1).choose 2 : ℕ) : k) * x ^ (i + 1) = x ^ 2 / (1 - x) ^ 3 := by
    rw [Finset.sum_range_one, show Nat.choose 1 2 = 0 from rfl, Nat.cast_zero, zero_mul,
      add_zero, div_mul_div_comm, show x * x = x ^ 2 by ring,
      show (1 - x) * (1 - x) ^ 2 = (1 - x) ^ 3 by ring]
  rwa [hval] at h3

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
/-- The inversion symmetry of the summands of `tateX`: `v/(1-v)² = v⁻¹/(1-v⁻¹)²`. This is
what makes the two-sided sum `∑_{n ∈ ℤ}` symmetric under `(u, n) ↦ (u⁻¹, -n)`, and it
converts the `n ≤ -1` half of the sum into geometric series in `q^{-n}u⁻¹`. -/
theorem TateCurve.div_one_sub_sq_inv {v : k} (hv : v ≠ 0) :
    v / (1 - v) ^ 2 = v⁻¹ / (1 - v⁻¹) ^ 2 := by
  rcases eq_or_ne v 1 with rfl | hv1
  · simp
  · have h1 : (1 : k) - v ≠ 0 := sub_ne_zero.mpr (Ne.symm hv1)
    have h2 : (1 : k) - v⁻¹ ≠ 0 := by
      rw [sub_ne_zero]
      exact fun h ↦ hv1 (by rw [← inv_inv v, ← h, inv_one])
    field_simp
    ring

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
/-- The inversion antisymmetry of the summands of `tateY`:
`v²/(1-v)³ = -(v⁻¹/(1-v⁻¹)³)`. It converts the `n ≤ -1` half of the `y`-coordinate sum
into (negated) geometric series in `q^{-n}u⁻¹`, and is the source of the asymmetric
coefficients `(d choose 2)uᵈ - (d+1 choose 2)u⁻ᵈ` in Silverman's `q`-expansion. -/
theorem TateCurve.sq_div_one_sub_cube_inv {v : k} (hv : v ≠ 0) :
    v ^ 2 / (1 - v) ^ 3 = -(v⁻¹ / (1 - v⁻¹) ^ 3) := by
  rcases eq_or_ne v 1 with rfl | hv1
  · simp
  · have h1 : (1 : k) - v ≠ 0 := sub_ne_zero.mpr (Ne.symm hv1)
    have h2 : (1 : k) - v⁻¹ ≠ 0 := by
      rw [sub_ne_zero]
      exact fun h ↦ hv1 (by rw [← inv_inv v, ← h, inv_one])
    field_simp
    ring

/-- The Lambert series rearrangement over a nonarchimedean local field: for any integer
coefficients `c` and `|q| < 1`,
`∑_{m≥1} c(m)qᵐ/(1 - qᵐ) = ∑_{N≥1} (∑_{d ∣ N} c(d))qᴺ`.
Each `qᵐ/(1-qᵐ)` expands as the geometric series `∑_{j≥1} q^{mj}`, and the resulting
double series — summable since its terms tend to zero nonarchimedeanly — is regrouped
along the fibres of `(m, j) ↦ mj`, which are exactly the divisor pairs of `N`. -/
theorem TateCurve.tsum_lambert (q : k) (hq : valuation k q < 1) (c : ℕ → ℤ) :
    ∑' m : ℕ, ((c (m + 1) : ℤ) : k) * q ^ (m + 1) / (1 - q ^ (m + 1)) =
      ∑' N : ℕ, ((∑ d ∈ N.divisors, c d : ℤ) : k) * q ^ N := by
  -- powers of `q` stay in the open unit disc
  have hqpow : ∀ n : ℕ+, valuation k (q ^ (n : ℕ)) < 1 := fun n ↦ by
    rw [map_pow]
    calc valuation k q ^ (n : ℕ) ≤ valuation k q ^ 1 :=
          pow_le_pow_right_of_le_one' hq.le n.pos
      _ = valuation k q := pow_one _
      _ < 1 := hq
  -- each row of the double series is a geometric series
  have hgeo : ∀ n : ℕ+, HasSum (fun j : ℕ ↦ ((c n : ℤ) : k) * q ^ ((n : ℕ) * (j + 1)))
      (((c n : ℤ) : k) * q ^ (n : ℕ) / (1 - q ^ (n : ℕ))) := fun n ↦ by
    have h := (hasSum_geometric_succ (hqpow n)).mul_left ((c n : ℤ) : k)
    rw [mul_div_assoc]
    simpa only [← pow_mul] using h
  -- the double series is summable, its terms tending to zero nonarchimedeanly
  obtain ⟨S, hS⟩ : Summable fun p : ℕ+ × ℕ+ ↦ ((c p.1 : ℤ) : k) * q ^ ((p.1 : ℕ) * (p.2 : ℕ)) := by
    refine summable_of_valuation_le_pow hq (fun p ↦ (p.1 : ℕ) * (p.2 : ℕ)) (fun N ↦ ?_) fun p ↦ ?_
    · refine (((Set.finite_Iio N).preimage PNat.coe_injective.injOn).prod
        ((Set.finite_Iio N).preimage PNat.coe_injective.injOn)).subset fun p hp ↦ ?_
      have h1 : (p.1 : ℕ) ≤ (p.1 : ℕ) * (p.2 : ℕ) := Nat.le_mul_of_pos_right _ p.2.pos
      have h2 : (p.2 : ℕ) ≤ (p.1 : ℕ) * (p.2 : ℕ) := Nat.le_mul_of_pos_left _ p.1.pos
      exact Set.mem_prod.mpr ⟨Set.mem_preimage.mpr (Set.mem_Iio.mpr (lt_of_le_of_lt h1 hp)),
        Set.mem_preimage.mpr (Set.mem_Iio.mpr (lt_of_le_of_lt h2 hp))⟩
    · rw [map_mul, map_pow]
      simpa using mul_le_mul_left (valuation_intCast_le_one _)
        (valuation k q ^ ((p.1 : ℕ) * (p.2 : ℕ)))
  -- summing the rows first gives the left-hand side
  have hrows : HasSum (fun n : ℕ+ ↦ ((c n : ℤ) : k) * q ^ (n : ℕ) / (1 - q ^ (n : ℕ))) S :=
    hS.prod_fiberwise fun n ↦ Equiv.pnatEquivNat.symm.hasSum_iff.mp (hgeo n)
  -- summing along the fibres of `(m, j) ↦ mj` gives the right-hand side
  have hsigma : HasSum ((fun p : ℕ+ × ℕ+ ↦ ((c p.1 : ℤ) : k) * q ^ ((p.1 : ℕ) * (p.2 : ℕ))) ∘
      ⇑sigmaAntidiagonalEquivProd) S :=
    sigmaAntidiagonalEquivProd.hasSum_iff.mpr hS
  have hfib : ∀ N : ℕ+, HasSum (fun x : (Nat.divisorsAntidiagonal (N : ℕ)) ↦
      ((fun p : ℕ+ × ℕ+ ↦ ((c p.1 : ℤ) : k) * q ^ ((p.1 : ℕ) * (p.2 : ℕ))) ∘
        ⇑sigmaAntidiagonalEquivProd) ⟨N, x⟩)
      (((∑ d ∈ (N : ℕ).divisors, c d : ℤ) : k) * q ^ (N : ℕ)) := by
    intro N
    have hterm : ∀ x : (Nat.divisorsAntidiagonal (N : ℕ)),
        ((fun p : ℕ+ × ℕ+ ↦ ((c p.1 : ℤ) : k) * q ^ ((p.1 : ℕ) * (p.2 : ℕ))) ∘
          ⇑sigmaAntidiagonalEquivProd) ⟨N, x⟩ = ((c (x : ℕ × ℕ).1 : ℤ) : k) * q ^ (N : ℕ) := by
      intro x
      have hx := (Nat.mem_divisorsAntidiagonal.mp x.2).1
      simp only [Function.comp_apply, sigmaAntidiagonalEquivProd, Equiv.coe_fn_mk,
        divisorsAntidiagonalFactors, PNat.mk_coe]
      rw [hx]
    convert hasSum_fintype _ using 1
    · symm
      rw [Finset.univ_eq_attach, Finset.sum_congr rfl fun x _ ↦ hterm x,
        Finset.sum_attach (Nat.divisorsAntidiagonal (N : ℕ))
          (fun y ↦ ((c y.1 : ℤ) : k) * q ^ (N : ℕ)),
        ← Finset.sum_mul, Nat.sum_divisorsAntidiagonal (fun d _ ↦ ((c d : ℤ) : k)),
        ← Int.cast_sum]
  have hcolsPNat : HasSum
      (fun N : ℕ+ ↦ ((∑ d ∈ (N : ℕ).divisors, c d : ℤ) : k) * q ^ (N : ℕ)) S :=
    hsigma.sigma hfib
  have hcols : HasSum (fun N : ℕ ↦ ((∑ d ∈ N.divisors, c d : ℤ) : k) * q ^ N) S := by
    refine (PNat.coe_injective.hasSum_iff fun x hx ↦ ?_).mp hcolsPNat
    cases x with
    | zero => simp
    | succ n => exact absurd ⟨n.succPNat, rfl⟩ hx
  rw [← tsum_pnat_eq_tsum_succ (f := fun n ↦ ((c n : ℤ) : k) * q ^ n / (1 - q ^ n)),
    hrows.tsum_eq, hcols.tsum_eq]

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
/-- The sublevel sets of `(d, e) ↦ de` on `ℕ+ × ℕ+` are finite. -/
theorem TateCurve.finite_pnat_mul_lt (N : ℕ) :
    {p : ℕ+ × ℕ+ | (p.1 : ℕ) * (p.2 : ℕ) < N}.Finite := by
  refine (((Set.finite_Iio N).preimage PNat.coe_injective.injOn).prod
    ((Set.finite_Iio N).preimage PNat.coe_injective.injOn)).subset fun p hp ↦ ?_
  have h1 : (p.1 : ℕ) ≤ (p.1 : ℕ) * (p.2 : ℕ) := Nat.le_mul_of_pos_right _ p.2.pos
  have h2 : (p.2 : ℕ) ≤ (p.1 : ℕ) * (p.2 : ℕ) := Nat.le_mul_of_pos_left _ p.1.pos
  exact Set.mem_prod.mpr ⟨Set.mem_preimage.mpr (Set.mem_Iio.mpr (lt_of_le_of_lt h1 hp)),
    Set.mem_preimage.mpr (Set.mem_Iio.mpr (lt_of_le_of_lt h2 hp))⟩

/-- Regrouping a double power series along `(d, e) ↦ de`: the `k`-coefficient core of the
Lambert rearrangement (`tsum_lambert` is the `ℤ`-coefficient case, composed with the
geometric expansion of `qᵈ/(1-qᵈ)`). Summability of the double family is a hypothesis, to
accommodate the annulus weights `d·u^{-d}`, whose natural bound is by powers of `q·u⁻¹`
rather than `q`. -/
theorem TateCurve.hasSum_sum_divisors_mul_pow (x : k) (w : ℕ → k)
    (hsum : Summable fun p : ℕ+ × ℕ+ ↦ w (p.1 : ℕ) * x ^ ((p.1 : ℕ) * (p.2 : ℕ))) :
    HasSum (fun N : ℕ ↦ (∑ d ∈ N.divisors, w d) * x ^ N)
      (∑' p : ℕ+ × ℕ+, w (p.1 : ℕ) * x ^ ((p.1 : ℕ) * (p.2 : ℕ))) := by
  obtain ⟨S, hS⟩ := hsum
  have hsigma : HasSum ((fun p : ℕ+ × ℕ+ ↦ w (p.1 : ℕ) * x ^ ((p.1 : ℕ) * (p.2 : ℕ))) ∘
      ⇑sigmaAntidiagonalEquivProd) S :=
    sigmaAntidiagonalEquivProd.hasSum_iff.mpr hS
  have hfib : ∀ N : ℕ+, HasSum (fun y : (Nat.divisorsAntidiagonal (N : ℕ)) ↦
      ((fun p : ℕ+ × ℕ+ ↦ w (p.1 : ℕ) * x ^ ((p.1 : ℕ) * (p.2 : ℕ))) ∘
        ⇑sigmaAntidiagonalEquivProd) ⟨N, y⟩)
      ((∑ d ∈ (N : ℕ).divisors, w d) * x ^ (N : ℕ)) := by
    intro N
    have hterm : ∀ y : (Nat.divisorsAntidiagonal (N : ℕ)),
        ((fun p : ℕ+ × ℕ+ ↦ w (p.1 : ℕ) * x ^ ((p.1 : ℕ) * (p.2 : ℕ))) ∘
          ⇑sigmaAntidiagonalEquivProd) ⟨N, y⟩ = w (y : ℕ × ℕ).1 * x ^ (N : ℕ) := by
      intro y
      have hy := (Nat.mem_divisorsAntidiagonal.mp y.2).1
      simp only [Function.comp_apply, sigmaAntidiagonalEquivProd, Equiv.coe_fn_mk,
        divisorsAntidiagonalFactors, PNat.mk_coe]
      rw [hy]
    convert hasSum_fintype _ using 1
    · symm
      rw [Finset.univ_eq_attach, Finset.sum_congr rfl fun y _ ↦ hterm y,
        Finset.sum_attach (Nat.divisorsAntidiagonal (N : ℕ)) (fun y ↦ w y.1 * x ^ (N : ℕ)),
        ← Finset.sum_mul, Nat.sum_divisorsAntidiagonal (fun d _ ↦ w d)]
  have hcolsPNat : HasSum (fun N : ℕ+ ↦ (∑ d ∈ (N : ℕ).divisors, w d) * x ^ (N : ℕ)) S :=
    hsigma.sigma hfib
  have hcols : HasSum (fun N : ℕ ↦ (∑ d ∈ N.divisors, w d) * x ^ N) S := by
    refine (PNat.coe_injective.hasSum_iff fun n hn ↦ ?_).mp hcolsPNat
    cases n with
    | zero => simp
    | succ n => exact absurd ⟨n.succPNat, rfl⟩ hn
  rwa [hS.tsum_eq]

/-- Workhorse for the annulus expansions: if `g` has the geometric-type expansion
`g x = ∑_{d ≥ 1} a(d)·xᵈ` on the open unit disc, then the row sums `∑_n g(qⁿ⁺¹t)`
regroup along `(d, e) ↦ de` into a `q`-power series with divisor-sum coefficients
`∑_{d ∣ N} a(d)·tᵈ`. Both `HasSum`s are returned with a common (junk-free) value.
Summability of the double family is a hypothesis, to accommodate both `t = u` (bounded
by powers of `q`) and `t = u⁻¹` (bounded by powers of `q·u⁻¹`). -/
theorem TateCurve.hasSum_geom_rows (q t : k) (a : ℕ → ℕ) (g : k → k)
    (hgeo : ∀ x : k, valuation k x < 1 →
      HasSum (fun j : ℕ ↦ ((a (j + 1) : ℕ) : k) * x ^ (j + 1)) (g x))
    (hlt : ∀ n : ℕ, valuation k (q ^ (n + 1) * t) < 1)
    (hsum : Summable fun p : ℕ+ × ℕ+ ↦
      ((a (p.1 : ℕ) : ℕ) : k) * t ^ (p.1 : ℕ) * q ^ ((p.1 : ℕ) * (p.2 : ℕ))) :
    ∃ T : k, HasSum (fun n : ℕ ↦ g (q ^ (n + 1) * t)) T ∧
      HasSum (fun N : ℕ ↦ (∑ d ∈ N.divisors, ((a d : ℕ) : k) * t ^ d) * q ^ N) T := by
  have hdouble : Summable fun p : ℕ × ℕ ↦
      ((a (p.2 + 1) : ℕ) : k) * (q ^ (p.1 + 1) * t) ^ (p.2 + 1) := by
    have he := ((Equiv.prodComm ℕ ℕ).trans
      (Equiv.prodCongr Equiv.pnatEquivNat.symm Equiv.pnatEquivNat.symm)).summable_iff.mpr hsum
    refine he.congr fun p ↦ ?_
    change ((a (p.2 + 1) : ℕ) : k) * t ^ (p.2 + 1) * q ^ ((p.2 + 1) * (p.1 + 1)) = _
    rw [mul_pow, ← pow_mul]
    ring
  have hrows : HasSum (fun n : ℕ ↦ g (q ^ (n + 1) * t)) (∑' p : ℕ × ℕ,
      ((a (p.2 + 1) : ℕ) : k) * (q ^ (p.1 + 1) * t) ^ (p.2 + 1)) :=
    hdouble.hasSum.prod_fiberwise fun n ↦ hgeo _ (hlt n)
  have hreg : HasSum (fun N : ℕ ↦ (∑ d ∈ N.divisors, ((a d : ℕ) : k) * t ^ d) * q ^ N)
      (∑' p : ℕ+ × ℕ+, ((a (p.1 : ℕ) : ℕ) : k) * t ^ (p.1 : ℕ) * q ^ ((p.1 : ℕ) * (p.2 : ℕ))) :=
    hasSum_sum_divisors_mul_pow q (fun d ↦ ((a d : ℕ) : k) * t ^ d) hsum
  refine ⟨_, hrows, ?_⟩
  convert hreg using 1
  rw [← ((Equiv.prodComm ℕ ℕ).trans (Equiv.prodCongr Equiv.pnatEquivNat.symm
    Equiv.pnatEquivNat.symm)).tsum_eq (fun p : ℕ+ × ℕ+ ↦
      ((a (p.1 : ℕ) : ℕ) : k) * t ^ (p.1 : ℕ) * q ^ ((p.1 : ℕ) * (p.2 : ℕ)))]
  refine tsum_congr fun p ↦ ?_
  change ((a (p.2 + 1) : ℕ) : k) * (q ^ (p.1 + 1) * t) ^ (p.2 + 1) =
    ((a (p.2 + 1) : ℕ) : k) * t ^ (p.2 + 1) * q ^ ((p.2 + 1) * (p.1 + 1))
  rw [mul_pow, ← pow_mul]
  ring

open scoped ArithmeticFunction.sigma in
/-- The Lambert series rearrangement `∑_{n≥1} n³qⁿ/(1-qⁿ) = ∑_{n≥1} σ₃(n)qⁿ` for
`|q| < 1`: the defining series of `tateA₄` is the evaluation of the formal series
`a₄(q) = -5s₃(q) ∈ ℤ⟦q⟧`. -/
theorem WeierstrassCurve.tateA₄_eq_evalInt (q : k) (hq : valuation k q < 1) :
    tateA₄ q = TateCurve.evalInt q TateCurve.a₄Formal := by
  set c : ℕ → ℤ := fun d ↦ (d : ℤ) ^ 3 with hc
  have h := TateCurve.tsum_lambert q hq c
  have h1 : tateA₄ q = -5 * ∑' m : ℕ, ((c (m + 1) : ℤ) : k) *
      q ^ (m + 1) / (1 - q ^ (m + 1)) := by
    simp only [tateA₄]
    congr 1
    refine tsum_congr fun m ↦ ?_
    simp only [hc]
    push_cast
    ring
  have h2 : TateCurve.evalInt q TateCurve.a₄Formal =
      -5 * ∑' N : ℕ, ((∑ d ∈ N.divisors, c d : ℤ) : k) * q ^ N := by
    simp only [TateCurve.evalInt, TateCurve.coeff_a₄Formal]
    rw [← tsum_mul_left]
    refine tsum_congr fun N ↦ ?_
    simp only [hc]
    rw [ArithmeticFunction.sigma_apply]
    push_cast
    ring
  rw [h1, h2, h]

open scoped ArithmeticFunction.sigma in
/-- The Lambert series rearrangement for `tateA₆`, as for `tateA₄_eq_evalInt`; the
bookkeeping of the exact division by `12` uses `12 ∣ 5d³ + 7d⁵` termwise. -/
theorem WeierstrassCurve.tateA₆_eq_evalInt (q : k) (hq : valuation k q < 1) :
    tateA₆ q = TateCurve.evalInt q TateCurve.a₆Formal := by
  have h12 : ∀ d : ℤ, (12 : ℤ) ∣ 5 * d ^ 3 + 7 * d ^ 5 := by
    intro d
    have hz : ((5 * d ^ 3 + 7 * d ^ 5 : ℤ) : ZMod 12) = 0 := by
      push_cast
      generalize (d : ZMod 12) = r
      revert r
      decide
    exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd _ 12).mp hz
  set c : ℕ → ℤ := fun d ↦ -((5 * (d : ℤ) ^ 3 + 7 * (d : ℤ) ^ 5) / 12) with hc
  have h := TateCurve.tsum_lambert q hq c
  have h1 : tateA₆ q = ∑' m : ℕ, ((c (m + 1) : ℤ) : k) * q ^ (m + 1) /
      (1 - q ^ (m + 1)) := by
    simp only [tateA₆]
    refine tsum_congr fun m ↦ ?_
    simp only [hc]
    push_cast
    ring
  have h2 : TateCurve.evalInt q TateCurve.a₆Formal = ∑' N : ℕ,
      ((∑ d ∈ N.divisors, c d : ℤ) : k) * q ^ N := by
    simp only [TateCurve.evalInt, TateCurve.coeff_a₆Formal]
    refine tsum_congr fun N ↦ ?_
    -- the divisor sum commutes with the exact division by `12`
    have key : ∑ d ∈ N.divisors, c d = -((5 * (σ 3 N : ℤ) + 7 * (σ 5 N : ℤ)) / 12) := by
      simp only [hc]
      have hσ : ∑ d ∈ N.divisors, (5 * (d : ℤ) ^ 3 + 7 * (d : ℤ) ^ 5)
          = 5 * (σ 3 N : ℤ) + 7 * (σ 5 N : ℤ) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
          ArithmeticFunction.sigma_apply, ArithmeticFunction.sigma_apply]
        push_cast
        ring
      have hsum : (12 : ℤ) ∣ 5 * (σ 3 N : ℤ) + 7 * (σ 5 N : ℤ) := by
        rw [← hσ]
        exact Finset.dvd_sum fun d _ ↦ h12 d
      have hterm : ∀ d ∈ N.divisors, -((5 * (d : ℤ) ^ 3 + 7 * (d : ℤ) ^ 5) / 12) * 12
          = -(5 * (d : ℤ) ^ 3 + 7 * (d : ℤ) ^ 5) := fun d _ ↦ by
        rw [neg_mul, Int.ediv_mul_cancel (h12 d)]
      apply mul_right_cancel₀ (b := (12 : ℤ)) (by norm_num)
      rw [Finset.sum_mul, Finset.sum_congr rfl hterm, neg_mul, Int.ediv_mul_cancel hsum,
        ← hσ, Finset.sum_neg_distrib]
    rw [key]
  rw [h1, h2, h]

/-- If the first `M` coefficients of `F` vanish, its evaluation at a point of the open
unit disc has valuation at most `|q|^M`: the partial sums satisfy the bound by the
nonarchimedean triangle inequality, and it passes to the limit by the ultrametric
isosceles principle (if `v(σ - T) < v(T)` and `v(σ) < v(T)` then
`v(T) ≤ max(v(σ), v(σ - T)) < v(T)`, absurd). -/
theorem TateCurve.valuation_evalInt_le_pow (q : k) (hq : valuation k q < 1) {F : ℤ⟦X⟧}
    {M : ℕ} (hF : ∀ m < M, PowerSeries.coeff m F = 0) :
    valuation k (evalInt q F) ≤ valuation k q ^ M := by
  by_contra hlt
  rw [not_le] at hlt
  -- the partial sums satisfy the bound
  have hpart : ∀ s : Finset ℕ,
      valuation k (∑ n ∈ s, ((PowerSeries.coeff n F : ℤ) : k) * q ^ n) ≤
        valuation k q ^ M := by
    intro s
    refine Valuation.map_sum_le _ fun n _ ↦ ?_
    rcases lt_or_ge n M with h | h
    · simp [hF n h]
    · rw [map_mul, map_pow]
      calc valuation k ((PowerSeries.coeff n F : ℤ) : k) * valuation k q ^ n
          ≤ 1 * valuation k q ^ n := mul_le_mul_left (valuation_intCast_le_one _) _
        _ = valuation k q ^ n := one_mul _
        _ ≤ valuation k q ^ M := pow_le_pow_right_of_le_one' hq.le h
  -- some partial sum is closer to the limit than `v(evalInt q F)`
  have hS : HasSum (fun n : ℕ ↦ ((PowerSeries.coeff n F : ℤ) : k) * q ^ n) (evalInt q F) :=
    (summable_evalInt q hq F).hasSum
  simp only [HasSum, SummationFilter.unconditional_filter] at hS
  rw [(IsValuativeTopology.hasBasis_nhds (evalInt q F)).tendsto_right_iff] at hS
  obtain ⟨s, hs⟩ :=
    (hS (Units.mk0 _ (ne_of_gt (lt_of_le_of_lt zero_le hlt))) trivial).exists
  simp only [Set.mem_setOf_eq] at hs
  refine absurd ?_ (lt_irrefl (valuation k (evalInt q F)))
  calc valuation k (evalInt q F)
      = valuation k ((∑ n ∈ s, ((PowerSeries.coeff n F : ℤ) : k) * q ^ n) -
          ((∑ n ∈ s, ((PowerSeries.coeff n F : ℤ) : k) * q ^ n) - evalInt q F)) := by
        rw [sub_sub_cancel]
    _ ≤ max (valuation k (∑ n ∈ s, ((PowerSeries.coeff n F : ℤ) : k) * q ^ n))
          (valuation k ((∑ n ∈ s, ((PowerSeries.coeff n F : ℤ) : k) * q ^ n) -
            evalInt q F)) := Valuation.map_sub _ _ _
    _ < valuation k (evalInt q F) := max_lt (lt_of_le_of_lt (hpart s) hlt) hs

/-- The leading-term principle: if `F = X + O(X²)` then `|F(q)| = |q|` on the punctured
open unit disc — ultrametrically the leading term dominates the tail, which has valuation
at most `|q|²` by `valuation_evalInt_le_pow`. -/
theorem TateCurve.valuation_evalInt_eq (q : k) (hq0 : q ≠ 0) (hq : valuation k q < 1)
    {F : ℤ⟦X⟧} (h0 : PowerSeries.constantCoeff F = 0) (h1 : PowerSeries.coeff 1 F = 1) :
    valuation k (evalInt q F) = valuation k q := by
  have hsplit : evalInt q F = q + evalInt q (F - PowerSeries.X) := by
    conv_lhs => rw [show F = PowerSeries.X + (F - PowerSeries.X) by ring]
    rw [evalInt_add (summable_evalInt q hq _) (summable_evalInt q hq _), evalInt_X]
  have hlow : ∀ m < 2, PowerSeries.coeff m (F - PowerSeries.X) = 0 := by
    intro m hm
    rcases m with - | - | m
    · simp [PowerSeries.coeff_zero_eq_constantCoeff, h0]
    · simp [h1, PowerSeries.coeff_X]
    · exact absurd hm (by omega)
  have hr : valuation k (evalInt q (F - PowerSeries.X)) < valuation k q :=
    lt_of_le_of_lt (valuation_evalInt_le_pow q hq hlow)
      (pow_lt_self_of_lt_one₀ (zero_lt_iff.mpr ((valuation k).ne_zero_iff.mpr hq0)) hq
        one_lt_two)
  rw [hsplit, (valuation k).map_add_eq_of_lt_left hr]

/-- Quantitative tail bound: the evaluation of an integral power series on the open unit
disc is within `|q|^N` of its `N`-th partial sum. -/
theorem TateCurve.valuation_evalInt_sub_sum_le (q : k) (hq : valuation k q < 1)
    (F : ℤ⟦X⟧) (N : ℕ) :
    valuation k (evalInt q F -
      ∑ n ∈ Finset.range N, ((PowerSeries.coeff n F : ℤ) : k) * q ^ n) ≤
    valuation k q ^ N := by
  -- the partial sum is the evaluation of the truncation
  have htrunc : evalInt q ((F.trunc N : Polynomial ℤ) : ℤ⟦X⟧) =
      ∑ n ∈ Finset.range N, ((PowerSeries.coeff n F : ℤ) : k) * q ^ n := by
    have h0 : ∀ n ∉ Finset.range N,
        ((PowerSeries.coeff n ((F.trunc N : Polynomial ℤ) : ℤ⟦X⟧) : ℤ) : k) * q ^ n = 0 := by
      intro n hn
      rw [Polynomial.coeff_coe, PowerSeries.coeff_trunc,
        if_neg (by simpa using hn), Int.cast_zero, zero_mul]
    refine (hasSum_sum_of_ne_finset_zero h0).tsum_eq.trans ?_
    exact Finset.sum_congr rfl fun n hn ↦ by
      rw [Polynomial.coeff_coe, PowerSeries.coeff_trunc, if_pos (Finset.mem_range.mp hn)]
  rw [← htrunc, ← evalInt_sub (summable_evalInt q hq _) (summable_evalInt q hq _)]
  refine valuation_evalInt_le_pow q hq fun m hm ↦ ?_
  rw [map_sub, Polynomial.coeff_coe, PowerSeries.coeff_trunc, if_pos hm, sub_self]

open PowerSeries in
open scoped PowerSeries.WithPiTopology in
/-- Evaluation of the formal `η²⁴` product: for `|q| < 1` the formal series
`ΔFormal = X(∏(1-Xⁿ))²⁴ ∈ ℤ⟦X⟧` evaluates to the convergent product `q∏(1-qⁿ)²⁴` in `k`.
The evaluated finite partial products converge to `evalInt q (∏(1-Xⁿ⁺¹))` because the
difference has vanishing low coefficients (`coeff_prod_one_sub_X_pow_stable`), hence
small valuation (`valuation_evalInt_le_pow`); this is the statement `HasProd`, and the
rest is multiplicativity of `evalInt`. -/
theorem TateCurve.evalInt_ΔFormal (q : k) (hq : valuation k q < 1) :
    evalInt q ΔFormal = q * ∏' n : ℕ, (1 - q ^ (n + 1)) ^ 24 := by
  -- evaluation is multiplicative on finite partial products
  have hfin : ∀ s : Finset ℕ, evalInt q (∏ n ∈ s, ((1 : ℤ⟦X⟧) - PowerSeries.X ^ (n + 1))) =
      ∏ n ∈ s, (1 - q ^ (n + 1)) := by
    intro s
    induction s using Finset.cons_induction with
    | empty => simp
    | cons a s ha ih =>
      rw [Finset.prod_cons, Finset.prod_cons, evalInt_mul q hq, ih,
        evalInt_sub (summable_evalInt q hq 1) (summable_evalInt q hq (PowerSeries.X ^ (a + 1))),
        evalInt_one, evalInt_pow q hq, evalInt_X]
  -- the core: the evaluated partial products converge to the evaluated formal product
  have hprod : HasProd (fun n : ℕ ↦ 1 - q ^ (n + 1))
      (evalInt q (∏' n : ℕ, ((1 : ℤ⟦X⟧) - PowerSeries.X ^ (n + 1)))) := by
    simp only [HasProd, SummationFilter.unconditional_filter]
    rw [(IsValuativeTopology.hasBasis_nhds _).tendsto_right_iff]
    intro γ _
    obtain ⟨N, hN⟩ := exists_pow_valuation_lt q hq γ
    filter_upwards [Filter.eventually_ge_atTop (Finset.range (N + 1))] with s hs
    rw [← hfin s, ← evalInt_sub (summable_evalInt q hq _) (summable_evalInt q hq _)]
    refine lt_of_le_of_lt ((valuation_evalInt_le_pow q hq (M := N + 1)
      fun m hm ↦ ?_).trans (pow_le_pow_right_of_le_one' hq.le (Nat.le_succ N))) hN
    -- the difference of the partial and the full product has no low coefficients
    rw [map_sub, coeff_tprod_one_sub_X_pow m,
      coeff_prod_one_sub_X_pow_stable (Finset.range_subset_range.mpr (Nat.le_succ m))
        ((Finset.range_subset_range.mpr hm).trans hs), sub_self]
  -- promote to the 24-th powers and assemble
  have hpow : ∀ j : ℕ, HasProd (fun n : ℕ ↦ (1 - q ^ (n + 1)) ^ j)
      (evalInt q (∏' n : ℕ, ((1 : ℤ⟦X⟧) - PowerSeries.X ^ (n + 1))) ^ j) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih => simpa only [pow_succ, Pi.mul_apply] using ih.mul hprod
  rw [(hpow 24).tprod_eq]
  simp only [ΔFormal]
  rw [evalInt_mul q hq, evalInt_pow q hq, evalInt_X]

/-- Silverman, ATAEC V.1.1(b): the discriminant of the Tate curve is
`Δ(q) = q∏_{n≥1}(1 - qⁿ)²⁴`. In particular, for `q ≠ 0` each factor of the right-hand
side is a unit of `𝒪[k]`, so `Δ(q) ≠ 0` and `E_q` is an elliptic curve.

The proof is a pure assembly: expand the Weierstrass discriminant of
`y² + xy = x³ + a₄x + a₆` as a polynomial in `a₄, a₆`, replace `tateA₄ q`, `tateA₆ q` by
evaluations of the formal series (`tateA₄_eq_evalInt`, `tateA₆_eq_evalInt`), pull the
polynomial through the ring homomorphism `evalInt q` (`evalInt_add/sub/mul/pow/C_mul`),
apply Jacobi's formal discriminant identity `TateCurve.ΔFormal_eq` in `ℤ⟦q⟧`, and
evaluate the resulting product (`evalInt_ΔFormal`). -/
theorem WeierstrassCurve.tateΔ_eq_prod (q : k) (hq : valuation k q < 1) :
    (tateCurve q).Δ = q * ∏' n : ℕ, (1 - q ^ (n + 1)) ^ 24 := by
  have hS : ∀ F : ℤ⟦X⟧, Summable fun n ↦ ((PowerSeries.coeff n F : ℤ) : k) * q ^ n :=
    TateCurve.summable_evalInt q hq
  -- the Weierstrass discriminant of `E_q`, explicitly: `b₂ = 1`, `b₄ = 2a₄`, `b₆ = 4a₆`,
  -- `b₈ = a₆ - a₄²` give `Δ = a₄² - a₆ - 64a₄³ + 72a₄a₆ - 432a₆²`
  have h1 : (tateCurve q).Δ = tateA₄ q ^ 2 - tateA₆ q - 64 * tateA₄ q ^ 3 +
      72 * (tateA₄ q * tateA₆ q) - 432 * tateA₆ q ^ 2 := by
    simp only [tateCurve, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
      WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
    ring
  rw [h1, tateA₄_eq_evalInt q hq, tateA₆_eq_evalInt q hq, ← TateCurve.evalInt_ΔFormal q hq,
    TateCurve.ΔFormal_eq, TateCurve.evalInt_sub (hS _) (hS _),
    TateCurve.evalInt_add (hS _) (hS _), TateCurve.evalInt_sub (hS _) (hS _),
    TateCurve.evalInt_sub (hS _) (hS _), TateCurve.evalInt_C_mul, TateCurve.evalInt_C_mul,
    TateCurve.evalInt_C_mul, TateCurve.evalInt_mul q hq, TateCurve.evalInt_pow q hq,
    TateCurve.evalInt_pow q hq, TateCurve.evalInt_pow q hq]
  push_cast
  ring

/-- The discriminant of the Tate curve is the evaluation of the formal discriminant. -/
theorem WeierstrassCurve.tateCurve_Δ_eq_evalInt (q : k) (hq : valuation k q < 1) :
    (tateCurve q).Δ = TateCurve.evalInt q TateCurve.ΔFormal := by
  rw [tateΔ_eq_prod q hq, TateCurve.evalInt_ΔFormal q hq]

/-- `c₄` of the Tate curve is the evaluation of the Eisenstein series `E₄ = 1 + 240s₃`. -/
theorem WeierstrassCurve.tateCurve_c₄_eq_evalInt (q : k) (hq : valuation k q < 1) :
    (tateCurve q).c₄ = TateCurve.evalInt q TateCurve.c₄Formal := by
  have h1 : (tateCurve q).c₄ = 1 - 48 * tateA₄ q := by
    simp only [tateCurve, WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄]
    ring
  have h2 : TateCurve.c₄Formal = 1 - PowerSeries.C 48 * TateCurve.a₄Formal := by
    simp only [TateCurve.c₄Formal, TateCurve.a₄Formal, map_ofNat]
    ring
  rw [h1, tateA₄_eq_evalInt q hq, h2,
    TateCurve.evalInt_sub (TateCurve.summable_evalInt q hq _)
      (TateCurve.summable_evalInt q hq _),
    TateCurve.evalInt_one, TateCurve.evalInt_C_mul]
  push_cast
  ring

/-- For `q ≠ 0` in the open unit disc, `|Δ(q)| = |q|`: the discriminant of the Tate curve
is `q + O(q²)`, and the leading term dominates ultrametrically. -/
theorem WeierstrassCurve.valuation_tateCurve_Δ (q : k) (hq0 : q ≠ 0)
    (hq : valuation k q < 1) : valuation k (tateCurve q).Δ = valuation k q := by
  rw [tateCurve_Δ_eq_evalInt q hq]
  exact TateCurve.valuation_evalInt_eq q hq0 hq TateCurve.constantCoeff_ΔFormal
    TateCurve.coeff_one_ΔFormal

/-- The Tate curve of a nonzero `q` in the open unit disc has nonvanishing discriminant
(so it is an elliptic curve). -/
theorem WeierstrassCurve.tateCurve_Δ_ne_zero (q : k) (hq0 : q ≠ 0)
    (hq : valuation k q < 1) : (tateCurve q).Δ ≠ 0 := by
  intro h
  have hv := valuation_tateCurve_Δ q hq0 hq
  rw [h, map_zero] at hv
  exact (valuation k).ne_zero_iff.mpr hq0 hv.symm

/-- `|c₄(q)| = 1` on the open unit disc: `c₄ = 1 + O(q)`. -/
theorem WeierstrassCurve.valuation_tateCurve_c₄ (q : k) (hq : valuation k q < 1) :
    valuation k (tateCurve q).c₄ = 1 := by
  rw [tateCurve_c₄_eq_evalInt q hq]
  have hsplit : TateCurve.evalInt q TateCurve.c₄Formal =
      1 + TateCurve.evalInt q (TateCurve.c₄Formal - 1) := by
    conv_lhs => rw [show TateCurve.c₄Formal = 1 + (TateCurve.c₄Formal - 1) by ring]
    rw [TateCurve.evalInt_add (TateCurve.summable_evalInt q hq _)
      (TateCurve.summable_evalInt q hq _), TateCurve.evalInt_one]
  have htail : valuation k (TateCurve.evalInt q (TateCurve.c₄Formal - 1)) < 1 := by
    refine lt_of_le_of_lt (TateCurve.valuation_evalInt_le_pow q hq (M := 1) fun m hm ↦ ?_)
      (by rwa [pow_one])
    rcases m with - | m
    · simp [PowerSeries.coeff_zero_eq_constantCoeff, TateCurve.constantCoeff_c₄Formal]
    · exact absurd hm (by omega)
  rw [hsplit, (valuation k).map_add_eq_of_lt_left (by rwa [map_one]), map_one]

theorem WeierstrassCurve.tateCurve_c₄_ne_zero (q : k) (hq : valuation k q < 1) :
    (tateCurve q).c₄ ≠ 0 := by
  intro h
  have hv := valuation_tateCurve_c₄ q hq
  rw [h, map_zero] at hv
  exact zero_ne_one hv

/-- The evaluation of the formal series `jInv = Δ/c₄³` is the reciprocal of the
`j`-invariant of the Tate curve: the glue between the formal inversion theory of
`TateCurve.jInvReverse` and the function `tateJ`. -/
theorem WeierstrassCurve.evalInt_jInv (q : k) (hq : valuation k q < 1) :
    TateCurve.evalInt q TateCurve.jInv = (tateJ q)⁻¹ := by
  have hglue : TateCurve.evalInt q TateCurve.jInv * (tateCurve q).c₄ ^ 3 =
      (tateCurve q).Δ := by
    rw [tateCurve_c₄_eq_evalInt q hq, tateCurve_Δ_eq_evalInt q hq,
      ← TateCurve.evalInt_pow q hq, ← TateCurve.evalInt_mul q hq,
      TateCurve.jInv_mul_c₄Formal]
  simp only [tateJ]
  rw [inv_div, eq_div_iff (pow_ne_zero 3 (tateCurve_c₄_ne_zero q hq))]
  exact hglue

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] in
/-- The `x`-coordinate series of Tate's uniformisation is invariant under `u ↦ qu`:
reindex the `ℤ`-indexed sum by `n ↦ n + 1`. This is the invariance that makes
`tateCurvePoint` descend to the quotient `kˣ/qᶻ`. -/
theorem WeierstrassCurve.tateX_mul_left (q : kˣ) (u : k) :
    tateX ((q : k) * u) (q : k) = tateX u (q : k) := by
  simp only [tateX]
  congr 1
  calc ∑' n : ℤ, (q : k) ^ n * ((q : k) * u) / (1 - (q : k) ^ n * ((q : k) * u)) ^ 2
      = ∑' n : ℤ, (q : k) ^ (n + 1) * u / (1 - (q : k) ^ (n + 1) * u) ^ 2 := by
        refine tsum_congr fun n ↦ ?_
        rw [zpow_add_one₀ (Units.ne_zero q)]
        ring
    _ = ∑' n : ℤ, (q : k) ^ n * u / (1 - (q : k) ^ n * u) ^ 2 :=
        (Equiv.addRight (1 : ℤ)).tsum_eq
          fun n ↦ (q : k) ^ n * u / (1 - (q : k) ^ n * u) ^ 2

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] in
/-- The `y`-coordinate series of Tate's uniformisation is invariant under `u ↦ qu`. -/
theorem WeierstrassCurve.tateY_mul_left (q : kˣ) (u : k) :
    tateY ((q : k) * u) (q : k) = tateY u (q : k) := by
  simp only [tateY]
  congr 1
  calc ∑' n : ℤ, ((q : k) ^ n * ((q : k) * u)) ^ 2 / (1 - (q : k) ^ n * ((q : k) * u)) ^ 3
      = ∑' n : ℤ, ((q : k) ^ (n + 1) * u) ^ 2 / (1 - (q : k) ^ (n + 1) * u) ^ 3 := by
        refine tsum_congr fun n ↦ ?_
        rw [zpow_add_one₀ (Units.ne_zero q)]
        ring
    _ = ∑' n : ℤ, ((q : k) ^ n * u) ^ 2 / (1 - (q : k) ^ n * u) ^ 3 :=
        (Equiv.addRight (1 : ℤ)).tsum_eq
          fun n ↦ ((q : k) ^ n * u) ^ 2 / (1 - (q : k) ^ n * u) ^ 3

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] in
/-- The `x`-coordinate series is invariant under `u ↦ qᵐu` for every `m : ℤ`. -/
theorem WeierstrassCurve.tateX_zpow_mul_left (q : kˣ) (m : ℤ) (u : k) :
    tateX ((q : k) ^ m * u) (q : k) = tateX u (q : k) := by
  induction m using Int.induction_on with
  | zero => simp
  | succ m ih =>
      rw [show (q : k) ^ ((m : ℤ) + 1) * u = (q : k) * ((q : k) ^ (m : ℤ) * u) by
        rw [zpow_add_one₀ (Units.ne_zero q)]; ring, tateX_mul_left, ih]
  | pred m ih =>
      have h1 := tateX_mul_left q ((q : k) ^ (-(m : ℤ) - 1) * u)
      rw [show (q : k) * ((q : k) ^ (-(m : ℤ) - 1) * u) = (q : k) ^ (-(m : ℤ) - 1 + 1) * u by
        rw [zpow_add_one₀ (Units.ne_zero q)]; ring, Int.sub_add_cancel] at h1
      exact h1.symm.trans ih

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] in
/-- The `y`-coordinate series is invariant under `u ↦ qᵐu` for every `m : ℤ`. -/
theorem WeierstrassCurve.tateY_zpow_mul_left (q : kˣ) (m : ℤ) (u : k) :
    tateY ((q : k) ^ m * u) (q : k) = tateY u (q : k) := by
  induction m using Int.induction_on with
  | zero => simp
  | succ m ih =>
      rw [show (q : k) ^ ((m : ℤ) + 1) * u = (q : k) * ((q : k) ^ (m : ℤ) * u) by
        rw [zpow_add_one₀ (Units.ne_zero q)]; ring, tateY_mul_left, ih]
  | pred m ih =>
      have h1 := tateY_mul_left q ((q : k) ^ (-(m : ℤ) - 1) * u)
      rw [show (q : k) * ((q : k) ^ (-(m : ℤ) - 1) * u) = (q : k) ^ (-(m : ℤ) - 1 + 1) * u by
        rw [zpow_add_one₀ (Units.ne_zero q)]; ring, Int.sub_add_cancel] at h1
      exact h1.symm.trans ih

/-- Silverman's `q`-expansion of the `x`-coordinate on the annulus `|q| < |u| ≤ 1`:
`X(u, q) = u/(1-u)² + ∑_{N ≥ 1} (∑_{d ∣ N} (d·uᵈ + d·u⁻ᵈ - 2d))·qᴺ`. The two halves of
the two-sided sum expand geometrically (`hasSum_geom_rows` with `hasSum_geometric_deriv`,
the `n ≤ -1` half after the inversion `div_one_sub_sq_inv`), and the Lambert correction
regroups by `tsum_lambert`. -/
theorem WeierstrassCurve.tateX_eq_annulus (q u : kˣ) (hq : valuation k (q : k) < 1)
    (h₁ : valuation k (q : k) < valuation k (u : k)) (h₂ : valuation k (u : k) ≤ 1) :
    tateX (u : k) (q : k) = (u : k) / (1 - (u : k)) ^ 2 +
      ∑' N : ℕ, (∑ d ∈ N.divisors, ((d : k) * (u : k) ^ d
        + (d : k) * ((u : k)⁻¹) ^ d - 2 * (d : k))) * (q : k) ^ N := by
  have hq0 : (q : k) ≠ 0 := Units.ne_zero q
  have hu0 : (u : k) ≠ 0 := Units.ne_zero u
  have hvu : valuation k (u : k) ≠ 0 := (valuation k).ne_zero_iff.mpr hu0
  have hρ : valuation k ((q : k) * (u : k)⁻¹) < 1 := by
    rw [map_mul, map_inv₀, ← div_eq_mul_inv]
    exact (div_lt_one₀ (zero_lt_iff.mpr hvu)).mpr h₁
  -- the discs on which the geometric expansions are valid
  have hposlt : ∀ n : ℕ, valuation k ((q : k) ^ (n + 1) * (u : k)) < 1 := by
    intro n
    rw [map_mul, map_pow]
    calc valuation k (q : k) ^ (n + 1) * valuation k (u : k)
        ≤ valuation k (q : k) ^ (n + 1) * 1 := mul_le_mul' le_rfl h₂
      _ = valuation k (q : k) ^ (n + 1) := mul_one _
      _ ≤ valuation k (q : k) ^ 1 := pow_le_pow_right_of_le_one' hq.le (by omega)
      _ = valuation k (q : k) := pow_one _
      _ < 1 := hq
  have hneglt : ∀ n : ℕ, valuation k ((q : k) ^ (n + 1) * (u : k)⁻¹) < 1 := by
    intro n
    refine lt_of_le_of_lt ?_ hρ
    rw [map_mul, map_mul, map_pow]
    refine mul_le_mul' ?_ le_rfl
    calc valuation k (q : k) ^ (n + 1) ≤ valuation k (q : k) ^ 1 :=
          pow_le_pow_right_of_le_one' hq.le (by omega)
      _ = valuation k (q : k) := pow_one _
  -- summability of the two double families
  have hsumApos : Summable fun p : ℕ+ × ℕ+ ↦
      ((p.1 : ℕ) : k) * (u : k) ^ (p.1 : ℕ) * (q : k) ^ ((p.1 : ℕ) * (p.2 : ℕ)) := by
    refine TateCurve.summable_of_valuation_le_pow hq (fun p ↦ (p.1 : ℕ) * (p.2 : ℕ))
      (fun N ↦ TateCurve.finite_pnat_mul_lt N) fun p ↦ ?_
    rw [map_mul, map_mul, map_pow, map_pow]
    calc valuation k ((p.1 : ℕ) : k) * valuation k (u : k) ^ (p.1 : ℕ) *
          valuation k (q : k) ^ ((p.1 : ℕ) * (p.2 : ℕ))
        ≤ 1 * 1 * valuation k (q : k) ^ ((p.1 : ℕ) * (p.2 : ℕ)) :=
          mul_le_mul' (mul_le_mul' (TateCurve.valuation_natCast_le_one _)
            (pow_le_one' h₂ _)) le_rfl
      _ = valuation k (q : k) ^ ((p.1 : ℕ) * (p.2 : ℕ)) := by rw [one_mul, one_mul]
  have hsumAneg : Summable fun p : ℕ+ × ℕ+ ↦
      ((p.1 : ℕ) : k) * ((u : k)⁻¹) ^ (p.1 : ℕ) * (q : k) ^ ((p.1 : ℕ) * (p.2 : ℕ)) := by
    refine TateCurve.summable_of_valuation_le_pow hρ (fun p ↦ (p.1 : ℕ) * (p.2 : ℕ))
      (fun N ↦ TateCurve.finite_pnat_mul_lt N) fun p ↦ ?_
    simp only [map_mul, map_pow, map_inv₀]
    have h1u : (1 : ValueGroupWithZero k) ≤ (valuation k (u : k))⁻¹ :=
      (one_le_inv₀ (zero_lt_iff.mpr hvu)).mpr h₂
    calc valuation k ((p.1 : ℕ) : k) * (valuation k (u : k))⁻¹ ^ (p.1 : ℕ) *
          valuation k (q : k) ^ ((p.1 : ℕ) * (p.2 : ℕ))
        ≤ 1 * (valuation k (u : k))⁻¹ ^ ((p.1 : ℕ) * (p.2 : ℕ)) *
            valuation k (q : k) ^ ((p.1 : ℕ) * (p.2 : ℕ)) :=
          mul_le_mul' (mul_le_mul' (TateCurve.valuation_natCast_le_one _)
            (pow_le_pow_right' h1u (Nat.le_mul_of_pos_right _ p.2.pos))) le_rfl
      _ = (valuation k (q : k) * (valuation k (u : k))⁻¹) ^ ((p.1 : ℕ) * (p.2 : ℕ)) := by
          rw [one_mul, mul_pow, mul_comm]
  -- the two regrouped halves
  obtain ⟨TA, hrowsA, hNA⟩ := TateCurve.hasSum_geom_rows (q : k) (u : k) (fun d ↦ d)
    (fun x ↦ x / (1 - x) ^ 2) (fun x hx ↦ TateCurve.hasSum_geometric_deriv hx) hposlt hsumApos
  obtain ⟨TC, hrowsC, hNC⟩ := TateCurve.hasSum_geom_rows (q : k) ((u : k)⁻¹) (fun d ↦ d)
    (fun x ↦ x / (1 - x) ^ 2) (fun x hx ↦ TateCurve.hasSum_geometric_deriv hx) hneglt hsumAneg
  have hNA' : HasSum (fun N : ℕ ↦
      (∑ d ∈ N.divisors, ((d : ℕ) : k) * (u : k) ^ d) * (q : k) ^ N) TA := hNA
  have hNC' : HasSum (fun N : ℕ ↦
      (∑ d ∈ N.divisors, ((d : ℕ) : k) * ((u : k)⁻¹) ^ d) * (q : k) ^ N) TC := hNC
  -- rows in the shape of the two-sided sum
  have hcoe : ∀ n : ℕ, (q : k) ^ ((n : ℤ) + 1) = (q : k) ^ (n + 1) := by
    intro n
    rw [show ((n : ℤ) + 1) = ((n + 1 : ℕ) : ℤ) by push_cast; ring, zpow_natCast]
  have hposrows : HasSum (fun n : ℕ ↦
      (q : k) ^ ((n : ℤ) + 1) * (u : k) / (1 - (q : k) ^ ((n : ℤ) + 1) * (u : k)) ^ 2) TA := by
    have heq : (fun n : ℕ ↦
        (q : k) ^ ((n : ℤ) + 1) * (u : k) / (1 - (q : k) ^ ((n : ℤ) + 1) * (u : k)) ^ 2) =
        fun n : ℕ ↦ (q : k) ^ (n + 1) * (u : k) / (1 - (q : k) ^ (n + 1) * (u : k)) ^ 2 := by
      funext n
      rw [hcoe n]
    rw [heq]
    exact hrowsA
  have hnegrows : HasSum (fun n : ℕ ↦ (q : k) ^ (-((n : ℤ) + 1)) * (u : k) /
      (1 - (q : k) ^ (-((n : ℤ) + 1)) * (u : k)) ^ 2) TC := by
    have heq : (fun n : ℕ ↦ (q : k) ^ (-((n : ℤ) + 1)) * (u : k) /
        (1 - (q : k) ^ (-((n : ℤ) + 1)) * (u : k)) ^ 2) =
        fun n : ℕ ↦ (q : k) ^ (n + 1) * (u : k)⁻¹ /
          (1 - (q : k) ^ (n + 1) * (u : k)⁻¹) ^ 2 := by
      funext n
      rw [zpow_neg, hcoe n,
        TateCurve.div_one_sub_sq_inv (v := ((q : k) ^ (n + 1))⁻¹ * (u : k))
          (mul_ne_zero (inv_ne_zero (pow_ne_zero _ hq0)) hu0),
        mul_inv, inv_inv]
    rw [heq]
    exact hrowsC
  have hzsum : HasSum (fun n : ℤ ↦ (q : k) ^ n * (u : k) / (1 - (q : k) ^ n * (u : k)) ^ 2)
      (TA + (u : k) / (1 - (u : k)) ^ 2 + TC) := by
    have h := HasSum.of_add_one_of_neg_add_one
      (f := fun n : ℤ ↦ (q : k) ^ n * (u : k) / (1 - (q : k) ^ n * (u : k)) ^ 2)
      hposrows hnegrows
    simpa using h
  -- the Lambert correction
  have hσ : Summable fun N : ℕ ↦ (∑ d ∈ N.divisors, ((d : ℕ) : k)) * (q : k) ^ N := by
    refine TateCurve.summable_of_valuation_le_pow hq (fun N ↦ N)
      (fun N ↦ Set.finite_Iio N) fun N ↦ ?_
    rw [map_mul, map_pow]
    calc valuation k (∑ d ∈ N.divisors, ((d : ℕ) : k)) * valuation k (q : k) ^ N
        ≤ 1 * valuation k (q : k) ^ N :=
          mul_le_mul_left ((valuation k).map_sum_le
            fun d _ ↦ TateCurve.valuation_natCast_le_one d) _
      _ = valuation k (q : k) ^ N := one_mul _
  have hlam : (∑' m : ℕ, ((m + 1 : ℕ) : k) * (q : k) ^ (m + 1) / (1 - (q : k) ^ (m + 1)))
      = ∑' N : ℕ, (∑ d ∈ N.divisors, ((d : ℕ) : k)) * (q : k) ^ N := by
    calc ∑' m : ℕ, ((m + 1 : ℕ) : k) * (q : k) ^ (m + 1) / (1 - (q : k) ^ (m + 1))
        = ∑' m : ℕ, (((fun d ↦ (d : ℤ)) (m + 1) : ℤ) : k) * (q : k) ^ (m + 1) /
            (1 - (q : k) ^ (m + 1)) := tsum_congr fun m ↦ by push_cast; ring
      _ = ∑' N : ℕ, ((∑ d ∈ N.divisors, (d : ℤ) : ℤ) : k) * (q : k) ^ N :=
          TateCurve.tsum_lambert (q : k) hq fun d ↦ (d : ℤ)
      _ = ∑' N : ℕ, (∑ d ∈ N.divisors, ((d : ℕ) : k)) * (q : k) ^ N :=
          tsum_congr fun N ↦ by push_cast; ring
  -- assemble
  have hcomb : (∑' N : ℕ, (∑ d ∈ N.divisors, ((d : ℕ) : k) * (u : k) ^ d) * (q : k) ^ N) +
      (∑' N : ℕ, (∑ d ∈ N.divisors, ((d : ℕ) : k) * ((u : k)⁻¹) ^ d) * (q : k) ^ N) -
      2 * ∑' N : ℕ, (∑ d ∈ N.divisors, ((d : ℕ) : k)) * (q : k) ^ N =
      ∑' N : ℕ, (∑ d ∈ N.divisors, ((d : k) * (u : k) ^ d
        + (d : k) * ((u : k)⁻¹) ^ d - 2 * (d : k))) * (q : k) ^ N := by
    rw [← Summable.tsum_add hNA'.summable hNC'.summable,
      show (2 : k) * ∑' N : ℕ, (∑ d ∈ N.divisors, ((d : ℕ) : k)) * (q : k) ^ N =
        ∑' N : ℕ, 2 * ((∑ d ∈ N.divisors, ((d : ℕ) : k)) * (q : k) ^ N) from tsum_mul_left.symm,
      ← Summable.tsum_sub (hNA'.summable.add hNC'.summable) (hσ.mul_left 2)]
    refine tsum_congr fun N ↦ ?_
    rw [← add_mul, ← Finset.sum_add_distrib, ← mul_assoc, Finset.mul_sum, ← sub_mul,
      ← Finset.sum_sub_distrib]
  simp only [tateX]
  rw [hzsum.tsum_eq, hlam, ← hNA'.tsum_eq, ← hNC'.tsum_eq]
  linear_combination hcomb

/-- Silverman's `q`-expansion of the `y`-coordinate on the annulus `|q| < |u| ≤ 1`:
`Y(u, q) = u²/(1-u)³ + ∑_{N ≥ 1} (∑_{d ∣ N} ((d 2)uᵈ - (d+1 2)u⁻ᵈ + d))·qᴺ`, with
binomial-coefficient weights. The `n ≤ -1` half enters with a sign through the inversion
antisymmetry `sq_div_one_sub_cube_inv`. -/
theorem WeierstrassCurve.tateY_eq_annulus (q u : kˣ) (hq : valuation k (q : k) < 1)
    (h₁ : valuation k (q : k) < valuation k (u : k)) (h₂ : valuation k (u : k) ≤ 1) :
    tateY (u : k) (q : k) = (u : k) ^ 2 / (1 - (u : k)) ^ 3 +
      ∑' N : ℕ, (∑ d ∈ N.divisors, (((d.choose 2 : ℕ) : k) * (u : k) ^ d
        - (((d + 1).choose 2 : ℕ) : k) * ((u : k)⁻¹) ^ d + (d : k))) * (q : k) ^ N := by
  have hq0 : (q : k) ≠ 0 := Units.ne_zero q
  have hu0 : (u : k) ≠ 0 := Units.ne_zero u
  have hvu : valuation k (u : k) ≠ 0 := (valuation k).ne_zero_iff.mpr hu0
  have hρ : valuation k ((q : k) * (u : k)⁻¹) < 1 := by
    rw [map_mul, map_inv₀, ← div_eq_mul_inv]
    exact (div_lt_one₀ (zero_lt_iff.mpr hvu)).mpr h₁
  have hposlt : ∀ n : ℕ, valuation k ((q : k) ^ (n + 1) * (u : k)) < 1 := by
    intro n
    rw [map_mul, map_pow]
    calc valuation k (q : k) ^ (n + 1) * valuation k (u : k)
        ≤ valuation k (q : k) ^ (n + 1) * 1 := mul_le_mul' le_rfl h₂
      _ = valuation k (q : k) ^ (n + 1) := mul_one _
      _ ≤ valuation k (q : k) ^ 1 := pow_le_pow_right_of_le_one' hq.le (by omega)
      _ = valuation k (q : k) := pow_one _
      _ < 1 := hq
  have hneglt : ∀ n : ℕ, valuation k ((q : k) ^ (n + 1) * (u : k)⁻¹) < 1 := by
    intro n
    refine lt_of_le_of_lt ?_ hρ
    rw [map_mul, map_mul, map_pow]
    refine mul_le_mul' ?_ le_rfl
    calc valuation k (q : k) ^ (n + 1) ≤ valuation k (q : k) ^ 1 :=
          pow_le_pow_right_of_le_one' hq.le (by omega)
      _ = valuation k (q : k) := pow_one _
  have hsumYpos : Summable fun p : ℕ+ × ℕ+ ↦
      (((p.1 : ℕ).choose 2 : ℕ) : k) * (u : k) ^ (p.1 : ℕ) *
        (q : k) ^ ((p.1 : ℕ) * (p.2 : ℕ)) := by
    refine TateCurve.summable_of_valuation_le_pow hq (fun p ↦ (p.1 : ℕ) * (p.2 : ℕ))
      (fun N ↦ TateCurve.finite_pnat_mul_lt N) fun p ↦ ?_
    rw [map_mul, map_mul, map_pow, map_pow]
    calc valuation k ((((p.1 : ℕ).choose 2 : ℕ)) : k) * valuation k (u : k) ^ (p.1 : ℕ) *
          valuation k (q : k) ^ ((p.1 : ℕ) * (p.2 : ℕ))
        ≤ 1 * 1 * valuation k (q : k) ^ ((p.1 : ℕ) * (p.2 : ℕ)) :=
          mul_le_mul' (mul_le_mul' (TateCurve.valuation_natCast_le_one _)
            (pow_le_one' h₂ _)) le_rfl
      _ = valuation k (q : k) ^ ((p.1 : ℕ) * (p.2 : ℕ)) := by rw [one_mul, one_mul]
  have hsumYneg : Summable fun p : ℕ+ × ℕ+ ↦
      ((((p.1 : ℕ) + 1).choose 2 : ℕ) : k) * ((u : k)⁻¹) ^ (p.1 : ℕ) *
        (q : k) ^ ((p.1 : ℕ) * (p.2 : ℕ)) := by
    refine TateCurve.summable_of_valuation_le_pow hρ (fun p ↦ (p.1 : ℕ) * (p.2 : ℕ))
      (fun N ↦ TateCurve.finite_pnat_mul_lt N) fun p ↦ ?_
    simp only [map_mul, map_pow, map_inv₀]
    have h1u : (1 : ValueGroupWithZero k) ≤ (valuation k (u : k))⁻¹ :=
      (one_le_inv₀ (zero_lt_iff.mpr hvu)).mpr h₂
    calc valuation k (((((p.1 : ℕ) + 1).choose 2 : ℕ)) : k) *
          (valuation k (u : k))⁻¹ ^ (p.1 : ℕ) *
          valuation k (q : k) ^ ((p.1 : ℕ) * (p.2 : ℕ))
        ≤ 1 * (valuation k (u : k))⁻¹ ^ ((p.1 : ℕ) * (p.2 : ℕ)) *
            valuation k (q : k) ^ ((p.1 : ℕ) * (p.2 : ℕ)) :=
          mul_le_mul' (mul_le_mul' (TateCurve.valuation_natCast_le_one _)
            (pow_le_pow_right' h1u (Nat.le_mul_of_pos_right _ p.2.pos))) le_rfl
      _ = (valuation k (q : k) * (valuation k (u : k))⁻¹) ^ ((p.1 : ℕ) * (p.2 : ℕ)) := by
          rw [one_mul, mul_pow, mul_comm]
  obtain ⟨TA, hrowsA, hNA⟩ := TateCurve.hasSum_geom_rows (q : k) (u : k) (fun d ↦ d.choose 2)
    (fun x ↦ x ^ 2 / (1 - x) ^ 3) (fun x hx ↦ TateCurve.hasSum_geometric_sq_div_cube hx)
    hposlt hsumYpos
  obtain ⟨TC, hrowsC, hNC⟩ := TateCurve.hasSum_geom_rows (q : k) ((u : k)⁻¹)
    (fun d ↦ (d + 1).choose 2) (fun x ↦ x / (1 - x) ^ 3)
    (fun x hx ↦ TateCurve.hasSum_geometric_div_cube hx) hneglt hsumYneg
  have hNA' : HasSum (fun N : ℕ ↦
      (∑ d ∈ N.divisors, ((d.choose 2 : ℕ) : k) * (u : k) ^ d) * (q : k) ^ N) TA := hNA
  have hNC' : HasSum (fun N : ℕ ↦
      (∑ d ∈ N.divisors, (((d + 1).choose 2 : ℕ) : k) * ((u : k)⁻¹) ^ d) * (q : k) ^ N) TC :=
    hNC
  have hcoe : ∀ n : ℕ, (q : k) ^ ((n : ℤ) + 1) = (q : k) ^ (n + 1) := by
    intro n
    rw [show ((n : ℤ) + 1) = ((n + 1 : ℕ) : ℤ) by push_cast; ring, zpow_natCast]
  have hposrows : HasSum (fun n : ℕ ↦ ((q : k) ^ ((n : ℤ) + 1) * (u : k)) ^ 2 /
      (1 - (q : k) ^ ((n : ℤ) + 1) * (u : k)) ^ 3) TA := by
    have heq : (fun n : ℕ ↦ ((q : k) ^ ((n : ℤ) + 1) * (u : k)) ^ 2 /
        (1 - (q : k) ^ ((n : ℤ) + 1) * (u : k)) ^ 3) =
        fun n : ℕ ↦ ((q : k) ^ (n + 1) * (u : k)) ^ 2 /
          (1 - (q : k) ^ (n + 1) * (u : k)) ^ 3 := by
      funext n
      rw [hcoe n]
    rw [heq]
    exact hrowsA
  have hnegrows : HasSum (fun n : ℕ ↦ ((q : k) ^ (-((n : ℤ) + 1)) * (u : k)) ^ 2 /
      (1 - (q : k) ^ (-((n : ℤ) + 1)) * (u : k)) ^ 3) (-TC) := by
    have heq : (fun n : ℕ ↦ ((q : k) ^ (-((n : ℤ) + 1)) * (u : k)) ^ 2 /
        (1 - (q : k) ^ (-((n : ℤ) + 1)) * (u : k)) ^ 3) =
        fun n : ℕ ↦ -((q : k) ^ (n + 1) * (u : k)⁻¹ /
          (1 - (q : k) ^ (n + 1) * (u : k)⁻¹) ^ 3) := by
      funext n
      rw [zpow_neg, hcoe n,
        TateCurve.sq_div_one_sub_cube_inv (v := ((q : k) ^ (n + 1))⁻¹ * (u : k))
          (mul_ne_zero (inv_ne_zero (pow_ne_zero _ hq0)) hu0),
        mul_inv, inv_inv]
    rw [heq]
    exact hrowsC.neg
  have hzsum : HasSum (fun n : ℤ ↦ ((q : k) ^ n * (u : k)) ^ 2 /
      (1 - (q : k) ^ n * (u : k)) ^ 3)
      (TA + (u : k) ^ 2 / (1 - (u : k)) ^ 3 + -TC) := by
    have h := HasSum.of_add_one_of_neg_add_one
      (f := fun n : ℤ ↦ ((q : k) ^ n * (u : k)) ^ 2 / (1 - (q : k) ^ n * (u : k)) ^ 3)
      hposrows hnegrows
    simpa using h
  have hσ : Summable fun N : ℕ ↦ (∑ d ∈ N.divisors, ((d : ℕ) : k)) * (q : k) ^ N := by
    refine TateCurve.summable_of_valuation_le_pow hq (fun N ↦ N)
      (fun N ↦ Set.finite_Iio N) fun N ↦ ?_
    rw [map_mul, map_pow]
    calc valuation k (∑ d ∈ N.divisors, ((d : ℕ) : k)) * valuation k (q : k) ^ N
        ≤ 1 * valuation k (q : k) ^ N :=
          mul_le_mul_left ((valuation k).map_sum_le
            fun d _ ↦ TateCurve.valuation_natCast_le_one d) _
      _ = valuation k (q : k) ^ N := one_mul _
  have hlam : (∑' m : ℕ, ((m + 1 : ℕ) : k) * (q : k) ^ (m + 1) / (1 - (q : k) ^ (m + 1)))
      = ∑' N : ℕ, (∑ d ∈ N.divisors, ((d : ℕ) : k)) * (q : k) ^ N := by
    calc ∑' m : ℕ, ((m + 1 : ℕ) : k) * (q : k) ^ (m + 1) / (1 - (q : k) ^ (m + 1))
        = ∑' m : ℕ, (((fun d ↦ (d : ℤ)) (m + 1) : ℤ) : k) * (q : k) ^ (m + 1) /
            (1 - (q : k) ^ (m + 1)) := tsum_congr fun m ↦ by push_cast; ring
      _ = ∑' N : ℕ, ((∑ d ∈ N.divisors, (d : ℤ) : ℤ) : k) * (q : k) ^ N :=
          TateCurve.tsum_lambert (q : k) hq fun d ↦ (d : ℤ)
      _ = ∑' N : ℕ, (∑ d ∈ N.divisors, ((d : ℕ) : k)) * (q : k) ^ N :=
          tsum_congr fun N ↦ by push_cast; ring
  have hcomb : (∑' N : ℕ,
      (∑ d ∈ N.divisors, ((d.choose 2 : ℕ) : k) * (u : k) ^ d) * (q : k) ^ N) -
      (∑' N : ℕ,
        (∑ d ∈ N.divisors, (((d + 1).choose 2 : ℕ) : k) * ((u : k)⁻¹) ^ d) * (q : k) ^ N) +
      ∑' N : ℕ, (∑ d ∈ N.divisors, ((d : ℕ) : k)) * (q : k) ^ N =
      ∑' N : ℕ, (∑ d ∈ N.divisors, (((d.choose 2 : ℕ) : k) * (u : k) ^ d
        - (((d + 1).choose 2 : ℕ) : k) * ((u : k)⁻¹) ^ d + (d : k))) * (q : k) ^ N := by
    rw [← Summable.tsum_sub hNA'.summable hNC'.summable,
      ← Summable.tsum_add (hNA'.summable.sub hNC'.summable) hσ]
    refine tsum_congr fun N ↦ ?_
    rw [← sub_mul, ← Finset.sum_sub_distrib, ← add_mul, ← Finset.sum_add_distrib]
  simp only [tateY]
  rw [hzsum.tsum_eq, hlam, ← hNA'.tsum_eq, ← hNC'.tsum_eq]
  linear_combination hcomb

/-! ### Evaluation of `k`-coefficient power series on the annulus

The annulus `q`-expansions above present `tateX` and `tateY` as values of power series in
`k⟦q⟧` whose terms at `q` are `O(ρⁿ)` in valuation, for `ρ = |q|/|u| < 1`
(`TateCurve.EvalBounded`). On this class, evaluation (`TateCurve.evalK`) is a ring
homomorphism — the nonarchimedean Mertens theorem again, now with the constant tracked
through the bounds. Applying it to the descended formal identity
`TateCurve.weierstrass_equation_field` yields the Weierstrass equation for the values,
which is the annulus case of Silverman V.1.1(a). -/

/-- Powers of any `ρ < 1` in the value group eventually drop below any nonzero `γ`: the
generalisation of `exists_pow_valuation_lt` from `|q|` to arbitrary `ρ`, by the same
rank-one embedding argument. -/
theorem TateCurve.exists_pow_lt {ρ : ValueGroupWithZero k} (hρ : ρ < 1)
    (γ : (ValueGroupWithZero k)ˣ) : ∃ N : ℕ, ρ ^ N < γ := by
  rcases eq_or_ne ρ 0 with rfl | h0
  · exact ⟨1, by rw [pow_one]; exact zero_lt_iff.mpr γ.ne_zero⟩
  · obtain ⟨s⟩ := ValuativeRel.IsRankLeOne.nonempty (R := k)
    obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one
      (show 0 < s.emb γ from by simpa using s.strictMono (zero_lt_iff.mpr γ.ne_zero))
      (show s.emb ρ < 1 from by simpa using s.strictMono hρ)
    exact ⟨N, s.strictMono.lt_iff_lt.mp (by rwa [map_pow])⟩

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
/-- Clearing the constant: `ρᴺ < C⁻¹γ` implies `CρᴺN < γ` in the value group. -/
theorem TateCurve.mul_pow_lt {C ρ γ : ValueGroupWithZero k} (hC : C ≠ 0) {N : ℕ}
    (hN : ρ ^ N < C⁻¹ * γ) : C * ρ ^ N < γ := by
  have hle : C * ρ ^ N ≤ γ := by
    calc C * ρ ^ N ≤ C * (C⁻¹ * γ) := mul_le_mul' le_rfl hN.le
      _ = γ := by rw [← mul_assoc, mul_inv_cancel₀ hC, one_mul]
  refine lt_of_le_of_ne hle fun heq ↦ hN.ne ?_
  exact mul_left_cancel₀ hC (by rw [heq, ← mul_assoc, mul_inv_cancel₀ hC, one_mul])

/-- The nonarchimedean summability criterion with a constant: a series whose terms have
valuation at most `C·ρⁿ` with `ρ < 1` converges. Generalises
`summable_of_valuation_le_pow` to carry the constant `C` needed for series with large
leading coefficients (such as `u/(1-u)²` for `u` close to `1`). -/
theorem TateCurve.summable_of_valuation_le_const_mul_pow {C ρ : ValueGroupWithZero k}
    (hC : C ≠ 0) (hρ : ρ < 1) (f : ℕ → k)
    (hf : ∀ n, valuation k (f n) ≤ C * ρ ^ n) : Summable f := by
  letI : UniformSpace k := IsTopologicalAddGroup.rightUniformSpace k
  haveI : IsUniformAddGroup k := isUniformAddGroup_of_addCommGroup
  haveI : NonarchimedeanRing k := by
    convert! ValuativeRel.nonarchimedeanRing k
    exact Valuation.toTopologicalSpace_eq _
  apply NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
  rw [Nat.cofinite_eq_atTop, (IsValuativeTopology.hasBasis_nhds (0 : k)).tendsto_right_iff]
  intro γ _
  obtain ⟨N, hN⟩ := exists_pow_lt hρ (Units.mk0 (C⁻¹ * (γ : ValueGroupWithZero k))
    (mul_ne_zero (inv_ne_zero hC) γ.ne_zero))
  filter_upwards [Filter.eventually_ge_atTop N] with n hn
  simp only [sub_zero]
  calc valuation k (f n) ≤ C * ρ ^ n := hf n
    _ ≤ C * ρ ^ N := mul_le_mul' le_rfl (pow_le_pow_right_of_le_one' hρ.le hn)
    _ < γ := mul_pow_lt hC hN

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
/-- The class of power series `F ∈ k⟦X⟧` whose terms at `q` are `O(ρⁿ)` in valuation:
`|coeff n F·qⁿ| ≤ C·ρⁿ` for some nonzero constant `C`. For `ρ < 1` such series are
evaluable at `q` (`EvalBounded.summable`), and the class is a subring on which evaluation
is multiplicative (`evalK_mul`) — the constant is what accommodates coefficients like
`u/(1-u)²` (large for `u` near `1`) and the growing denominators `u⁻ᵈ` of the annulus
expansions (bounded by `ρ = |q|/|u|`-powers rather than `|q|`-powers). -/
def TateCurve.EvalBounded (q : k) (ρ : ValueGroupWithZero k) (F : k⟦X⟧) : Prop :=
  ∃ C : ValueGroupWithZero k, C ≠ 0 ∧
    ∀ n : ℕ, valuation k (PowerSeries.coeff n F * q ^ n) ≤ C * ρ ^ n

theorem TateCurve.EvalBounded.summable {q : k} {ρ : ValueGroupWithZero k} {F : k⟦X⟧}
    (hF : EvalBounded q ρ F) (hρ : ρ < 1) :
    Summable fun n : ℕ ↦ PowerSeries.coeff n F * q ^ n := by
  obtain ⟨C, hC, hb⟩ := hF
  exact summable_of_valuation_le_const_mul_pow hC hρ _ hb

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem TateCurve.EvalBounded.add {q : k} {ρ : ValueGroupWithZero k} {F G : k⟦X⟧}
    (hF : EvalBounded q ρ F) (hG : EvalBounded q ρ G) : EvalBounded q ρ (F + G) := by
  obtain ⟨C₁, hC₁, h₁⟩ := hF
  obtain ⟨C₂, hC₂, h₂⟩ := hG
  refine ⟨max C₁ C₂, (lt_max_of_lt_left (zero_lt_iff.mpr hC₁)).ne', fun n ↦ ?_⟩
  rw [map_add, add_mul]
  refine le_trans ((valuation k).map_add _ _) (max_le ?_ ?_)
  · exact (h₁ n).trans (mul_le_mul' (le_max_left _ _) le_rfl)
  · exact (h₂ n).trans (mul_le_mul' (le_max_right _ _) le_rfl)

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem TateCurve.EvalBounded.mul {q : k} {ρ : ValueGroupWithZero k} {F G : k⟦X⟧}
    (hF : EvalBounded q ρ F) (hG : EvalBounded q ρ G) : EvalBounded q ρ (F * G) := by
  obtain ⟨C₁, hC₁, h₁⟩ := hF
  obtain ⟨C₂, hC₂, h₂⟩ := hG
  refine ⟨C₁ * C₂, mul_ne_zero hC₁ hC₂, fun n ↦ ?_⟩
  rw [PowerSeries.coeff_mul, Finset.sum_mul]
  refine (valuation k).map_sum_le fun kl hkl ↦ ?_
  rw [Finset.mem_antidiagonal] at hkl
  calc valuation k (PowerSeries.coeff kl.1 F * PowerSeries.coeff kl.2 G * q ^ n)
      = valuation k (PowerSeries.coeff kl.1 F * q ^ kl.1) *
        valuation k (PowerSeries.coeff kl.2 G * q ^ kl.2) := by
        rw [← map_mul]
        congr 1
        rw [← hkl, pow_add]
        ring
    _ ≤ C₁ * ρ ^ kl.1 * (C₂ * ρ ^ kl.2) := mul_le_mul' (h₁ _) (h₂ _)
    _ = C₁ * C₂ * ρ ^ n := by rw [mul_mul_mul_comm, ← pow_add, hkl]

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem TateCurve.EvalBounded.pow {q : k} {ρ : ValueGroupWithZero k} {F : k⟦X⟧}
    (hF : EvalBounded q ρ F) (m : ℕ) : EvalBounded q ρ (F ^ m) := by
  induction m with
  | zero =>
      refine ⟨1, one_ne_zero, fun n ↦ ?_⟩
      rcases eq_or_ne n 0 with rfl | hn
      · simp
      · simp [PowerSeries.coeff_one, hn]
  | succ m ih =>
      rw [pow_succ]
      exact ih.mul hF

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
/-- Constant power series are evaluation-bounded (with constant `max 1 |a|`). -/
theorem TateCurve.evalBounded_C (q : k) (ρ : ValueGroupWithZero k) (a : k) :
    EvalBounded q ρ (PowerSeries.C a) := by
  refine ⟨max 1 (valuation k a), (lt_max_of_lt_left zero_lt_one).ne', fun n ↦ ?_⟩
  rcases eq_or_ne n 0 with rfl | hn
  · rw [pow_zero, mul_one, pow_zero, mul_one, PowerSeries.coeff_zero_C]
    exact le_max_right _ _
  · rw [PowerSeries.coeff_C, if_neg hn, zero_mul, map_zero]
    exact zero_le

/-- Evaluation of a `k`-coefficient power series at `q`: `F(q) = ∑ₙ (coeff n F)·qⁿ`
(junk unless the series converges, e.g. for `EvalBounded` series at `ρ < 1`). Extends
`TateCurve.evalInt` from integral to `k`-coefficient series. -/
noncomputable def TateCurve.evalK (q : k) (F : k⟦X⟧) : k :=
  ∑' n : ℕ, PowerSeries.coeff n F * q ^ n

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] in
/-- `evalK` at an integral series is `evalInt`. -/
theorem TateCurve.evalK_intSeries (q : k) (F : ℤ⟦X⟧) :
    evalK q (F.map (Int.castRingHom k)) = evalInt q F :=
  tsum_congr fun n ↦ by rw [PowerSeries.coeff_map, eq_intCast]

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
/-- Integral series are evaluation-bounded (with constant `1`) for any `ρ ≥ |q|`. -/
theorem TateCurve.evalBounded_intSeries (q : k) {ρ : ValueGroupWithZero k}
    (hqρ : valuation k q ≤ ρ) (F : ℤ⟦X⟧) :
    EvalBounded q ρ (F.map (Int.castRingHom k)) := by
  refine ⟨1, one_ne_zero, fun n ↦ ?_⟩
  rw [one_mul, PowerSeries.coeff_map, eq_intCast, map_mul, map_pow]
  calc valuation k ((PowerSeries.coeff n F : ℤ) : k) * valuation k q ^ n
      ≤ 1 * valuation k q ^ n := mul_le_mul_left (valuation_intCast_le_one _) _
    _ = valuation k q ^ n := one_mul _
    _ ≤ ρ ^ n := pow_le_pow_left' hqρ n

theorem TateCurve.evalK_add {q : k} {ρ : ValueGroupWithZero k} (hρ : ρ < 1) {F G : k⟦X⟧}
    (hF : EvalBounded q ρ F) (hG : EvalBounded q ρ G) :
    evalK q (F + G) = evalK q F + evalK q G := by
  simp only [evalK, map_add, add_mul]
  exact Summable.tsum_add (hF.summable hρ) (hG.summable hρ)

/-- Evaluation of `k`-coefficient power series is multiplicative on the bounded class:
the nonarchimedean Mertens theorem, with the constant carried through the double-series
summability bound. Extends `TateCurve.evalInt_mul`. -/
theorem TateCurve.evalK_mul {q : k} {ρ : ValueGroupWithZero k} (hρ : ρ < 1) {F G : k⟦X⟧}
    (hF : EvalBounded q ρ F) (hG : EvalBounded q ρ G) :
    evalK q (F * G) = evalK q F * evalK q G := by
  have hf := hF.summable hρ
  have hg := hG.summable hρ
  obtain ⟨C₁, hC₁, h₁⟩ := hF
  obtain ⟨C₂, hC₂, h₂⟩ := hG
  have hfg : Summable fun x : ℕ × ℕ ↦
      (PowerSeries.coeff x.1 F * q ^ x.1) * (PowerSeries.coeff x.2 G * q ^ x.2) := by
    letI : UniformSpace k := IsTopologicalAddGroup.rightUniformSpace k
    haveI : IsUniformAddGroup k := isUniformAddGroup_of_addCommGroup
    haveI : NonarchimedeanRing k := by
      convert! ValuativeRel.nonarchimedeanRing k
      exact Valuation.toTopologicalSpace_eq _
    apply NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
    rw [(IsValuativeTopology.hasBasis_nhds (0 : k)).tendsto_right_iff]
    intro γ _
    obtain ⟨N, hN⟩ := exists_pow_lt hρ (Units.mk0
      ((C₁ * C₂)⁻¹ * (γ : ValueGroupWithZero k))
      (mul_ne_zero (inv_ne_zero (mul_ne_zero hC₁ hC₂)) γ.ne_zero))
    rw [Filter.eventually_cofinite]
    refine Set.Finite.subset ((Set.finite_Iio N).prod (Set.finite_Iio N)) fun x hx ↦ ?_
    simp only [Set.mem_setOf_eq, sub_zero] at hx
    have hbound : valuation k ((PowerSeries.coeff x.1 F * q ^ x.1) *
        (PowerSeries.coeff x.2 G * q ^ x.2)) ≤ C₁ * C₂ * ρ ^ (x.1 + x.2) :=
      calc valuation k ((PowerSeries.coeff x.1 F * q ^ x.1) *
            (PowerSeries.coeff x.2 G * q ^ x.2))
          = valuation k (PowerSeries.coeff x.1 F * q ^ x.1) *
            valuation k (PowerSeries.coeff x.2 G * q ^ x.2) := map_mul _ _ _
        _ ≤ C₁ * ρ ^ x.1 * (C₂ * ρ ^ x.2) := mul_le_mul' (h₁ _) (h₂ _)
        _ = C₁ * C₂ * ρ ^ (x.1 + x.2) := by rw [mul_mul_mul_comm, ← pow_add]
    have hlt : x.1 + x.2 < N := lt_of_not_ge fun hge ↦
      hx (lt_of_le_of_lt (hbound.trans (mul_le_mul' le_rfl
        (pow_le_pow_right_of_le_one' hρ.le hge))) (mul_pow_lt (mul_ne_zero hC₁ hC₂) hN))
    exact Set.mem_prod.mpr ⟨Set.mem_Iio.mpr (lt_of_le_of_lt (Nat.le_add_right _ _) hlt),
      Set.mem_Iio.mpr (lt_of_le_of_lt (Nat.le_add_left _ _) hlt)⟩
  simp only [evalK]
  rw [hf.tsum_mul_tsum_eq_tsum_sum_antidiagonal hg hfg]
  refine tsum_congr fun n ↦ ?_
  rw [PowerSeries.coeff_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun kl hkl ↦ ?_
  rw [Finset.mem_antidiagonal] at hkl
  rw [← hkl, pow_add]
  ring

theorem TateCurve.evalK_pow {q : k} {ρ : ValueGroupWithZero k} (hρ : ρ < 1) {F : k⟦X⟧}
    (hF : EvalBounded q ρ F) (m : ℕ) : evalK q (F ^ m) = evalK q F ^ m := by
  induction m with
  | zero =>
      rw [pow_zero, pow_zero]
      have h : (fun n : ℕ ↦ PowerSeries.coeff n (1 : k⟦X⟧) * q ^ n) =
          fun n ↦ if n = 0 then 1 else 0 := by
        funext n
        rcases eq_or_ne n 0 with rfl | hn
        · simp
        · simp [PowerSeries.coeff_one, hn]
      rw [show evalK q 1 = ∑' n : ℕ, PowerSeries.coeff n (1 : k⟦X⟧) * q ^ n from rfl, h,
        tsum_ite_eq]
  | succ m ih => rw [pow_succ, pow_succ, evalK_mul hρ (hF.pow m) hF, ih]

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
/-- The divisor-sum tail of `XField u` is evaluation-bounded by `(|q|/|u|)ⁿ`-powers: the
`u⁻ᵈ`-terms grow like `|u|⁻ⁿ`, which the annulus bound absorbs. -/
theorem TateCurve.evalBounded_XField_tail (q u : kˣ) (h₂ : valuation k (u : k) ≤ 1) :
    EvalBounded (q : k) (valuation k (q : k) * (valuation k (u : k))⁻¹)
      (PowerSeries.mk fun n ↦ ∑ d ∈ n.divisors,
        ((d : k) * (u : k) ^ d + (d : k) * ((u : k)⁻¹) ^ d - 2 * (d : k))) := by
  have hvu : valuation k (u : k) ≠ 0 := (valuation k).ne_zero_iff.mpr (Units.ne_zero u)
  have h1u : (1 : ValueGroupWithZero k) ≤ (valuation k (u : k))⁻¹ :=
    (one_le_inv₀ (zero_lt_iff.mpr hvu)).mpr h₂
  refine ⟨1, one_ne_zero, fun n ↦ ?_⟩
  have h1n : (1 : ValueGroupWithZero k) ≤ (valuation k (u : k))⁻¹ ^ n := by
    calc (1 : ValueGroupWithZero k) = (valuation k (u : k))⁻¹ ^ 0 := (pow_zero _).symm
      _ ≤ (valuation k (u : k))⁻¹ ^ n := pow_le_pow_right' h1u (Nat.zero_le n)
  have hsum : valuation k (∑ d ∈ n.divisors,
      ((d : k) * (u : k) ^ d + (d : k) * ((u : k)⁻¹) ^ d - 2 * (d : k)))
      ≤ (valuation k (u : k))⁻¹ ^ n := by
    refine (valuation k).map_sum_le fun d hd ↦ ?_
    have hdn : d ≤ n := Nat.divisor_le hd
    refine le_trans ((valuation k).map_sub _ _) (max_le (le_trans
      ((valuation k).map_add _ _) (max_le ?_ ?_)) ?_)
    · rw [map_mul, map_pow]
      calc valuation k ((d : ℕ) : k) * valuation k (u : k) ^ d
          ≤ 1 * 1 := mul_le_mul' (valuation_natCast_le_one d) (pow_le_one' h₂ d)
        _ = 1 := one_mul 1
        _ ≤ (valuation k (u : k))⁻¹ ^ n := h1n
    · rw [map_mul, map_pow, map_inv₀]
      calc valuation k ((d : ℕ) : k) * (valuation k (u : k))⁻¹ ^ d
          ≤ 1 * (valuation k (u : k))⁻¹ ^ d :=
            mul_le_mul_left (valuation_natCast_le_one d) _
        _ = (valuation k (u : k))⁻¹ ^ d := one_mul _
        _ ≤ (valuation k (u : k))⁻¹ ^ n := pow_le_pow_right' h1u hdn
    · rw [show ((2 : k) * (d : k)) = ((2 * d : ℕ) : k) by push_cast; ring]
      exact le_trans (valuation_natCast_le_one _) h1n
  rw [one_mul, PowerSeries.coeff_mk, map_mul, map_pow, mul_pow]
  calc valuation k (∑ d ∈ n.divisors,
        ((d : k) * (u : k) ^ d + (d : k) * ((u : k)⁻¹) ^ d - 2 * (d : k))) *
        valuation k (q : k) ^ n
      ≤ (valuation k (u : k))⁻¹ ^ n * valuation k (q : k) ^ n := mul_le_mul' hsum le_rfl
    _ = valuation k (q : k) ^ n * ((valuation k (u : k))⁻¹) ^ n := mul_comm _ _

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem TateCurve.evalBounded_XField (q u : kˣ) (h₂ : valuation k (u : k) ≤ 1) :
    EvalBounded (q : k) (valuation k (q : k) * (valuation k (u : k))⁻¹)
      (XField (u : k)) :=
  (evalBounded_C _ _ _).add (evalBounded_XField_tail q u h₂)

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
/-- The divisor-sum tail of `YField u`; as for `evalBounded_XField_tail`. -/
theorem TateCurve.evalBounded_YField_tail (q u : kˣ) (h₂ : valuation k (u : k) ≤ 1) :
    EvalBounded (q : k) (valuation k (q : k) * (valuation k (u : k))⁻¹)
      (PowerSeries.mk fun n ↦ ∑ d ∈ n.divisors, (((d.choose 2 : ℕ) : k) * (u : k) ^ d
        - (((d + 1).choose 2 : ℕ) : k) * ((u : k)⁻¹) ^ d + (d : k))) := by
  have hvu : valuation k (u : k) ≠ 0 := (valuation k).ne_zero_iff.mpr (Units.ne_zero u)
  have h1u : (1 : ValueGroupWithZero k) ≤ (valuation k (u : k))⁻¹ :=
    (one_le_inv₀ (zero_lt_iff.mpr hvu)).mpr h₂
  refine ⟨1, one_ne_zero, fun n ↦ ?_⟩
  have h1n : (1 : ValueGroupWithZero k) ≤ (valuation k (u : k))⁻¹ ^ n := by
    calc (1 : ValueGroupWithZero k) = (valuation k (u : k))⁻¹ ^ 0 := (pow_zero _).symm
      _ ≤ (valuation k (u : k))⁻¹ ^ n := pow_le_pow_right' h1u (Nat.zero_le n)
  have hsum : valuation k (∑ d ∈ n.divisors, (((d.choose 2 : ℕ) : k) * (u : k) ^ d
      - (((d + 1).choose 2 : ℕ) : k) * ((u : k)⁻¹) ^ d + (d : k)))
      ≤ (valuation k (u : k))⁻¹ ^ n := by
    refine (valuation k).map_sum_le fun d hd ↦ ?_
    have hdn : d ≤ n := Nat.divisor_le hd
    refine le_trans ((valuation k).map_add _ _) (max_le (le_trans
      ((valuation k).map_sub _ _) (max_le ?_ ?_)) ?_)
    · rw [map_mul, map_pow]
      calc valuation k ((d.choose 2 : ℕ) : k) * valuation k (u : k) ^ d
          ≤ 1 * 1 := mul_le_mul' (valuation_natCast_le_one _) (pow_le_one' h₂ d)
        _ = 1 := one_mul 1
        _ ≤ (valuation k (u : k))⁻¹ ^ n := h1n
    · rw [map_mul, map_pow, map_inv₀]
      calc valuation k (((d + 1).choose 2 : ℕ) : k) * (valuation k (u : k))⁻¹ ^ d
          ≤ 1 * (valuation k (u : k))⁻¹ ^ d :=
            mul_le_mul_left (valuation_natCast_le_one _) _
        _ = (valuation k (u : k))⁻¹ ^ d := one_mul _
        _ ≤ (valuation k (u : k))⁻¹ ^ n := pow_le_pow_right' h1u hdn
    · exact le_trans (valuation_natCast_le_one d) h1n
  rw [one_mul, PowerSeries.coeff_mk, map_mul, map_pow, mul_pow]
  calc valuation k (∑ d ∈ n.divisors, (((d.choose 2 : ℕ) : k) * (u : k) ^ d
        - (((d + 1).choose 2 : ℕ) : k) * ((u : k)⁻¹) ^ d + (d : k))) *
        valuation k (q : k) ^ n
      ≤ (valuation k (u : k))⁻¹ ^ n * valuation k (q : k) ^ n := mul_le_mul' hsum le_rfl
    _ = valuation k (q : k) ^ n * ((valuation k (u : k))⁻¹) ^ n := mul_comm _ _

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem TateCurve.evalBounded_YField (q u : kˣ) (h₂ : valuation k (u : k) ≤ 1) :
    EvalBounded (q : k) (valuation k (q : k) * (valuation k (u : k))⁻¹)
      (YField (u : k)) :=
  (evalBounded_C _ _ _).add (evalBounded_YField_tail q u h₂)

/-- On the annulus, `tateX` is the value at `q` of the formal series `XField u`:
`tateX_eq_annulus` in evaluation form. -/
theorem WeierstrassCurve.tateX_eq_evalK (q u : kˣ) (hq : valuation k (q : k) < 1)
    (h₁ : valuation k (q : k) < valuation k (u : k)) (h₂ : valuation k (u : k) ≤ 1) :
    tateX (u : k) (q : k) = TateCurve.evalK (q : k) (TateCurve.XField (u : k)) := by
  have hvu : valuation k (u : k) ≠ 0 := (valuation k).ne_zero_iff.mpr (Units.ne_zero u)
  have hρ1 : valuation k (q : k) * (valuation k (u : k))⁻¹ < 1 := by
    rw [← div_eq_mul_inv]
    exact (div_lt_one₀ (zero_lt_iff.mpr hvu)).mpr h₁
  have htail : Summable fun n : ℕ ↦ (∑ d ∈ n.divisors,
      ((d : k) * (u : k) ^ d + (d : k) * ((u : k)⁻¹) ^ d - 2 * (d : k))) * (q : k) ^ n :=
    ((TateCurve.evalBounded_XField_tail q u h₂).summable hρ1).congr fun n ↦ by
      rw [PowerSeries.coeff_mk]
  have hterm : ∀ n : ℕ,
      PowerSeries.coeff n (TateCurve.XField (u : k)) * (q : k) ^ n =
      (if n = 0 then (u : k) / (1 - (u : k)) ^ 2 else 0) + (∑ d ∈ n.divisors,
        ((d : k) * (u : k) ^ d + (d : k) * ((u : k)⁻¹) ^ d - 2 * (d : k))) * (q : k) ^ n := by
    intro n
    rw [TateCurve.coeff_XField, add_mul]
    congr 1
    rcases eq_or_ne n 0 with rfl | hn
    · rw [if_pos rfl, pow_zero, mul_one]
    · rw [if_neg hn, zero_mul]
  rw [tateX_eq_annulus q u hq h₁ h₂,
    show TateCurve.evalK (q : k) (TateCurve.XField (u : k)) = ∑' n : ℕ,
      ((if n = 0 then (u : k) / (1 - (u : k)) ^ 2 else 0) + (∑ d ∈ n.divisors,
        ((d : k) * (u : k) ^ d + (d : k) * ((u : k)⁻¹) ^ d - 2 * (d : k))) * (q : k) ^ n)
      from tsum_congr hterm,
    Summable.tsum_add ((hasSum_ite_eq 0 _).summable) htail, tsum_ite_eq]

/-- On the annulus, `tateY` is the value at `q` of the formal series `YField u`:
`tateY_eq_annulus` in evaluation form. -/
theorem WeierstrassCurve.tateY_eq_evalK (q u : kˣ) (hq : valuation k (q : k) < 1)
    (h₁ : valuation k (q : k) < valuation k (u : k)) (h₂ : valuation k (u : k) ≤ 1) :
    tateY (u : k) (q : k) = TateCurve.evalK (q : k) (TateCurve.YField (u : k)) := by
  have hvu : valuation k (u : k) ≠ 0 := (valuation k).ne_zero_iff.mpr (Units.ne_zero u)
  have hρ1 : valuation k (q : k) * (valuation k (u : k))⁻¹ < 1 := by
    rw [← div_eq_mul_inv]
    exact (div_lt_one₀ (zero_lt_iff.mpr hvu)).mpr h₁
  have htail : Summable fun n : ℕ ↦ (∑ d ∈ n.divisors,
      (((d.choose 2 : ℕ) : k) * (u : k) ^ d
        - (((d + 1).choose 2 : ℕ) : k) * ((u : k)⁻¹) ^ d + (d : k))) * (q : k) ^ n :=
    ((TateCurve.evalBounded_YField_tail q u h₂).summable hρ1).congr fun n ↦ by
      rw [PowerSeries.coeff_mk]
  have hterm : ∀ n : ℕ,
      PowerSeries.coeff n (TateCurve.YField (u : k)) * (q : k) ^ n =
      (if n = 0 then (u : k) ^ 2 / (1 - (u : k)) ^ 3 else 0) + (∑ d ∈ n.divisors,
        (((d.choose 2 : ℕ) : k) * (u : k) ^ d
          - (((d + 1).choose 2 : ℕ) : k) * ((u : k)⁻¹) ^ d + (d : k))) * (q : k) ^ n := by
    intro n
    rw [TateCurve.coeff_YField, add_mul]
    congr 1
    rcases eq_or_ne n 0 with rfl | hn
    · rw [if_pos rfl, pow_zero, mul_one]
    · rw [if_neg hn, zero_mul]
  rw [tateY_eq_annulus q u hq h₁ h₂,
    show TateCurve.evalK (q : k) (TateCurve.YField (u : k)) = ∑' n : ℕ,
      ((if n = 0 then (u : k) ^ 2 / (1 - (u : k)) ^ 3 else 0) + (∑ d ∈ n.divisors,
        (((d.choose 2 : ℕ) : k) * (u : k) ^ d
          - (((d + 1).choose 2 : ℕ) : k) * ((u : k)⁻¹) ^ d + (d : k))) * (q : k) ^ n)
      from tsum_congr hterm,
    Summable.tsum_add ((hasSum_ite_eq 0 _).summable) htail, tsum_ite_eq]

/-- `tateA₄` is the value at `q` of the formal series `a₄Field k`. -/
theorem WeierstrassCurve.tateA₄_eq_evalK (q : k) (hq : valuation k q < 1) :
    tateA₄ q = TateCurve.evalK q (TateCurve.a₄Field k) :=
  (tateA₄_eq_evalInt q hq).trans (TateCurve.evalK_intSeries q TateCurve.a₄Formal).symm

/-- `tateA₆` is the value at `q` of the formal series `a₆Field k`. -/
theorem WeierstrassCurve.tateA₆_eq_evalK (q : k) (hq : valuation k q < 1) :
    tateA₆ q = TateCurve.evalK q (TateCurve.a₆Field k) :=
  (tateA₆_eq_evalInt q hq).trans (TateCurve.evalK_intSeries q TateCurve.a₆Formal).symm

/-- The annulus case of Silverman, ATAEC V.1.1(a): for `|q| < |u| ≤ 1` and `u ≠ 1`, the
pair `(X(u, q), Y(u, q))` satisfies the Weierstrass equation of the Tate curve. (In the
annulus the only power of `q` is `1` itself, so `u ≠ 1` is the full nondegeneracy
condition.)

The proof composes the three layers built above:

* the annulus `q`-expansions `tateX_eq_annulus`, `tateY_eq_annulus` present the
  coordinates as values `evalK q (XField u)`, `evalK q (YField u)` of formal series
  whose coefficients are Silverman's divisor sums (`tateX_eq_evalK`, `tateY_eq_evalK`),
  and likewise `tateA₄`, `tateA₆` for the Weierstrass coefficients;
* all four series are evaluation-bounded by `(|q|/|u|)ⁿ`-powers (`EvalBounded`), and on
  that class evaluation is a ring homomorphism (`evalK_add`, `evalK_mul`, `evalK_pow` —
  the nonarchimedean Mertens theorem);
* the formal Weierstrass identity, proved analytically over `ℚ(u)` and descended
  through `ℤ[u, u⁻¹, (1-u)⁻¹]` to every field (`weierstrass_equation_field`, using
  `u ≠ 0, 1`), therefore evaluates to the equation between the values. -/
theorem WeierstrassCurve.tateCurve_equation_of_annulus (q : kˣ)
    (hq : valuation k (q : k) < 1) (u : kˣ) (hu1 : u ≠ 1)
    (h₁ : valuation k (q : k) < valuation k (u : k)) (h₂ : valuation k (u : k) ≤ 1) :
    ((tateCurve (q : k))⁄k).Equation (tateX (u : k) (q : k)) (tateY (u : k) (q : k)) := by
  have hu0 : (u : k) ≠ 0 := Units.ne_zero u
  have hu1' : (u : k) ≠ 1 := fun h ↦ hu1 (Units.ext (by rw [Units.val_one]; exact h))
  have hvu : valuation k (u : k) ≠ 0 := (valuation k).ne_zero_iff.mpr hu0
  have hρ1 : valuation k (q : k) * (valuation k (u : k))⁻¹ < 1 := by
    rw [← div_eq_mul_inv]
    exact (div_lt_one₀ (zero_lt_iff.mpr hvu)).mpr h₁
  have hqρ : valuation k (q : k) ≤ valuation k (q : k) * (valuation k (u : k))⁻¹ :=
    calc valuation k (q : k) = valuation k (q : k) * 1 := (mul_one _).symm
      _ ≤ valuation k (q : k) * (valuation k (u : k))⁻¹ :=
        mul_le_mul' le_rfl ((one_le_inv₀ (zero_lt_iff.mpr hvu)).mpr h₂)
  -- the four series are evaluation-bounded on the annulus
  have hX := TateCurve.evalBounded_XField q u h₂
  have hY := TateCurve.evalBounded_YField q u h₂
  have hA₄ : TateCurve.EvalBounded (q : k) (valuation k (q : k) * (valuation k (u : k))⁻¹)
      (TateCurve.a₄Field k) := TateCurve.evalBounded_intSeries (q : k) hqρ TateCurve.a₄Formal
  have hA₆ : TateCurve.EvalBounded (q : k) (valuation k (q : k) * (valuation k (u : k))⁻¹)
      (TateCurve.a₆Field k) := TateCurve.evalBounded_intSeries (q : k) hqρ TateCurve.a₆Formal
  -- reduce to the coefficient identity `Y² + XY = X³ + a₄X + a₆`
  rw [show (tateCurve (q : k))⁄k = tateCurve (q : k) by
    simp only [WeierstrassCurve.baseChange, Algebra.algebraMap_self, WeierstrassCurve.map_id],
    WeierstrassCurve.Affine.equation_iff]
  rw [show (tateCurve (q : k)).a₁ = 1 from rfl, show (tateCurve (q : k)).a₂ = 0 from rfl,
    show (tateCurve (q : k)).a₃ = 0 from rfl,
    show (tateCurve (q : k)).a₄ = tateA₄ (q : k) from rfl,
    show (tateCurve (q : k)).a₆ = tateA₆ (q : k) from rfl,
    one_mul, zero_mul, add_zero, zero_mul, add_zero]
  -- express everything as values of the formal series and use the descended identity
  rw [tateX_eq_evalK q u hq h₁ h₂, tateY_eq_evalK q u hq h₁ h₂,
    tateA₄_eq_evalK (q : k) hq, tateA₆_eq_evalK (q : k) hq,
    ← TateCurve.evalK_pow hρ1 hY 2, ← TateCurve.evalK_mul hρ1 hX hY,
    ← TateCurve.evalK_add hρ1 (hY.pow 2) (hX.mul hY),
    ← TateCurve.evalK_pow hρ1 hX 3, ← TateCurve.evalK_mul hρ1 hA₄ hX,
    ← TateCurve.evalK_add hρ1 (hX.pow 3) (hA₄.mul hX),
    ← TateCurve.evalK_add hρ1 ((hX.pow 3).add (hA₄.mul hX)) hA₆]
  exact congrArg (TateCurve.evalK (q : k))
    (TateCurve.weierstrass_equation_field hu0 hu1')

/-- Silverman, ATAEC V.1.1(a), over `k`: for `u` not a power of `q`, the pair
`(X(u, q), Y(u, q))` satisfies the Weierstrass equation of the Tate curve `E_q`. The
formal kernel is `TateCurve.weierstrass_equation`, the identity
`Y² + XY = X³ + a₄X + a₆` in `(RatFunc ℚ)⟦q⟧` proved in
`FLT.KnownIn1980s.EllipticCurves.TateCurveConstruction`. The transport to `k` should
mirror `tateΔ_eq_prod`:

* the coefficients of the formal `X(u, q)`, `Y(u, q)` are Laurent polynomials in `u` over
  `ℤ` (only the `q⁰`-coefficients also require inverting `1 - u`), so the formal identity
  descends from `RatFunc ℚ` to the subring `ℤ[u, u⁻¹, (1 - u)⁻¹]` by injectivity;
* for `|q| < 1` and `u ∉ qᶻ` the doubly-infinite defining series of `tateX` and `tateY`
  rearrange into power series in `q` with those coefficients evaluated at `u ∈ kˣ` —
  legal, since `u ≠ 0, 1` — by the two-variable analogue of the Lambert rearrangement
  `TateCurve.tsum_lambert` (over `ℂ` this is `TateCurve.hasSum_X_eval` and
  `TateCurve.hasSum_Y_eval`);
* evaluation is a ring homomorphism on convergent series (`evalInt_add`, `evalInt_mul`
  and their two-variable extensions), so the formal identity evaluates to the equation
  in `k`.

Here the general case is reduced to the annulus case `tateCurve_equation_of_annulus`:
normalise `u` into `|q| < |u| ≤ 1` by a power of `q` (`exists_zpow_mul_mem_annulus`),
under which `tateX` and `tateY` are invariant (`tateX_zpow_mul_left`,
`tateY_zpow_mul_left`). -/
theorem WeierstrassCurve.tateCurve_equation (q : kˣ) (hq : valuation k (q : k) < 1)
    (u : kˣ) (hu : u ∉ Subgroup.zpowers q) :
    ((tateCurve (q : k))⁄k).Equation (tateX (u : k) (q : k)) (tateY (u : k) (q : k)) := by
  -- normalise `u` into the annulus `|q| < |·| ≤ 1` by a power of `q`
  obtain ⟨m, h₁, h₂⟩ := TateCurve.exists_zpow_mul_mem_annulus q hq u
  have hu' : q ^ m * u ∉ Subgroup.zpowers q := fun h ↦ hu (by
    have h2 := Subgroup.mul_mem _ (Subgroup.zpow_mem _ (Subgroup.mem_zpowers q) (-m)) h
    rwa [show q ^ (-m) * (q ^ m * u) = u by group] at h2)
  have hu1 : (q ^ m * u : kˣ) ≠ 1 := fun h ↦ hu' (h ▸ Subgroup.one_mem _)
  have hcoe : ((q ^ m * u : kˣ) : k) = (q : k) ^ m * (u : k) := by push_cast; ring
  have h := tateCurve_equation_of_annulus q hq (q ^ m * u) hu1 (by rwa [hcoe])
    (by rwa [hcoe])
  rw [hcoe, tateX_zpow_mul_left, tateY_zpow_mul_left] at h
  exact h

/-- Silverman, ATAEC V.1.1(a): for `u` not a power of `q`, the pair `(X(u, q), Y(u, q))`
is a *nonsingular* point of the Tate curve `E_q`: it satisfies the Weierstrass equation
(`tateCurve_equation`), and every point of a Weierstrass curve with nonvanishing
discriminant is nonsingular (`tateCurve_Δ_ne_zero`, since `0 < |q| < 1`). -/
theorem WeierstrassCurve.tateCurve_nonsingular (q : kˣ) (hq : valuation k (q : k) < 1)
    (u : kˣ) (hu : u ∉ Subgroup.zpowers q) :
    ((tateCurve (q : k))⁄k).Nonsingular (tateX (u : k) (q : k)) (tateY (u : k) (q : k)) := by
  have hΔ : ((tateCurve (q : k))⁄k).Δ ≠ 0 := by
    rw [show (tateCurve (q : k))⁄k = tateCurve (q : k) by
      simp only [WeierstrassCurve.baseChange, Algebra.algebraMap_self, WeierstrassCurve.map_id]]
    exact tateCurve_Δ_ne_zero (q : k) q.ne_zero hq
  exact (Affine.equation_iff_nonsingular_of_Δ_ne_zero hΔ).mp (tateCurve_equation q hq u hu)

open scoped Classical in
/-- The point of `E_q(k)` attached to a unit `u ∈ kˣ` by Tate's uniformisation: the affine
point `(X(u, q), Y(u, q))` when `u` is not a power of `q`, and the point at infinity `O`
(the class of `qᶻ`) otherwise. This descends to `tateCurveEquiv` below. -/
noncomputable def WeierstrassCurve.tateCurvePoint (q : kˣ) (hq : valuation k (q : k) < 1)
    (u : kˣ) : ((tateCurve (q : k))⁄k).Point :=
  if hu : u ∈ Subgroup.zpowers q then .zero
  else .some (tateX (u : k) (q : k)) (tateY (u : k) (q : k)) (tateCurve_nonsingular q hq u hu)

/-- `tateCurvePoint` only depends on the class of `u` in `kˣ/qᶻ`: on the point at
infinity the two membership conditions agree, and on affine points the coordinate series
are `qᶻ`-invariant (`tateX_zpow_mul_left`, `tateY_zpow_mul_left`). -/
theorem WeierstrassCurve.tateCurvePoint_eq (q : kˣ) (hq : valuation k (q : k) < 1)
    (u v : kˣ) (h : u⁻¹ * v ∈ Subgroup.zpowers q) :
    tateCurvePoint q hq u = tateCurvePoint q hq v := by
  obtain ⟨m, hm⟩ := h
  have hm' : q ^ m = u⁻¹ * v := hm
  have hv : v = q ^ m * u := by
    rw [hm', mul_comm u⁻¹ v, inv_mul_cancel_right]
  subst hv
  have hXeq : tateX ((q ^ m * u : kˣ) : k) (q : k) = tateX (u : k) (q : k) := by
    push_cast
    exact tateX_zpow_mul_left q m u
  have hYeq : tateY ((q ^ m * u : kˣ) : k) (q : k) = tateY (u : k) (q : k) := by
    push_cast
    exact tateY_zpow_mul_left q m u
  simp only [tateCurvePoint]
  split_ifs with h1 h2 h2
  · rfl
  · exact absurd (Subgroup.mul_mem _ (Subgroup.zpow_mem _ (Subgroup.mem_zpowers q) m) h1) h2
  · exact absurd
      ((Subgroup.mul_mem_cancel_left _ (Subgroup.zpow_mem _ (Subgroup.mem_zpowers q) m)).mp h2) h1
  · simp only [hXeq, hYeq]

-- `DecidableEq k` is needed for the group law on the points
variable [DecidableEq k] in
/-- Tate's uniformisation of the Tate curve `E_q`, given by the explicit power series
`x = X(u, q)`, `y = Y(u, q)` of Silverman, ATAEC V.3. The forward map sends the class of a
unit `u` to the point `tateCurvePoint q hq u = (X(u, q), Y(u, q))` (and the trivial class
`qᶻ` to `O`). Unlike `tateEquiv` below, this involves no choices at all: it commutes on the
nose with every valuative field morphism (see `tateCurve_baseChange` for the equation-level
statement). -/
noncomputable def WeierstrassCurve.tateCurveEquiv (q : kˣ) (hq : valuation k (q : k) < 1) :
    Additive (kˣ ⧸ Subgroup.zpowers q) ≃+ ((tateCurve (q : k))⁄k).Point where
  toFun m := Quotient.liftOn' (Additive.toMul m) (tateCurvePoint q hq) fun u v h ↦
    tateCurvePoint_eq q hq u v (QuotientGroup.leftRel_apply.mp h)
  invFun := sorry
  left_inv := sorry
  right_inv := sorry
  map_add' := sorry

-- `tateParameter` — the inverse of `q ↦ j(q)` of Silverman, ATAEC V.5.2, by which the
-- Tate parameter is *defined* below, choice-freely — is constructed in
-- `FLT.KnownIn1980s.EllipticCurves.TateParameter` (imported above) as the evaluation at
-- `j⁻¹` of an explicit integral power series. Here we state its interaction with the
-- valuation and with `tateJ` (the two halves of V.5.2).

/-- The Tate parameter of `j` has valuation exactly `|j|⁻¹`: the leading term `j⁻¹` of
the inverse series `q = j⁻¹ + 744j⁻² + ⋯` dominates ultrametrically. -/
theorem WeierstrassCurve.valuation_tateParameter_eq {j : k} (hj : 1 < valuation k j) :
    valuation k (tateParameter j) = (valuation k j)⁻¹ := by
  have hj0 : j ≠ 0 := by
    rintro rfl
    rw [map_zero] at hj
    simp at hj
  have hjinv : valuation k j⁻¹ < 1 := by
    rw [map_inv₀]
    exact inv_lt_one_of_one_lt₀ hj
  have h := TateCurve.valuation_evalInt_eq j⁻¹ (inv_ne_zero hj0) hjinv
    TateCurve.constantCoeff_jInvReverse TateCurve.coeff_one_jInvReverse
  rw [show tateParameter j = TateCurve.evalInt j⁻¹ TateCurve.jInvReverse from rfl, h,
    map_inv₀]

theorem WeierstrassCurve.tateParameter_ne_zero {j : k} (hj : 1 < valuation k j) :
    tateParameter j ≠ 0 := by
  intro h
  have heq := valuation_tateParameter_eq hj
  rw [h, map_zero] at heq
  exact inv_ne_zero (ne_of_gt (lt_trans zero_lt_one hj)) heq.symm

theorem WeierstrassCurve.valuation_tateParameter_lt_one {j : k} (hj : 1 < valuation k j) :
    valuation k (tateParameter j) < 1 := by
  rw [valuation_tateParameter_eq hj]
  exact inv_lt_one_of_one_lt₀ hj

/-- `tateParameter` is a right inverse of `tateJ`: the *existence* half of Silverman,
ATAEC V.5.2. The evaluation of the formal identity `jInv ∘ jInvReverse = X` at `j⁻¹`,
via `evalInt_subst`. -/
theorem WeierstrassCurve.tateJ_tateParameter {j : k} (hj : 1 < valuation k j) :
    tateJ (tateParameter j) = j := by
  have hjinv : valuation k j⁻¹ < 1 := by
    rw [map_inv₀]
    exact inv_lt_one_of_one_lt₀ hj
  have h2 : TateCurve.evalInt (tateParameter j) TateCurve.jInv = j⁻¹ := by
    rw [show tateParameter j = TateCurve.evalInt j⁻¹ TateCurve.jInvReverse from rfl,
      ← TateCurve.evalInt_subst j⁻¹ hjinv TateCurve.constantCoeff_jInvReverse TateCurve.jInv,
      TateCurve.jInv_subst_jInvReverse, TateCurve.evalInt_X]
  exact inv_injective
    (((evalInt_jInv (tateParameter j) (valuation_tateParameter_lt_one hj)).symm.trans h2))

/-- `tateParameter` is a left inverse of `tateJ` on the open unit disc: the *uniqueness*
half of Silverman, ATAEC V.5.2, stated choice-freely as a round-trip identity — if
`q₁, q₂` both lie in the disc and `tateJ q₁ = tateJ q₂`, apply `tateParameter` to both
sides. (At `q = 0` the junk values of `tateJ` and `tateParameter` happen to align, so
the puncture is not needed.) -/
theorem WeierstrassCurve.tateParameter_tateJ {q : k}
    (hq1 : valuation k q < 1) : tateParameter (tateJ q) = q := by
  rw [show tateParameter (tateJ q) =
      TateCurve.evalInt (tateJ q)⁻¹ TateCurve.jInvReverse from rfl,
    ← evalInt_jInv q hq1,
    ← TateCurve.evalInt_subst q hq1 TateCurve.constantCoeff_jInv TateCurve.jInvReverse,
    TateCurve.subst_jInvReverse, TateCurve.evalInt_X]

/-- An elliptic curve over `k` with split multiplicative reduction has non-integral
`j`-invariant, `|j(E)| > 1`: indeed `v(j) = -v(Δ_min) < 0`, since `c₄` is a unit when the
reduction is multiplicative. -/
theorem WeierstrassCurve.one_lt_valuation_j (E : WeierstrassCurve k) [E.IsElliptic]
    [E.IsMinimal 𝒪[k]] [E.HasSplitMultiplicativeReduction 𝒪[k]] :
    1 < valuation k E.j := by
  have hmult : E.HasMultiplicativeReduction 𝒪[k] := inferInstance
  -- transfer `mathlib`'s reduction-theoretic facts (stated for the adic valuation of the
  -- discrete valuation ring `𝒪[k]`) to the canonical valuation of `k`, through unit and
  -- maximal-ideal membership in `𝒪[k]`
  have hint := Valuation.integer.integers (valuation k)
  -- `|Δ| < 1`: the discriminant of the integral model lies in the maximal ideal
  have hΔlt : valuation k E.Δ < 1 := by
    have hbad := hmult.badReduction
    rw [← integralModel_Δ_eq 𝒪[k] E] at hbad ⊢
    have hmem : (integralModel 𝒪[k] E).Δ ∈ IsLocalRing.maximalIdeal 𝒪[k] :=
      (IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem _ _).mp hbad
    have hne : ¬IsUnit (integralModel 𝒪[k] E).Δ :=
      mem_nonunits_iff.mp ((IsLocalRing.mem_maximalIdeal _).mp hmem)
    exact lt_of_le_of_ne (hint.map_le_one _)
      fun h ↦ hne (hint.isUnit_iff_valuation_eq_one.mpr h)
  -- `|c₄| = 1`: `c₄` of the integral model is a unit of `𝒪[k]`
  have hc₄ : valuation k E.c₄ = 1 := by
    have hmul := hmult.multiplicativeReduction
    rw [← integralModel_c₄_eq 𝒪[k] E] at hmul ⊢
    have hunit : IsUnit (integralModel 𝒪[k] E).c₄ := by
      by_contra h
      exact ((IsDedekindDomain.HeightOneSpectrum.valuation_eq_one_iff_notMem _).mp hmul)
        ((IsLocalRing.mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr h))
    exact hint.isUnit_iff_valuation_eq_one.mp hunit
  -- hence `|j| = |c₄|³/|Δ| = |Δ|⁻¹ > 1`
  have hΔ0 : valuation k E.Δ ≠ 0 := by
    rw [(valuation k).ne_zero_iff, ← E.coe_Δ']
    exact Units.ne_zero _
  have hj : valuation k E.j = (valuation k E.Δ)⁻¹ := by
    rw [show E.j = (↑(E.Δ'⁻¹) : k) * E.c₄ ^ 3 from rfl, map_mul, map_pow, hc₄, one_pow,
      mul_one, Units.val_inv_eq_inv_val, map_inv₀, E.coe_Δ']
  rw [hj]
  exact (one_lt_inv₀ (zero_lt_iff.mpr hΔ0)).mpr hΔlt

/-- The Tate parameter of an elliptic curve `E`, given by a minimal Weierstrass equation with
split multiplicative reduction over a nonarchimedean local field `k`: the unique element
`q` of `k` with `0 < |q| < 1` such that `j(E) = j(q) = q⁻¹ + 744 + 196884q + ⋯`, defined
directly (with no appeal to choice) as `tateParameter E.j`, the inverse `j`-series
evaluated at `j(E)`. Equivalently, the unique `q` such that `E(k̄)` is Galois-equivariantly
isomorphic to `k̄ˣ/q^ℤ`. (The bare existence of an abstract isomorphism `E(k) ≅ kˣ/q^ℤ`
would not pin down `q`: already over `ℚ_p` the groups `ℚ_pˣ/p^ℤ` and `ℚ_pˣ/(p(1+p))^ℤ`
are isomorphic, even topologically.) -/
noncomputable def WeierstrassCurve.q (E : WeierstrassCurve k) [E.IsElliptic]
    [E.IsMinimal 𝒪[k]] [E.HasSplitMultiplicativeReduction 𝒪[k]] : k :=
  tateParameter E.j

-- Let E/k be an elliptic curve, given by a minimal Weierstrass equation,
-- with split multiplicative reduction
variable (E : WeierstrassCurve k) [E.IsElliptic] [E.IsMinimal 𝒪[k]]
  [E.HasSplitMultiplicativeReduction 𝒪[k]]

theorem WeierstrassCurve.q_ne_zero : E.q ≠ 0 :=
  tateParameter_ne_zero E.one_lt_valuation_j

/-- The Tate parameter has norm less than `1`. -/
theorem WeierstrassCurve.valuation_q_lt_one : valuation k E.q < 1 :=
  valuation_tateParameter_lt_one E.one_lt_valuation_j

/-- The defining property of the Tate parameter: `j(E) = j(q(E))`. -/
theorem WeierstrassCurve.j_eq_tateJ_q : E.j = tateJ E.q :=
  (tateJ_tateParameter E.one_lt_valuation_j).symm

/-- Silverman, ATAEC V.5.2 applied to `E`: the Tate parameter is the *unique* element of
the punctured open unit disc with `j(E) = j(q)`. Existence and uniqueness both follow
from the round-trip identities of `tateParameter`; no choice is involved. (The disc
constraint on `q` is needed for uniqueness as `tateJ` takes junk values outside it.) -/
theorem WeierstrassCurve.existsUnique_tateJ_eq :
    ∃! q : k, q ≠ 0 ∧ valuation k q < 1 ∧ E.j = tateJ q := by
  refine ⟨E.q, ⟨E.q_ne_zero, E.valuation_q_lt_one, E.j_eq_tateJ_q⟩, ?_⟩
  rintro q' ⟨-, hq1, hj⟩
  rw [← tateParameter_tateJ hq1, ← hj]
  rfl

/-- The Tate parameter as an element of `kˣ`. -/
noncomputable def WeierstrassCurve.qUnit : kˣ :=
  Units.mk0 E.q E.q_ne_zero

-- `DecidableEq k` is needed for the group law on `(E⁄k).Point`
variable [DecidableEq k] in
/-- Tate's uniformization theorem: if `E/k` is an elliptic curve with split multiplicative
reduction then `E(k)` is isomorphic to `kˣ/⟨q⟩`.
-/
noncomputable def WeierstrassCurve.tateEquiv :
    Additive (kˣ ⧸ Subgroup.zpowers E.qUnit) ≃+ (E⁄k).Point :=
  sorry

-- Tate's theorem (Silverman, ATAEC V.5.3): an elliptic curve with split multiplicative
-- reduction is isomorphic, by a change of Weierstrass coordinates, to the Tate curve of its
-- Tate parameter. Since `j(E)` is non-integral, `Aut` of the curve is `{±1}` and there are
-- exactly *two* such `C`, differing by negation. `tateEquiv` is `tateCurveEquiv` transported
-- along a choice of one of them; this binary choice, for each `E`, is the only choice in
-- the whole theory, and it cannot be made functorially in `E` — see `tateEquiv_baseChange`.
theorem WeierstrassCurve.exists_variableChange_tateCurve :
    ∃ C : VariableChange k, C • tateCurve E.q = E :=
  sorry

/-! ### Functoriality

Now let `l` be a second nonarchimedean local field and let `k → l` be a morphism of fields
inducing the valuative relation on `k` from the one on `l` (the `ValuativeExtension`
hypothesis). The compatibility hypothesis is what makes the morphism continuous, hence
commute with the power series defining Tate's theory; it is automatic for `k`-embeddings
between algebraic extensions of `k` (by uniqueness of extensions of valuations over the
complete field `k`), but not for arbitrary abstract field morphisms.
-/

variable {l : Type*} [Field l] [ValuativeRel l] [TopologicalSpace l]
  [IsNonarchimedeanLocalField l] [Algebra k l] [ValuativeExtension k l]

-- The base change of E is elliptic. (Mathlib has this instance for `E.map f`, but
-- `WeierstrassCurve.baseChange` is a non-reducible `def`, so instance search cannot
-- see through it.)
instance : (E.baseChange l).IsElliptic :=
  inferInstanceAs (E.map (algebraMap k l)).IsElliptic

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] [TopologicalSpace l]
  [IsNonarchimedeanLocalField l] in
/-- A valuative extension maps the open unit disc into the open unit disc: the induced
map of value groups (`ValuativeExtension.mapValueGroupWithZero`) is strictly monotone. -/
theorem TateCurve.valuation_algebraMap_lt_one {q : k} (hq : valuation k q < 1) :
    valuation l (algebraMap k l q) < 1 := by
  simpa using ValuativeExtension.mapValueGroupWithZero_strictMono (A := k) (B := l) hq

/-- Evaluation of integral power series commutes with valuative extensions of
nonarchimedean local fields: the coefficients are (the same) integers on both sides, and
both evaluations are within `|q|^N` of the common `N`-th partial sum
(`valuation_evalInt_sub_sum_le`), whose bound transfers along the strictly monotone map
of value groups — no continuity argument is needed. -/
theorem TateCurve.evalInt_map (q : k) (hq : valuation k q < 1) (F : ℤ⟦X⟧) :
    algebraMap k l (evalInt q F) = evalInt (algebraMap k l q) F := by
  have hq' : valuation l (algebraMap k l q) < 1 := valuation_algebraMap_lt_one hq
  rw [← sub_eq_zero]
  by_contra h
  obtain ⟨N, hN⟩ := exists_pow_valuation_lt (algebraMap k l q) hq'
    (Units.mk0 _ ((valuation l).ne_zero_iff.mpr h))
  -- the image of the `k`-side partial sum is the `l`-side partial sum
  have hmapsum : algebraMap k l
      (∑ n ∈ Finset.range N, ((PowerSeries.coeff n F : ℤ) : k) * q ^ n) =
      ∑ n ∈ Finset.range N, ((PowerSeries.coeff n F : ℤ) : l) * (algebraMap k l q) ^ n := by
    rw [map_sum]
    exact Finset.sum_congr rfl fun n _ ↦ by rw [map_mul, map_pow, map_intCast]
  -- the `k`-side tail bound, transferred along the map of value groups
  have h1 : valuation l (algebraMap k l (evalInt q F) -
      ∑ n ∈ Finset.range N, ((PowerSeries.coeff n F : ℤ) : l) * (algebraMap k l q) ^ n) ≤
      valuation l (algebraMap k l q) ^ N := by
    rw [← hmapsum, ← map_sub]
    calc valuation l (algebraMap k l (evalInt q F -
            ∑ n ∈ Finset.range N, ((PowerSeries.coeff n F : ℤ) : k) * q ^ n))
        = ValuativeExtension.mapValueGroupWithZero k l (valuation k (evalInt q F -
            ∑ n ∈ Finset.range N, ((PowerSeries.coeff n F : ℤ) : k) * q ^ n)) :=
          (ValuativeExtension.mapValueGroupWithZero_valuation _).symm
      _ ≤ ValuativeExtension.mapValueGroupWithZero k l (valuation k q ^ N) :=
          ValuativeExtension.mapValueGroupWithZero_strictMono.monotone
            (valuation_evalInt_sub_sum_le q hq F N)
      _ = valuation l (algebraMap k l q) ^ N := by
          rw [map_pow, ValuativeExtension.mapValueGroupWithZero_valuation]
  -- the `l`-side tail bound
  have h2 := valuation_evalInt_sub_sum_le (algebraMap k l q) hq' F N
  -- ultrametrically, the difference is then smaller than its own valuation: absurd
  refine absurd ?_ (lt_irrefl (valuation l
    (algebraMap k l (evalInt q F) - evalInt (algebraMap k l q) F)))
  calc valuation l (algebraMap k l (evalInt q F) - evalInt (algebraMap k l q) F)
      = valuation l ((algebraMap k l (evalInt q F) -
          ∑ n ∈ Finset.range N, ((PowerSeries.coeff n F : ℤ) : l) * (algebraMap k l q) ^ n) -
        (evalInt (algebraMap k l q) F -
          ∑ n ∈ Finset.range N, ((PowerSeries.coeff n F : ℤ) : l) * (algebraMap k l q) ^ n)) := by
        congr 1
        ring
    _ ≤ max _ _ := Valuation.map_sub _ _ _
    _ ≤ valuation l (algebraMap k l q) ^ N := max_le h1 h2
    _ < _ := hN

/-- The construction of the Tate curve commutes on the nose with any valuative morphism:
its coefficients are power series in `q` with *integer* coefficients, and the partial
sums converge at matching rates on both sides (`TateCurve.evalInt_map`). The same is true
of the uniformisation `tateCurveEquiv` (a statement we defer, as it needs transport along
this equality).

On the hypothesis `|q| < 1`: the coefficient series `tateA₄`, `tateA₆` are `tsum`s, which
take *junk values* outside the open unit disc (the `tsum` of a non-summable family is
`0`, and terms with vanishing denominators `1 - qⁿ = 0` are the junk `x/0 = 0`). Without
the hypothesis this lemma would be a statement about the alignment of junk values across
two different fields: for `|q| > 1` it would hold by accident — each term of `tateA₄` has
size `|(n+1)³|`, which does not tend to `0`, so both sides are non-summable and both junk
to `0` — but for `|q| = 1` summability hinges on how well `qⁿ` approximates `1`, a
Diophantine condition on `q`, and transferring (non-)summability along `k → l` would
further require the image of `ValuativeExtension.mapValueGroupWithZero` to be cofinal in
the value group of `l` (true for local fields, by finiteness of ramification, but yet
another argument). None of this buys anything: every consumer feeds this lemma a Tate
parameter, which lies strictly inside the disc (`valuation_q_lt_one`). So the hypothesis
is free in practice, and keeps the statement the honest identity of convergent series
that it is in Silverman. -/
theorem WeierstrassCurve.tateCurve_baseChange (q : k) (hq : valuation k q < 1) :
    (tateCurve q)⁄l = tateCurve (algebraMap k l q) := by
  have hq' : valuation l (algebraMap k l q) < 1 := TateCurve.valuation_algebraMap_lt_one hq
  have h4 : algebraMap k l (tateA₄ q) = tateA₄ (algebraMap k l q) := by
    rw [tateA₄_eq_evalInt q hq, tateA₄_eq_evalInt _ hq', TateCurve.evalInt_map q hq]
  have h6 : algebraMap k l (tateA₆ q) = tateA₆ (algebraMap k l q) := by
    rw [tateA₆_eq_evalInt q hq, tateA₆_eq_evalInt _ hq', TateCurve.evalInt_map q hq]
  ext <;> simp [WeierstrassCurve.baseChange, tateCurve, h4, h6]

-- Claude says that the base change of E to l is still given by a minimal Weierstrass equation.
-- This uses the multiplicative reduction hypothesis (which makes `c₄` a unit): minimality by
-- itself is not preserved by ramified base change — `y² = x³ + p` is minimal over `ℚ_p` but not
-- over `ℚ_p(p^{1/6})`.
instance : (E.baseChange l).IsMinimal 𝒪[l] :=
  sorry

-- and it still has split multiplicative reduction. (The `IsMinimal` instance argument of
-- `HasSplitMultiplicativeReduction` is found from the preceding instance.)
instance : (E.baseChange l).HasSplitMultiplicativeReduction 𝒪[l] :=
  sorry

/-- The Tate parameter series commutes with valuative extensions: it is the evaluation of
an integral power series at `j⁻¹`, so this is a direct instance of `evalInt_map`. -/
theorem WeierstrassCurve.tateParameter_map {j : k} (hj : 1 < valuation k j) :
    tateParameter (algebraMap k l j) = algebraMap k l (tateParameter j) := by
  have hjinv : valuation k j⁻¹ < 1 := by
    rw [map_inv₀]
    exact inv_lt_one_of_one_lt₀ hj
  rw [show tateParameter j = TateCurve.evalInt j⁻¹ TateCurve.jInvReverse from rfl,
    show tateParameter (algebraMap k l j) =
      TateCurve.evalInt (algebraMap k l j)⁻¹ TateCurve.jInvReverse from rfl,
    TateCurve.evalInt_map j⁻¹ hjinv, map_inv₀]

-- The Tate parameter pushes forward under base change: `j` is functorial and the inverse
-- `j`-series has universal integer coefficients, so commutes with the extension.
theorem WeierstrassCurve.q_baseChange : (E.baseChange l).q = algebraMap k l E.q := by
  rw [show (E.baseChange l).q = tateParameter (E.baseChange l).j from rfl,
    show E.q = tateParameter E.j from rfl,
    show (E.baseChange l).j = algebraMap k l E.j from E.map_j (algebraMap k l),
    tateParameter_map E.one_lt_valuation_j]

-- The uniformisations of `E` and of its base change fit into a commutative diagram, but only
-- up to a sign `ε` which cannot in general be removed, whatever choices are made in
-- `tateEquiv`. It is tempting to think the diagrams must commute on the nose because the
-- theory is given by universal power series — and for the curves `tateCurve q` themselves
-- they do. But `tateEquiv` for a general `E` also involves the choice of one of the two
-- isomorphisms `C : tateCurve E.q ≅ E`, whose scaling parameter is a square root
-- `u₀ = ±√(c₆(E_q)c₄(E)/(c₆(E)c₄(E_q)))`, and no choice of square roots is Galois-natural.
-- Concretely: let `E₀/ℚ_p` have *non-split* multiplicative reduction, let `k := ℚ_{p²}`
-- (the unramified quadratic extension, which splits the reduction), `E := (E₀)_k`, and let
-- `σ ∈ Gal(k/ℚ_p)` be Frobenius. Take `l := k` with the `Algebra k l` structure given by
-- `σ` (legal: `σ` is valuative). Then `E.baseChange l = E` and both routes around the
-- diagram use the *same* uniformisation `E.tateEquiv` — no choice can distinguish them —
-- while `u₀² ∈ ℚ_p` is a nonsquare (otherwise `E₀` would be split), so `σ(u₀) = -u₀` and
-- the diagram anticommutes: `ε = -1` is forced.
-- (When the morphism is `k`-linear the sign disappears: see `tateEquiv_galois` below.)
variable [DecidableEq k] [DecidableEq l] in
theorem WeierstrassCurve.tateEquiv_baseChange :
    ∃ ε : ℤˣ, ∀ u : kˣ,
      Affine.Point.baseChange (W' := E) k l (E.tateEquiv (Additive.ofMul ↑u)) =
        (ε : ℤ) • (E.baseChange l).tateEquiv
          (Additive.ofMul
            (Units.map (algebraMap k l).toMonoidHom u :
              lˣ ⧸ Subgroup.zpowers (E.baseChange l).qUnit)) :=
  sorry

-- Galois equivariance: for a `k`-*algebra* automorphism `σ` of `l` the diagram commutes
-- with no sign, because `E` and a choice of uniformisation for it already live over `k`,
-- and `σ` fixes `k`. This is the statement needed to compute the Galois action on the
-- torsion of `E`. The continuity hypothesis on `σ` is automatic when `l/k` is algebraic
-- (e.g. a finite extension), by uniqueness of extensions of valuations.
variable [DecidableEq l] in
theorem WeierstrassCurve.tateEquiv_galois (σ : l ≃ₐ[k] l) (hσ : Continuous σ) (u : lˣ) :
    Affine.Point.map (W' := E) σ.toAlgHom
        ((E.baseChange l).tateEquiv (Additive.ofMul ↑u) : (E⁄l).Point) =
      (E.baseChange l).tateEquiv
        (Additive.ofMul ↑(Units.map σ.toAlgHom.toRingHom.toMonoidHom u)) :=
  sorry

/-! ### Torsion and the Weil pairing

Passing to the limit over the finite subextensions of a separable closure `Ω` of `k`, the
uniformisations above glue to a Galois-equivariant uniformisation `E(Ω) ≅ Ωˣ/qᶻ`. The
`N`-torsion of `Ωˣ/qᶻ` is generated by the `N`-th roots of unity and (the classes of) the
`N`-th roots of `q`, so the uniformisation identifies the `N`-torsion of `E` explicitly:
this is how one computes the Galois representations attached to `E`.

The identification is compatible with the Weil pairing: with a suitable sign convention in
the definition of the Weil pairing `e_N`, we have `e_N(ζ, q^{1/N}) = ζ` for every `N`-th
root of unity `ζ` and every `N`-th root `q^{1/N}` of `q`, where on the left-hand side units
are identified with points of `E` via the uniformisation. This is the content of
`weilPairing_tatePoint` below; see the comment there for exactly what this does and
does not pin down.
-/

-- Now let `Ω` be a separable closure of `k`. It is not itself a nonarchimedean local field
-- (it is not complete), so it does not fit the framework above; but `E(Ω)` is the union of
-- the `E(l)` over the finite subextensions `l/k` of `Ω`, and Tate's theory applies to each.
variable (Ω : Type*) [Field Ω] [Algebra k Ω] [IsSepClosed Ω] [Algebra.IsSeparable k Ω]

-- the base change of E to Ω is elliptic (same remark as for `l` above)
instance : (E.baseChange Ω).IsElliptic :=
  inferInstanceAs (E.map (algebraMap k Ω)).IsElliptic

/-- The image of the Tate parameter in a separable closure `Ω` of `k`, as a unit. (`Ω` is
not a nonarchimedean local field, so this is not literally `(E.baseChange Ω).qUnit`.) -/
noncomputable def WeierstrassCurve.qUnitSepClosure : Ωˣ :=
  Units.map (algebraMap k Ω).toMonoidHom E.qUnit

-- `DecidableEq Ω` is needed for the group law on `(E⁄Ω).Point`
variable [DecidableEq Ω]

/-- Tate's uniformisation over a separable closure `Ω` of `k`: the union of the
uniformisations of the `E(l)` over the finite subextensions `l/k` of `Ω`. Its sign is
pinned to that of `tateEquiv` by `tatePoint_baseChange`. -/
noncomputable def WeierstrassCurve.tateEquivSepClosure :
    Additive (Ωˣ ⧸ Subgroup.zpowers (E.qUnitSepClosure Ω)) ≃+ (E⁄Ω).Point :=
  sorry

/-- The point of `E(Ω)` corresponding to a unit `x ∈ Ωˣ` under Tate's uniformisation. -/
noncomputable def WeierstrassCurve.tatePoint (x : Ωˣ) : (E⁄Ω).Point :=
  E.tateEquivSepClosure Ω (Additive.ofMul ↑x)

-- The uniformisations over `k` and over `Ω` commute on the nose, not merely up to sign:
-- the inclusion `k → Ω` is a `k`-algebra map, so this is an instance of the same
-- phenomenon as `tateEquiv_galois`, not of `tateEquiv_baseChange`. This statement is what
-- pins the sign of `tateEquivSepClosure` to the sign of `tateEquiv`.
variable [DecidableEq k] in
theorem WeierstrassCurve.tatePoint_baseChange (u : kˣ) :
    Affine.Point.baseChange (W' := E) k Ω (E.tateEquiv (Additive.ofMul ↑u)) =
      E.tatePoint Ω (Units.map (algebraMap k Ω).toMonoidHom u) :=
  sorry

-- Galois equivariance of the uniformisation over `Ω`: no continuity hypothesis is needed
-- this time, since `Ω/k` is algebraic.
theorem WeierstrassCurve.tatePoint_galois (σ : Ω ≃ₐ[k] Ω) (u : Ωˣ) :
    Affine.Point.map (W' := E) σ.toAlgHom (E.tatePoint Ω u) =
      E.tatePoint Ω (Units.map σ.toAlgHom.toRingHom.toMonoidHom u) :=
  sorry

/-- `N`-th roots of unity give `N`-torsion points of `E` under Tate's uniformisation. -/
theorem WeierstrassCurve.tatePoint_mem_torsionBy_of_mem_rootsOfUnity {N : ℕ} {ζ : Ωˣ}
    (hζ : ζ ∈ rootsOfUnity N Ω) :
    E.tatePoint Ω ζ ∈ AddSubgroup.torsionBy (E⁄Ω).Point (N : ℤ) :=
  sorry

/-- `N`-th roots of the Tate parameter give `N`-torsion points of `E` under Tate's
uniformisation. -/
theorem WeierstrassCurve.tatePoint_mem_torsionBy_of_pow_eq {N : ℕ} {r : Ωˣ}
    (hr : r ^ N = E.qUnitSepClosure Ω) :
    E.tatePoint Ω r ∈ AddSubgroup.torsionBy (E⁄Ω).Point (N : ℤ) :=
  sorry

-- `weilPairing` and `tateEquiv`/`tateEquivSepClosure` are all currently `sorry`ed data,
-- each pinned down mathematically only up to a sign. The following compatibility, due to
-- Tate, is the demand that these signs be chosen coherently. Note that it constrains the
-- sign convention in the *Weil pairing* (about which the literature does not agree) in
-- terms of the uniformisation, and not vice versa: by bilinearity `e_N(-P, -Q) = e_N(P, Q)`,
-- so the demand is insensitive to negating `tateEquivSepClosure`.
theorem WeierstrassCurve.weilPairing_tatePoint (N : ℕ) [NeZero (N : Ω)] {ζ r : Ωˣ}
    (hζ : ζ ∈ rootsOfUnity N Ω) (hr : r ^ N = E.qUnitSepClosure Ω) :
    (E⁄Ω).weilPairing Ω N
      ⟨E.tatePoint Ω ζ, E.tatePoint_mem_torsionBy_of_mem_rootsOfUnity Ω hζ⟩
      ⟨E.tatePoint Ω r, E.tatePoint_mem_torsionBy_of_pow_eq Ω hr⟩ =
    Additive.ofMul (⟨ζ, hζ⟩ : rootsOfUnity N Ω) :=
  sorry
