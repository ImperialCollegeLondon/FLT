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
  have hfin : ∀ s : Finset ℕ, evalInt q (∏ n ∈ s, ((1 : ℤ⟦X⟧) - X ^ (n + 1))) =
      ∏ n ∈ s, (1 - q ^ (n + 1)) := by
    intro s
    induction s using Finset.cons_induction with
    | empty => simp
    | cons a s ha ih =>
      rw [Finset.prod_cons, Finset.prod_cons, evalInt_mul q hq, ih,
        evalInt_sub (summable_evalInt q hq 1) (summable_evalInt q hq (X ^ (a + 1))),
        evalInt_one, evalInt_pow q hq, evalInt_X]
  -- the core: the evaluated partial products converge to the evaluated formal product
  have hprod : HasProd (fun n : ℕ ↦ 1 - q ^ (n + 1))
      (evalInt q (∏' n : ℕ, ((1 : ℤ⟦X⟧) - X ^ (n + 1)))) := by
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
      (evalInt q (∏' n : ℕ, ((1 : ℤ⟦X⟧) - X ^ (n + 1))) ^ j) := by
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

/-- Silverman, ATAEC V.1.1(a): for `u` not a power of `q`, the pair `(X(u, q), Y(u, q))` is
a nonsingular point of the Tate curve `E_q`. The equation `Y² + XY = X³ + a₄X + a₆` itself
is `TateCurve.weierstrass_equation`; here we transport it to `k` and add nonsingularity. -/
theorem WeierstrassCurve.tateCurve_nonsingular (q : kˣ) (hq : valuation k (q : k) < 1)
    (u : kˣ) (hu : u ∉ Subgroup.zpowers q) :
    ((tateCurve (q : k))⁄k).Nonsingular (tateX (u : k) (q : k)) (tateY (u : k) (q : k)) :=
  sorry

open scoped Classical in
/-- The point of `E_q(k)` attached to a unit `u ∈ kˣ` by Tate's uniformisation: the affine
point `(X(u, q), Y(u, q))` when `u` is not a power of `q`, and the point at infinity `O`
(the class of `qᶻ`) otherwise. This descends to `tateCurveEquiv` below. -/
noncomputable def WeierstrassCurve.tateCurvePoint (q : kˣ) (hq : valuation k (q : k) < 1)
    (u : kˣ) : ((tateCurve (q : k))⁄k).Point :=
  if hu : u ∈ Subgroup.zpowers q then .zero
  else .some (tateX (u : k) (q : k)) (tateY (u : k) (q : k)) (tateCurve_nonsingular q hq u hu)

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
  toFun m := Quotient.liftOn' (Additive.toMul m) (tateCurvePoint q hq) (fun _ _ _ => sorry)
  invFun := sorry
  left_inv := sorry
  right_inv := sorry
  map_add' := sorry

-- `tateParameter` — the inverse of `q ↦ j(q)` of Silverman, ATAEC V.5.2, by which the
-- Tate parameter is *defined* below, choice-freely — is constructed in
-- `FLT.KnownIn1980s.EllipticCurves.TateParameter` (imported above) as the evaluation at
-- `j⁻¹` of an explicit integral power series. Here we state its interaction with the
-- valuation and with `tateJ` (the two halves of V.5.2).

theorem WeierstrassCurve.tateParameter_ne_zero {j : k} (hj : 1 < valuation k j) :
    tateParameter j ≠ 0 :=
  sorry

theorem WeierstrassCurve.valuation_tateParameter_lt_one {j : k} (hj : 1 < valuation k j) :
    valuation k (tateParameter j) < 1 :=
  sorry

/-- `tateParameter` is a right inverse of `tateJ`: the *existence* half of Silverman,
ATAEC V.5.2. -/
theorem WeierstrassCurve.tateJ_tateParameter {j : k} (hj : 1 < valuation k j) :
    tateJ (tateParameter j) = j :=
  sorry

/-- `tateParameter` is a left inverse of `tateJ` on the punctured open unit disc: the
*uniqueness* half of Silverman, ATAEC V.5.2, stated choice-freely as a round-trip
identity — if `q₁, q₂` both lie in the punctured disc and `tateJ q₁ = tateJ q₂`, apply
`tateParameter` to both sides. -/
theorem WeierstrassCurve.tateParameter_tateJ {q : k} (hq0 : q ≠ 0)
    (hq1 : valuation k q < 1) : tateParameter (tateJ q) = q :=
  sorry

/-- An elliptic curve over `k` with split multiplicative reduction has non-integral
`j`-invariant, `|j(E)| > 1`: indeed `v(j) = -v(Δ_min) < 0`, since `c₄` is a unit when the
reduction is multiplicative. -/
theorem WeierstrassCurve.one_lt_valuation_j (E : WeierstrassCurve k) [E.IsElliptic]
    [E.IsMinimal 𝒪[k]] [E.HasSplitMultiplicativeReduction 𝒪[k]] :
    1 < valuation k E.j :=
  sorry

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
  rintro q' ⟨hq0, hq1, hj⟩
  rw [← tateParameter_tateJ hq0 hq1, ← hj]
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

-- The construction of the Tate curve commutes on the nose with any valuative morphism:
-- its coefficients are power series in `q` with *integer* coefficients, and a valuative
-- morphism is continuous, so preserves the sums. The same is true of the uniformisation
-- `tateCurveEquiv` (a statement we defer, as it needs transport along this equality).
theorem WeierstrassCurve.tateCurve_baseChange (q : k) :
    (tateCurve q)⁄l = tateCurve (algebraMap k l q) :=
  sorry

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

-- The Tate parameter pushes forward under base change.
theorem WeierstrassCurve.q_baseChange : (E.baseChange l).q = algebraMap k l E.q :=
  sorry

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
