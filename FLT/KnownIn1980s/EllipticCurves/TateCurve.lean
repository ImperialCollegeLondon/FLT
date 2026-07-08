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
public import FLT.KnownIn1980s.EllipticCurves.TateCurveBaseChange
public import FLT.KnownIn1980s.EllipticCurves.ReductionBaseChange

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

end TateCurve

-- let k be a nonarchimedean local field
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k]

-- `DecidableEq k` is needed for the group law on the points
variable [DecidableEq k] in
/-- Tate's uniformisation of the Tate curve `E_q`, given by the explicit power series
`x = X(u, q)`, `y = Y(u, q)` of Silverman, ATAEC V.3. Unlike `tateEquiv` below, this
involves no choices at all: it commutes on the nose with every valuative field morphism
(see `tateCurve_baseChange` for the equation-level statement). -/
noncomputable def WeierstrassCurve.tateCurveEquiv (q : kˣ) (hq : valuation k (q : k) < 1) :
    Additive (kˣ ⧸ Subgroup.zpowers q) ≃+ ((tateCurve (q : k))⁄k).Point :=
  sorry

-- `tateParameter` — the inverse of `q ↦ j(q)` of Silverman, ATAEC V.5.2, by which the
-- Tate parameter is *defined* below, choice-freely — is constructed in
-- `FLT.KnownIn1980s.EllipticCurves.TateParameter` (imported above) as the evaluation at
-- `j⁻¹` of an explicit integral power series. Here we state its interaction with the
-- valuation.

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] in
lemma WeierstrassCurve.tateParameter_eq {j : k} : WeierstrassCurve.tateParameter j =
    TateCurve.evalInt j⁻¹ TateCurve.jInvReverse := by
  rfl

/-- The Tate parameter of `j` has valuation exactly `|j|⁻¹`: the leading term `j⁻¹` of
the inverse series `q = j⁻¹ + 744j⁻² + ⋯` dominates ultrametrically. -/
theorem WeierstrassCurve.valuation_tateParameter_eq {j : k} (hj : 1 < valuation k j) :
    valuation k (tateParameter j) = (valuation k j)⁻¹ := by
  have hj0 : j ≠ 0 := by
    rintro rfl
    simp [map_zero] at hj
  have h := TateCurve.valuation_evalInt_eq j⁻¹ (inv_ne_zero hj0)
    (by simpa [map_inv₀] using inv_lt_one_of_one_lt₀ hj) TateCurve.constantCoeff_jInvReverse
    TateCurve.coeff_one_jInvReverse
  rw [WeierstrassCurve.tateParameter_eq, h, map_inv₀]

theorem WeierstrassCurve.tateParameter_ne_zero {j : k} (hj : 1 < valuation k j) :
    tateParameter j ≠ 0 := by
  intro h
  have heq := valuation_tateParameter_eq hj
  rw [h, map_zero] at heq
  exact inv_ne_zero (ne_of_gt (lt_trans zero_lt_one hj)) heq.symm

theorem WeierstrassCurve.valuation_tateParameter_lt_one {j : k} (hj : 1 < valuation k j) :
    valuation k (tateParameter j) < 1 := by
  simpa [valuation_tateParameter_eq hj] using inv_lt_one_of_one_lt₀ hj

-- The next few lemmas transfer `mathlib`'s reduction-theoretic facts (stated for the adic
-- valuation of the discrete valuation ring `𝒪[k]`) to the canonical valuation of `k`,
-- through unit and maximal-ideal membership in `𝒪[k]`.

/-- An elliptic curve over `k` with bad (here multiplicative) reduction has discriminant of
valuation less than `1`: the discriminant of the integral model lies in the maximal ideal. -/
theorem WeierstrassCurve.valuation_Δ_lt_one (E : WeierstrassCurve k)
    [E.HasMultiplicativeReduction 𝒪[k]] :
    valuation k E.Δ < 1 := by
  have hbad := HasMultiplicativeReduction.badReduction (R := 𝒪[k]) (W := E)
  rw [← integralModel_Δ_eq 𝒪[k] E] at hbad ⊢
  exact adicValuation_lt_one_iff.mp hbad

/-- An elliptic curve over `k` with multiplicative reduction has `c₄` of valuation exactly
`1`: `c₄` of the integral model is a unit of `𝒪[k]`. -/
theorem WeierstrassCurve.valuation_c₄_eq_one (E : WeierstrassCurve k)
    [E.HasMultiplicativeReduction 𝒪[k]] :
    valuation k E.c₄ = 1 := by
  have hmul := HasMultiplicativeReduction.multiplicativeReduction (R := 𝒪[k]) (W := E)
  rw [← integralModel_c₄_eq 𝒪[k] E] at hmul ⊢
  exact adicValuation_eq_one_iff.mp hmul

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
/-- The discriminant of an elliptic curve has nonzero valuation. -/
theorem WeierstrassCurve.valuation_Δ_ne_zero (E : WeierstrassCurve k) [E.IsElliptic] :
    valuation k E.Δ ≠ 0 := by
  rw [(valuation k).ne_zero_iff, ← E.coe_Δ']
  exact Units.ne_zero _

/-- An elliptic curve over `k` with multiplicative reduction has `|j| = |c₄|³/|Δ| = |Δ|⁻¹`. -/
theorem WeierstrassCurve.valuation_j_eq (E : WeierstrassCurve k) [E.IsElliptic]
    [E.HasMultiplicativeReduction 𝒪[k]] :
    valuation k E.j = (valuation k E.Δ)⁻¹ := by
  rw [show E.j = (↑(E.Δ'⁻¹) : k) * E.c₄ ^ 3 from rfl, map_mul, map_pow,
    E.valuation_c₄_eq_one, one_pow, mul_one, Units.val_inv_eq_inv_val, map_inv₀, E.coe_Δ']

/-- An elliptic curve over `k` with split multiplicative reduction has non-integral
`j`-invariant, `|j(E)| > 1`: indeed `v(j) = -v(Δ_min) < 0`, since `c₄` is a unit when the
reduction is multiplicative. -/
theorem WeierstrassCurve.one_lt_valuation_j (E : WeierstrassCurve k) [E.IsElliptic]
    [E.HasSplitMultiplicativeReduction 𝒪[k]] :
    1 < valuation k E.j := by
  rw [E.valuation_j_eq]
  exact (one_lt_inv₀ (zero_lt_iff.mpr E.valuation_Δ_ne_zero)).mpr E.valuation_Δ_lt_one

/-- The Tate parameter of an elliptic curve `E`, given by a minimal Weierstrass equation with
split multiplicative reduction over a nonarchimedean local field `k`: the unique element
`q` of `k` with `0 < |q| < 1` such that `j(E) = j(q) = q⁻¹ + 744 + 196884q + ⋯`, defined
directly (with no appeal to choice) as `tateParameter E.j`, the inverse `j`-series
evaluated at `j(E)`. Equivalently, the unique `q` such that `E(k̄)` is Galois-equivariantly
isomorphic to `k̄ˣ/q^ℤ`. (The bare existence of an abstract isomorphism `E(k) ≅ kˣ/q^ℤ`
would not pin down `q`: already over `ℚ_p` the groups `ℚ_pˣ/p^ℤ` and `ℚ_pˣ/(p(1+p))^ℤ`
are isomorphic, even topologically.) -/
noncomputable def WeierstrassCurve.q (E : WeierstrassCurve k) [E.IsElliptic] : k :=
  tateParameter E.j

-- Let E/k be an elliptic curve, given by a minimal Weierstrass equation,
-- with split multiplicative reduction
variable (E : WeierstrassCurve k) [E.IsElliptic] [E.HasSplitMultiplicativeReduction 𝒪[k]]
-- [E.IsMinimal 𝒪[k]] - caused lake lint errors; re-add back later

theorem WeierstrassCurve.q_ne_zero : E.q ≠ 0 :=
  tateParameter_ne_zero E.one_lt_valuation_j

/-- The Tate parameter has norm less than `1`. -/
theorem WeierstrassCurve.valuation_q_lt_one : valuation k E.q < 1 :=
  valuation_tateParameter_lt_one E.one_lt_valuation_j

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

open scoped ArithmeticFunction.sigma in
/-- The Lambert series rearrangement `∑_{n≥1} n³qⁿ/(1-qⁿ) = ∑_{n≥1} σ₃(n)qⁿ` for
`|q| < 1`: the defining series of `tateA₄` is the evaluation of the formal series
`a₄(q) = -5s₃(q) ∈ ℤ⟦q⟧`. -/
theorem WeierstrassCurve.tateA₄_eq_evalInt (q : k) (hq : valuation k q < 1) :
    tateA₄ q = TateCurve.evalInt q TateCurve.a₄Formal := by
  have hF : ∀ n, PowerSeries.coeff n TateCurve.a₄Formal
      = ∑ d ∈ n.divisors, -5 * (d : ℤ) ^ 3 := by
    intro n
    rw [TateCurve.coeff_a₄Formal, ArithmeticFunction.sigma_apply]
    push_cast
    rw [Finset.mul_sum]
  rw [← TateCurve.tsum_lambert_eq_evalInt q hq _ hF]
  simp only [tateA₄]
  rw [← tsum_mul_left]
  exact tsum_congr fun m ↦ by push_cast; ring

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
  -- the coefficients of `a₆Formal` are the divisor sums of `c`: the divisor sum commutes
  -- with the exact division by `12`
  have hF : ∀ N, PowerSeries.coeff N TateCurve.a₆Formal = ∑ d ∈ N.divisors, c d := by
    intro N
    rw [TateCurve.coeff_a₆Formal]
    symm
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
  rw [← TateCurve.tsum_lambert_eq_evalInt q hq c hF]
  simp only [tateA₆]
  refine tsum_congr fun m ↦ ?_
  simp only [hc]
  push_cast
  ring

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

-- The base change of `E` to `l` is still given by a minimal Weierstrass equation. This uses the
-- multiplicative reduction hypothesis (which makes `c₄` a unit): minimality by itself is not
-- preserved by ramified base change — `y² = x³ + p` is minimal over `ℚ_p` but not over
-- `ℚ_p(p^{1/6})`. See `WeierstrassCurve.isMinimal_baseChange` in `ReductionBaseChange`.
instance : (E.baseChange l).IsMinimal 𝒪[l] :=
  E.isMinimal_baseChange

-- and it still has split multiplicative reduction, via
-- `WeierstrassCurve.hasSplitMultiplicativeReduction_baseChange` in `ReductionBaseChange`
-- (from which the preceding `IsMinimal` also follows by class-parent projection).
instance : (E.baseChange l).HasSplitMultiplicativeReduction 𝒪[l] :=
  E.hasSplitMultiplicativeReduction_baseChange

/-- The Tate parameter series commutes with valuative extensions: it is the evaluation of
an integral power series at `j⁻¹`, so this is a direct instance of `evalInt_map`. -/
theorem WeierstrassCurve.tateParameter_map {j : k} (hj : 1 < valuation k j) :
    tateParameter (algebraMap k l j) = algebraMap k l (tateParameter j) := by
  have hjinv : valuation k j⁻¹ < 1 := by
    simpa [map_inv₀] using inv_lt_one_of_one_lt₀ hj
  simp_rw [WeierstrassCurve.tateParameter_eq, TateCurve.evalInt_map j⁻¹ hjinv, map_inv₀]

-- The Tate parameter pushes forward under base change.
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
