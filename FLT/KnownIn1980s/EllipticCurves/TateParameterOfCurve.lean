/-
Copyright (c) 2026 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, William Coram, Samuel Yin
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Reduction
public import Mathlib.NumberTheory.LocalField.Basic
public import FLT.KnownIn1980s.EllipticCurves.TateParameter
public import FLT.KnownIn1980s.EllipticCurves.ReductionBaseChange

/-!

# The Tate parameter of an elliptic curve

Let `E/k` be an elliptic curve, given by a minimal Weierstrass equation with split
multiplicative reduction over a nonarchimedean local field `k`. Its `j`-invariant is
non-integral, `|j(E)| > 1` (`one_lt_valuation_j`: indeed `v(j) = -v(Δ) < 0` since `c₄` is a
unit when the reduction is multiplicative), and its *Tate parameter*
`E.q := tateParameter E.j` — the evaluation at `j(E)⁻¹` of the explicit integral inverse
`j`-series constructed in `FLT.KnownIn1980s.EllipticCurves.TateParameter` — is the unique
`q ∈ k` with `0 < |q| < 1` (`q_ne_zero`, `valuation_q_lt_one`) whose Tate curve has
`j`-invariant `j(E)`.

This file sits strictly upstream of the Tate-curve theory proper: downstream,
`FLT.KnownIn1980s.EllipticCurves.SplitMultiplicativeDescent` proves that `E` is isomorphic
to `tateCurve E.q` by a change of Weierstrass variables
(`exists_variableChange_tateCurve`), and `FLT.KnownIn1980s.EllipticCurves.TateCurve`
assembles Tate's uniformisation `E(k) ≅ kˣ/qᶻ` from it.
-/

@[expose] public section

open ValuativeRel -- `𝒪[k]` notation for the ring of integers of `k`, and `valuation`

-- let k be a nonarchimedean local field
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k]

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

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
/-- An elliptic curve with non-integral `j`-invariant has `c₄ ≠ 0`: otherwise `j = 0`. -/
theorem WeierstrassCurve.c₄_ne_zero_of_one_lt_valuation_j (W : WeierstrassCurve k)
    [W.IsElliptic] (hj : 1 < valuation k W.j) :
    W.c₄ ≠ 0 := by
  intro h0
  rw [show W.j = (↑(W.Δ'⁻¹) : k) * W.c₄ ^ 3 from rfl, h0] at hj
  simp at hj

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
/-- An elliptic curve with non-integral `j`-invariant has `c₆ ≠ 0`: otherwise
`c₄³ = 1728Δ` by the relation `1728Δ = c₄³ - c₆²`, so `j = 1728`, which is integral. -/
theorem WeierstrassCurve.c₆_ne_zero_of_one_lt_valuation_j (W : WeierstrassCurve k)
    [W.IsElliptic] (hj : 1 < valuation k W.j) :
    W.c₆ ≠ 0 := by
  intro h0
  have hc₄ : W.c₄ ^ 3 = 1728 * W.Δ := by linear_combination -W.c_relation + W.c₆ * h0
  have hj1728 : W.j = 1728 := by
    rw [show W.j = (↑(W.Δ'⁻¹) : k) * W.c₄ ^ 3 from rfl, hc₄, ← W.coe_Δ', mul_left_comm,
      Units.inv_mul, mul_one]
  rw [hj1728] at hj
  have h1728 : valuation k (1728 : k) ≤ 1 := by
    simpa using ValuativeRel.valuation_natCast_le_one (R := k) 1728
  exact absurd hj (not_lt.mpr h1728)

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

-- Let E/k be an elliptic curve, given by a minimal Weierstrass equation, with split
-- multiplicative reduction (minimality is part of `HasSplitMultiplicativeReduction`)
variable (E : WeierstrassCurve k) [E.IsElliptic] [E.HasSplitMultiplicativeReduction 𝒪[k]]

theorem WeierstrassCurve.q_ne_zero : E.q ≠ 0 :=
  tateParameter_ne_zero E.one_lt_valuation_j

/-- The Tate parameter has norm less than `1`. -/
theorem WeierstrassCurve.valuation_q_lt_one : valuation k E.q < 1 :=
  valuation_tateParameter_lt_one E.one_lt_valuation_j

/-- The Tate parameter as an element of `kˣ`. -/
noncomputable def WeierstrassCurve.qUnit : kˣ :=
  Units.mk0 E.q E.q_ne_zero
