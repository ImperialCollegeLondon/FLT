/-
Copyright (c) 2026 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, William Coram
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Reduction

/-!
# A minimality criterion for Weierstrass equations

Material destined for Mathlib (`Mathlib.AlgebraicGeometry.EllipticCurve.Reduction`).

This file proves the unit-`c₄` case of the Kraus–Laska minimality criterion
(`WeierstrassCurve.isMinimal_of_valuation_c₄_eq_one`): an integral Weierstrass equation
over the fraction field of a discrete valuation ring `R` whose `c₄` has adic valuation `1`
is minimal. This is the special case "`v(c₄) < 4` or `v(Δ) < 12` implies minimal" of
Silverman, *The Arithmetic of Elliptic Curves*, Remark VII.1.1, restricted to `v(c₄) = 0`;
it is the piece of reduction theory needed to show that multiplicative reduction is
preserved under base change (a Weierstrass equation with multiplicative reduction has
`v(c₄) = 1`, and this property visibly transfers along any extension, forcing minimality
of the base change).

The hypothesis is stated at the field level — via the adic valuation of `W.c₄ : K` — to
match mathlib's phrasing of `WeierstrassCurve.HasMultiplicativeReduction`, whose
`multiplicativeReduction` field is exactly `(maximalIdeal R).valuation K W.c₄ = 1`.
-/

@[expose] public section

namespace WeierstrassCurve

variable (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

open IsDiscreteValuationRing IsDedekindDomain.HeightOneSpectrum

/-- An integral Weierstrass equation whose `c₄` has adic valuation `1` is minimal: the
unit-`c₄` case of the Kraus–Laska criterion (Silverman AEC, Remark VII.1.1). -/
theorem isMinimal_of_valuation_c₄_eq_one (W : WeierstrassCurve K) [IsIntegral R W]
    (hc₄ : (maximalIdeal R).valuation K W.c₄ = 1) :
    IsMinimal R W := by
  refine ⟨⟨by simpa using ‹IsIntegral R W›, ?_⟩⟩
  intro C hC _
  simp only [one_smul, ← Subtype.coe_le_coe, valuation_Δ_aux_eq_of_isIntegral R (C • W),
    valuation_Δ_aux_eq_of_isIntegral R W]
  have hint : (maximalIdeal R).valuation K (C • W).c₄ ≤ 1 := by
    simpa [← integralModel_c₄_eq R (C • W)] using valuation_le_one _ _
  rw [variableChange_c₄, map_mul, map_pow, hc₄, mul_one] at hint
  simpa [variableChange_Δ, map_mul, map_pow] using mul_le_of_le_one_left'
    (pow_le_one' ((pow_le_one_iff (by norm_num)).mp hint) 12)

end WeierstrassCurve
