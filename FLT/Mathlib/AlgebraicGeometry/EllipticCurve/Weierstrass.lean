/-
Copyright (c) 2026 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Claude
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass

/-!
# Complements on Weierstrass curves

Material for `Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass`: ellipticity of base
changes, the discriminant identity behind split multiplicative reduction, `c₆ = 0 ↔ j = 1728`,
and `a₁ ≠ 0 ∨ a₃ ≠ 0` in characteristic `2`.
-/

@[expose] public section

namespace WeierstrassCurve

universe u

/-- The base change of an elliptic curve is an elliptic curve. Restates the instance for
`WeierstrassCurve.map`, which does not apply to `baseChange` directly since the latter is a
non-reducible definition. -/
instance {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] (W : WeierstrassCurve R)
    [W.IsElliptic] : (W.baseChange A).IsElliptic :=
  inferInstanceAs (W.map (algebraMap R A)).IsElliptic

section

variable {A : Type*} [CommRing A] (E : WeierstrassCurve A)

/-- The discriminant of the node's tangent polynomial `c₄ T² + a₁ c₄ T - (54 b₆ - 3 b₂ b₄ + a₂ c₄)`
(the quadratic controlling split multiplicative reduction) equals `-c₄ c₆`. Hence the tangent
directions at the node are rational over the residue field exactly when `-c₄ c₆` is a square there;
twisting by `(t, n)` multiplies `-c₄ c₆` by `(t² - 4n)⁵ = (t² - 4n)⁴ · (t² - 4n)`, i.e. by the
twisting parameter up to a square (see `c₄_quadraticTwistOf`, `c₆_quadraticTwistOf`). -/
theorem splitPolynomial_discrim :
    (E.a₁ * E.c₄) ^ 2 + 4 * E.c₄ * (54 * E.b₆ - 3 * E.b₂ * E.b₄ + E.a₂ * E.c₄)
      = -(E.c₄ * E.c₆) := by
  simp only [c₄, c₆, b₂, b₄, b₆]; ring

end

variable {K : Type u} [Field K] (E : WeierstrassCurve K)

/-- In characteristic `2`, an elliptic curve has `a₁ ≠ 0` or `a₃ ≠ 0`: otherwise `a₁ = a₃ = 0`
makes the partial derivative `∂/∂y = 2y + a₁x + a₃` vanish identically, so `Δ = 0`. -/
lemma a₁_ne_zero_or_a₃_ne_zero_of_two_eq_zero [E.IsElliptic] (h2 : (2 : K) = 0) :
    E.a₁ ≠ 0 ∨ E.a₃ ≠ 0 := by
  by_contra! h
  exact E.isUnit_Δ.ne_zero (by rw [Δ, b₈, b₆, b₄, b₂, h.1, h.2]; grobner)

/-- `c₆(E) = 0` if and only if `j(E) = 1728`, by the relation `1728·Δ = c₄³ - c₆²`. This is the
analogue for `j = 1728` of `WeierstrassCurve.j_eq_zero_iff` (`j = 0 ↔ c₄ = 0`). -/
lemma c₆_eq_zero_iff_j_eq_1728 [E.IsElliptic] : E.c₆ = 0 ↔ E.j = 1728 := by
  have h : E.c₆ ^ 2 = E.c₄ ^ 3 - 1728 * E.Δ := by linear_combination E.c_relation
  rw [← sq_eq_zero_iff, h, sub_eq_zero, j, Units.inv_mul_eq_iff_eq_mul, coe_Δ',
    mul_comm E.Δ 1728]

section

variable (L : Type*) [Field L] [Algebra K L]
variable (M : Type*) [Field M] [Algebra K M] [Algebra L M] [IsScalarTower K L M]

lemma baseChange_map_algebraMap (V : WeierstrassCurve K) :
    (V.baseChange L).map (algebraMap L M) = V.baseChange M :=
  V.map_baseChange (IsScalarTower.toAlgHom K L M)

end

end WeierstrassCurve

end
