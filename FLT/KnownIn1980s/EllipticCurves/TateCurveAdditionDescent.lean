/-
Copyright (c) 2026 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, William Coram, Samuel Yin
-/
module

public import FLT.KnownIn1980s.EllipticCurves.TateCurveAddition
public import FLT.KnownIn1980s.EllipticCurves.TateCurveDescent

/-!

# Descent of the Tate curve chord law to arbitrary fields

The formal chord-law identities `TateCurve.chord_x`, `TateCurve.chord_y` (proved in
`TateCurveAddition` over `ℚ(u₁, u₂)` by complex-analytic methods) descend to every field
`K` at every pair `v₁, v₂ ∈ K` with `v₁, v₂ ∉ {0, 1}` and `v₁v₂ ≠ 1` — in particular to
nonarchimedean local fields of any residue characteristic. This is the two-variable
analogue of `TateCurveDescent`, with the initial coefficient ring
`ℤ[t₁, t₂][(t₁t₂(1-t₁)(1-t₂)(1-t₁t₂))⁻¹]`: the `q`-coefficients of all six series
`X(u₁), X(u₂), X(u₁u₂), Y(u₁), Y(u₂), Y(u₁u₂)` lie in it, it injects into `ℚ(u₁, u₂)`
by `(t₁, t₂) ↦ (u₁, u₂)`, and it maps to `K` at every admissible pair by the universal
property of the localization. Note that no factor `t₁ - t₂` is inverted: the polynomial
form of the chord law has no denominators beyond those of the series themselves.

The deliverables `chord_x_field` and `chord_y_field` are stated purely in terms of the
`K`-coefficient series `TateCurve.XField`/`TateCurve.YField` of `TateCurveDescent`, at
the three points `v₁, v₂, v₁v₂`; this is the form consumed on the local-field side (in
`TateCurveUniformisation`). We also record here the formal inversion symmetries
`XField_inv`, `YField_inv` used to evaluate on the upper half `1 < |u| < |q|⁻¹` of the
wide annulus.
-/

open scoped PowerSeries

@[expose] public section

namespace TateCurve

noncomputable section AdditionDescent

/-! ### Formal inversion symmetries of the coordinate series -/

/-- The `x`-coordinate series is invariant under `v ↦ v⁻¹`: coefficientwise, the divisor
sums `∑_{d ∣ n} d(vᵈ + v⁻ᵈ - 2d)` are symmetric and `v/(1-v)² = v⁻¹/(1-v⁻¹)²`. -/
theorem XField_inv {K : Type*} [Field K] {v : K} (hv : v ≠ 0) :
    XField v⁻¹ = XField v := by
  ext n
  rw [coeff_XField, coeff_XField]
  rcases eq_or_ne n 0 with rfl | hn
  · simp only [Nat.divisors_zero, Finset.sum_empty, add_zero, ↓reduceIte]
    rcases eq_or_ne v 1 with rfl | hv1
    · rw [inv_one]
    · have h1 : (1 : K) - v ≠ 0 := sub_ne_zero.mpr (Ne.symm hv1)
      have h2 : (1 : K) - v⁻¹ ≠ 0 := sub_ne_zero.mpr fun h => hv1 (inv_eq_one.mp h.symm)
      rw [div_eq_div_iff (pow_ne_zero 2 h2) (pow_ne_zero 2 h1)]
      field_simp
      ring
  · simp only [if_neg hn, zero_add]
    apply Finset.sum_congr rfl
    intro d _
    rw [inv_inv]
    ring

/-- Parameter inversion negates the `y`-coordinate series on the curve
`y² + xy = x³ + a₄x + a₆`: `Y(v⁻¹) = -Y(v) - X(v)` coefficientwise, using
`(d choose 2) + d = (d+1 choose 2)` and `v²/(1-v)³ = -(v⁻¹/(1-v⁻¹)³) `. -/
theorem YField_inv {K : Type*} [Field K] {v : K} (hv : v ≠ 0) :
    YField v⁻¹ = -YField v - XField v := by
  ext n
  rw [map_sub, map_neg, coeff_YField, coeff_YField, coeff_XField]
  rcases eq_or_ne n 0 with rfl | hn
  · simp only [Nat.divisors_zero, Finset.sum_empty, add_zero, ↓reduceIte]
    rcases eq_or_ne v 1 with rfl | hv1
    · simp
    · have h1 : (1 : K) - v ≠ 0 := sub_ne_zero.mpr (Ne.symm hv1)
      have h2 : (1 : K) - v⁻¹ ≠ 0 := sub_ne_zero.mpr fun h => hv1 (inv_eq_one.mp h.symm)
      field_simp
      ring
  · simp only [if_neg hn, zero_add]
    rw [← Finset.sum_neg_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro d _
    rw [inv_inv]
    have hnat : (d + 1).choose 2 = d.choose 2 + d := by
      rw [Nat.choose_succ_succ, Nat.choose_one_right, Nat.add_comm]
    push_cast [hnat]
    ring

/-! ### The two-variable initial coefficient ring -/

/-- The two-variable polynomial ring `ℤ[t₁, t₂]`, with `t₁` the inner and `t₂` the outer
variable. -/
abbrev PolyRing₂ : Type := Polynomial (Polynomial ℤ)

/-- The inner variable `t₁ ∈ ℤ[t₁, t₂]`. -/
def t₁ : PolyRing₂ := Polynomial.C Polynomial.X

/-- The outer variable `t₂ ∈ ℤ[t₁, t₂]`. -/
def t₂ : PolyRing₂ := Polynomial.X

/-- The element `t₁t₂(1-t₁)(1-t₂)(1-t₁t₂) ∈ ℤ[t₁, t₂]` inverted in the coefficient ring
of the two-variable descent. -/
def descA₂ : PolyRing₂ := t₁ * t₂ * (1 - t₁) * (1 - t₂) * (1 - t₁ * t₂)

/-- The coefficient ring `ℤ[t₁, t₂][(t₁t₂(1-t₁)(1-t₂)(1-t₁t₂))⁻¹]` of the two-variable
descent: initial among commutative rings equipped with elements `t₁, t₂` such that
`t₁, t₂, 1-t₁, 1-t₂, 1-t₁t₂` are all invertible. -/
abbrev CoeffRing₂ : Type := Localization.Away descA₂

/-! ### Units of the two-variable coefficient ring -/

/-- The image of the inner variable `t₁` in `CoeffRing₂`. -/
private def τ₁ : CoeffRing₂ := algebraMap PolyRing₂ CoeffRing₂ t₁

/-- The image of the outer variable `t₂` in `CoeffRing₂`. -/
private def τ₂ : CoeffRing₂ := algebraMap PolyRing₂ CoeffRing₂ t₂

private theorem isUnit_descA₂ : IsUnit (algebraMap PolyRing₂ CoeffRing₂ descA₂) :=
  IsLocalization.Away.algebraMap_isUnit descA₂

private theorem descA₂_image :
    algebraMap PolyRing₂ CoeffRing₂ descA₂ =
      τ₁ * τ₂ * (1 - τ₁) * (1 - τ₂) * (1 - τ₁ * τ₂) := by
  simp only [descA₂, τ₁, τ₂, map_mul, map_sub, map_one]

private theorem isUnit_τ₁ : IsUnit τ₁ := by
  have h := isUnit_descA₂; rw [descA₂_image] at h
  exact isUnit_of_mul_isUnit_left (isUnit_of_mul_isUnit_left
    (isUnit_of_mul_isUnit_left (isUnit_of_mul_isUnit_left h)))

private theorem isUnit_τ₂ : IsUnit τ₂ := by
  have h := isUnit_descA₂; rw [descA₂_image] at h
  exact isUnit_of_mul_isUnit_right (isUnit_of_mul_isUnit_left
    (isUnit_of_mul_isUnit_left (isUnit_of_mul_isUnit_left h)))

private theorem isUnit_τ₁τ₂ : IsUnit (τ₁ * τ₂) := by
  have h := isUnit_descA₂; rw [descA₂_image] at h
  exact isUnit_of_mul_isUnit_left (isUnit_of_mul_isUnit_left (isUnit_of_mul_isUnit_left h))

private theorem isUnit_one_sub_τ₁ : IsUnit (1 - τ₁) := by
  have h := isUnit_descA₂; rw [descA₂_image] at h
  exact isUnit_of_mul_isUnit_right (isUnit_of_mul_isUnit_left (isUnit_of_mul_isUnit_left h))

private theorem isUnit_one_sub_τ₂ : IsUnit (1 - τ₂) := by
  have h := isUnit_descA₂; rw [descA₂_image] at h
  exact isUnit_of_mul_isUnit_right (isUnit_of_mul_isUnit_left h)

private theorem isUnit_one_sub_τ₁τ₂ : IsUnit (1 - τ₁ * τ₂) := by
  have h := isUnit_descA₂; rw [descA₂_image] at h
  exact isUnit_of_mul_isUnit_right h

/-- Identify the generic `x`-series at `w = φ(u)` with `TateCurve.X` pushed along a
coefficient embedding `φ : ℚ(u) → L`. -/
private theorem XAt_emb {L : Type*} [Field L] (φ : RatFunc ℚ →+* L) (w : L)
    (hw : φ RatFunc.X = w) : XAt w w⁻¹ (1 - w)⁻¹ = X.map φ := by
  ext n
  rw [PowerSeries.coeff_map]
  simp only [XAt, X, map_add, PowerSeries.coeff_C, PowerSeries.coeff_mk]
  congr 1
  · rw [apply_ite φ, map_zero]
    rcases eq_or_ne n 0 with rfl | hn
    · rw [if_pos rfl, if_pos rfl, map_div₀, map_pow, map_sub, map_one, hw, inv_pow,
        ← div_eq_mul_inv]
    · rw [if_neg hn, if_neg hn]
  · rw [map_sum]
    apply Finset.sum_congr rfl
    intro d _
    rw [map_mul, map_natCast, map_sub, map_add, map_pow, map_pow, map_inv₀, hw, map_ofNat]
    ring

/-- Identify the generic `y`-series at `w = φ(u)` with `TateCurve.Y` pushed along `φ`. -/
private theorem YAt_emb {L : Type*} [Field L] (φ : RatFunc ℚ →+* L) (w : L)
    (hw : φ RatFunc.X = w) : YAt w w⁻¹ (1 - w)⁻¹ = Y.map φ := by
  ext n
  rw [PowerSeries.coeff_map]
  simp only [YAt, Y, map_add, PowerSeries.coeff_C, PowerSeries.coeff_mk]
  congr 1
  · rw [apply_ite φ, map_zero]
    rcases eq_or_ne n 0 with rfl | hn
    · rw [if_pos rfl, if_pos rfl, map_div₀, map_pow, map_pow, map_sub, map_one, hw, inv_pow,
        ← div_eq_mul_inv]
    · rw [if_neg hn, if_neg hn]
  · rw [map_sum]
    apply Finset.sum_congr rfl
    intro d _
    simp only [map_add, map_sub, map_mul, map_natCast, map_pow, map_inv₀, hw]

/-! ### The six coordinate series over `CoeffRing₂` -/

private def X₁C : CoeffRing₂⟦X⟧ := XAt τ₁ ↑isUnit_τ₁.unit⁻¹ ↑isUnit_one_sub_τ₁.unit⁻¹
private def X₂C : CoeffRing₂⟦X⟧ := XAt τ₂ ↑isUnit_τ₂.unit⁻¹ ↑isUnit_one_sub_τ₂.unit⁻¹
private def X₃C : CoeffRing₂⟦X⟧ :=
  XAt (τ₁ * τ₂) ↑isUnit_τ₁τ₂.unit⁻¹ ↑isUnit_one_sub_τ₁τ₂.unit⁻¹
private def Y₁C : CoeffRing₂⟦X⟧ := YAt τ₁ ↑isUnit_τ₁.unit⁻¹ ↑isUnit_one_sub_τ₁.unit⁻¹
private def Y₂C : CoeffRing₂⟦X⟧ := YAt τ₂ ↑isUnit_τ₂.unit⁻¹ ↑isUnit_one_sub_τ₂.unit⁻¹
private def Y₃C : CoeffRing₂⟦X⟧ :=
  YAt (τ₁ * τ₂) ↑isUnit_τ₁τ₂.unit⁻¹ ↑isUnit_one_sub_τ₁τ₂.unit⁻¹

/-! ### The evaluation homomorphisms out of `CoeffRing₂` -/

/-- Generic evaluation `ℤ[t₁, t₂] →+* L`, `t₁ ↦ w₁`, `t₂ ↦ w₂`. -/
private def evalPoly₂Hom {L : Type*} [CommRing L] (w₁ w₂ : L) : PolyRing₂ →+* L :=
  Polynomial.eval₂RingHom (Polynomial.eval₂RingHom (Int.castRingHom L) w₁) w₂

private theorem evalPoly₂Hom_t₁ {L : Type*} [CommRing L] (w₁ w₂ : L) :
    evalPoly₂Hom w₁ w₂ t₁ = w₁ := by simp [evalPoly₂Hom, t₁]

private theorem evalPoly₂Hom_t₂ {L : Type*} [CommRing L] (w₁ w₂ : L) :
    evalPoly₂Hom w₁ w₂ t₂ = w₂ := by simp [evalPoly₂Hom, t₂]

private theorem evalPoly₂Hom_descA₂ {L : Type*} [CommRing L] (w₁ w₂ : L) :
    evalPoly₂Hom w₁ w₂ descA₂ = w₁ * w₂ * (1 - w₁) * (1 - w₂) * (1 - w₁ * w₂) := by
  simp only [descA₂, map_mul, map_sub, map_one, evalPoly₂Hom_t₁, evalPoly₂Hom_t₂]

/-- The two-variable evaluation is injective at the transcendental point `(u₁, u₂)`:
factor `ℤ[t₁,t₂] → ℚ(u)[t₂] → ℚ(u₁,u₂)` and use that `u₂` is transcendental over `ℚ(u)`
and `u ↦ u₁` is injective. -/
private theorem evalPoly₂_injective : Function.Injective (evalPoly₂Hom u₁ u₂) := by
  have hg : Function.Injective
      (Polynomial.eval₂RingHom (Int.castRingHom (RatFunc ℚ)) RatFunc.X) := by
    have heq : (Polynomial.eval₂RingHom (Int.castRingHom (RatFunc ℚ)) RatFunc.X) =
        (algebraMap (Polynomial ℚ) (RatFunc ℚ)).comp
          (Polynomial.mapRingHom (Int.castRingHom ℚ)) := by
      refine Polynomial.ringHom_ext (fun a ↦ ?_) ?_
      · simp
      · simp [RatFunc.algebraMap_X]
    rw [heq]
    exact (RatFunc.algebraMap_injective ℚ).comp (Polynomial.map_injective _ Int.cast_injective)
  have hinner : (Polynomial.eval₂RingHom (Int.castRingHom RatFunc₂) u₁ :
        Polynomial ℤ →+* RatFunc₂) = (algebraMap (RatFunc ℚ) RatFunc₂).comp
        (Polynomial.eval₂RingHom (Int.castRingHom (RatFunc ℚ)) RatFunc.X) := by
    refine Polynomial.ringHom_ext (fun a ↦ ?_) ?_
    · simp
    · simp [u₁]
  rw [injective_iff_map_eq_zero]
  intro p hp
  have h1 : (Polynomial.aeval u₂) (Polynomial.map
      (Polynomial.eval₂RingHom (Int.castRingHom (RatFunc ℚ)) RatFunc.X) p) = 0 := by
    rw [Polynomial.aeval_def, Polynomial.eval₂_map, ← hinner]; exact hp
  have h3 : Polynomial.map
      (Polynomial.eval₂RingHom (Int.castRingHom (RatFunc ℚ)) RatFunc.X) p = 0 :=
    (transcendental_iff_injective.mp transcendental_u₂) (by rw [h1, map_zero])
  exact Polynomial.map_injective _ hg (by rw [h3, Polynomial.map_zero])

/-- Generic evaluation `CoeffRing₂ →+* L`, admissible when `descA₂ ↦ nonzero`. -/
private noncomputable abbrev evalAway₂ {L : Type*} [Field L] (w₁ w₂ : L)
    (h : evalPoly₂Hom w₁ w₂ descA₂ ≠ 0) : CoeffRing₂ →+* L :=
  Localization.awayLift (evalPoly₂Hom w₁ w₂) descA₂ (isUnit_iff_ne_zero.mpr h)

private theorem evalAway₂_algebraMap {L : Type*} [Field L] {w₁ w₂ : L}
    (h : evalPoly₂Hom w₁ w₂ descA₂ ≠ 0) (p : PolyRing₂) :
    evalAway₂ w₁ w₂ h (algebraMap PolyRing₂ CoeffRing₂ p) = evalPoly₂Hom w₁ w₂ p :=
  IsLocalization.Away.lift_eq _ _ _

private theorem evalAway₂_τ₁ {L : Type*} [Field L] {w₁ w₂ : L}
    (h : evalPoly₂Hom w₁ w₂ descA₂ ≠ 0) : evalAway₂ w₁ w₂ h τ₁ = w₁ := by
  rw [τ₁, evalAway₂_algebraMap, evalPoly₂Hom_t₁]

private theorem evalAway₂_τ₂ {L : Type*} [Field L] {w₁ w₂ : L}
    (h : evalPoly₂Hom w₁ w₂ descA₂ ≠ 0) : evalAway₂ w₁ w₂ h τ₂ = w₂ := by
  rw [τ₂, evalAway₂_algebraMap, evalPoly₂Hom_t₂]

private theorem evalAway₂_τ₁τ₂ {L : Type*} [Field L] {w₁ w₂ : L}
    (h : evalPoly₂Hom w₁ w₂ descA₂ ≠ 0) : evalAway₂ w₁ w₂ h (τ₁ * τ₂) = w₁ * w₂ := by
  rw [map_mul, evalAway₂_τ₁, evalAway₂_τ₂]

private theorem evalAway₂_τ₁_inv {L : Type*} [Field L] {w₁ w₂ : L}
    (h : evalPoly₂Hom w₁ w₂ descA₂ ≠ 0) : evalAway₂ w₁ w₂ h ↑isUnit_τ₁.unit⁻¹ = w₁⁻¹ := by
  rw [map_isUnit_unit_inv, evalAway₂_τ₁]

private theorem evalAway₂_τ₂_inv {L : Type*} [Field L] {w₁ w₂ : L}
    (h : evalPoly₂Hom w₁ w₂ descA₂ ≠ 0) : evalAway₂ w₁ w₂ h ↑isUnit_τ₂.unit⁻¹ = w₂⁻¹ := by
  rw [map_isUnit_unit_inv, evalAway₂_τ₂]

private theorem evalAway₂_τ₁τ₂_inv {L : Type*} [Field L] {w₁ w₂ : L}
    (h : evalPoly₂Hom w₁ w₂ descA₂ ≠ 0) :
    evalAway₂ w₁ w₂ h ↑isUnit_τ₁τ₂.unit⁻¹ = (w₁ * w₂)⁻¹ := by
  rw [map_isUnit_unit_inv, evalAway₂_τ₁τ₂]

private theorem evalAway₂_one_sub_τ₁_inv {L : Type*} [Field L] {w₁ w₂ : L}
    (h : evalPoly₂Hom w₁ w₂ descA₂ ≠ 0) :
    evalAway₂ w₁ w₂ h ↑isUnit_one_sub_τ₁.unit⁻¹ = (1 - w₁)⁻¹ := by
  rw [map_isUnit_unit_inv, map_sub, map_one, evalAway₂_τ₁]

private theorem evalAway₂_one_sub_τ₂_inv {L : Type*} [Field L] {w₁ w₂ : L}
    (h : evalPoly₂Hom w₁ w₂ descA₂ ≠ 0) :
    evalAway₂ w₁ w₂ h ↑isUnit_one_sub_τ₂.unit⁻¹ = (1 - w₂)⁻¹ := by
  rw [map_isUnit_unit_inv, map_sub, map_one, evalAway₂_τ₂]

private theorem evalAway₂_one_sub_τ₁τ₂_inv {L : Type*} [Field L] {w₁ w₂ : L}
    (h : evalPoly₂Hom w₁ w₂ descA₂ ≠ 0) :
    evalAway₂ w₁ w₂ h ↑isUnit_one_sub_τ₁τ₂.unit⁻¹ = (1 - w₁ * w₂)⁻¹ := by
  rw [map_isUnit_unit_inv, map_sub, map_one, evalAway₂_τ₁τ₂]

private theorem evalAway₂_injective {h : evalPoly₂Hom u₁ u₂ descA₂ ≠ 0} :
    Function.Injective (evalAway₂ u₁ u₂ h) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨⟨p, m⟩, hm⟩ := IsLocalization.surj (Submonoid.powers descA₂) x
  dsimp only at hm
  have h2 := congrArg (evalAway₂ u₁ u₂ h) hm
  rw [map_mul, hx, zero_mul, evalAway₂_algebraMap] at h2
  have hp : p = 0 := evalPoly₂_injective (by rw [_root_.map_zero]; exact h2.symm)
  rw [hp, _root_.map_zero] at hm
  exact (IsUnit.mul_left_eq_zero (IsLocalization.map_units CoeffRing₂ m)).mp hm

/-! ### Admissibility at the transcendental point `(u₁, u₂)` -/

private theorem u₁_ne_one : u₁ ≠ 1 := by
  have hinj : Function.Injective (algebraMap (RatFunc ℚ) RatFunc₂) :=
    FaithfulSMul.algebraMap_injective (RatFunc ℚ) RatFunc₂
  intro h
  refine RatFunc.X_ne_one (K := ℚ) (hinj ?_)
  rw [map_one]; exact h

private theorem u₂_ne_one : u₂ ≠ 1 := fun h ↦
  transcendental_u₂ (by rw [h]; exact isAlgebraic_one)

private theorem u₁u₂_ne_one : u₁ * u₂ ≠ 1 := fun h ↦
  transcendental_u₁_mul_u₂ (by rw [h]; exact isAlgebraic_one)

private theorem hu_transcendental : evalPoly₂Hom u₁ u₂ descA₂ ≠ 0 := by
  rw [evalPoly₂Hom_descA₂]
  refine mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero u₁_ne_zero u₂_ne_zero) ?_) ?_) ?_
  · exact sub_ne_zero.mpr (Ne.symm u₁_ne_one)
  · exact sub_ne_zero.mpr (Ne.symm u₂_ne_one)
  · exact sub_ne_zero.mpr (Ne.symm u₁u₂_ne_one)

/-! ### The chord law over `CoeffRing₂` -/

private theorem chord_x_coeffRing :
    (X₁C - X₂C) ^ 2 * X₃C =
      (Y₁C - Y₂C) ^ 2 + (Y₁C - Y₂C) * (X₁C - X₂C) - (X₁C + X₂C) * (X₁C - X₂C) ^ 2 := by
  apply PowerSeries.map_injective _ (evalAway₂_injective (h := hu_transcendental))
  simp only [map_add, map_mul, map_pow, map_sub, X₁C, X₂C, X₃C, Y₁C, Y₂C,
    map_XAt, map_YAt, evalAway₂_τ₁, evalAway₂_τ₂, evalAway₂_τ₁_inv,
    evalAway₂_τ₂_inv, evalAway₂_τ₁τ₂_inv, evalAway₂_one_sub_τ₁_inv,
    evalAway₂_one_sub_τ₂_inv, evalAway₂_one_sub_τ₁τ₂_inv]
  rw [XAt_emb emb₁ u₁ emb₁_ratFuncX, XAt_emb emb₂ u₂ emb₂_ratFuncX,
    XAt_emb emb₃ (u₁ * u₂) emb₃_ratFuncX, YAt_emb emb₁ u₁ emb₁_ratFuncX,
    YAt_emb emb₂ u₂ emb₂_ratFuncX]
  exact chord_x

private theorem chord_y_coeffRing :
    (X₂C - X₁C) * Y₃C =
      -((Y₂C - Y₁C) + (X₂C - X₁C)) * X₃C - (Y₁C * X₂C - Y₂C * X₁C) := by
  apply PowerSeries.map_injective _ (evalAway₂_injective (h := hu_transcendental))
  simp only [map_add, map_mul, map_sub, map_neg, X₁C, X₂C, X₃C, Y₁C, Y₂C, Y₃C,
    map_XAt, map_YAt, evalAway₂_τ₁, evalAway₂_τ₂, evalAway₂_τ₁_inv,
    evalAway₂_τ₂_inv, evalAway₂_τ₁τ₂_inv, evalAway₂_one_sub_τ₁_inv,
    evalAway₂_one_sub_τ₂_inv, evalAway₂_one_sub_τ₁τ₂_inv]
  rw [XAt_emb emb₁ u₁ emb₁_ratFuncX, XAt_emb emb₂ u₂ emb₂_ratFuncX,
    XAt_emb emb₃ (u₁ * u₂) emb₃_ratFuncX, YAt_emb emb₁ u₁ emb₁_ratFuncX,
    YAt_emb emb₂ u₂ emb₂_ratFuncX, YAt_emb emb₃ (u₁ * u₂) emb₃_ratFuncX]
  exact chord_y

/-! ### The descended chord law -/

/-- **The chord law for the Tate coordinate series over any field**, `x`-coordinate:
for `v₁, v₂ ∉ {0, 1}` with `v₁v₂ ≠ 1`,

`(X(v₁) - X(v₂))²·X(v₁v₂) = (Y(v₁) - Y(v₂))² + (Y(v₁) - Y(v₂))(X(v₁) - X(v₂)) -
(X(v₁) + X(v₂))(X(v₁) - X(v₂))²`

in `K⟦q⟧`. Proved over `ℚ(u₁, u₂)` by complex-analytic methods (`TateCurve.chord_x`),
descended through `ℤ[t₁, t₂][(t₁t₂(1-t₁)(1-t₂)(1-t₁t₂))⁻¹]`. -/
theorem chord_x_field {K : Type*} [Field K] {v₁ v₂ : K} (h₁0 : v₁ ≠ 0) (h₁1 : v₁ ≠ 1)
    (h₂0 : v₂ ≠ 0) (h₂1 : v₂ ≠ 1) (h₃ : v₁ * v₂ ≠ 1) :
    (XField v₁ - XField v₂) ^ 2 * XField (v₁ * v₂) =
      (YField v₁ - YField v₂) ^ 2 + (YField v₁ - YField v₂) * (XField v₁ - XField v₂)
        - (XField v₁ + XField v₂) * (XField v₁ - XField v₂) ^ 2 := by
  have hv : evalPoly₂Hom v₁ v₂ descA₂ ≠ 0 := by
    rw [evalPoly₂Hom_descA₂]
    refine mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero h₁0 h₂0) ?_) ?_) ?_
    · exact sub_ne_zero.mpr (Ne.symm h₁1)
    · exact sub_ne_zero.mpr (Ne.symm h₂1)
    · exact sub_ne_zero.mpr (Ne.symm h₃)
  have h := congrArg (PowerSeries.map (evalAway₂ v₁ v₂ hv)) chord_x_coeffRing
  simp only [map_add, map_mul, map_pow, map_sub, X₁C, X₂C, X₃C, Y₁C, Y₂C,
    map_XAt, map_YAt, evalAway₂_τ₁, evalAway₂_τ₂, evalAway₂_τ₁_inv,
    evalAway₂_τ₂_inv, evalAway₂_τ₁τ₂_inv, evalAway₂_one_sub_τ₁_inv,
    evalAway₂_one_sub_τ₂_inv, evalAway₂_one_sub_τ₁τ₂_inv] at h
  rw [XField_eq_XAt v₁, XField_eq_XAt v₂, XField_eq_XAt (v₁ * v₂),
    YField_eq_YAt v₁, YField_eq_YAt v₂]
  exact h

/-- **The chord law for the Tate coordinate series over any field**, `y`-coordinate:
for `v₁, v₂ ∉ {0, 1}` with `v₁v₂ ≠ 1`,

`(X(v₂) - X(v₁))·Y(v₁v₂) = -((Y(v₂) - Y(v₁)) + (X(v₂) - X(v₁)))·X(v₁v₂) -
(Y(v₁)X(v₂) - Y(v₂)X(v₁))`

in `K⟦q⟧`. -/
theorem chord_y_field {K : Type*} [Field K] {v₁ v₂ : K} (h₁0 : v₁ ≠ 0) (h₁1 : v₁ ≠ 1)
    (h₂0 : v₂ ≠ 0) (h₂1 : v₂ ≠ 1) (h₃ : v₁ * v₂ ≠ 1) :
    (XField v₂ - XField v₁) * YField (v₁ * v₂) =
      -((YField v₂ - YField v₁) + (XField v₂ - XField v₁)) * XField (v₁ * v₂)
        - (YField v₁ * XField v₂ - YField v₂ * XField v₁) := by
  have hv : evalPoly₂Hom v₁ v₂ descA₂ ≠ 0 := by
    rw [evalPoly₂Hom_descA₂]
    refine mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero h₁0 h₂0) ?_) ?_) ?_
    · exact sub_ne_zero.mpr (Ne.symm h₁1)
    · exact sub_ne_zero.mpr (Ne.symm h₂1)
    · exact sub_ne_zero.mpr (Ne.symm h₃)
  have h := congrArg (PowerSeries.map (evalAway₂ v₁ v₂ hv)) chord_y_coeffRing
  simp only [map_add, map_mul, map_sub, map_neg, X₁C, X₂C, X₃C, Y₁C, Y₂C, Y₃C,
    map_XAt, map_YAt, evalAway₂_τ₁, evalAway₂_τ₂, evalAway₂_τ₁_inv,
    evalAway₂_τ₂_inv, evalAway₂_τ₁τ₂_inv, evalAway₂_one_sub_τ₁_inv,
    evalAway₂_one_sub_τ₂_inv, evalAway₂_one_sub_τ₁τ₂_inv] at h
  rw [XField_eq_XAt v₁, XField_eq_XAt v₂, XField_eq_XAt (v₁ * v₂),
    YField_eq_YAt v₁, YField_eq_YAt v₂, YField_eq_YAt (v₁ * v₂)]
  exact h

end AdditionDescent

end TateCurve
