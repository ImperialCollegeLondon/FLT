/-
Copyright (c) 2026 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, William Coram
-/
module

public import FLT.KnownIn1980s.EllipticCurves.TateCurveConstruction
public import FLT.KnownIn1980s.EllipticCurves.TateParameter

/-!

# Descent of the Tate curve Weierstrass equation to arbitrary fields

`TateCurve.weierstrass_equation` (in `TateCurveConstruction`) proves that the formal
coordinates `X(u, q)`, `Y(u, q)` of the Tate uniformisation satisfy the Weierstrass
equation `Y² + XY = X³ + a₄X + a₆` in `ℚ(u)⟦q⟧`, by analytic methods over `ℂ`. The
intended consumers are nonarchimedean local fields `k` — of *any* residue
characteristic, and possibly of positive characteristic, in which case `ℚ(u)` has no
image in `k` and the identity cannot be transported directly.

This file performs the descent. The `q`-coefficients of `X`, `Y`, `a₄` and `a₆` all lie
in the subring `ℤ[t, t⁻¹, (1-t)⁻¹]` of `ℚ(u)` (for `a₆` this uses the divisibility
`12 ∣ 5σ₃(n) + 7σ₅(n)`, `TateCurve.twelve_dvd_sigma`), and that subring is *initial*
among rings equipped with an element `t` such that `t` and `1 - t` are invertible: it is
the localization `TateCurve.CoeffRing` of `ℤ[t]` away from `t(1-t)`. Concretely:

* `CoeffRing` injects into `ℚ(u)` by `t ↦ u` (`evalAway_ratFunc_injective`), because `u`
  is transcendental; pulling back `weierstrass_equation` along this injection gives the
  identity over `CoeffRing` (`TateCurve.weierstrass_equation_coeffRing`);
* `CoeffRing` maps to every field `K` at every `v ≠ 0, 1` by `t ↦ v` (the universal
  property of localization), and pushing forward gives the identity in `K⟦q⟧`
  (`TateCurve.weierstrass_equation_field`) — the form consumed on the local-field side,
  whose coefficients are the exact divisor-sum expressions appearing in
  `WeierstrassCurve.tateX_eq_annulus` and `WeierstrassCurve.tateY_eq_annulus`.

-/

open scoped PowerSeries

open ArithmeticFunction

@[expose] public section

namespace TateCurve

noncomputable section Descent

/-! ### The series over a field, at a point of the punctured disc -/

/-- The `x`-coordinate of the formal Tate uniformisation over a field `K`, at `v ∈ K`:
`X_v = v/(1-v)² + ∑_{n ≥ 1} (∑_{d ∣ n} (d·vᵈ + d·v⁻ᵈ - 2d))qⁿ ∈ K⟦q⟧`. Its coefficients
are the exact expressions appearing in `WeierstrassCurve.tateX_eq_annulus`. -/
def XField {K : Type*} [Field K] (v : K) : K⟦X⟧ :=
  .C (v / (1 - v) ^ 2) +
    .mk fun n ↦ ∑ d ∈ n.divisors, ((d : K) * v ^ d + (d : K) * (v⁻¹) ^ d - 2 * (d : K))

/-- The `y`-coordinate of the formal Tate uniformisation over a field `K`, at `v ∈ K`:
`Y_v = v²/(1-v)³ + ∑_{n ≥ 1} (∑_{d ∣ n} ((d 2)vᵈ - (d+1 2)v⁻ᵈ + d))qⁿ ∈ K⟦q⟧`. Its
coefficients are the exact expressions appearing in `WeierstrassCurve.tateY_eq_annulus`. -/
def YField {K : Type*} [Field K] (v : K) : K⟦X⟧ :=
  .C (v ^ 2 / (1 - v) ^ 3) +
    .mk fun n ↦ ∑ d ∈ n.divisors, (((d.choose 2 : ℕ) : K) * v ^ d
      - (((d + 1).choose 2 : ℕ) : K) * (v⁻¹) ^ d + (d : K))

/-- The Weierstrass coefficient `a₄ = -5s₃ ∈ K⟦q⟧`: the integral series
`TateCurve.a₄Formal` mapped into `K`. -/
def a₄Field (K : Type*) [Field K] : K⟦X⟧ := a₄Formal.map (Int.castRingHom K)

/-- The Weierstrass coefficient `a₆ = -(5s₃ + 7s₅)/12 ∈ K⟦q⟧`: the integral series
`TateCurve.a₆Formal` (whose coefficients are the *integers* `-(5σ₃(n) + 7σ₅(n))/12`,
by `TateCurve.twelve_dvd_sigma`) mapped into `K`. -/
def a₆Field (K : Type*) [Field K] : K⟦X⟧ := a₆Formal.map (Int.castRingHom K)

theorem coeff_XField {K : Type*} [Field K] (v : K) (n : ℕ) :
    PowerSeries.coeff n (XField v) = (if n = 0 then v / (1 - v) ^ 2 else 0) +
      ∑ d ∈ n.divisors, ((d : K) * v ^ d + (d : K) * (v⁻¹) ^ d - 2 * (d : K)) := by
  rw [show XField v = PowerSeries.C (v / (1 - v) ^ 2) +
      PowerSeries.mk (fun n ↦ ∑ d ∈ n.divisors,
        ((d : K) * v ^ d + (d : K) * (v⁻¹) ^ d - 2 * (d : K))) from rfl,
    map_add, PowerSeries.coeff_C, PowerSeries.coeff_mk]

theorem coeff_YField {K : Type*} [Field K] (v : K) (n : ℕ) :
    PowerSeries.coeff n (YField v) = (if n = 0 then v ^ 2 / (1 - v) ^ 3 else 0) +
      ∑ d ∈ n.divisors, (((d.choose 2 : ℕ) : K) * v ^ d
        - (((d + 1).choose 2 : ℕ) : K) * (v⁻¹) ^ d + (d : K)) := by
  rw [show YField v = PowerSeries.C (v ^ 2 / (1 - v) ^ 3) +
      PowerSeries.mk (fun n ↦ ∑ d ∈ n.divisors, (((d.choose 2 : ℕ) : K) * v ^ d
        - (((d + 1).choose 2 : ℕ) : K) * (v⁻¹) ^ d + (d : K))) from rfl,
    map_add, PowerSeries.coeff_C, PowerSeries.coeff_mk]

/-! ### The series over a commutative ring, given explicit inverses -/

/-- The `x`-coordinate series over any commutative ring, given an element `t` and
(intended) inverses `ti` of `t` and `oi` of `1 - t`. Machinery for the descent:
specialised to `CoeffRing` and compared with `XField` and `TateCurve.X`. -/
def XAt {A : Type*} [CommRing A] (t ti oi : A) : A⟦X⟧ :=
  .C (t * oi ^ 2) +
    .mk fun n ↦ ∑ d ∈ n.divisors, ((d : A) * t ^ d + (d : A) * ti ^ d - 2 * (d : A))

/-- The `y`-coordinate series over any commutative ring; cf. `XAt`. -/
def YAt {A : Type*} [CommRing A] (t ti oi : A) : A⟦X⟧ :=
  .C (t ^ 2 * oi ^ 3) +
    .mk fun n ↦ ∑ d ∈ n.divisors, (((d.choose 2 : ℕ) : A) * t ^ d
      - (((d + 1).choose 2 : ℕ) : A) * ti ^ d + (d : A))

private theorem XField_eq_XAt {K : Type*} [Field K] (v : K) :
    XField v = XAt v v⁻¹ (1 - v)⁻¹ := by
  ext n
  simp only [XField, XAt, map_add, PowerSeries.coeff_C, PowerSeries.coeff_mk]
  congr 1
  rcases eq_or_ne n 0 with rfl | hn
  · rw [if_pos rfl, if_pos rfl, inv_pow, ← div_eq_mul_inv]
  · rw [if_neg hn, if_neg hn]

private theorem YField_eq_YAt {K : Type*} [Field K] (v : K) :
    YField v = YAt v v⁻¹ (1 - v)⁻¹ := by
  ext n
  simp only [YField, YAt, map_add, PowerSeries.coeff_C, PowerSeries.coeff_mk]
  congr 1
  rcases eq_or_ne n 0 with rfl | hn
  · rw [if_pos rfl, if_pos rfl, inv_pow, ← div_eq_mul_inv]
  · rw [if_neg hn, if_neg hn]

private theorem map_XAt {A B : Type*} [CommRing A] [CommRing B] (ψ : A →+* B)
    (t ti oi : A) : PowerSeries.map ψ (XAt t ti oi) = XAt (ψ t) (ψ ti) (ψ oi) := by
  ext n
  simp only [XAt, PowerSeries.coeff_map, map_add, PowerSeries.coeff_mk, map_mul,
    map_pow, map_sum, map_sub, map_natCast, map_ofNat, PowerSeries.map_C]

private theorem map_YAt {A B : Type*} [CommRing A] [CommRing B] (ψ : A →+* B)
    (t ti oi : A) : PowerSeries.map ψ (YAt t ti oi) = YAt (ψ t) (ψ ti) (ψ oi) := by
  ext n
  simp only [YAt, PowerSeries.coeff_map, map_add, PowerSeries.coeff_mk, map_mul,
    map_pow, map_sum, map_sub, map_natCast, PowerSeries.map_C]

/-- Mapping an integral power series into `B` factors through any intermediate ring:
there is only one ring homomorphism out of `ℤ`. -/
private theorem map_intSeries {A B : Type*} [CommRing A] [CommRing B] (ψ : A →+* B)
    (F : ℤ⟦X⟧) : PowerSeries.map ψ (F.map (Int.castRingHom A)) =
      F.map (Int.castRingHom B) := by
  ext n
  simp only [PowerSeries.coeff_map, eq_intCast, map_intCast]

/-- A ring homomorphism into a field sends the chosen inverse of a unit to the field
inverse of its image. -/
private theorem map_isUnit_unit_inv {A L : Type*} [CommRing A] [Field L] (ψ : A →+* L)
    {a : A} (h : IsUnit a) : ψ ↑h.unit⁻¹ = (ψ a)⁻¹ := by
  have h1 : ψ a * ψ ↑h.unit⁻¹ = 1 := by
    rw [← map_mul, IsUnit.mul_val_inv, map_one]
  exact (inv_eq_of_mul_eq_one_right h1).symm

/-! ### Identification with the coordinates over `ℚ(u)` -/

private theorem ratFuncX_ne_one : (RatFunc.X : RatFunc ℚ) ≠ 1 := fun h ↦ by
  have h2 : (Polynomial.X : Polynomial ℚ) = 1 := RatFunc.algebraMap_injective ℚ
    (by rw [RatFunc.algebraMap_X, map_one]; exact h)
  simpa using congrArg Polynomial.natDegree h2

private theorem XAt_ratFunc :
    XAt (RatFunc.X : RatFunc ℚ) (RatFunc.X : RatFunc ℚ)⁻¹ ((1 : RatFunc ℚ) - RatFunc.X)⁻¹
      = X := by
  ext n
  simp only [XAt, X, map_add, PowerSeries.coeff_C, PowerSeries.coeff_mk]
  congr 1
  · rcases eq_or_ne n 0 with rfl | hn
    · rw [if_pos rfl, if_pos rfl, inv_pow, ← div_eq_mul_inv]
    · rw [if_neg hn, if_neg hn]
  · exact Finset.sum_congr rfl fun d _ ↦ by ring

private theorem YAt_ratFunc :
    YAt (RatFunc.X : RatFunc ℚ) (RatFunc.X : RatFunc ℚ)⁻¹ ((1 : RatFunc ℚ) - RatFunc.X)⁻¹
      = Y := by
  ext n
  simp only [YAt, Y, map_add, PowerSeries.coeff_C, PowerSeries.coeff_mk]
  congr 1
  rcases eq_or_ne n 0 with rfl | hn
  · rw [if_pos rfl, if_pos rfl, inv_pow, ← div_eq_mul_inv]
  · rw [if_neg hn, if_neg hn]

open scoped ArithmeticFunction.sigma in
private theorem a₄Formal_ratFunc :
    a₄Formal.map (Int.castRingHom (RatFunc ℚ)) = a₄ := by
  ext n
  rw [PowerSeries.coeff_map, coeff_a₄Formal]
  simp only [a₄, s, neg_mul, map_neg,
    show ((5 : (RatFunc ℚ)⟦X⟧)) = PowerSeries.C (5 : RatFunc ℚ) from
      (map_ofNat (PowerSeries.C : RatFunc ℚ →+* (RatFunc ℚ)⟦X⟧) 5).symm,
    PowerSeries.coeff_C_mul, PowerSeries.coeff_mk, eq_intCast]
  push_cast
  ring

open scoped ArithmeticFunction.sigma in
private theorem a₆Formal_ratFunc :
    a₆Formal.map (Int.castRingHom (RatFunc ℚ)) = a₆ := by
  ext n
  rw [PowerSeries.coeff_map, coeff_a₆Formal]
  obtain ⟨c, hc⟩ := twelve_dvd_sigma n
  simp only [a₆, PowerSeries.coeff_smul, map_neg, map_add, s,
    show ((5 : (RatFunc ℚ)⟦X⟧)) = PowerSeries.C (5 : RatFunc ℚ) from
      (map_ofNat (PowerSeries.C : RatFunc ℚ →+* (RatFunc ℚ)⟦X⟧) 5).symm,
    show ((7 : (RatFunc ℚ)⟦X⟧)) = PowerSeries.C (7 : RatFunc ℚ) from
      (map_ofNat (PowerSeries.C : RatFunc ℚ →+* (RatFunc ℚ)⟦X⟧) 7).symm,
    PowerSeries.coeff_C_mul, PowerSeries.coeff_mk, smul_eq_mul, eq_intCast]
  rw [hc, Int.mul_ediv_cancel_left c (by norm_num)]
  have h12 : ((5 : RatFunc ℚ) * (σ 3 n : ℚ) + 7 * (σ 5 n : ℚ)) = 12 * (c : RatFunc ℚ) := by
    exact_mod_cast congrArg (fun z : ℤ ↦ (z : RatFunc ℚ)) hc
  push_cast at h12 ⊢
  rw [h12]
  ring

/-! ### The initial coefficient ring `ℤ[t, t⁻¹, (1-t)⁻¹]` -/

/-- The polynomial `t(1 - t) ∈ ℤ[t]` inverted in the coefficient ring of the descent. -/
def descA : Polynomial ℤ := Polynomial.X * (1 - Polynomial.X)

/-- The coefficient ring `ℤ[t, t⁻¹, (1-t)⁻¹]` of the Tate curve descent: the
localization of `ℤ[t]` away from `t(1-t)`. It is initial among commutative rings
equipped with an element `t` such that `t` and `1 - t` are invertible: it injects into
`ℚ(u)` by `t ↦ u`, and maps to every field `K` at every `v ≠ 0, 1`. -/
abbrev CoeffRing : Type := Localization.Away descA

/-- The element `t ∈ ℤ[t, t⁻¹, (1-t)⁻¹]`. -/
def tC : CoeffRing := algebraMap (Polynomial ℤ) CoeffRing Polynomial.X

theorem isUnit_descA : IsUnit (algebraMap (Polynomial ℤ) CoeffRing descA) :=
  IsLocalization.Away.algebraMap_isUnit descA

theorem isUnit_tC : IsUnit tC := by
  have h : IsUnit (algebraMap (Polynomial ℤ) CoeffRing (Polynomial.X * (1 - Polynomial.X))) :=
    isUnit_descA
  rw [map_mul] at h
  exact isUnit_of_mul_isUnit_left h

theorem isUnit_one_sub_tC :
    IsUnit (algebraMap (Polynomial ℤ) CoeffRing (1 - Polynomial.X)) := by
  have h : IsUnit (algebraMap (Polynomial ℤ) CoeffRing (Polynomial.X * (1 - Polynomial.X))) :=
    isUnit_descA
  rw [map_mul] at h
  exact isUnit_of_mul_isUnit_right h

/-- The `x`-coordinate of the formal Tate uniformisation over the initial ring
`ℤ[t, t⁻¹, (1-t)⁻¹]`. -/
def XCoeff : CoeffRing⟦X⟧ := XAt tC ↑isUnit_tC.unit⁻¹ ↑isUnit_one_sub_tC.unit⁻¹

/-- The `y`-coordinate of the formal Tate uniformisation over the initial ring
`ℤ[t, t⁻¹, (1-t)⁻¹]`. -/
def YCoeff : CoeffRing⟦X⟧ := YAt tC ↑isUnit_tC.unit⁻¹ ↑isUnit_one_sub_tC.unit⁻¹

/-- The Weierstrass coefficient `a₄` over `ℤ[t, t⁻¹, (1-t)⁻¹]` (constant in `t`). -/
def a₄Coeff : CoeffRing⟦X⟧ := a₄Formal.map (Int.castRingHom CoeffRing)

/-- The Weierstrass coefficient `a₆` over `ℤ[t, t⁻¹, (1-t)⁻¹]` (constant in `t`). -/
def a₆Coeff : CoeffRing⟦X⟧ := a₆Formal.map (Int.castRingHom CoeffRing)

/-! ### Evaluation homomorphisms out of the coefficient ring -/

/-- Evaluation `ℤ[t, t⁻¹, (1-t)⁻¹] →+* L` at an element `w ≠ 0, 1` of a field `L`:
the universal property of the localization away from `t(1-t)`. -/
private noncomputable abbrev evalAway {L : Type*} [Field L] {w : L} (hw0 : w ≠ 0)
    (hw1 : w ≠ 1) : CoeffRing →+* L :=
  Localization.awayLift (Polynomial.eval₂RingHom (Int.castRingHom L) w) descA
    (by
      have h : Polynomial.eval₂RingHom (Int.castRingHom L) w descA = w * (1 - w) := by
        simp [descA]
      rw [h]
      exact isUnit_iff_ne_zero.mpr
        (mul_ne_zero hw0 (sub_ne_zero.mpr (Ne.symm hw1))))

private theorem evalAway_algebraMap {L : Type*} [Field L] {w : L} (hw0 : w ≠ 0)
    (hw1 : w ≠ 1) (p : Polynomial ℤ) :
    evalAway hw0 hw1 (algebraMap (Polynomial ℤ) CoeffRing p) =
      Polynomial.eval₂ (Int.castRingHom L) w p :=
  IsLocalization.Away.lift_eq _ _ _

private theorem evalAway_tC {L : Type*} [Field L] {w : L} (hw0 : w ≠ 0) (hw1 : w ≠ 1) :
    evalAway hw0 hw1 tC = w := by
  rw [tC, evalAway_algebraMap]
  simp

private theorem evalAway_tC_inv {L : Type*} [Field L] {w : L} (hw0 : w ≠ 0)
    (hw1 : w ≠ 1) : evalAway hw0 hw1 ↑isUnit_tC.unit⁻¹ = w⁻¹ := by
  rw [map_isUnit_unit_inv, evalAway_tC]

private theorem evalAway_one_sub_tC_inv {L : Type*} [Field L] {w : L} (hw0 : w ≠ 0)
    (hw1 : w ≠ 1) : evalAway hw0 hw1 ↑isUnit_one_sub_tC.unit⁻¹ = (1 - w)⁻¹ := by
  rw [map_isUnit_unit_inv, evalAway_algebraMap]
  simp

/-- Evaluation of `ℤ[t, t⁻¹, (1-t)⁻¹]` in `ℚ(u)` at the transcendental element `u` is
injective: an element is `p(t)/(t(1-t))ⁿ`, and `p(u) = 0` forces `p = 0`. -/
private theorem evalAway_ratFunc_injective :
    Function.Injective (evalAway (RatFunc.X_ne_zero (K := ℚ)) ratFuncX_ne_one) := by
  have hf : Function.Injective
      (Polynomial.eval₂RingHom (Int.castRingHom (RatFunc ℚ)) RatFunc.X) := by
    have heq : Polynomial.eval₂RingHom (Int.castRingHom (RatFunc ℚ)) RatFunc.X =
        (algebraMap (Polynomial ℚ) (RatFunc ℚ)).comp
          (Polynomial.mapRingHom (Int.castRingHom ℚ)) := by
      refine Polynomial.ringHom_ext (fun a ↦ ?_) ?_
      · simp
      · simp [RatFunc.algebraMap_X]
    rw [heq]
    exact (RatFunc.algebraMap_injective ℚ).comp
      (Polynomial.map_injective _ Int.cast_injective)
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨⟨p, m⟩, hm⟩ := IsLocalization.surj (Submonoid.powers descA) x
  dsimp only at hm
  have h2 := congrArg (evalAway (RatFunc.X_ne_zero (K := ℚ)) ratFuncX_ne_one) hm
  rw [map_mul, hx, zero_mul, evalAway_algebraMap] at h2
  have hp : p = 0 := hf (by
    rw [_root_.map_zero]
    exact h2.symm)
  rw [hp, _root_.map_zero] at hm
  exact (IsUnit.mul_left_eq_zero (IsLocalization.map_units CoeffRing m)).mp hm

/-! ### The descended Weierstrass equations -/

/-- **The Weierstrass equation of the Tate curve over `ℤ[t, t⁻¹, (1-t)⁻¹]`**: the
analytically-proved identity `TateCurve.weierstrass_equation` in `ℚ(u)⟦q⟧`, pulled back
along the injection `t ↦ u`. This is the initial form of the identity: every other
instance is its image under a ring homomorphism. -/
theorem weierstrass_equation_coeffRing :
    YCoeff ^ 2 + XCoeff * YCoeff = XCoeff ^ 3 + a₄Coeff * XCoeff + a₆Coeff := by
  apply PowerSeries.map_injective _ evalAway_ratFunc_injective
  simp only [map_add, map_mul, map_pow, XCoeff, YCoeff, a₄Coeff, a₆Coeff]
  rw [map_XAt, map_YAt, map_intSeries, map_intSeries, evalAway_tC, evalAway_tC_inv,
    evalAway_one_sub_tC_inv, XAt_ratFunc, YAt_ratFunc, a₄Formal_ratFunc,
    a₆Formal_ratFunc]
  exact weierstrass_equation

/-- **Descent of the Tate curve Weierstrass equation** (the formal kernel of Silverman,
ATAEC V.1.1(a)): for every field `K` and every `v ∈ K` with `v ≠ 0, 1`, the formal
coordinates of the Tate uniformisation at `v` satisfy
`Y² + XY = X³ + a₄X + a₆` in `K⟦q⟧`.

The identity is proved over `ℚ(u)` at `v = u` by analytic methods
(`TateCurve.weierstrass_equation`); it descends to the initial coefficient ring
`ℤ[t, t⁻¹, (1-t)⁻¹]` (`weierstrass_equation_coeffRing`), which maps onto the data
`(v, v⁻¹, (1-v)⁻¹)` in any field. In particular the identity holds over nonarchimedean
local fields of positive characteristic, where `ℚ(u)` itself has no image. -/
theorem weierstrass_equation_field {K : Type*} [Field K] {v : K} (hv0 : v ≠ 0)
    (hv1 : v ≠ 1) :
    YField v ^ 2 + XField v * YField v =
      XField v ^ 3 + a₄Field K * XField v + a₆Field K := by
  have h := congrArg (PowerSeries.map (evalAway hv0 hv1)) weierstrass_equation_coeffRing
  simp only [map_add, map_mul, map_pow, XCoeff, YCoeff, a₄Coeff, a₆Coeff] at h
  rw [map_XAt, map_YAt, map_intSeries, map_intSeries, evalAway_tC, evalAway_tC_inv,
    evalAway_one_sub_tC_inv] at h
  rw [XField_eq_XAt, YField_eq_YAt]
  exact h

end Descent

end TateCurve
