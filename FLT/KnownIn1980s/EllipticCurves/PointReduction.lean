/-
Copyright (c) 2026 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Bryan Wang Peng Jun
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.AlgebraicGeometry.EllipticCurve.Reduction
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.Valuation.RamificationGroup
public import Mathlib.RingTheory.Valuation.LocalSubring
public import FLT.KnownIn1980s.EllipticCurves.DivisionPolynomialTorsion

/-!

# Reduction of torsion points: the local infrastructure

This file builds the ring-theoretic infrastructure needed to reduce the `n`-torsion points of
`E(kˢᵉᵖ)` modulo a valuation subring `𝒪` of `kˢᵉᵖ` lying over the discrete valuation ring `R`,
feeding the packaging lemma `WeierstrassCurve.exists_reduction_hom_injective_of_good_reduction`
in `FLT.KnownIn1980s.EllipticCurves.GoodReduction`. It is the concrete first half of the argument
of Silverman (AEC VII.3): the coordinates of a prime-to-`p` torsion point are integral over `𝒪`,
so they can be reduced.

The standing hypothesis relating `𝒪` and `R` is
`h𝒪 : (𝒪.comap (algebraMap k ksep)).toSubring = (algebraMap R k).range`, i.e. `𝒪 ∩ k = R`.

## Main results

* `integerHom` : the ring homomorphism `R →+* 𝒪`, a *local* homomorphism, inducing
* `residueFieldHom` : the map `ResidueField R →+* ResidueField 𝒪`, base field of the reduced
  curve;
* `natCast_isUnit` : `n` invertible in the residue field of `R` makes `(n : 𝒪)` a unit;
* `xCoord_mem` (**Silverman AEC VII.3**): the `x`-coordinate of a nonzero `n`-torsion point of
  `E(kˢᵉᵖ)` lies in `𝒪`.

The construction of the reduction map itself on points, with its
additivity/injectivity/equivariance, is the remaining content of the packaging lemma; see the
`sorry`s and roadmap in `FLT.KnownIn1980s.EllipticCurves.GoodReduction`.
-/

@[expose] public section

open scoped WeierstrassCurve.Affine
open Polynomial

namespace WeierstrassCurve.PointReduction

variable (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable (k : Type*) [Field k] [Algebra R k] [IsFractionRing R k]
variable (ksep : Type*) [Field ksep] [Algebra k ksep]
variable (𝒪 : ValuationSubring ksep)

/-- The ring homomorphism `R →+* 𝒪` sending `r` to the image of `r` in `𝒪`, well defined because
`𝒪 ∩ k = R` (the hypothesis `h𝒪`). This is the map used to reduce the coordinates of points. -/
noncomputable def integerHom
    (h𝒪 : (𝒪.comap (algebraMap k ksep)).toSubring = (algebraMap R k).range) : R →+* 𝒪 :=
  RingHom.codRestrict ((algebraMap k ksep).comp (algebraMap R k)) 𝒪.toSubring fun r => by
    have hx : algebraMap R k r ∈ (algebraMap R k).range := ⟨r, rfl⟩
    rw [← h𝒪] at hx
    exact ValuationSubring.mem_comap.mp hx

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R k] in
@[simp]
theorem coe_integerHom
    (h𝒪 : (𝒪.comap (algebraMap k ksep)).toSubring = (algebraMap R k).range) (r : R) :
    (integerHom R k ksep 𝒪 h𝒪 r : ksep) = algebraMap k ksep (algebraMap R k r) :=
  rfl

/-- `integerHom` is a *local* homomorphism: if `integerHom r` is a unit then so is `r`. This makes
`IsLocalRing.ResidueField.map` applicable, giving `residueFieldHom`. -/
instance instIsLocalHomIntegerHom
    (h𝒪 : (𝒪.comap (algebraMap k ksep)).toSubring = (algebraMap R k).range) :
    IsLocalHom (integerHom R k ksep 𝒪 h𝒪) where
  map_nonunit r hr := by
    obtain ⟨v, hv⟩ := hr.exists_right_inv
    have hcoe : algebraMap k ksep (algebraMap R k r) * (v : ksep) = 1 := by
      have := congrArg Subtype.val hv
      simpa [integerHom, RingHom.codRestrict] using this
    have hrne : algebraMap R k r ≠ 0 := by rintro h0; rw [h0] at hcoe; simp at hcoe
    have hvval : (algebraMap k ksep (algebraMap R k r))⁻¹ = (v : ksep) :=
      inv_eq_of_mul_eq_one_right hcoe
    have hmem : (algebraMap R k r)⁻¹ ∈ 𝒪.comap (algebraMap k ksep) := by
      rw [ValuationSubring.mem_comap, map_inv₀, hvval]; exact v.2
    rw [← ValuationSubring.mem_toSubring, h𝒪] at hmem
    obtain ⟨s, hs⟩ := hmem
    have heq : algebraMap R k (r * s) = 1 := by rw [map_mul, hs, mul_inv_cancel₀ hrne]
    exact IsUnit.of_mul_eq_one s (IsFractionRing.injective R k (by rw [heq, map_one]))

/-- The induced map of residue fields `ResidueField R →+* ResidueField 𝒪`, from the local
homomorphism `integerHom`. The reduced curve `E.reduction R` over `ResidueField R` is transported
to a curve over `ResidueField 𝒪` along this map. -/
noncomputable def residueFieldHom
    (h𝒪 : (𝒪.comap (algebraMap k ksep)).toSubring = (algebraMap R k).range) :
    IsLocalRing.ResidueField R →+* IsLocalRing.ResidueField 𝒪 :=
  IsLocalRing.ResidueField.map (integerHom R k ksep 𝒪 h𝒪)

/-- If `n` is invertible in the residue field of `R`, then `(n : 𝒪)` is a unit: `residueFieldHom`
sends `(n : ResidueField R)` to `(n : ResidueField 𝒪)` preserving units, and an element of the
local ring `𝒪` with unit residue is a unit. -/
theorem natCast_isUnit
    (h𝒪 : (𝒪.comap (algebraMap k ksep)).toSubring = (algebraMap R k).range) (n : ℕ)
    (hn : IsUnit (n : IsLocalRing.ResidueField R)) : IsUnit (n : 𝒪) := by
  have h1 : IsUnit (n : IsLocalRing.ResidueField 𝒪) := by
    have := hn.map (IsLocalRing.ResidueField.map (integerHom R k ksep 𝒪 h𝒪))
    rwa [map_natCast] at this
  exact isUnit_of_map_unit (IsLocalRing.residue 𝒪) _ (by rwa [map_natCast])

/-- A root of a polynomial with a *unit* leading coefficient is integral: scaling by the inverse
of the leading unit produces a monic polynomial with the same root. -/
theorem isIntegral_of_isUnit_leadingCoeff {O S : Type*} [CommRing O] [IsDomain O] [CommRing S]
    [Algebra O S] (p : O[X]) (hlc : IsUnit p.leadingCoeff) {x : S} (hx : aeval x p = 0) :
    _root_.IsIntegral O x := by
  refine ⟨C (↑hlc.unit⁻¹ : O) * p, ?_, ?_⟩
  · rw [Monic, leadingCoeff_mul, leadingCoeff_C]; exact hlc.val_inv_mul
  · change aeval x (C (↑hlc.unit⁻¹ : O) * p) = 0
    rw [map_mul, hx, mul_zero]

variable (E : WeierstrassCurve k) [E.IsElliptic] [E.HasGoodReduction R]

/-- **Integrality of the `x`-coordinate of a torsion point** (Silverman, *The Arithmetic of
Elliptic Curves*, VII.3). If `n` is invertible in the residue field of `R` and `𝒪` lies over `R`,
then the `x`-coordinate of a nonzero `n`-torsion point of `E(kˢᵉᵖ)` lies in `𝒪`.

The `x`-coordinate is a root of `ΨSqₙ` (`Affine.Point.eval_ΨSq_eq_zero_of_smul_eq_zero`). Writing
`E𝒪` for the integral model of `E` over `𝒪` (from the integral model over `R` via `integerHom`),
`ΨSqₙ` of `E(kˢᵉᵖ)` is the image of `E𝒪.ΨSqₙ` under `𝒪 → kˢᵉᵖ` (`WeierstrassCurve.map_ΨSq`), whose
leading coefficient `n²` is a unit of `𝒪` (`natCast_isUnit`). So `x` is integral over `𝒪`, and
`𝒪`, a valuation subring, is integrally closed. -/
theorem xCoord_mem [DecidableEq ksep]
    (h𝒪 : (𝒪.comap (algebraMap k ksep)).toSubring = (algebraMap R k).range) (n : ℕ)
    (hn : IsUnit (n : IsLocalRing.ResidueField R)) {x y : ksep}
    (h : (E⁄ksep).toAffine.Nonsingular x y)
    (htors : (n : ℤ) • (Affine.Point.some x y h : (E⁄ksep).Point) = 0) :
    x ∈ 𝒪 := by
  haveI : (E⁄ksep).IsElliptic := inferInstanceAs (E.map (algebraMap k ksep)).IsElliptic
  have hnR : (n : R) ≠ 0 := fun hh =>
    hn.ne_zero (by rw [← map_natCast (IsLocalRing.residue R) n, hh, map_zero])
  have hnksep : ((n : ℤ) : ksep) ≠ 0 := by
    push_cast; intro hz; apply hnR
    have e2 : (n : k) = 0 :=
      (algebraMap k ksep).injective (by rw [map_natCast, map_zero]; exact_mod_cast hz)
    exact IsFractionRing.injective R k (by rw [map_natCast, map_zero]; exact e2)
  have hnZ : (n : ℤ) ≠ 0 := by intro hh; apply hnksep; rw [hh]; simp
  have hroot : ((E⁄ksep).ΨSq (n : ℤ)).eval x = 0 :=
    Affine.Point.eval_ΨSq_eq_zero_of_smul_eq_zero h hnZ htors
  set incl := algebraMap 𝒪 ksep with hincl
  set E𝒪 : WeierstrassCurve 𝒪 :=
    (WeierstrassCurve.integralModel R E).map (integerHom R k ksep 𝒪 h𝒪) with hE𝒪
  have hcomp : incl.comp (integerHom R k ksep 𝒪 h𝒪) =
      (algebraMap k ksep).comp (algebraMap R k) := by ext r; rfl
  have hEeq : (WeierstrassCurve.integralModel R E).map (algebraMap R k) = E :=
    WeierstrassCurve.baseChange_integralModel_eq R E
  have hcurve : E𝒪.map incl = (E⁄ksep) := by
    rw [hE𝒪, WeierstrassCurve.map_map, hcomp, ← WeierstrassCurve.map_map, hEeq]; rfl
  have hΨrel : (E⁄ksep).ΨSq (n : ℤ) = (E𝒪.ΨSq (n : ℤ)).map incl := by
    rw [← hcurve, WeierstrassCurve.map_ΨSq]
  have haeval : aeval x (E𝒪.ΨSq (n : ℤ)) = 0 := by
    have hh : ((E𝒪.ΨSq (n : ℤ)).map incl).eval x = 0 := by rw [← hΨrel]; exact hroot
    rwa [Polynomial.eval_map, ← aeval_def] at hh
  have hu : IsUnit ((n : ℤ) : 𝒪) := by exact_mod_cast natCast_isUnit R k ksep 𝒪 h𝒪 n hn
  have hlc : IsUnit (E𝒪.ΨSq (n : ℤ)).leadingCoeff := by
    rw [WeierstrassCurve.leadingCoeff_ΨSq _ (by exact_mod_cast hu.ne_zero)]
    exact hu.pow 2
  have hint : _root_.IsIntegral 𝒪 x := isIntegral_of_isUnit_leadingCoeff _ hlc haeval
  obtain ⟨z, hz⟩ := (IsIntegrallyClosed.isIntegral_iff (R := 𝒪) (x := x)).mp hint
  rw [← hz]; exact z.2

end WeierstrassCurve.PointReduction
