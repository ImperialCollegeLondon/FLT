/-
Copyright (c) 2026 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Claude
-/
module

public import FLT.KnownIn1980s.EllipticCurves.QuadraticTwists.QuadraticTwists
public import FLT.Mathlib.Algebra.Algebra.Equiv
public import FLT.Mathlib.AlgebraicGeometry.EllipticCurve.Reduction
public import FLT.Mathlib.RingTheory.Norm.Quotient

import FLT.KnownIn1980s.EllipticCurves.QuadraticTwists.LiftSeparableExtension
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.LocalRing.Quotient
import Mathlib.RingTheory.Localization.NormTrace

/-!
# Multiplicative reduction becomes split after a quadratic twist

Let `R` be a discrete valuation ring with fraction field `K` (for example the ring of integers
of a nonarchimedean local field), and let `E` be an elliptic curve over `K` with multiplicative
reduction. This file proves that if the reduction is *nonsplit*, then the quadratic twist of `E`
(`FLT.KnownIn1980s.EllipticCurves.QuadraticTwists.QuadraticTwists`) by the unramified quadratic
extension of `K` (`FLT.KnownIn1980s.EllipticCurves.QuadraticTwists.LiftSeparableExtension`) has
*split* multiplicative reduction: the reduction of the twist is the same nodal cubic with the
Galois action on the two tangent directions at the node twisted into triviality.

## Main definitions and statements

* `WeierstrassCurve.exists_quadraticTwist_hasSplitMultiplicativeReduction` : over the fraction
  field of a discrete valuation ring, an elliptic curve with nonsplit multiplicative reduction
  has a quadratic twist with split multiplicative reduction.

The generic ingredients — the node polynomial `WeierstrassCurve.nodePoly` with its splitting
criteria, and the invariance of split multiplicative reduction under isomorphism of minimal
models (`WeierstrassCurve.HasSplitMultiplicativeReduction.of_isMinimal_smul`) — are in
`FLT.Mathlib.AlgebraicGeometry.EllipticCurve.Reduction` and
`FLT.Mathlib.Algebra.QuadraticDiscriminant`.

## TODO

* Behaviour of reduction types under twisting in general: over the fraction field of a DVR, an
  unramified quadratic twist preserves good and multiplicative reduction (exchanging split and
  nonsplit), while a ramified quadratic twist of a curve with good or multiplicative reduction
  has additive reduction (at least in residue characteristic ≠ 2).
* Compatibility with the Tate curve (`FLT.KnownIn1980s.EllipticCurves.TateCurve`): for `E` with
  nonsplit multiplicative reduction over a nonarchimedean local field, the Galois representation
  of `E` is the unramified quadratic twist of the Tate-curve representation of its split twist.
  This is the main FLT-facing application of this file together with
  `exists_quadraticTwist_hasSplitMultiplicativeReduction`.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], VII.§1 and VII.§5
* [J.-P. Serre, *Propriétés galoisiennes des points d'ordre fini des courbes elliptiques*],
  §5.3 (for the interaction of twists with reduction types)
-/

@[expose] public section

namespace WeierstrassCurve

universe u

variable {K : Type u} [Field K] (E : WeierstrassCurve K)

/-! ### Multiplicative reduction becomes split after a quadratic twist -/

section Reduction

-- Let `R` be a discrete valuation ring with fraction field `K` (for example the ring of
-- integers of a nonarchimedean local field). The instances are introduced in stages, as needed.
variable (R : Type u) [CommRing R] [Algebra R K]

open Polynomial in
/-- **Twisting flips the square class (residue characteristic ≠ 2).** Combining the split criterion
`nodePoly_map_splits_iff_isSquare` with the coefficient scaling of the quadratic twist
(`c₄_quadraticTwistOf`, `c₆_quadraticTwistOf`), the node polynomial of `W.quadraticTwistOf t n`
splits over a field `k` of characteristic `≠ 2` exactly when `D · (-c₄ c₆)` is a square there, where
`D = t² - 4n`. Thus twisting multiplies the square class governing splitting by `D`: it converts a
nonsplit reduction into a split one precisely when `D` and `-c₄ c₆` lie in the same square class. -/
lemma nodePoly_quadraticTwistOf_map_splits_iff {A : Type*} [CommRing A] {k : Type*} [Field k]
    [NeZero (2 : k)] (φ : A →+* k) (W : WeierstrassCurve A) (t n : A) (hc₄ : φ W.c₄ ≠ 0)
    (hD : φ (t ^ 2 - 4 * n) ≠ 0) :
    ((W.quadraticTwistOf t n).nodePoly.map φ).Splits
      ↔ IsSquare (φ ((t ^ 2 - 4 * n) * -(W.c₄ * W.c₆))) := by
  have key : ∀ s y : k, s ≠ 0 → (IsSquare (s ^ 2 * y) ↔ IsSquare y) := fun s y hs ↦
    ⟨fun ⟨w, hw⟩ ↦ ⟨w / s, by field_simp; linear_combination hw⟩,
      fun ⟨w, hw⟩ ↦ ⟨s * w, by rw [hw]; ring⟩⟩
  have hc₄' : φ (W.quadraticTwistOf t n).c₄ ≠ 0 := by
    rw [c₄_quadraticTwistOf, map_mul, map_pow]; exact mul_ne_zero (pow_ne_zero 2 hD) hc₄
  rw [nodePoly_map_splits_iff_isSquare φ (W.quadraticTwistOf t n) hc₄',
    show -((W.quadraticTwistOf t n).c₄ * (W.quadraticTwistOf t n).c₆)
        = ((t ^ 2 - 4 * n) ^ 2) ^ 2 * ((t ^ 2 - 4 * n) * -(W.c₄ * W.c₆)) from by
      rw [c₄_quadraticTwistOf, c₆_quadraticTwistOf]; ring,
    map_mul, map_pow,
    key _ _ (show φ ((t ^ 2 - 4 * n) ^ 2) ≠ 0 by rw [map_pow]; exact pow_ne_zero 2 hD)]

/-- The `R`-model twist base-changes to the twist over `K`: for `E` integral over `R`, twisting its
integral model by `t, n : R` and base-changing to `K` equals twisting `E` by the images
`(algebraMap R K t, algebraMap R K n)`. Together with the coefficient laws this is the bridge from
the `K`-twist `E.quadraticTwist L` to a genuine `R`-model whose reduction can be computed. -/
theorem baseChange_integralModel_quadraticTwistOf [IsIntegral R E] (t n : R) :
    ((E.integralModel R).quadraticTwistOf t n)⁄K
      = E.quadraticTwistOf (algebraMap R K t) (algebraMap R K n) := by
  change ((E.integralModel R).quadraticTwistOf t n).map (algebraMap R K) = _
  rw [quadraticTwistOf_map, show (E.integralModel R).map (algebraMap R K) = E
    from baseChange_integralModel_eq R E]

variable [IsFractionRing R K]

variable [IsDomain R]

/-- The base change of the twisted integral model has nonzero discriminant: its `Δ` is
`(t'² - 4n')⁶ · Δ` (`Δ_quadraticTwistOf`), and both factors are nonzero. -/
theorem Δ_baseChange_quadraticTwistOf_ne_zero [E.IsElliptic] [IsIntegral R E] (t' n' : R)
    (hD : t' ^ 2 - 4 * n' ≠ 0) :
    ((((E.integralModel R).quadraticTwistOf t' n'))⁄K).Δ ≠ 0 := by
  have hΔint : (E.integralModel R).Δ ≠ 0 := fun h0 ↦
    E.isUnit_Δ.ne_zero (by rw [← integralModel_Δ_eq R E, h0, map_zero])
  rw [show ((((E.integralModel R).quadraticTwistOf t' n'))⁄K).Δ
    = algebraMap R K ((E.integralModel R).quadraticTwistOf t' n').Δ from map_Δ _ _,
    Δ_quadraticTwistOf, Ne, map_eq_zero_iff _ (IsFractionRing.injective R K), mul_eq_zero]
  exact not_or.mpr ⟨pow_ne_zero 6 hD, hΔint⟩

-- From here on, `R` is a discrete valuation ring.
variable [IsDiscreteValuationRing R]

open IsLocalRing IsDedekindDomain.HeightOneSpectrum in
/-- **The twist by a unit discriminant keeps multiplicative reduction.** If `E` has multiplicative
reduction and `D = t² - 4n` is a unit of `R` (residue `≠ 0`), then the base change of the `R`-model
twist `(E.integralModel R).quadraticTwistOf t n` again has multiplicative reduction: its
`c₄ = D² · c₄` is a unit (so the model is minimal and the reduction multiplicative) and its
`Δ = D⁶ · Δ` still has positive valuation. -/
theorem hasMultiplicativeReduction_baseChange_quadraticTwistOf [E.HasMultiplicativeReduction R]
    (t n : R) (hD : residue R (t ^ 2 - 4 * n) ≠ 0) :
    (((E.integralModel R).quadraticTwistOf t n)⁄K).HasMultiplicativeReduction R := by
  set W := (E.integralModel R).quadraticTwistOf t n with hW
  have hWint : IsIntegral R (W⁄K) := ⟨⟨W, rfl⟩⟩
  -- `residue W.c₄ = residue D² · residue (E.integralModel R).c₄ ≠ 0`, `residue W.Δ = 0`.
  have hc₄res : residue R W.c₄ ≠ 0 := by
    rw [hW, c₄_quadraticTwistOf, map_mul, map_pow]
    exact mul_ne_zero (pow_ne_zero 2 hD) (residue_integralModel_c₄_ne_zero E R)
  have hΔres : residue R W.Δ = 0 := by
    rw [hW, Δ_quadraticTwistOf, map_mul, map_pow, residue_integralModel_Δ_eq_zero E R, mul_zero]
  -- Convert to the valuation conditions on the base change `W⁄K`.
  have hc₄val : valuation K (IsDiscreteValuationRing.maximalIdeal R) (W⁄K).c₄ = 1 := by
    rw [show (W⁄K).c₄ = algebraMap R K W.c₄ from map_c₄ W (algebraMap R K)]
    exact (IsDiscreteValuationRing.maximalIdeal R).valuation_eq_one_iff_notMem.mpr
      fun hmem ↦ hc₄res ((residue_eq_zero_iff W.c₄).mpr hmem)
  have hΔval : valuation K (IsDiscreteValuationRing.maximalIdeal R) (W⁄K).Δ < 1 := by
    rw [show (W⁄K).Δ = algebraMap R K W.Δ from map_Δ W (algebraMap R K)]
    exact ((IsDiscreteValuationRing.maximalIdeal R).valuation_lt_one_iff_mem W.Δ).mpr
      ((residue_eq_zero_iff W.Δ).mp hΔres)
  have : IsMinimal R (W⁄K) := isMinimal_of_valuation_c₄_eq_one R (W⁄K) hc₄val
  exact { badReduction := hΔval, multiplicativeReduction := hc₄val }

open IsLocalRing in
/-- If the residue of an integral element `θ` of `S` does not come from the residue field of `R`,
then `θ` does not come from `K` either: an element of `K` integral over the integrally closed `R`
lies in `R`, and residues are compatible. -/
theorem notMem_range_algebraMap_of_residue_notMem {S : Type u} [CommRing S] [IsLocalRing S]
    [Algebra R S] [Algebra.IsIntegral R S] [IsLocalHom (algebraMap R S)] {L : Type u} [Field L]
    [Algebra K L] [Algebra R L] [Algebra S L] [IsScalarTower R S L] [IsScalarTower R K L]
    [IsFractionRing S L] {θ : S}
    (hθ : residue S θ ∉ Set.range (algebraMap (ResidueField R) (ResidueField S))) :
    algebraMap S L θ ∉ Set.range (algebraMap K L) := by
  rintro ⟨a, ha⟩
  have haint : _root_.IsIntegral R a := by
    have h1 : _root_.IsIntegral R (algebraMap S L θ) :=
      _root_.IsIntegral.map (IsScalarTower.toAlgHom R S L) (Algebra.IsIntegral.isIntegral θ)
    rw [← ha] at h1
    exact (isIntegral_algHom_iff (IsScalarTower.toAlgHom R K L)
      (FaithfulSMul.algebraMap_injective K L)).mp h1
  obtain ⟨r, hr⟩ := IsIntegrallyClosed.isIntegral_iff.mp haint
  refine hθ ⟨residue R r, ?_⟩
  rw [show algebraMap (ResidueField R) (ResidueField S) (residue R r)
    = residue S (algebraMap R S r) by simp only [← ResidueField.algebraMap_residue]]
  congr 1
  apply IsFractionRing.injective S L
  rw [← ha, ← hr, ← IsScalarTower.algebraMap_apply R S L, ← IsScalarTower.algebraMap_apply R K L]

open IsLocalRing in
/-- If the root of the reduced node polynomial `P̄` (assumed irreducible) satisfies a monic
quadratic relation `X² - t·X + n` over the residue field, then comparing with the defining
relation of `P̄` (`aeval_root_nodePoly_map`) and using the linear independence of `1` and the root
(`AdjoinRoot.eq_zero_of_mul_root_add_eq_zero`) yields the relations `φc₄·t + φ(a₁c₄) = 0` and
`φc₄·n + φκ = 0` (φ = residue, `κ = 54b₆ - 3b₂b₄ + a₂c₄`). -/
theorem nodePoly_map_root_relations [E.HasMultiplicativeReduction R]
    (hirr : Irreducible ((E.integralModel R).nodePoly.map (algebraMap R (ResidueField R))))
    {t n : ResidueField R}
    (hρ : AdjoinRoot.root ((E.integralModel R).nodePoly.map (algebraMap R (ResidueField R))) ^ 2
        - algebraMap (ResidueField R)
            (AdjoinRoot ((E.integralModel R).nodePoly.map (algebraMap R (ResidueField R)))) t
          * AdjoinRoot.root ((E.integralModel R).nodePoly.map (algebraMap R (ResidueField R)))
        + algebraMap (ResidueField R)
            (AdjoinRoot ((E.integralModel R).nodePoly.map (algebraMap R (ResidueField R)))) n
        = 0) :
    residue R (E.integralModel R).c₄ * t
        + residue R ((E.integralModel R).a₁ * (E.integralModel R).c₄) = 0
      ∧ residue R (E.integralModel R).c₄ * n
        + residue R (54 * (E.integralModel R).b₆
          - 3 * (E.integralModel R).b₂ * (E.integralModel R).b₄
          + (E.integralModel R).a₂ * (E.integralModel R).c₄) = 0 := by
  set P := (E.integralModel R).nodePoly.map (algebraMap R (ResidueField R)) with hP
  have : Fact (Irreducible P) := ⟨hirr⟩
  have hPdeg2 : P.natDegree = 2 := natDegree_nodePoly_map E R
  have hρ2 : algebraMap (ResidueField R) (AdjoinRoot P)
          (algebraMap R (ResidueField R) (E.integralModel R).c₄) * (AdjoinRoot.root P) ^ 2
        + algebraMap (ResidueField R) (AdjoinRoot P)
          (algebraMap R (ResidueField R) ((E.integralModel R).a₁ * (E.integralModel R).c₄))
          * (AdjoinRoot.root P)
        - algebraMap (ResidueField R) (AdjoinRoot P) (algebraMap R (ResidueField R)
          (54 * (E.integralModel R).b₆ - 3 * (E.integralModel R).b₂ * (E.integralModel R).b₄
            + (E.integralModel R).a₂ * (E.integralModel R).c₄)) = 0 :=
    aeval_root_nodePoly_map (algebraMap R (ResidueField R)) (E.integralModel R)
  obtain ⟨hA, hB⟩ := AdjoinRoot.eq_zero_of_mul_root_add_eq_zero hPdeg2.ge
    (a := residue R (E.integralModel R).c₄ * t
      + residue R ((E.integralModel R).a₁ * (E.integralModel R).c₄))
    (b := -(residue R (E.integralModel R).c₄ * n
      + residue R (54 * (E.integralModel R).b₆
        - 3 * (E.integralModel R).b₂ * (E.integralModel R).b₄
        + (E.integralModel R).a₂ * (E.integralModel R).c₄))) (by
    simp only [IsLocalRing.ResidueField.algebraMap_eq, map_add, map_mul, map_neg] at hρ2 ⊢
    linear_combination hρ2
      - algebraMap (ResidueField R) (AdjoinRoot P) (residue R (E.integralModel R).c₄) * hρ)
  rw [neg_eq_zero] at hB
  exact ⟨hA, hB⟩

open IsLocalRing in
/-- The key identity `φc₄ · φ(t'² - 4n') = -φc₆` of the twisting datum `(t', n')`: if its residues
satisfy the trace and norm relations cut out by the node polynomial
(`κ = 54 b₆ - 3 b₂ b₄ + a₂ c₄`), then the discriminant identity `splitPolynomial_discrim` turns
them into this identity. -/
theorem residue_c₄_mul_residue_eq_neg_c₆ [E.HasMultiplicativeReduction R] (t' n' : R)
    (hA : residue R (E.integralModel R).c₄ * residue R t'
      + residue R ((E.integralModel R).a₁ * (E.integralModel R).c₄) = 0)
    (hB : residue R (E.integralModel R).c₄ * residue R n'
      + residue R (54 * (E.integralModel R).b₆
        - 3 * (E.integralModel R).b₂ * (E.integralModel R).b₄
        + (E.integralModel R).a₂ * (E.integralModel R).c₄) = 0) :
    residue R (E.integralModel R).c₄ * residue R (t' ^ 2 - 4 * n')
      = -residue R (E.integralModel R).c₆ := by
  set c₄' := (E.integralModel R).c₄ with hc₄'
  set κ' := 54 * (E.integralModel R).b₆ - 3 * (E.integralModel R).b₂ * (E.integralModel R).b₄
    + (E.integralModel R).a₂ * c₄' with hκ'
  simp only [map_mul] at hA
  have hRid : ((E.integralModel R).a₁ * c₄') ^ 2 + 4 * c₄' * κ'
      = -(c₄' * (E.integralModel R).c₆) := by
    rw [hκ', hc₄']
    exact splitPolynomial_discrim (E.integralModel R)
  have hdisc := congrArg (residue R) hRid
  simp only [map_add, map_mul, map_pow, map_neg, map_ofNat] at hdisc
  apply mul_left_cancel₀ (residue_integralModel_c₄_ne_zero E R)
  simp only [map_sub, map_mul, map_pow, map_ofNat]
  linear_combination hdisc
    + (residue R c₄' * residue R t' - residue R (E.integralModel R).a₁ * residue R c₄') * hA
    - 4 * residue R c₄' * hB

open IsLocalRing in
/-- The residue characteristic `2` case of `nodePoly_quadraticTwistOf_map_splits_of_residue`:
the Artin–Schreier split condition (`nodePoly_map_splits_iff_of_two_eq_zero`) holds with `z = 0`,
because `φ κ_W = 0`. Indeed `κ_W = D³κ - D²·n·a₁²·c₄` (`kappa_quadraticTwistOf`), and
`φκ = -φc₄·φn` (`hB`), `φa₁ = -φt'` (`hA`), `φD = φt'²` (as `4 = 0`), so
`φκ_W = -φD²·φc₄·φn·(φD + φa₁²) = -φD²·φc₄·φn·(2·φt'²) = 0`. -/
theorem nodePoly_quadraticTwistOf_map_splits_of_residue_of_two_eq_zero
    [E.HasMultiplicativeReduction R] (t' n' : R) (h2 : (2 : ResidueField R) = 0)
    (hA : residue R (E.integralModel R).c₄ * residue R t'
      + residue R ((E.integralModel R).a₁ * (E.integralModel R).c₄) = 0)
    (hB : residue R (E.integralModel R).c₄ * residue R n'
      + residue R (54 * (E.integralModel R).b₆
        - 3 * (E.integralModel R).b₂ * (E.integralModel R).b₄
        + (E.integralModel R).a₂ * (E.integralModel R).c₄) = 0) :
    Polynomial.Splits (((E.integralModel R).quadraticTwistOf t' n').nodePoly.map
      (algebraMap R (ResidueField R))) := by
  -- `D = t'²-4n'` has nonzero residue (`residue_c₄_mul_residue_eq_neg_c₆`: `φc₄·φD = -φc₆ ≠ 0`).
  have hkey := residue_c₄_mul_residue_eq_neg_c₆ E R t' n' hA hB
  have hDne : residue R (t' ^ 2 - 4 * n') ≠ 0 := fun h0 ↦
    residue_integralModel_c₆_ne_zero E R (neg_eq_zero.mp (by rw [← hkey, h0, mul_zero]))
  set c₄' := (E.integralModel R).c₄ with hc₄'
  set κ' := 54 * (E.integralModel R).b₆ - 3 * (E.integralModel R).b₂ * (E.integralModel R).b₄
    + (E.integralModel R).a₂ * c₄' with hκ'
  simp only [map_mul] at hA
  have hc₄0 : residue R (E.integralModel R).c₄ ≠ 0 := residue_integralModel_c₄_ne_zero E R
  have hc₄map : algebraMap R (ResidueField R) (E.integralModel R).c₄ ≠ 0 := by
    rw [ResidueField.algebraMap_eq]; exact hc₄0
  set D := t' ^ 2 - 4 * n' with hDdef
  have h4 : (4 : ResidueField R) = 0 := by
    rw [show (4 : ResidueField R) = 2 * 2 by norm_num, h2, mul_zero]
  have hDmap : algebraMap R (ResidueField R) D ≠ 0 := by
    rw [ResidueField.algebraMap_eq]; exact hDne
  have hDt : residue R D = residue R t' ^ 2 := by
    rw [hDdef, map_sub, map_mul, map_pow, map_ofNat, h4, zero_mul, sub_zero]
  have hWc₄ : algebraMap R (ResidueField R)
      ((E.integralModel R).quadraticTwistOf t' n').c₄ ≠ 0 := by
    rw [c₄_quadraticTwistOf, ← hDdef, map_mul, map_pow]
    exact mul_ne_zero (pow_ne_zero 2 hDmap) hc₄map
  have hWc₆ : algebraMap R (ResidueField R)
      ((E.integralModel R).quadraticTwistOf t' n').c₆ ≠ 0 := by
    rw [c₆_quadraticTwistOf, ← hDdef, map_mul, map_pow]
    exact mul_ne_zero (pow_ne_zero 3 hDmap)
      (by rw [ResidueField.algebraMap_eq]; exact residue_integralModel_c₆_ne_zero E R)
  have hta : residue R (E.integralModel R).a₁ = -residue R t' := by
    rcases mul_eq_zero.mp (show residue R c₄'
        * (residue R t' + residue R (E.integralModel R).a₁) = 0 by linear_combination hA)
      with hz | hz
    · exact absurd hz hc₄0
    · linear_combination hz
  have hκW_eq : 54 * ((E.integralModel R).quadraticTwistOf t' n').b₆
      - 3 * ((E.integralModel R).quadraticTwistOf t' n').b₂
          * ((E.integralModel R).quadraticTwistOf t' n').b₄
      + ((E.integralModel R).quadraticTwistOf t' n').a₂
          * ((E.integralModel R).quadraticTwistOf t' n').c₄
      = D ^ 3 * κ' - D ^ 2 * n' * (E.integralModel R).a₁ ^ 2 * c₄' := by
    rw [hDdef, hκ', hc₄']
    exact kappa_quadraticTwistOf (E.integralModel R) t' n'
  have hWc₄eq : ((E.integralModel R).quadraticTwistOf t' n').c₄ = D ^ 2 * c₄' := by
    rw [c₄_quadraticTwistOf, ← hDdef, hc₄']
  have hκW0 : algebraMap R (ResidueField R)
      (D ^ 3 * κ' - D ^ 2 * n' * (E.integralModel R).a₁ ^ 2 * c₄') = 0 := by
    simp only [map_sub, map_mul, map_pow, ResidueField.algebraMap_eq, hDt, hta]
    linear_combination (residue R t') ^ 6 * hB
      - (residue R t') ^ 6 * residue R n' * residue R c₄' * h2
  rw [nodePoly_map_splits_iff_of_two_eq_zero h2 (algebraMap R (ResidueField R))
    ((E.integralModel R).quadraticTwistOf t' n') hWc₄ hWc₆]
  refine ⟨0, ?_⟩
  rw [hκW_eq, hWc₄eq, show (0 : ResidueField R) ^ 2 + 0 = 0 from by ring, mul_zero, hκW0,
    neg_zero, mul_zero]

open IsLocalRing in
/-- If the residues of `(t', n')` satisfy the trace and norm relations cut out by the node
polynomial, then the node polynomial of the quadratic twist of the integral model by `(t', n')`
splits over the residue field: the key identity `φc₄ · φ(t'² - 4n') = -φc₆`
(`residue_c₄_mul_residue_eq_neg_c₆`) reduces this to a square-class computation for residue
characteristic `≠ 2`, and to an Artin–Schreier computation for residue characteristic `2`
(`nodePoly_quadraticTwistOf_map_splits_of_residue_of_two_eq_zero`). -/
theorem nodePoly_quadraticTwistOf_map_splits_of_residue
    [E.HasMultiplicativeReduction R] (t' n' : R)
    (hA : residue R (E.integralModel R).c₄ * residue R t'
      + residue R ((E.integralModel R).a₁ * (E.integralModel R).c₄) = 0)
    (hB : residue R (E.integralModel R).c₄ * residue R n'
      + residue R (54 * (E.integralModel R).b₆
        - 3 * (E.integralModel R).b₂ * (E.integralModel R).b₄
        + (E.integralModel R).a₂ * (E.integralModel R).c₄) = 0) :
    Polynomial.Splits (((E.integralModel R).quadraticTwistOf t' n').nodePoly.map
      (algebraMap R (ResidueField R))) := by
  rcases ne_or_eq (2 : ResidueField R) 0 with h2 | h2
  · -- Residue characteristic `≠ 2`: split ↔ `IsSquare (φ((t'²-4n')·-(c₄c₆)))`, which `hkey` shows
    -- equals `IsSquare (φc₆²)`.
    have hkey := residue_c₄_mul_residue_eq_neg_c₆ E R t' n' hA hB
    have hDne : residue R (t' ^ 2 - 4 * n') ≠ 0 := fun h0 ↦
      residue_integralModel_c₆_ne_zero E R (neg_eq_zero.mp (by rw [← hkey, h0, mul_zero]))
    have hc₄0 : residue R (E.integralModel R).c₄ ≠ 0 := residue_integralModel_c₄_ne_zero E R
    have : NeZero (2 : ResidueField R) := ⟨h2⟩
    rw [nodePoly_quadraticTwistOf_map_splits_iff (algebraMap R (ResidueField R))
      (E.integralModel R) t' n' (by rw [ResidueField.algebraMap_eq]; exact hc₄0)
      (by rw [ResidueField.algebraMap_eq]; exact hDne)]
    refine ⟨residue R (E.integralModel R).c₆, ?_⟩
    apply mul_left_cancel₀ hc₄0
    rw [ResidueField.algebraMap_eq]
    simp only [map_mul, map_neg]
    linear_combination
      (-(residue R (E.integralModel R).c₄ * residue R (E.integralModel R).c₆)) * hkey
  · exact nodePoly_quadraticTwistOf_map_splits_of_residue_of_two_eq_zero E R t' n' h2 hA hB

open IsLocalRing in
/-- Packaging `nodePoly_quadraticTwistOf_map_splits_of_residue`: if the base change of the twisted
integral model has multiplicative reduction and the residues of `(t', n')` satisfy the trace and
norm relations, then the reduction is *split* multiplicative. -/
theorem hasSplitMultiplicativeReduction_quadraticTwistOf_of_residue
    [E.HasMultiplicativeReduction R] (t' n' : R)
    [hW : (((E.integralModel R).quadraticTwistOf t' n')⁄K).HasMultiplicativeReduction R]
    (hA : residue R (E.integralModel R).c₄ * residue R t'
      + residue R ((E.integralModel R).a₁ * (E.integralModel R).c₄) = 0)
    (hB : residue R (E.integralModel R).c₄ * residue R n'
      + residue R (54 * (E.integralModel R).b₆
        - 3 * (E.integralModel R).b₂ * (E.integralModel R).b₄
        + (E.integralModel R).a₂ * (E.integralModel R).c₄) = 0) :
    (((E.integralModel R).quadraticTwistOf t' n')⁄K).HasSplitMultiplicativeReduction R := by
  refine { hW with splitMultiplicativeReduction := ?_ }
  rw [show (((E.integralModel R).quadraticTwistOf t' n')⁄K).integralModel R
    = (E.integralModel R).quadraticTwistOf t' n' from integralModel_baseChange R _]
  exact nodePoly_quadraticTwistOf_map_splits_of_residue E R t' n' hA hB

variable [E.IsElliptic]

open IsLocalRing in
/-- If `E` has multiplicative reduction which is not split, then `E` has a quadratic twist with
split multiplicative reduction — namely the twist by the unramified quadratic extension of `K`:
the reduction of the twist is the same nodal cubic with the Galois action on the two tangent
directions at the node twisted into triviality.

Mathlib's reduction-type predicates apply to a specific Weierstrass equation and require it to
be minimal, while our chosen model `E.quadraticTwist L` of the twist need not be; so the
conclusion is phrased via the minimal model `(E.quadraticTwist L).minimal R`. (Being split
multiplicative is intrinsic, so any other minimal model would do.)

The nonsplitness hypothesis `h` cannot be dropped: if `E` already has split multiplicative
reduction then *no* quadratic twist of `E` has split multiplicative reduction, since the
unramified quadratic twist has nonsplit multiplicative reduction and ramified quadratic twists
have additive reduction. -/
theorem exists_quadraticTwist_hasSplitMultiplicativeReduction [E.HasMultiplicativeReduction R]
    (h : ¬E.HasSplitMultiplicativeReduction R) :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra K L) (_ : Algebra.IsQuadraticExtension K L)
      (_ : Algebra.IsSeparable K L),
      ((E.quadraticTwist L).minimal R).HasSplitMultiplicativeReduction R := by
  -- The node polynomial reduced to the residue field `k`; nonsplitness makes it irreducible
  -- (`irreducible_nodePoly_map`), and multiplicative reduction makes it separable
  -- (`separable_nodePoly_map`). Its root field `k' = k[X]/(P)` is therefore a separable
  -- quadratic extension of `k`.
  set P := (E.integralModel R).nodePoly.map (algebraMap R (ResidueField R)) with hP
  have hirr : Irreducible P := irreducible_nodePoly_map E R h
  have : Fact (Irreducible P) := ⟨hirr⟩
  have hPdeg2 : P.natDegree = 2 := natDegree_nodePoly_map E R
  have hk'rank : Module.finrank (ResidueField R) (AdjoinRoot P) = 2 :=
    AdjoinRoot.finrank_eq_natDegree.trans hPdeg2
  have : FiniteDimensional (ResidueField R) (AdjoinRoot P) := .of_finrank_eq_succ hk'rank
  have : Algebra.IsSeparable (ResidueField R) (AdjoinRoot P) :=
    AdjoinRoot.isSeparable_of_separable (separable_nodePoly_map E R)
  -- Lift `k'` to the unramified quadratic extension `L/K` (`LiftSeparableExtension`).
  obtain ⟨L, _, _, _, _, _, _, S, _, _, _, _, _, _, _, _, _, hLrank, ⟨resIso⟩⟩ :=
    exists_unramified_extension_of_residueField (R := R) (K := K) (AdjoinRoot P)
  have : Algebra.IsQuadraticExtension K L := ⟨hLrank.trans hk'rank⟩
  refine ⟨L, ‹Field L›, ‹Algebra K L›, ‹Algebra.IsQuadraticExtension K L›,
    ‹Algebra.IsSeparable K L›, ?_⟩
  -- `S = 𝒪_L` is the integral closure of `R` in `L` (now that `Frac S = L` is proved), so `L` is
  -- the base-change localization of `S`, and `R`-trace/norm are compatible with `K`-trace/norm.
  have : Algebra.IsIntegral R S := Algebra.IsIntegral.of_finite R S
  have : IsIntegralClosure S R L := IsIntegralClosure.of_isIntegrallyClosed S R L
  have : IsLocalization (Algebra.algebraMapSubmonoid S (nonZeroDivisors R)) L :=
    IsIntegralClosure.isLocalization_of_isSeparable R K L S
  have : Module.IsTorsionFree R L := Module.IsTorsionFree.trans_faithfulSMul R K L
  have : Module.Free R S := IsIntegralClosure.module_free R K L S
  have hSrank : Module.finrank R S = 2 :=
    (IsIntegralClosure.rank R K L S).trans (Algebra.IsQuadraticExtension.finrank_eq_two K L)
  obtain ⟨θ', hθ'res⟩ := IsLocalRing.residue_surjective (resIso.symm (AdjoinRoot.root P))
  -- Via `resIso`, `root P` satisfies the Cayley–Hamilton relation `X² - φ(t')·X + φ(n')` of `θ'`
  -- (`sq_sub_trace_mul_self_add_norm_residue`); comparing with the defining relation of `P` gives
  -- the residue relations `φc₄·φt' = -φ(a₁c₄)` and `φc₄·φn' = -φκ` (`nodePoly_map_root_relations`).
  have hρ1 := sq_sub_trace_mul_self_add_norm_residue R hSrank resIso θ'
  rw [hθ'res, resIso.apply_symm_apply] at hρ1
  obtain ⟨hA, hB⟩ := nodePoly_map_root_relations E R hirr hρ1
  set t' := Algebra.trace R S θ'
  set n' := Algebra.norm R θ'
  -- `root P ∉ k` (its minimal polynomial has degree 2), so `θ'̄ = resIso⁻¹(root P) ∉ k` and, since
  -- `R` is integrally closed, `algebraMap S L θ' ∉ K` — the twist by `θ'` is nontrivial.
  have hθ' : algebraMap S L θ' ∉ Set.range (algebraMap K L) :=
    notMem_range_algebraMap_of_residue_notMem R (by
      rw [hθ'res]
      exact fun hmem ↦ AdjoinRoot.root_notMem_range_algebraMap hPdeg2.ge
        (resIso.symm.apply_mem_range_algebraMap_iff.mp hmem))
  -- Trace/norm land in `K`, giving the connection to the `R`-model `W = quadraticTwistOf t' n'`.
  have htr : Algebra.trace K L (algebraMap S L θ') = algebraMap R K t' :=
    Algebra.trace_localization R (nonZeroDivisors R) θ'
  have hnr : Algebra.norm K (algebraMap S L θ') = algebraMap R K n' :=
    Algebra.norm_localization R (nonZeroDivisors R) θ'
  obtain ⟨C, hC⟩ := E.exists_smul_quadraticTwist_eq_quadraticTwistBy L hθ'
  rw [quadraticTwistBy, htr, hnr, ← baseChange_integralModel_quadraticTwistOf E R t' n'] at hC
  -- `D = t'²-4n'` is a unit (`residue_c₄_mul_residue_eq_neg_c₆`: `φc₄·φD = -φc₆ ≠ 0`), so `W⁄K`
  -- has multiplicative reduction; the relations `hA`, `hB` make it split
  -- (`nodePoly_quadraticTwistOf_map_splits_of_residue`).
  have hkey := residue_c₄_mul_residue_eq_neg_c₆ E R t' n' hA hB
  have hDne : residue R (t' ^ 2 - 4 * n') ≠ 0 := fun h0 ↦
    residue_integralModel_c₆_ne_zero E R (neg_eq_zero.mp (by rw [← hkey, h0, mul_zero]))
  have hWmult := hasMultiplicativeReduction_baseChange_quadraticTwistOf E R t' n' hDne
  have hWsplit := hasSplitMultiplicativeReduction_quadraticTwistOf_of_residue E R t' n' hA hB
  -- `hWsplit : (W⁄K).HasSplitMultiplicativeReduction R` with `W⁄K` minimal and
  -- `hC : C • E.quadraticTwist L = W⁄K`. Split multiplicativity transfers to the chosen minimal
  -- model `(E.quadraticTwist L).minimal R`, which is another minimal model of
  -- `E.quadraticTwist L` (`of_isMinimal_smul`).
  have : IsMinimal R (((E.integralModel R).quadraticTwistOf t' n')⁄K) := hWmult.toIsMinimal
  have hD : (((E.quadraticTwist L).exists_isMinimal R).choose * C⁻¹)
      • (((E.integralModel R).quadraticTwistOf t' n')⁄K) = (E.quadraticTwist L).minimal R := by
    rw [mul_smul, ← hC, inv_smul_smul]; rfl
  have : (((E.integralModel R).quadraticTwistOf t' n')⁄K).IsElliptic :=
    ⟨(Δ_baseChange_quadraticTwistOf_ne_zero E R t' n' fun h0 ↦
      hDne (by rw [h0, map_zero])).isUnit⟩
  exact HasSplitMultiplicativeReduction.of_isMinimal_smul R _ hD hWsplit

end Reduction

end WeierstrassCurve

end
