/-
Copyright (c) 2026 Pedro Paulo Marques do Nascimento. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pedro Paulo Marques do Nascimento
-/
module

public import FLT.Data.QHat.Padics
public import FLT.NumberField.AdeleRing

/-!
# The finite rational adeles as `QHat`

This file identifies the finite adele ring of `ℚ`, defined as a restricted product over the
finite places of `ℚ`, with the explicit model `QHat = ℚ ⊗[ℤ] ZHat`. It also shows that the
principal rational adeles correspond to `QHat.ratsub` and that the integral finite adeles
correspond to `QHat.zHatsub`.

## Main definitions

* `finiteAdeleRingEquivQHat`: the `ℚ`-algebra equivalence between the two models of the finite
  rational adeles.
-/

@[expose] public section

open NumberField IsDedekindDomain
open scoped RestrictedProduct

local instance {p : Nat.Primes} : Fact p.1.Prime := ⟨p.2⟩

variable (K : Type*) [Field K] [NumberField K]

/-- The subgroup of principal finite adeles `(x)ᵥ`, where `x ∈ K`. -/
noncomputable def FiniteAdeleRing.principalSubgroup :
    AddSubgroup (FiniteAdeleRing (𝓞 K) K) :=
  (algebraMap K _).range.toAddSubgroup

/-- The `ℚ`-algebra equivalence between `FiniteAdeleRing (𝓞 ℚ) ℚ` and `QHat`. -/
noncomputable def finiteAdeleRingEquivQHat :
    FiniteAdeleRing (𝓞 ℚ) ℚ ≃ₐ[ℚ] QHat :=
  Rat.FiniteAdeleRing.padicEquiv.trans QHat.padicRestrictedProductEquiv.symm

theorem finiteAdeleRingEquivQHat_algebraMap (q : ℚ) :
    finiteAdeleRingEquivQHat (algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) q) = QHat.i₁ q := by
  rw [finiteAdeleRingEquivQHat.commutes]
  rfl

theorem principalSubgroup_equiv_ratsub :
    finiteAdeleRingEquivQHat '' (FiniteAdeleRing.principalSubgroup ℚ) = QHat.ratsub := by
  ext q
  constructor
  · rintro ⟨a, ⟨r, rfl⟩, rfl⟩
    exact ⟨r, (finiteAdeleRingEquivQHat_algebraMap r).symm⟩
  · rintro ⟨r, rfl⟩
    exact ⟨algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) r, ⟨r, rfl⟩,
      finiteAdeleRingEquivQHat_algebraMap r⟩

theorem toPadicRestrictedProduct_finiteAdeleRingEquivQHat
    (a : FiniteAdeleRing (𝓞 ℚ) ℚ) :
    QHat.toPadicRestrictedProduct (finiteAdeleRingEquivQHat a) =
      Rat.FiniteAdeleRing.padicEquiv a := by
  change QHat.padicRestrictedProductEquiv
      (QHat.padicRestrictedProductEquiv.symm (Rat.FiniteAdeleRing.padicEquiv a)) = _
  exact QHat.padicRestrictedProductEquiv.apply_symm_apply _

theorem finiteIntegralAdeles_equiv_zHatsub :
    finiteAdeleRingEquivQHat ''
        (FiniteAdeleRing.integralAdeles (𝓞 ℚ) ℚ : Set (FiniteAdeleRing (𝓞 ℚ) ℚ)) =
      (QHat.zHatsub : Set QHat) := by
  ext q
  constructor
  · rintro ⟨a, ha, rfl⟩
    have hT : Rat.FiniteAdeleRing.padicEquiv a ∈
        RestrictedProduct.structureSubring
          (fun p : Nat.Primes ↦ ℚ_[p]) (fun p ↦ PadicInt.subring p) Filter.cofinite :=
      Rat.FiniteAdeleRing.padicEquiv_bijOn.mapsTo ha
    have hT' : QHat.toPadicRestrictedProduct (finiteAdeleRingEquivQHat a) ∈
        RestrictedProduct.structureSubring
          (fun p : Nat.Primes ↦ ℚ_[p]) (fun p ↦ PadicInt.subring p) Filter.cofinite := by
      rwa [toPadicRestrictedProduct_finiteAdeleRingEquivQHat]
    have hImage := (Set.ext_iff.mp QHat.image_zHatsub
      (QHat.toPadicRestrictedProduct (finiteAdeleRingEquivQHat a))).mpr hT'
    obtain ⟨q, hq, hqmap⟩ := hImage
    have hqeq : q = finiteAdeleRingEquivQHat a :=
      QHat.toPadicRestrictedProduct_injective hqmap
    simpa [hqeq] using hq
  · intro hq
    have hT : QHat.toPadicRestrictedProduct q ∈
        RestrictedProduct.structureSubring
          (fun p : Nat.Primes ↦ ℚ_[p]) (fun p ↦ PadicInt.subring p) Filter.cofinite := by
      exact (Set.ext_iff.mp QHat.image_zHatsub
        (QHat.toPadicRestrictedProduct q)).mp ⟨q, hq, rfl⟩
    let a : FiniteAdeleRing (𝓞 ℚ) ℚ :=
      Rat.FiniteAdeleRing.padicEquiv.symm (QHat.toPadicRestrictedProduct q)
    have ha : a ∈ FiniteAdeleRing.integralAdeles (𝓞 ℚ) ℚ := by
      exact (Rat.FiniteAdeleRing.padicEquiv_bijOn.symm
        Rat.FiniteAdeleRing.padicEquiv.toEquiv.invOn).mapsTo hT
    refine ⟨a, ha, ?_⟩
    apply QHat.toPadicRestrictedProduct_injective
    rw [toPadicRestrictedProduct_finiteAdeleRingEquivQHat]
    exact Rat.FiniteAdeleRing.padicEquiv.apply_symm_apply _
