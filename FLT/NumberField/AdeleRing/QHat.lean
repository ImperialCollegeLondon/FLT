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

/-- The `ℚ`-algebra equivalence between `FiniteAdeleRing (𝓞 ℚ) ℚ` and `QHat`. -/
noncomputable def finiteAdeleRingEquivQHat :
    FiniteAdeleRing (𝓞 ℚ) ℚ ≃ₐ[ℚ] QHat :=
  Rat.FiniteAdeleRing.padicEquiv.trans QHat.padicRestrictedProductEquiv.symm

theorem finiteAdeleRingEquivQHat_algebraMap (q : ℚ) :
    finiteAdeleRingEquivQHat (algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) q) = QHat.i₁ q := by
  rw [finiteAdeleRingEquivQHat.commutes]
  rfl

theorem finiteAdeleRingEquivQHat_map_principalSubgroup :
    (FiniteAdeleRing.principalSubgroup (𝓞 ℚ) ℚ).map
      finiteAdeleRingEquivQHat.toAddMonoidHom = QHat.ratsub := by
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

theorem finiteAdeleRingEquivQHat_map_integralAdeles :
    (FiniteAdeleRing.integralAdeles (𝓞 ℚ) ℚ).toAddSubgroup.map
      finiteAdeleRingEquivQHat.toAddMonoidHom = QHat.zHatsub := by
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
    have hMap : QHat.toPadicRestrictedProduct (finiteAdeleRingEquivQHat a) ∈
        QHat.zHatsub.map QHat.toPadicRestrictedProduct.toAddMonoidHom := by
      rwa [QHat.toPadicRestrictedProduct_map_zHatsub]
    obtain ⟨q, hq, hqmap⟩ := hMap
    have hqeq : q = finiteAdeleRingEquivQHat a :=
      QHat.toPadicRestrictedProduct_injective hqmap
    simpa [hqeq] using hq
  · intro hq
    have hT : QHat.toPadicRestrictedProduct q ∈
        RestrictedProduct.structureSubring
          (fun p : Nat.Primes ↦ ℚ_[p]) (fun p ↦ PadicInt.subring p) Filter.cofinite := by
      have hMap : QHat.toPadicRestrictedProduct q ∈
          QHat.zHatsub.map QHat.toPadicRestrictedProduct.toAddMonoidHom := ⟨q, hq, rfl⟩
      exact (SetLike.ext_iff.mp QHat.toPadicRestrictedProduct_map_zHatsub _).mp hMap
    let a : FiniteAdeleRing (𝓞 ℚ) ℚ :=
      Rat.FiniteAdeleRing.padicEquiv.symm (QHat.toPadicRestrictedProduct q)
    have ha : a ∈ FiniteAdeleRing.integralAdeles (𝓞 ℚ) ℚ := by
      exact (Rat.FiniteAdeleRing.padicEquiv_bijOn.symm
        Rat.FiniteAdeleRing.padicEquiv.toEquiv.invOn).mapsTo hT
    refine ⟨a, ha, ?_⟩
    apply QHat.toPadicRestrictedProduct_injective
    change QHat.toPadicRestrictedProduct (finiteAdeleRingEquivQHat a) = _
    rw [toPadicRestrictedProduct_finiteAdeleRingEquivQHat]
    exact Rat.FiniteAdeleRing.padicEquiv.apply_symm_apply _
