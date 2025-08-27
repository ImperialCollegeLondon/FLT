/-
Copyright (c) 2025 Matthew Jasper. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Jasper
-/

import FLT.DedekindDomain.FiniteAdeleRing.TensorPi
import FLT.Mathlib.Topology.Algebra.RestrictedProduct.Basic
import Mathlib.RingTheory.Flat.Basic

namespace RestrictedProduct

open TensorProduct

variable (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M]
  {ι : Type*} (N : ι → Type*) [∀ i, AddCommGroup (N i)]
  [∀ i, Module R (N i)]

variable (ℱ : Filter ι) (L : ∀ i, Submodule R (N i))

/-- `M ⊗_R (L i)` as a submodule of `M ⊗_R (N i)`. -/
def rangeLTensor (i : ι) : Submodule R (M ⊗[R] N i) :=
  LinearMap.range (LinearMap.lTensor M ((L i).subtype))

/-- The `R`-linear map `φ : M ⊗_R ∏'_i [N i, L i]_[𝓕] → ∏'_i [M ⊗_R (N i), M ⊗_R (L i)]_[𝓕]`
given by `φ (m ⊗ n) i = m ⊗ (n i)`. -/
def lTensor :
    M ⊗[R] Πʳ i, [N i, L i]_[ℱ] →ₗ[R] Πʳ i, [M ⊗[R] N i, rangeLTensor R M N L i]_[ℱ] :=
  have hmap : ∀ (m : M), ∀ᶠ (j : ι) in ℱ, Set.MapsTo
      (TensorProduct.mk R M (N j) m) (L j) (rangeLTensor R M N L j) := by
    intro m
    filter_upwards with i n hn using ⟨m ⊗ₜ[R] ⟨n, hn⟩, rfl⟩
  TensorProduct.lift {
    toFun m := mapAlongLinearMap N _ id Filter.tendsto_id
        (fun i ↦ TensorProduct.mk R M (N i) m) (hmap m)
    map_add' m n := by ext; simp
    map_smul' a m := by ext; simp
  }

@[simp]
lemma lTensor_tmul (m : M) (f : Πʳ i, [N i, L i]_[ℱ]) (i : ι) :
    lTensor R M N ℱ L (m ⊗ₜ f) i = m ⊗ₜ (f i) :=
  rfl

variable (S : Set ι) [Module.FinitePresentation R M] [Module.Flat R M]

/-- `R`-Linear isomorphism between `M ⊗_R (L i)` and `rangeLTensor R M N L i`. -/
noncomputable def tmulEquivRangeLTensor (i : ι) : M ⊗[R] (L i) ≃ₗ[R] rangeLTensor R M N L i :=
  LinearEquiv.ofInjective (LinearMap.lTensor M (Submodule.subtype <| L i))
    (Module.Flat.lTensor_preserves_injective_linearMap (L i).subtype
      (Submodule.injective_subtype (L i)))

open scoped Filter in
/-- `R`-Linear isomorphism that's propositionally equal to `lTensor`. -/
noncomputable def lTensorPrincipalEquiv :
    M ⊗[R] Πʳ i, [N i, L i]_[𝓟 S] ≃ₗ[R] Πʳ i, [M ⊗[R] N i, rangeLTensor R M N L i]_[𝓟 S] :=
  open scoped Classical in
  let N' (i : ι) := if i ∈ S then L i else (⊤ : Submodule R (N i))
  let f : Πʳ i, [N i, L i]_[𝓟 S] ≃ₗ[R] (Π i, N' i) := {
    toFun x i := ⟨x i, by
      by_cases h : i ∈ S
      · simpa [N', h] using x.property h
      · simp [N', h]⟩
    invFun x := ⟨fun i ↦ x i, by
      rw [Filter.eventually_principal]
      intro y hy
      simpa only [N', hy, ↓reduceIte] using (x y).prop⟩
    map_add' x y := by ext; simp
    map_smul' a x := by ext; simp
  }
  let g1 : M ⊗[R] Πʳ i, [N i, L i]_[𝓟 S] ≃ₗ[R] M ⊗[R] (Π i, N' i) := LinearEquiv.lTensor M f
  let g2 : M ⊗[R] (Π i, N' i) ≃ₗ[R] Π i, M ⊗[R] N' i :=
    tensorPi_equiv_piTensor' R M fun i ↦ ↥(N' i)
  let gEquiv (i : ι) (h : i ∈ S) : M ⊗[R] (N' i) ≃ₗ[R] rangeLTensor R M N L i :=
    (LinearEquiv.lTensor M (LinearEquiv.ofEq _ _ (by simp [N', h]))) ≪≫ₗ
      (tmulEquivRangeLTensor R M N L i)
  let gEquiv' (i : ι) (h : i ∉ S) : M ⊗[R] (N' i) ≃ₗ[R] M ⊗[R] N i :=
    LinearEquiv.lTensor M <| LinearEquiv.ofTop (N' i) (by simp [N', h])
  let g3 : (Π i, M ⊗[R] N' i) ≃ₗ[R] Πʳ i, [M ⊗[R] N i, rangeLTensor R M N L i]_[𝓟 S] := {
    toFun x := ⟨
      fun i ↦ if h : i ∈ S then gEquiv i h (x i) else gEquiv' i h (x i),
      by
        rw [Filter.eventually_principal]
        intro i h
        simp [h]⟩
    invFun x i := if h : i ∈ S then
        gEquiv i h |>.symm ⟨(x i), by simpa using x.property h⟩
      else
        gEquiv' i h |>.symm (x i)
    left_inv x := by
      ext i
      by_cases h : i ∈ S <;> simp [h]
    right_inv x := by
      ext i
      by_cases h : i ∈ S <;> simp [h]
    map_add' x y := by
      ext i
      by_cases h : i ∈ S <;> simp [h]
    map_smul' a x := by
      ext i
      by_cases h : i ∈ S <;> simp [h]
  }
  g1 ≪≫ₗ g2 ≪≫ₗ g3

open scoped Filter in
lemma lTensorPrincipalEquiv_tmul (m : M) (x : Πʳ i, [N i, L i]_[𝓟 S]) (i : ι) :
    lTensorPrincipalEquiv R M N L S (m ⊗ₜ x) i = m ⊗ₜ x i := by
  simp [lTensorPrincipalEquiv, tensorPi_equiv_piTensor'_apply, tmulEquivRangeLTensor,
      rangeLTensor]

lemma lTensor_bijective : Function.Bijective (lTensor R M N ℱ L) :=
  -- Should follow from the above and general results about direct
  -- limits of tensor products.
  sorry

/-- The `R`-linear isomorphism given by `lTensor` when `M` is a finite flat `R`-module. -/
noncomputable def lTensorEquiv :
    M ⊗[R] Πʳ i, [N i, L i]_[ℱ] ≃ₗ[R] Πʳ i, [M ⊗[R] N i, rangeLTensor R M N L i]_[ℱ] :=
  LinearEquiv.ofBijective (lTensor R M N ℱ L) (lTensor_bijective R M N ℱ L)

@[simp]
lemma lTensorEquiv_tmul (m : M) (f : Πʳ i, [N i, L i]_[ℱ]) (i : ι) :
    lTensorEquiv R M N ℱ L (m ⊗ₜ f) i = m ⊗ₜ (f i) :=
  rfl

end RestrictedProduct
