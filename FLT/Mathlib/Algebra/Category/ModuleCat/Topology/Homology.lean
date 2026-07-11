/-
Copyright (c) 2026 Yunzhou Xie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Edison Xie
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Topology.Homology
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import FLT.Mathlib.Algebra.Category.ModuleCat.Topology.Basic

/-!
# Kernels, cokernels and homology of topological modules

This file develops API for the concrete kernel and cokernel models of `TopModuleCat`:

* `TopModuleCat.cokerDesc`: the universal property of the concrete quotient `TopModuleCat.coker`.
* `TopModuleCat.cokerCongr`: cokernels of morphisms identified under an isomorphism of the
  targets are isomorphic.
* `TopModuleCat.cokerDescCLM` and `TopModuleCat.cokerDescBilinear`: descending continuous linear
  maps and jointly continuous bilinear pairings along cokernel projections.
* `HomologicalComplex.cyclesIsoKer` and `HomologicalComplex.homologyIsoCoker`: the cycles and
  homology of a complex of topological modules identified with the kernel of the differential
  carrying the subspace topology, respectively the quotient of the cycles by the boundaries
  carrying the quotient topology.

Material destined for `Mathlib.Algebra.Category.ModuleCat.Topology.Homology`.
-/

@[expose] public section

universe u v w

namespace TopModuleCat

open CategoryTheory Limits

variable {k : Type u} [CommRing k] [TopologicalSpace k]

section Coker

variable {M N N' P : TopModuleCat.{v} k}

/-- The universal property of the concrete quotient `TopModuleCat.coker`: a morphism killing
the range descends to the quotient. -/
noncomputable def cokerDesc (φ : M ⟶ N) (ψ : N ⟶ P) (w : φ ≫ ψ = 0) : coker φ ⟶ P :=
  (isColimitCoker φ).desc (CokernelCofork.ofπ ψ w)

@[reassoc (attr := simp)]
lemma cokerπ_cokerDesc (φ : M ⟶ N) (ψ : N ⟶ P) (w : φ ≫ ψ = 0) :
    cokerπ φ ≫ cokerDesc φ ψ w = ψ :=
  (isColimitCoker φ).fac (CokernelCofork.ofπ ψ w) WalkingParallelPair.one

@[simp]
lemma cokerDesc_apply (φ : M ⟶ N) (ψ : N ⟶ P) (w : φ ≫ ψ = 0) (y : ↥N) :
    cokerDesc φ ψ w (cokerπ φ y) = ψ y :=
  congr($(cokerπ_cokerDesc φ ψ w) y)

lemma cokerπ_eq_zero_iff (φ : M ⟶ N) (y : ↥N) :
    cokerπ φ y = 0 ↔ y ∈ φ.hom.range :=
  Submodule.Quotient.mk_eq_zero _

/-- Cokernels of morphisms identified under an isomorphism of the targets are isomorphic. -/
noncomputable def cokerCongr {φ : M ⟶ N} {ψ : M ⟶ N'} (e : N ≅ N') (w : φ ≫ e.hom = ψ) :
    coker φ ≅ coker ψ where
  hom := cokerDesc φ (e.hom ≫ cokerπ ψ) (by rw [← Category.assoc, w, comp_cokerπ])
  inv := cokerDesc ψ (e.inv ≫ cokerπ φ) (by rw [← w]; simp)
  hom_inv_id := by rw [← cancel_epi (cokerπ φ)]; simp
  inv_hom_id := by rw [← cancel_epi (cokerπ ψ)]; simp

@[reassoc (attr := simp)]
lemma cokerπ_cokerCongr_hom {φ : M ⟶ N} {ψ : M ⟶ N'} (e : N ≅ N') (w : φ ≫ e.hom = ψ) :
    cokerπ φ ≫ (cokerCongr e w).hom = e.hom ≫ cokerπ ψ :=
  cokerπ_cokerDesc _ _ _

lemma isOpenQuotientMap_cokerπ (φ : M ⟶ N) : IsOpenQuotientMap ⇑(cokerπ φ).hom :=
  Submodule.isOpenQuotientMap_mkQ _

lemma cokerπ_surjective' (φ : M ⟶ N) (q : ↥(coker φ)) : ∃ y, cokerπ φ y = q :=
  cokerπ_surjective φ q

section DescBilinear

variable {M₂ N₂ M₃ N₃ : TopModuleCat.{v} k}

/-- Descend a continuous linear map along cokernel projections on both sides. -/
noncomputable def cokerDescCLM (φ₂ : M₂ ⟶ N₂) (φ₃ : M₃ ⟶ N₃) (u : ↥N₂ →L[k] ↥N₃)
    (h : ∀ y, cokerπ φ₃ (u (φ₂ y)) = 0) :
    ↥(coker φ₂) →L[k] ↥(coker φ₃) :=
  (cokerDesc φ₂ (ofHom ((cokerπ φ₃).hom ∘L u))
    (ConcreteCategory.hom_ext _ _ fun y ↦ h y)).hom

@[simp]
lemma cokerDescCLM_apply (φ₂ : M₂ ⟶ N₂) (φ₃ : M₃ ⟶ N₃) (u : ↥N₂ →L[k] ↥N₃)
    (h : ∀ y, cokerπ φ₃ (u (φ₂ y)) = 0) (y : ↥N₂) :
    cokerDescCLM φ₂ φ₃ u h (cokerπ φ₂ y) = cokerπ φ₃ (u y) :=
  congr($(cokerπ_cokerDesc φ₂ (ofHom ((cokerπ φ₃).hom ∘L u))
    (ConcreteCategory.hom_ext _ _ fun z ↦ h z)) y)

variable {N₁ : TopModuleCat.{v} k}

/-- The descended family of continuous linear maps has jointly continuous uncurried form. -/
lemma continuous_cokerDescCLM_uncurry (φ₂ : M₂ ⟶ N₂) (φ₃ : M₃ ⟶ N₃)
    (F : ↥N₁ → (↥N₂ →L[k] ↥N₃)) (h : ∀ σ y, cokerπ φ₃ (F σ (φ₂ y)) = 0)
    (hF : Continuous fun p : ↥N₁ × ↥N₂ ↦ F p.1 p.2) :
    Continuous fun p : ↥N₁ × ↥(coker φ₂) ↦ cokerDescCLM φ₂ φ₃ (F p.1) (h p.1) p.2 :=
  ((IsOpenQuotientMap.id.prodMap (isOpenQuotientMap_cokerπ φ₂)).continuous_comp_iff).1
    ((cokerπ φ₃).hom.continuous.comp hF)

/-- Descend a bilinear pairing, bundled as a morphism into the internal hom, along cokernel
projections in all three slots. -/
noncomputable def cokerDescBilinear {M₁ : TopModuleCat.{v} k}
    (φ₁ : M₁ ⟶ N₁) (φ₂ : M₂ ⟶ N₂) (φ₃ : M₃ ⟶ N₃) (F : N₁ ⟶ linHom N₂ N₃)
    (hF : Continuous fun p : ↥N₁ × ↥N₂ ↦ F p.1 p.2)
    (h₁ : ∀ (y : ↥M₁) (τ : ↥N₂), cokerπ φ₃ (F (φ₁ y) τ) = 0)
    (h₂ : ∀ (σ : ↥N₁) (y : ↥M₂), cokerπ φ₃ (F σ (φ₂ y)) = 0) :
    coker φ₁ ⟶ linHom (coker φ₂) (coker φ₃) :=
  cokerDesc φ₁
    (homOfBilinear (fun σ ↦ cokerDescCLM φ₂ φ₃ (F σ) (h₂ σ))
      (fun σ σ' q ↦ by
        obtain ⟨y, rfl⟩ := cokerπ_surjective' φ₂ q
        rw [cokerDescCLM_apply, cokerDescCLM_apply, cokerDescCLM_apply, map_add, add_apply,
          map_add])
      (fun c σ q ↦ by
        obtain ⟨y, rfl⟩ := cokerπ_surjective' φ₂ q
        rw [cokerDescCLM_apply, cokerDescCLM_apply, map_smul, smul_apply, map_smul])
      (continuous_cokerDescCLM_uncurry φ₂ φ₃ F h₂ hF))
    (ConcreteCategory.hom_ext _ _ fun y ↦ ContinuousLinearMap.ext fun q ↦ by
      obtain ⟨τ, rfl⟩ := cokerπ_surjective' φ₂ q
      exact h₁ y τ)

@[simp]
lemma cokerDescBilinear_apply {M₁ : TopModuleCat.{v} k}
    (φ₁ : M₁ ⟶ N₁) (φ₂ : M₂ ⟶ N₂) (φ₃ : M₃ ⟶ N₃) (F : N₁ ⟶ linHom N₂ N₃)
    (hF : Continuous fun p : ↥N₁ × ↥N₂ ↦ F p.1 p.2)
    (h₁ : ∀ (y : ↥M₁) (τ : ↥N₂), cokerπ φ₃ (F (φ₁ y) τ) = 0)
    (h₂ : ∀ (σ : ↥N₁) (y : ↥M₂), cokerπ φ₃ (F σ (φ₂ y)) = 0)
    (σ : ↥N₁) (τ : ↥N₂) :
    cokerDescBilinear φ₁ φ₂ φ₃ F hF h₁ h₂ (cokerπ φ₁ σ) (cokerπ φ₂ τ) =
      cokerπ φ₃ (F σ τ) := rfl

end DescBilinear

end Coker

end TopModuleCat

namespace HomologicalComplex

open CategoryTheory Limits

variable {k : Type u} [CommRing k] [TopologicalSpace k]
variable {ι : Type w} {c : ComplexShape ι} (K : HomologicalComplex (TopModuleCat.{v} k) c)

/-- The cycles of a complex of topological modules, identified with the kernel of the
differential carrying the subspace topology. -/
noncomputable def cyclesIsoKer (i j : ι) (hij : c.next i = j) :
    K.cycles i ≅ TopModuleCat.ker (K.d i j) :=
  KernelFork.mapIsoOfIsLimit (K.cyclesIsKernel i j hij) (TopModuleCat.isLimitKer _) (Iso.refl _)

@[reassoc (attr := simp)]
lemma cyclesIsoKer_hom_kerι (i j : ι) (hij : c.next i = j) :
    (K.cyclesIsoKer i j hij).hom ≫ TopModuleCat.kerι (K.d i j) = K.iCycles i :=
  KernelFork.mapOfIsLimit_ι _ (TopModuleCat.isLimitKer (K.d i j)) (𝟙 _)

@[simp]
lemma cyclesIsoKer_hom_apply_coe (i j : ι) (hij : c.next i = j)
    (z : ↥(K.cycles i)) :
    ((K.cyclesIsoKer i j hij).hom z).1 = K.iCycles i z :=
  congr($(K.cyclesIsoKer_hom_kerι i j hij) z)

/-- The homology of a complex of topological modules, identified with the quotient of the
cycles by the boundaries, carrying the quotient topology. -/
noncomputable def homologyIsoCoker (i j : ι) (hij : c.prev j = i) :
    K.homology j ≅ TopModuleCat.coker (K.toCycles i j) :=
  CokernelCofork.mapIsoOfIsColimit (K.homologyIsCokernel i j hij)
    (TopModuleCat.isColimitCoker _) (Iso.refl _)

end HomologicalComplex
