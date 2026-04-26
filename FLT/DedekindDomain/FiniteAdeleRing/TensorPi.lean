/-
Copyright (c) 2025 Madison Crim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Madison Crim
-/
module

public import Mathlib.LinearAlgebra.DirectSum.Finsupp
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.Algebra.FiveLemma
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.Algebra.Module.PUnit
/-!

# Tensor product commutes with direct product when tensoring with a finite free module

If `M` is a finite free module and `Nᵢ` is an indexed collection of modules of a commutative ring
`R` then there is an `R`-module isomorphism between `M ⊗ ∏ᵢ Nᵢ` and `∏ᵢ (M ⊗ Nᵢ)`.

## Main definition

* `tensorPi_equiv_piTensor` : `M ⊗[R] (Π i, N i) ≃ₗ[R] Π i, (M ⊗[R] N i)` for finite free modules
* `tensorPi_equiv_piTensor'` : the same but for finitely-presented modules.

## TODO

Switch the names around because the primed version is more general hence better.

-/

@[expose] public section
open DirectSum Function

section

theorem Module.FinitePresentation.exists_fin_exact (R : Type*) (M : Type*)
  [Ring R] [AddCommGroup M] [Module R M] [fp : Module.FinitePresentation R M] :
  ∃ (n m : ℕ) (f : (Fin m → R) →ₗ[R] (Fin n → R)) (g : (Fin n → R) →ₗ[R] M),
    Exact f g ∧ Surjective g := by
  obtain ⟨n, K, iso, S, hS⟩ := Module.FinitePresentation.exists_fin R M
  let m := S.card
  let gens : Fin m → (Fin n → R) := Subtype.val ∘ (Finset.equivFin S).symm
  let f : (Fin m → R) →ₗ[R] (Fin n → R) := Fintype.linearCombination R gens
  let g : (Fin n → R) →ₗ[R] M := iso.symm.toLinearMap.comp (Submodule.mkQ K)
  have h₁ : LinearMap.range f = K := by
    simp only [← hS, f, Fintype.range_linearCombination, gens, (Surjective.range_comp
    (Finset.equivFin S).symm.surjective Subtype.val), Subtype.range_val_subtype, Finset.setOf_mem]
  have h₂ : LinearMap.ker g = K := by
    simp only [g, LinearEquiv.ker_comp, Submodule.ker_mkQ]
  have exact_fg : Exact f g := LinearMap.exact_iff.mpr (h₂.trans h₁.symm)
  have : Surjective g := by
    simp only [g, LinearMap.coe_comp, LinearEquiv.coe_coe, EquivLike.comp_surjective,
      Submodule.mkQ_surjective]
  exact ⟨n, m, f, g, exact_fg, this⟩
end


section

variable {ι' : Type*} [Fintype ι'] [DecidableEq ι'] {R ι : Type*} [Semiring R]
  {M N : ι → ι' → Type*} [∀ i i', AddCommMonoid (M i i')] [∀ i i', AddCommMonoid (N i i')]
  [∀ i i', Module R (M i i')] [∀ i i', Module R (N i i')]

/-- `⨁ⱼ(∏ᵢ Nᵢⱼ) ≅ ∏ᵢ(⨁ⱼNᵢⱼ)` if `j` ranges over a finite index set and `i` over an arbitrary
index set. This variant is for `R`-modules and gives an `R`-module isomorphism. -/
def directSumPi_equiv_piSum : (⨁ (i' : ι'), (∀ i, N i i')) ≃ₗ[R] (∀ i, (⨁ i', N i i')) where
  toFun nm i := ∑ i', DirectSum.of (fun i' ↦ N i i') i' (nm i' i)
  map_add' x y := by
    simp only [add_apply, Pi.add_apply, map_add]
    ext i
    simp [Finset.sum_add_distrib]
  map_smul' r nm := by
    ext i
    simp only [RingHom.id_apply, Pi.smul_apply]
    rw [Finset.smul_sum, Finset.sum_congr rfl]
    intro i' _
    rw [← DirectSum.of_smul]
    rfl
  invFun nm :=  ∑ i', DirectSum.of (fun j ↦ ∀ i, N i j) i' (fun i ↦ nm i i')
  left_inv nm := by
    simp only
    convert sum_univ_of (x := nm) with j _ i
    conv_rhs => rw [← DirectSum.sum_univ_of nm]
    simp only [sum_apply, Finset.sum_apply]
    congr with k
    obtain rfl | h := eq_or_ne j k
    · simp
    · simp [of_eq_of_ne _ _ _ h]
  right_inv nm := by
    simp only
    refine funext (fun i ↦ ?_)
    convert sum_univ_of (x := nm i) with j _ i
    conv_rhs => rw [← DirectSum.sum_univ_of (nm i)]
    simp only [sum_apply, Finset.sum_apply]
    congr with k
    obtain rfl | h := eq_or_ne j k
    · simp
    · simp [of_eq_of_ne _ _ _ h]

end

section

variable (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M] [Module.Free R M]
  [Module.Finite R M] {ι : Type*} (N : ι → Type*) [∀ i, AddCommGroup (N i)] [∀ i, Module R (N i)]

open TensorProduct

/-- The isomorphism `M ⊗ ∏ᵢ Nᵢ ≅ (B →₀ R) ⊗ ∏ᵢ Nᵢ`, where `M` is assumed free and
`B` is the basis of `M` given by Lean's global axiom-of-choice operator. This is an
auxiliary definition. -/
noncomputable def freeModule_tensorPiEquiv :
    M ⊗[R] (∀ i, N i) ≃ₗ[R] (Module.Free.ChooseBasisIndex R M →₀ R) ⊗[R] (∀ i, N i) :=
  TensorProduct.congr (Module.Free.chooseBasis R M).repr (LinearEquiv.refl R ((i : ι) → N i))

/-- If `B` is finite then tensoring by the free module with basis `B` commutes with
arbitrary products. -/
noncomputable def finsuppLeft_TensorPi_equiv_piTensor (B : Type*) [Fintype B] [DecidableEq B] :
    (B →₀ R) ⊗[R] (Π i, N i) ≃ₗ[R] Π i, (B →₀ R) ⊗[R] (N i) :=
  -- (B →₀ R) ⊗[R] (Π i, N i) ≃ₗ[R] B →₀ (Π i, N i)
  finsuppScalarLeft R (∀i, N i) B ≪≫ₗ
    -- ≃ₗ[R] ⨁_b (Π i, N i)
    (finsuppLEquivDirectSum R (∀i, N i) B) ≪≫ₗ
    -- ≃ₗ[R] Π i, (⨁_b N i) (this is where we assume B is finite)
    directSumPi_equiv_piSum  ≪≫ₗ
    -- ≃ₗ[R] Π i, (B →₀ N i)
    LinearEquiv.piCongrRight (fun i ↦(finsuppLEquivDirectSum R (N i) B).symm) ≪≫ₗ
    -- ≃ₗ[R] Π i, (B →₀ R) ⊗ N i
    LinearEquiv.piCongrRight (fun i ↦ (finsuppScalarLeft R (N i) B).symm)

/-- The isomorphism `Πᵢ ((B →₀ R) ⊗ Nᵢ) ≅ Πᵢ (M ⊗ Nᵢ)` where `M` is assumed free and
`B` is the basis of `M` given by Lean's global axiom-of-choice operator. This is an
auxiliary definition. -/
noncomputable def tensorPiEquiv_finitefreeModule :
    (Π i, (Module.Free.ChooseBasisIndex R M →₀ R) ⊗[R] N i) ≃ₗ[R] Π i, (M ⊗[R] N i) :=
  LinearEquiv.piCongrRight
    (fun i ↦ (LinearEquiv.rTensor (N i) (Module.Free.chooseBasis R M).repr.symm))

/-- Tensoring with a finite free module commutes with arbitrary products. -/
noncomputable def tensorPi_equiv_piTensor :
    M ⊗[R] (Π i, N i) ≃ₗ[R] Π i, (M ⊗[R] N i) :=
  -- M ⊗ (Π i, N i) ≃ₗ[R] (B →₀ R) ⊗ (Π i, N i)
  (freeModule_tensorPiEquiv R M N) ≪≫ₗ
    -- ≃ₗ[R] Π i, ((B →₀ R) ⊗ N i)
    (finsuppLeft_TensorPi_equiv_piTensor R N _) ≪≫ₗ
    -- ≃ₗ[R] Π i, (M ⊗ N i)
    (tensorPiEquiv_finitefreeModule R M N)

lemma tensorPi_equiv_piTensor_apply (m : M) (n : ∀ i, N i) :
    tensorPi_equiv_piTensor R M N (m ⊗ₜ n) = fun i ↦ (m ⊗ₜ n i) := by
  unfold tensorPi_equiv_piTensor
  simp only [freeModule_tensorPiEquiv, LinearEquiv.trans_apply, congr_tmul,
    LinearEquiv.refl_apply]
  let m' := (Module.Free.chooseBasis R M).repr m
  have hm' : (Module.Free.chooseBasis R M).repr.symm m' = m := by simp [m']
  rw [← hm', LinearEquiv.apply_symm_apply]
  induction m' using Finsupp.induction_linear
  · ext
    simp
  · ext i
    simp_all [add_tmul]
  · rw [← LinearEquiv.eq_symm_apply]
    simp only [tensorPiEquiv_finitefreeModule, LinearEquiv.piCongrRight_symm]
    ext i
    simp only [LinearEquiv.piCongrRight_apply, LinearEquiv.rTensor_symm_tmul, LinearEquiv.symm_symm,
      LinearEquiv.apply_symm_apply, finsuppLeft_TensorPi_equiv_piTensor, LinearEquiv.trans_apply]
    rw [LinearEquiv.symm_apply_eq, finsuppScalarLeft_apply_tmul, Finsupp.sum_single_index (by simp),
      LinearEquiv.symm_apply_eq, finsuppLEquivDirectSum_single, finsuppScalarLeft_apply_tmul,
      Finsupp.sum_single_index (by simp), finsuppLEquivDirectSum_single, directSumPi_equiv_piSum,
      ← LinearEquiv.toFun_eq_coe]
    ext k
    simp only [DirectSum.lof_eq_of R, of_apply, eq_rec_constant, dite_eq_ite, sum_apply,
      Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
    rw [ite_apply, Pi.zero_apply, Pi.smul_apply]

end

section

open TensorProduct

variable (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M]
  [h : Module.FinitePresentation R M] {ι : Type*} (N : ι → Type*) [∀ i, AddCommGroup (N i)]
  [∀ i, Module R (N i)]

/-- Tensoring with a finitely-presented module commutes with arbitrary products.
To prove this, we consider the following commutative diagram. The goal is to show
that `i₃` is an isomorphism, which we do using the five lemma:

```
Rᵐ ⊗[R] (Π i, N i) --f₁--> Rⁿ ⊗[R] (Π i, N i) --f₂--> M ⊗[R] (Π i, N i) --f₃--> 0 --f₄--> 0
        |                         |                         |                   |         |
        i₁                        i₂                        i₃                  i₄        i₅
        |                         |                         |                   |         |
        v                         v                         v                   v         v
Π i, (Rᵐ ⊗[R] N i) --g₁--> Π i, (Rⁿ ⊗[R] N i) --g₂--> Π i, (M ⊗[R] N i) --g₃--> 0 --g₄--> 0
```
-/
noncomputable def tensorPi_equiv_piTensor' [Module.FinitePresentation R M] :
    M ⊗[R] (Π i, N i) ≃ₗ[R] Π i, (M ⊗[R] N i) := IsTensorProduct.equiv
    (f := TensorProduct.piRightHomBil R R M N) <| by
  obtain ⟨n, m, f, g, exact, surj⟩ := Module.FinitePresentation.exists_fin_exact R M
  set i₁ : (Fin m → R) ⊗[R] (Π i, N i) →ₗ[R] Π i, ((Fin m → R) ⊗[R] N i) :=
    (tensorPi_equiv_piTensor R (Fin m → R) N).toLinearMap
  set i₂ : (Fin n → R) ⊗[R] (Π i, N i) →ₗ[R] Π i, ((Fin n → R) ⊗[R] N i) :=
    (tensorPi_equiv_piTensor R (Fin n → R) N).toLinearMap
  set i₃ : M ⊗[R] (Π i, N i) →ₗ[R] Π i, (M ⊗[R] N i) := TensorProduct.piRightHom R R M N
  set i₄ : (PUnit : Type) →ₗ[R] (PUnit : Type) := LinearMap.id   -- map to zero to zero
  set i₅ : (PUnit : Type)  →ₗ[R] (PUnit : Type)  := LinearMap.id  -- map to zero to zero
  set f₁ : (Fin m → R) ⊗[R] (Π i, N i) →ₗ[R] (Fin n → R) ⊗[R] (Π i, N i) := f.rTensor (Π i, N i)
  set f₂ : (Fin n → R) ⊗[R] (Π i, N i) →ₗ[R] M ⊗[R] (Π i, N i) := g.rTensor (Π i, N i)
  set f₃ : M ⊗[R] (Π i, N i) →ₗ[R] (PUnit : Type) := 0
  set f₄ : (PUnit : Type) →ₗ[R] (PUnit : Type) := LinearMap.id -- map to zero to zero
  set g₁ : (Π i, ((Fin m → R) ⊗[R] N i)) →ₗ[R] Π i, ((Fin n → R) ⊗[R] N i) :=
    LinearMap.pi (fun i ↦ (LinearMap.rTensor (N i) f)  ∘ₗ LinearMap.proj i)
  set g₂ : (Π i, ((Fin n → R) ⊗[R] N i)) →ₗ[R] Π i, (M ⊗[R] N i) :=
    LinearMap.pi (fun i ↦ (LinearMap.rTensor (N i) g)  ∘ₗ LinearMap.proj i)
  set g₃ : (Π i, (M ⊗[R] N i)) →ₗ[R] (PUnit : Type) := 0 -- map to zero
  set g₄ : (PUnit : Type) →ₗ[R] (PUnit : Type) := LinearMap.id -- map to zero to zero
  have hc₁ : g₁ ∘ₗ i₁ = i₂ ∘ₗ f₁ := by
    refine ext' fun x y ↦ ?_
    simp only [LinearMap.coe_comp, comp_apply, i₂, i₁, g₁, LinearEquiv.coe_coe]
    rw [LinearMap.rTensor_tmul, tensorPi_equiv_piTensor_apply, tensorPi_equiv_piTensor_apply]
    ext i
    simp only [LinearMap.pi_apply, LinearMap.coe_comp, Function.comp_apply, LinearMap.proj_apply,
      LinearMap.rTensor_tmul]
  have hc₂ : g₂ ∘ₗ i₂ = i₃ ∘ₗ f₂ := by
    refine ext' fun x y ↦ ?_
    simp only [LinearMap.coe_comp, comp_apply, i₂, g₂, i₃]
    rw [LinearMap.rTensor_tmul, piRightHom_tmul]
    ext i
    simp only [LinearMap.pi_apply, LinearMap.coe_comp, Function.comp_apply, LinearMap.proj_apply,
      LinearEquiv.coe_coe]
    rw [tensorPi_equiv_piTensor_apply, LinearMap.rTensor_tmul]
  have hc₃ : g₃ ∘ₗ i₃ = i₄ ∘ₗ f₃ := rfl
  have hc₄ : g₄ ∘ₗ i₄ = i₅ ∘ₗ f₄ := rfl
  have hf₁ : Function.Exact f₁ f₂ := rTensor_exact ((i : ι) → N i) exact surj
  have hf₂ : Function.Exact f₂ f₃ :=
    (LinearMap.exact_zero_iff_surjective _ _).mpr (LinearMap.rTensor_surjective _ surj)
  have hf₃ : Function.Exact f₃ f₄ :=
    (LinearMap.exact_zero_iff_injective _ LinearMap.id).mpr fun ⦃a₁ a₂⦄ ↦ congrFun rfl
  have hg₁ : Function.Exact g₁ g₂ := by
    intro y
    rw [Set.mem_range]
    have (i : ι) : Exact (LinearMap.rTensor (N i) f) (LinearMap.rTensor (N i) g) :=
      rTensor_exact (N i) exact surj
    constructor
    · intro h
      refine ⟨fun i ↦ Classical.choose
        (Set.mem_range.mp (((this i) (y i)).mp (congr_fun h i))), funext (fun i ↦ ?_)⟩
      exact (Classical.choose_spec (Set.mem_range.mp (((this i) (y i)).mp (congr_fun h i))))
    · intro h
      ext i
      obtain ⟨y₁, hy₁⟩ := h
      exact ((this i) (y i)).mpr (LinearMap.mem_range.mpr ⟨y₁ i, congr_fun hy₁ i⟩)
  have hg₂ : Function.Exact g₂ g₃ := by
    apply (LinearMap.exact_zero_iff_surjective _ g₂).mpr
    refine fun y ↦ ⟨fun i ↦
        Classical.choose (LinearMap.rTensor_surjective (N i) surj (y i)), funext fun i ↦ ?_⟩
    exact Classical.choose_spec (LinearMap.rTensor_surjective (N i) surj (y i))
  have hg₃ : Function.Exact g₃ g₄ :=
    (LinearMap.exact_zero_iff_injective _ LinearMap.id).mpr fun ⦃a₁ a₂⦄ ↦ congrFun rfl
  have hi₁ : Function.Surjective i₁ := (tensorPi_equiv_piTensor R (Fin m → R) N).surjective
  have hi₂ : Function.Bijective i₂ := ((tensorPi_equiv_piTensor R (Fin n → R) N)).bijective
  have hi₄ : Function.Bijective i₄ := Function.bijective_id
  have hi₅ : Function.Injective i₅ := Function.injective_id
  have := LinearMap.bijective_of_surjective_of_bijective_of_bijective_of_injective
    f₁ f₂ f₃ f₄ g₁ g₂ g₃ g₄ i₁ i₂ i₃ i₄ i₅
    hc₁ hc₂ hc₃ hc₄ hf₁ hf₂ hf₃ hg₁ hg₂ hg₃ hi₁ hi₂ hi₄ hi₅
  exact this

lemma tensorPi_equiv_piTensor'_apply (m : M) (n : ∀ i, N i) :
    tensorPi_equiv_piTensor' R M N (m ⊗ₜ n) = fun i ↦ (m ⊗ₜ n i) := rfl

end
