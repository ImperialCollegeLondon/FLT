/-
Copyright (c) 2025 Madison Crim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Madison Crim
-/
import Mathlib.LinearAlgebra.DirectSum.Finsupp
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.LinearAlgebra.Quotient.Pi
import Mathlib.Algebra.FiveLemma
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.Algebra.Module.PUnit
/-!

# Tensor product commutes with direct product when tensoring with a finite free module

If `M` is a finite free module and `Nᵢ` is an indexed collection of modules of a commutative ring
`R` then there is an `R`-module isomorphism between `M ⊗ ∏ᵢ Nᵢ` and `∏ᵢ (M ⊗ Nᵢ)`.

## Main definition

* tensorPi_equiv_piTensor : M ⊗[R] (Π i, N i) ≃ₗ[R] Π i, (M ⊗[R] N i)

## TODO

Prove the same for finitely-presented modules.

-/
open DirectSum Function

section test

theorem Module.FinitePresentation.exists_fin_exact (R : Type*) (M : Type*)
  [Ring R] [AddCommGroup M] [Module R M] [fp : Module.FinitePresentation R M] :
  ∃ (n m : ℕ) (f : (Fin m → R) →ₗ[R] (Fin n → R)) (g : (Fin n → R) →ₗ[R] M),
    Exact f g ∧ Surjective g := by

  choose n K iso KFG using Module.FinitePresentation.exists_fin R M

  unfold Submodule.FG at KFG

  choose S hS using KFG

  let m : ℕ := S.card

  let gens : Fin m → (Fin n → R) := Subtype.val ∘ (Finset.equivFin S).symm

  let f : (Fin m → R) →ₗ[R] (Fin n → R) := Fintype.linearCombination R gens

  let g : (Fin n → R) →ₗ[R] M := iso.symm.toLinearMap.comp (Submodule.mkQ K)

  have h₁ : LinearMap.range f = K := by
    rw [← hS]
    simp only [f, Fintype.range_linearCombination, gens]
    congr
    exact (Function.Surjective.range_comp (Finset.equivFin S).symm.surjective Subtype.val).trans
       Subtype.range_val_subtype

  have h₂ : LinearMap.ker g = K := by
    simp only [g, LinearEquiv.ker_comp]
    exact Submodule.ker_mkQ K

  have exact_fg : Exact f g := LinearMap.exact_iff.mpr (h₂.trans h₁.symm)

  have : Surjective g := by
    simp only [g, LinearMap.coe_comp, LinearEquiv.coe_coe, EquivLike.comp_surjective]
    exact Submodule.mkQ_surjective K

  exact ⟨n, m, f, g, exact_fg, this⟩

end test


section

variable {ι' : Type*} [Fintype ι'] [DecidableEq ι'] {R ι : Type*} [Semiring R]
  {M N : ι → ι' → Type*} [∀ i i', AddCommMonoid (M i i')] [∀ i i', AddCommMonoid (N i i')]
  [∀i i', Module R (M i i')] [∀i i', Module R (N i i')]

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
    rw [DFinsupp.finset_sum_apply, DFinsupp.finset_sum_apply, Finset.sum_apply]
    congr with k
    by_cases h : k = j
    · subst h; simp
    · simp [of_eq_of_ne _ _ _ h]
  right_inv nm := by
    simp only
    refine funext (fun i ↦ ?_)
    convert sum_univ_of (x := nm i) with j _ i
    conv_rhs => rw [← DirectSum.sum_univ_of (nm i)]
    rw [DFinsupp.finset_sum_apply, DFinsupp.finset_sum_apply, Finset.sum_apply]
    congr with k
    by_cases h : k = j
    · subst h; simp
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
  TensorProduct.congr (Module.Free.repr R M) (LinearEquiv.refl R ((i : ι) → N i))

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
    (Π i, (Module.Free.ChooseBasisIndex R M →₀ R) ⊗[R] N i) ≃ₗ[R] Π i, (M ⊗[R] N i):=
  LinearEquiv.piCongrRight (fun i ↦ (LinearEquiv.rTensor (N i) (Module.Free.repr R M).symm))

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
  let m' := (Module.Free.repr R M) m
  have hm' : (Module.Free.repr R M).symm m' = m := by simp [m']
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
      LinearEquiv.apply_symm_apply, m']
    rw [finsuppLeft_TensorPi_equiv_piTensor]
    simp only [LinearEquiv.trans_apply, LinearEquiv.piCongrRight_apply]
    rw [LinearEquiv.symm_apply_eq]
    ext k
    rw [finsuppScalarLeft_apply, LinearMap.rTensor_tmul, Finsupp.lapply_apply,
      TensorProduct.lid_tmul, Finsupp.single_apply, ite_smul, zero_smul, ← Finsupp.single_apply]
    congr
    rw [LinearEquiv.symm_apply_eq,finsuppLEquivDirectSum_single,
      finsuppScalarLeft_apply_tmul, Finsupp.sum_single_index (by simp),
      finsuppLEquivDirectSum_single, DirectSum.lof_eq_of, DirectSum.lof_eq_of,
      directSumPi_equiv_piSum]
    simp_rw [← LinearEquiv.toFun_eq_coe]
    conv_lhs =>
      enter [2, x]
      rw [DirectSum.of_apply]
      simp only [Eq.recOn.eq_def, eq_rec_constant, dif_eq_if]
      rw [ite_apply, Pi.zero_apply, Pi.smul_apply, apply_ite (DFunLike.coe _),
        AddMonoidHom.map_zero]
    apply Fintype.sum_dite_eq

end


section
open Finsupp

universe u v

open TensorProduct

variable {R : Type*} (M : Type*) [CommRing R] [AddCommGroup M] [Module R M]
  [h : Module.FinitePresentation R M] {ι : Type*} (N : ι → Type*) [∀ i, AddCommGroup (N i)]
  [∀ i, Module R (N i)] [Small.{v} R]

--Module.FinitePresentation.exists_fin_exact
#check Module R PUnit
open PUnit

#check LinearMap.compLeft
/-- Tensoring with a finitly presented module commutes with arbitrary products. -/
noncomputable def tensorPi_equiv_piTensor' [Module.FinitePresentation R M] :
    M ⊗[R] (Π i, N i) ≃ₗ[R] Π i, (M ⊗[R] N i) := by
  choose n m f g exact surj using Module.FinitePresentation.exists_fin_exact R M

  let M1 := (Fin m → R) ⊗[R] (Π i, N i)
  let M2 := (Fin n → R) ⊗[R] (Π i, N i)
  let M3 := M ⊗[R] (Π i, N i)
  show M3 ≃ₗ[R] _
  let M4 : Type* := PUnit
  let M5 : Type u_5 := PUnit

  let N1 := Π i, ((Fin m → R) ⊗[R] N i)
  let N2 := Π i, ((Fin n → R) ⊗[R] N i)
  let N3 := Π i, (M ⊗[R] N i)

  let N4 : Type u_5 := PUnit
  let N5 : Type u_5 := PUnit

  let equiv1 : (Fin n → R) ⊗[R] (Π i, N i)  ≃ₗ[R] Π i, ((Fin n → R) ⊗[R] N i):=
    tensorPi_equiv_piTensor R (Fin n → R) N
  let equiv2 : (Fin m → R) ⊗[R] (Π i, N i)  ≃ₗ[R] Π i, ((Fin m → R) ⊗[R] N i):=
    tensorPi_equiv_piTensor R (Fin m → R) N

  set i₁ : M1 →ₗ[R] N1 := equiv2.toLinearMap
  set i₂ : M2 →ₗ[R] N2 := equiv1.toLinearMap
  let i₃ : M3 →ₗ[R] N3 := TensorProduct.piRightHom R R M N
  set i₄ : M4 →ₗ[R] N4 := LinearMap.id   -- map to zero to zero
  set i₅ : M5 →ₗ[R] N5 := LinearMap.id  -- map to zero to zero

  let f₁ : M1 →ₗ[R] M2 := f.rTensor (Π i, N i)
  let f₂ : M2 →ₗ[R] M3 := g.rTensor (Π i, N i)
  set f₃ : M3 →ₗ[R] M4 := 0
  set f₄ : M4 →ₗ[R] M5 := LinearMap.id -- map to zero to zero (should I change to zero map?)

  let g₁ : N1 →ₗ[R] N2 :=
    LinearMap.pi (fun i ↦ (LinearMap.rTensor (N i) f)  ∘ₗ LinearMap.proj i)
  let g₂ : N2 →ₗ[R] N3 :=
    LinearMap.pi (fun i ↦ (LinearMap.rTensor (N i) g)  ∘ₗ LinearMap.proj i)
  set g₃ : N3 →ₗ[R] N4 := 0 -- map to zero
  set g₄ : N4 →ₗ[R] N5 := LinearMap.id -- map to zero to zero

  have hc₁ : g₁ ∘ₗ i₁ = i₂ ∘ₗ f₁ := by
    dsimp [g₁, i₁, i₂, f₁, equiv1, equiv2]
    refine ext' ?_
    intro x y
    simp only [LinearMap.coe_comp, comp_apply, IsLinearMap.mk'_apply, i₂, f₁, i₁, g₁, N3, N2, N1,
      equiv2, equiv1]
    rw [LinearMap.rTensor_tmul] --why isn't simp catching this? similarly for other applies
    erw [tensorPi_equiv_piTensor_apply, tensorPi_equiv_piTensor_apply]
    ext i
    simp only [LinearMap.pi_apply, LinearMap.coe_comp, Function.comp_apply, LinearMap.proj_apply,
      LinearMap.rTensor_tmul]
  have hc₂ : g₂ ∘ₗ i₂ = i₃ ∘ₗ f₂ := by
    dsimp [g₂, i₂, i₃, f₂, equiv1]
    refine ext' ?_
    intro x y
    simp only [LinearMap.coe_comp, comp_apply, IsLinearMap.mk'_apply, i₂, g₂, f₁, f₂, M1, i₁, g₁,
      N3, N2, N1, M2, i₃, equiv2, equiv1]
    rw [LinearMap.rTensor_tmul, piRightHom_tmul]
    ext i
    simp only [LinearMap.pi_apply, LinearMap.coe_comp, Function.comp_apply, LinearMap.proj_apply,
      LinearMap.rTensor_tmul]
    erw [tensorPi_equiv_piTensor_apply, LinearMap.rTensor_tmul]
  have hc₃ : g₃ ∘ₗ i₃ = i₄ ∘ₗ f₃ := by
    dsimp [g₃, i₃, i₄, f₃]
  have hc₄ : g₄ ∘ₗ i₄ = i₅ ∘ₗ f₄ := by
    dsimp [g₄, i₄, i₅, f₄]
  have hf₁ : Function.Exact ⇑f₁ ⇑f₂ := by
    dsimp [f₁, f₂]
    exact rTensor_exact ((i : ι) → N i) exact surj
  have hf₂ : Function.Exact ⇑f₂ ⇑f₃ := by
    dsimp [f₂, f₃]
    refine (LinearMap.exact_zero_iff_surjective M4 (LinearMap.rTensor ((i : ι) → N i) g)).mpr ?_
    exact LinearMap.rTensor_surjective _ surj
  have hf₃ : Function.Exact ⇑f₃ ⇑f₄ := by
    dsimp [f₃, f₄]
    exact (LinearMap.exact_zero_iff_injective M3 LinearMap.id).mpr fun ⦃a₁ a₂⦄ ↦ congrFun rfl
  have hg₁ : Function.Exact ⇑g₁ ⇑g₂ := by
    dsimp [g₁, g₂, IsLinearMap.mk']
    unfold Function.Exact N2 N1
    intro y
    have (i : ι) : Exact (LinearMap.rTensor (N i) f) (LinearMap.rTensor (N i) g)  := by
        exact rTensor_exact (N i) exact surj
    constructor
    · intro h
      refine Set.mem_range.mpr ?_
      have h' (i : ι):= congr_fun h i
      have (i: ι) : ∃ x, (LinearMap.rTensor (N i) f) x = y i := by
        refine Set.mem_range.mp ?_
        -- from Exact, get ker = range
        have : LinearMap.ker (LinearMap.rTensor (N i) g) = LinearMap.range (LinearMap.rTensor (N i) f) :=
          LinearMap.exact_iff.mp (this i)
        have hyi_in_ker : y i ∈ LinearMap.ker (LinearMap.rTensor (N i) g) :=
          LinearMap.mem_ker.mpr (h' i)
        rw [this] at hyi_in_ker
        exact hyi_in_ker
      let y₁ := fun i ↦ Classical.choose (this i)
      use y₁
      have hy₁_spec : ∀ i, (LinearMap.rTensor (N i) f) (y₁ i) = y i :=
        fun i ↦ Classical.choose_spec (this i)
      ext i
      exact hy₁_spec i
    · intro h
      have := Set.mem_range.mp h
      obtain ⟨y₁, hy₁⟩ := this
      have h' (i : ι):= congr_fun hy₁ i
      ext i
      simp only [i₂, g₂, f₁, N5, i₅, f₂, M1, g₃, M5, i₁, g₁, N4, N3, M3, f₃, i₄, g₄, N2, f₄, N1, M4,
        M2, i₃, equiv2, equiv1]
      have : LinearMap.ker (LinearMap.rTensor (N i) g) = LinearMap.range (LinearMap.rTensor (N i) f) :=
          LinearMap.exact_iff.mp (this i)
      have hyi_in_range : y i ∈ LinearMap.range (LinearMap.rTensor (N i) f) := by
          refine LinearMap.mem_range.mpr ?_
          use (y₁ i)
          exact h' i
      rw [← this] at hyi_in_range
      exact hyi_in_range
  have hg₂ : Function.Exact ⇑g₂ ⇑g₃ := by
    dsimp [g₂, g₃, IsLinearMap.mk]
    unfold Function.Exact N3 N2 N4
    intro y
    constructor
    · intro h
      refine Set.mem_range.mpr ?_
      have (i: ι) : ∃ x, (LinearMap.rTensor (N i) g) x = y i := by
        refine Set.mem_range.mp ?_
        refine LinearMap.mem_range.mpr ?_
        exact LinearMap.rTensor_surjective (N i) surj (y i)
      let y₁ := fun i ↦ Classical.choose (this i)
      use y₁
      have hy₁_spec : ∀ i, (LinearMap.rTensor (N i) g) (y₁ i) = y i :=
        fun i ↦ Classical.choose_spec (this i)
      ext i
      exact hy₁_spec i
    · intro h
      rfl
  have hg₃ : Function.Exact ⇑g₃ ⇑g₄ := by
    dsimp [g₃, g₄]
    exact (LinearMap.exact_zero_iff_injective N3 LinearMap.id).mpr fun ⦃a₁ a₂⦄ ↦ congrFun rfl
  have hi₁ : Function.Surjective ⇑i₁ := by
    dsimp [i₁, equiv2]
    exact (tensorPi_equiv_piTensor R (Fin m → R) N).surjective
  have hi₂ : Function.Bijective ⇑i₂ := by
    dsimp [i₂, equiv1, M2, N2]
    exact ((tensorPi_equiv_piTensor R (Fin n → R) N)).bijective
  have hi₄ : Function.Bijective ⇑i₄ := by
    dsimp [i₄]
    exact Function.bijective_id
  have hi₅ : Function.Injective ⇑i₅ := by
    dsimp [i₅]
    exact Function.injective_id
  have := LinearMap.bijective_of_surjective_of_bijective_of_bijective_of_injective
    f₁ f₂ f₃ f₄ g₁ g₂ g₃ g₄ i₁ i₂ i₃ i₄ i₅
    hc₁ hc₂ hc₃ hc₄ hf₁ hf₂ hf₃ hg₁ hg₂ hg₃ hi₁ hi₂ hi₄ hi₅

  exact IsTensorProduct.equiv this


#exit
#check List.get_mem
#check List.mem_iff_get
#check List.mem_toFinset
#check LinearMap.lsum
#check Fintype.linearCombination
/-- Tensoring with a finitly presented module commutes with arbitrary products. -/
noncomputable def tensorPi_equiv_piTensor'' [Module.FinitePresentation R M] :
   -- Module.Free R M := by
    M ⊗[R] (Π i, N i) ≃ₗ[R] Π i, (M ⊗[R] N i) := by
  have := Module.FinitePresentation.exists_fin R M
  choose n K iso fg using this -- why doesn't obtain work?
  have equiv: (Fin n → R) ⊗[R] (Π i, N i)  ≃ₗ[R] Π i, ((Fin n → R) ⊗[R] N i):= by
    exact tensorPi_equiv_piTensor R (Fin n → R) N

  --constructing the exact sequence K → R^n → M
  let f : K →ₗ[R] (Fin n → R) := K.subtype
  let π : (Fin n → R) →ₗ[R] (Fin n → R) ⧸ K := Submodule.mkQ K
  let g' := iso.symm.toLinearMap
  let g : (Fin n → R) →ₗ[R] M := g'.comp π
  have inj_f : Function.Injective f := Submodule.injective_subtype K
  have surj_g : Function.Surjective g := by
    unfold g g'
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, EquivLike.comp_surjective]
    exact Submodule.mkQ_surjective K
  have exact : Function.Exact f g := by
    refine (Function.Injective.comp_exact_iff_exact ?_).mpr ?_
    · exact LinearEquiv.injective iso.symm
    · exact LinearMap.exact_subtype_mkQ K
  have := rTensor.equiv (Π i, N i) exact surj_g


  let surj' : (Π i, ((Fin n → R) ⊗[R] (N i))) →ₗ[R] Π i, M ⊗[R] N i :=
    IsLinearMap.mk' (fun a i ↦ (LinearMap.rTensor (N i) g) (a i)) ({
      map_add x y := by
        simp only [Pi.add_apply, map_add]
        rfl,
      map_smul r x := by
        simp only [Pi.smul_apply, map_smul]
        rfl})
  have surj_surj' : Function.Surjective surj' :=
    Function.Surjective.piMap (fun i ↦ LinearMap.rTensor_surjective (N i) surj_g)
  have iso' := LinearMap.quotKerEquivOfSurjective surj' surj_surj'

  --constructing a map from R^m → R^n
  choose fin s using fg
  let m := fin.card
  let gens' : Fin m → (Fin n → R) := Subtype.val ∘ (Finset.equivFin fin).symm
  let rel_map : (Fin m → R) →ₗ[R] (Fin n → R) := Fintype.linearCombination R gens'

  have : LinearMap.range rel_map = K := by
    rw [← s]
    simp only [rel_map, Fintype.range_linearCombination, gens']
    congr
    exact (Function.Surjective.range_comp (Finset.equivFin fin).symm.surjective Subtype.val).trans
       Subtype.range_val_subtype

  have : LinearMap.ker g = K := by
    simp only [g, g', LinearEquiv.ker_comp]
    exact Submodule.ker_mkQ K

  sorry















  #exit


  --let x := Finset.toList fin
  --let a (i : Fin m) := fin i
  let gens : Fin m → (Fin n → R) := fun i ↦ ((Finset.equivFin fin).symm i).1

    apply le_antisymm
    · rintro g ⟨f, rfl⟩
      dsimp [rel_map]
      rw [Fintype.linearCombination_apply]
      apply Submodule.sum_smul_mem
      intro i _
      simp only [gens]
      rw [← s]
      have := Submodule.subset_span (Finset.coe_mem (fin.equivFin.symm i)) (R:=R) (s:= fin.toSet)
      exact Submodule.mem_span.mpr fun p a ↦ a (Finset.coe_mem (fin.equivFin.symm i))
    · rintro g hg
      rw [← s] at hg
      dsimp [rel_map]
      simp only [Fintype.range_linearCombination, gens]
      have : Set.range gens = fin := by
        dsimp [gens]
        refine Eq.symm (Set.Subset.antisymm ?_ ?_)
        · intro x hx
          use (Finset.equivFin fin) ⟨x, hx⟩
          simp only [Equiv.symm_apply_apply]
        · rintro x hx
          obtain ⟨i, hi⟩ := hx
          rw [← hi]
          exact Subtype.coe_prop (fin.equivFin.symm i)


      sorry



    sorry
  have : LinearMap.ker g = K := by
    unfold g g'
    simp only [LinearEquiv.ker_comp]
    exact Submodule.ker_mkQ K



  let map' : fin → fin :=  fun a ↦ a
  let map'' := ∑ x ∈ fin, map' x

  sorry
  #exit



  let K' : Submodule R ((Fin n → R) ⊗[R] (Π i, N i)) :=
    LinearMap.range (LinearMap.rTensor ((i : ι) → N i) f)
  let K'' : Submodule R (Π i, ((Fin n → R) ⊗[R] (N i))) :=
    Submodule.pi Set.univ (fun i ↦ LinearMap.range (LinearMap.rTensor (N i) f))
  --this I plan to delete later it's just to keep tracking easier for me
  have r : K' = LinearMap.range (LinearMap.rTensor ((i : ι) → N i) f)  := rfl
  rw [r.symm] at this

  -- this next have isn't quite what I want, need to rework it
  --have := LinearEquiv.piCongrRight (fun i ↦ rTensor.equiv (N i) exact surj_g)

  -- iso' reworks my isomorphism so the product behaves with the quotient
  -- how I want but seems like more code than what should be necessary
  let surj' : (Π i, ((Fin n → R) ⊗[R] (N i))) →ₗ[R] Π i, M ⊗[R] N i :=
    IsLinearMap.mk' (fun a i ↦ (LinearMap.rTensor (N i) g) (a i)) ({
      map_add x y := by
        simp only [Pi.add_apply, map_add]
        rfl,
      map_smul r x := by
        simp only [Pi.smul_apply, map_smul]
        rfl})
  have surj_surj' : Function.Surjective surj' :=
    Function.Surjective.piMap (fun i ↦ LinearMap.rTensor_surjective (N i) surj_g)
  have iso' := LinearMap.quotKerEquivOfSurjective surj' surj_surj'

  have equiv' := Submodule.Quotient.equiv K' (Submodule.map equiv K') equiv rfl
  let map : (Π i, (K ⊗[R] (N i))) →ₗ[R] Π i, (Fin n → R) ⊗[R] N i :=
    IsLinearMap.mk' (fun a i ↦ (LinearMap.rTensor (N i) f) (a i)) ({
      map_add x y := by
        simp only [Pi.add_apply, map_add]
        rfl,
      map_smul r x := by
        simp only [Pi.smul_apply, map_smul]
        rfl})
  -- let map' : (Π i, (K ⊗[R] (N i))) →ₗ[R] Π i, (Fin n → R) ⊗[R] N i  := by
  --   have (i: ι) := LinearMap.proj i (R:=R) (φ := (K ⊗[R] (N i)))
  --   have (i : ι):= LinearMap.comp (LinearMap.rTensor (N i) f) this
  have : LinearMap.ker surj' = ⨅(i : ι), LinearMap.ker (LinearMap.rTensor (N i) g) := by
    unfold surj'
    have :  (LinearMap.ker surj' = Πi,LinearMap.ker (LinearMap.rTensor (N i) g)) ↔
      (x ∈ LinearMap.ker surj' ↔ x ∈  Πi, LinearMap.ker (LinearMap.rTensor (N i) g)) := sorry
    simp only [LinearMap.mem_ker, IsLinearMap.mk'_apply]
    have : (Πi,LinearMap.ker (LinearMap.rTensor (N i) g)) =
      Πi, { x // ((LinearMap.rTensor (N i) g) (x)) = 0 } := rfl
    rw [this]

    sorry



  have exact' : Function.Exact map surj' := by
    refine LinearMap.exact_iff.mpr ?_
    refine Submodule.ext_iff.mpr ?_
    intro x
    constructor
    · intro h
      have :  ∀i, x i ∈ LinearMap.ker (LinearMap.rTensor (N i) g) := by
        intro i
        apply?


  -- have sub : introSubmodule.map equiv K' = LinearMap.ker surj' := by
  --   apply?

  -- ∏ (R^n ⊗ Ni)/ ∏ ranges this is what I want
  --let ψ := Πi, LinearMap.rTensor (N i) f

  -- let f' : (K ⊗[R] (Π i, N i)) →ₗ[R] ((Fin n → R) ⊗[R] (Π i, N i)) := by
  --   exact (TensorProduct.map f LinearMap.id)
  -- -- think I'll need this later to get my chain of isomorphisms


  have : LinearMap.range rel_map = K := by
    rw [← s]

    have (f : Fin m → R) : ∑ i, f i • gens i ∈ (Submodule.span R ↑fin) := by

      refine Submodule.mem_span_set'.mpr ?_
      refine ⟨m, f, ?_⟩
      simp only [gens]
      rw [List.mem_toFinset]





    --Π i, LinearMap.range (LinearMap.rTensor (N i) f)
  --have : (Π i, (Fin n → R) ⊗[R] N i) ⧸ K' ≃ₗ[R] (Π i, M ⊗[R] N i) := sorry
  -- have h₁ : K' = LinearMap.range (LinearMap.rTensor ((i : ι) → N i) f) := sorry
  -- --have h₂

  -- let a := (Πi,  ((Fin n → R)⊗[R] (N i))) ⧸K''
  -- let b :=
  --   Π i, ((Fin n → R) ⊗[R] (N i) ⧸ LinearMap.range (LinearMap.rTensor (N i) f))
  -- have : a ≃ₗ[R] b := by
  --   unfold a b K''
  --   apply?

  sorry
  -- have this (Fin n → R) ⊗[R] ((i : ι) → N i) ⧸ K') ≅ M ⊗ Π N i
  -- want this Πi, (R^n ⊗ N i) / (Submodule.map equiv K) ≅ ∏ M ⊗ Ni
  -- R^n ⊗ Ni / LinearMap.range (LinearMap.rTensor (N i) f) ≅ M ⊗ Ni
  -- have this Π [(R^n ⊗ N i) / range] ≅ Π M ⊗ N i

  --have : M ⊗[R] (Π i, N i) ≃ₗ[R] ((Fin n → R) ⊗[R] (Π i, N i) ⧸ (K ⊗[R] (Π i, N i))) := sorry


  --obtain ⟨s, hs, hs'⟩ := h
