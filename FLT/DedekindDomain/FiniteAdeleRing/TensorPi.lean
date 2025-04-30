/-
Copyright (c) 2025 Madison Crim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Madison Crim
-/
import Mathlib.LinearAlgebra.DirectSum.Finsupp
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic

/-!

# Tensor product commutes with direct product when tensoring with a finite free module

If `M` is a finite free module and `Nᵢ` is an indexed collection of modules of a commutative ring
`R` then there is an `R`-module isomorphism between `M ⊗ ∏ᵢ Nᵢ` and `∏ᵢ (M ⊗ Nᵢ)`.

## Main definition

* tensorPi_equiv_piTensor : M ⊗[R] (Π i, N i) ≃ₗ[R] Π i, (M ⊗[R] N i)

## TODO

Prove the same for finitely-presented modules.

-/
open DirectSum

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
