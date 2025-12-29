/-
Copyright (c) 2025 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/
import Mathlib.Algebra.EuclideanDomain.Field
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib

/-

# Lattices (A-modules in K-vector spaces)

A fixed free A-module in a given K-vector space.

-/

section defs

variable (A K : Type*) [CommRing A] [Field K]
    [Algebra A K]

def IntegralLattice (V : Type*) [AddCommGroup V] [Module K V]
    [Module A V] [IsScalarTower A K V] : Type _ :=
  (Submodule.span A (Module.Basis.ofVectorSpaceIndex K V) : Submodule A V)

namespace IntegralLattice

variable (V : Type*) [AddCommGroup V] [Module K V]
    [Module A V] [IsScalarTower A K V]

instance : AddCommGroup (IntegralLattice A K V) :=
  inferInstanceAs (AddCommGroup (Submodule.span _ _))

instance : Module A (IntegralLattice A K V) :=
  inferInstanceAs (Module A (Submodule.span _ _))

def basis_repr_symm :
  ((Module.Basis.ofVectorSpaceIndex K V) →₀ A) →ₗ[A] (IntegralLattice A K V) where
    toFun f := f.sum (fun i a ↦ a • ⟨i.1, Submodule.mem_span_of_mem i.2⟩)
    map_add' f₁ f₂ := by
      rw [Finsupp.sum_add_index' (by simp)]
      intros
      exact add_smul _ _ _
    map_smul' k f := by
      rw [Finsupp.sum_smul_index, Finsupp.smul_sum]
      · simp_rw [mul_smul]
        rfl
      · simp

lemma basis_repr_symm_apply (f : (Module.Basis.ofVectorSpaceIndex K V) →₀ A) :
    ((basis_repr_symm A K V f).1 : V) =
    (Module.Basis.ofVectorSpace K V).repr.symm
      (f.mapRange (algebraMap A K) (map_zero _)) := by
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg =>
    rw [map_add]
    change _ + _ = _
    rw [hf, hg]
    rw [Finsupp.mapRange_add, map_add]
    exact map_add _
  | single a b =>
    simp [basis_repr_symm]
    rfl

lemma basis_repr_symm_surjective : Function.Surjective (basis_repr_symm A K V) := by
  intro ⟨v, hv⟩
  induction hv using Submodule.span_induction with
  | mem x h =>
    use Finsupp.single ⟨x, h⟩ 1
    simp [basis_repr_symm]
  | zero => exact ⟨0, by simp [basis_repr_symm]; rfl⟩
  | add x y hx hy a b =>
    obtain ⟨a, ha⟩ := a
    obtain ⟨b, hb⟩ := b
    use a + b
    simp only [basis_repr_symm, LinearMap.coe_mk, AddHom.coe_mk] at ha hb ⊢
    rw [Finsupp.sum_add_index', ha, hb]
    · rfl
    · simp
    · simp [add_smul]
  | smul a x hx f =>
    obtain ⟨f, hf⟩ := f
    use a • f
    simp [basis_repr_symm] at hf ⊢
    simp [hf]
    rfl

-- for injectivity need A -> K injective

variable [FaithfulSMul A K]

lemma basis_repr_symm_injective :
    Function.Injective (basis_repr_symm A K V) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro f hf
  suffices Finsupp.mapRange (algebraMap A K) (map_zero _) f = 0 by
    apply Finsupp.mapRange_injective (algebraMap A K) (map_zero _)
    · rw [← faithfulSMul_iff_algebraMap_injective]
      infer_instance
    · simp [this]
  have hf' : ((basis_repr_symm A K V) f).1 = 0 := by simp [hf]
  rwa [basis_repr_symm_apply, LinearEquiv.map_eq_zero_iff] at hf'

noncomputable def basis_repr_symm_equiv :
    ((Module.Basis.ofVectorSpaceIndex K V) →₀ A) ≃ₗ[A] (IntegralLattice A K V) :=
  LinearEquiv.ofBijective (basis_repr_symm A K V)
    ⟨basis_repr_symm_injective A K V, basis_repr_symm_surjective A K V⟩

noncomputable def basis : Module.Basis
  (Module.Basis.ofVectorSpaceIndex K V) A (IntegralLattice A K V) where
    repr := (basis_repr_symm_equiv A K V).symm


-- for IsTensorProduct but not sure I'll need it
-- def f₁ : ((IntegralLattice A K V) →ₗ[A] K →ₗ[A] V) where
--   toFun m := .restrictScalars A (.toSpanSingleton K V m.1)
--   map_add' _ _ := by ext; exact smul_add _ _ _
--   map_smul' _ _ := by ext; exact smul_comm _ _ _

-- def f₂ : (K →ₗ[A] (IntegralLattice A K V) →ₗ[A] V) where
--   toFun k := k • (Submodule.subtype _)
--   map_add' k₁ k₂ := by ext; exact add_smul _ _ _
--   map_smul' a k := by ext; exact smul_assoc _ _ _

-- should be elsewhere
open TensorProduct in
noncomputable def _root_.Module.Basis.baseChangeEquiv (ι : Type*) (R S M N : Type*)
    [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module S N]
    [DecidableEq ι]
    (bR : Module.Basis ι R M) (bS : Module.Basis ι S N) :
    S ⊗[R] M ≃ₗ[S] N :=
  (bR.repr.baseChange R S M _) ≪≫ₗ (finsuppScalarRight' R _ ι _) ≪≫ₗ bS.repr.symm

-- should be elsewhere
open TensorProduct in
noncomputable def _root_.Module.Basis.baseChangeEquiv' (ι : Type*) (R S M N : Type*)
    [CommRing R] [CommRing S] [Algebra R S]
    [CommRing M] [Algebra R M] [CommRing N] [Algebra S N]
    [DecidableEq ι]
    (bR : Module.Basis ι R M) (bS : Module.Basis ι S N)
    (P : Type*) [AddCommGroup P] [Module R P] [Module S P] [IsScalarTower R S P] :
    P ⊗[R] M ≃ₗ[S] P ⊗[S] N :=
  AlgebraTensorModule.congr (TensorProduct.rid S P).symm (LinearEquiv.refl R M) ≪≫ₗ
  AlgebraTensorModule.assoc _ _ _ _ _ _ ≪≫ₗ
  AlgebraTensorModule.congr (LinearEquiv.refl S P)
    (Module.Basis.baseChangeEquiv ι R S M N bR bS)

end IntegralLattice

end defs
