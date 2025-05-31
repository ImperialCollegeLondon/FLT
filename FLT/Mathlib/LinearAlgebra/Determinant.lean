/-
Copyright (c) 2025 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Yunzhou Xie
-/
import Mathlib
import FLT.Mathlib.Algebra.Algebra.Bilinear

variable (k : Type*) [Field k] {D : Type*} [Ring D] [Algebra k D]
open scoped TensorProduct

lemma mulLeft_conj (K : Type*) [Field K] [Algebra k K] (n : ℕ) (d : D)
    (e : K ⊗[k] D ≃ₐ[K] Matrix (Fin n) (Fin n) K) :
    LinearMap.mulLeft K (e (1 ⊗ₜ d)) = e ∘ₗ LinearMap.mulLeft K ((1 : K) ⊗ₜ[k] d) ∘ₗ e.symm := by
  apply LinearMap.ext
  simp

lemma mulRight_conj (K : Type*) [Field K] [Algebra k K] (n : ℕ) (d : D)
    (e : K ⊗[k] D ≃ₐ[K] Matrix (Fin n) (Fin n) K) :
    LinearMap.mulRight K (e (1 ⊗ₜ d)) = e ∘ₗ LinearMap.mulRight K ((1 : K) ⊗ₜ[k] d) ∘ₗ e.symm := by
  apply LinearMap.ext
  simp

lemma linearMap_eq (K : Type*) [Field K] (n : ℕ) [NeZero n] (N : Matrix (Fin n) (Fin n) K) :
    (((Matrix.ofLinearEquiv K ≪≫ₗ Matrix.transposeLinearEquiv (Fin n) (Fin n) K K).symm.toLinearMap
    ∘ₗ (LinearMap.mulLeft K N) ∘ₗ ((Matrix.ofLinearEquiv K) ≪≫ₗ Matrix.transposeLinearEquiv
    (Fin n) (Fin n) K K).toLinearMap)) = LinearMap.pi fun i ↦ ((fun _ ↦ Matrix.toLin' N) i).comp
    (LinearMap.proj i) := by
  apply LinearMap.ext
  intro M
  ext i j
  simp only [LinearMap.pi_apply, LinearMap.coe_comp, LinearMap.coe_proj, Function.comp_apply,
    Function.eval, Matrix.toLin'_apply]
  rfl

lemma linearMap_eq' (K : Type*) [Field K] (n : ℕ) [NeZero n] (N : Matrix (Fin n) (Fin n) K) :
    ((Matrix.ofLinearEquiv K).symm.toLinearMap ∘ₗ
    LinearMap.mulRight K N ∘ₗ (Matrix.ofLinearEquiv K).toLinearMap :
    (Fin n → Fin n → K) →ₗ[K] (Fin n) → Fin n → K) =
    LinearMap.pi fun i ↦ ((fun _ ↦ Matrix.toLin' N.transpose) i).comp (LinearMap.proj i) := by
  apply LinearMap.ext
  intro M
  ext i j
  simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, mul_comm]

variable [Algebra.IsCentral k D] [IsSimpleRing D] [FiniteDimensional k D]

instance IsSimpleRing.tensor_product (A B : Type*) [Ring A] [Ring B] [Algebra k A] [Algebra k B]
    [Algebra.IsCentral k B] [IsSimpleRing A] [IsSimpleRing B]: IsSimpleRing (A ⊗[k] B) := sorry

lemma IsSimpleRing.mulLeft_det_eq_mulRight_det (d : D) :
    (LinearMap.mulLeft k d).det = (LinearMap.mulRight k d).det := by
  let K' := AlgebraicClosure k
  obtain ⟨n, hn, ⟨e⟩⟩ := IsSimpleRing.exists_algEquiv_matrix_of_isAlgClosed K' (K' ⊗[k] D)
  have h1 := LinearMap.det_baseChange (R := k) (A := K') (LinearMap.mulLeft k d) |>.symm
  have h2 := LinearMap.det_baseChange (R := k) (A := K') (LinearMap.mulRight k d) |>.symm
  have h3 : (LinearMap.mulLeft k d).baseChange K' = LinearMap.mulLeft K' ((1 : K') ⊗ₜ[k] d) := by
    ext; simp
  have h4 : (LinearMap.mulRight k d).baseChange K' = LinearMap.mulRight K' ((1 : K') ⊗ₜ[k] d) := by
    ext; simp
  apply FaithfulSMul.algebraMap_injective k K'
  rw [h1, h2, h3, h4]
  have h5 : LinearMap.det (LinearMap.mulLeft K' ((1 : K') ⊗ₜ[k] d)) =
    LinearMap.det (LinearMap.mulLeft K' (e ((1 : K') ⊗ₜ d))) := by
    rw [← LinearMap.det_conj (LinearMap.mulLeft _ _) e.toLinearEquiv, mulLeft_conj]
    rfl
  rw [h5]
  rw [← LinearMap.det_conj (LinearMap.mulLeft K' (e (1 ⊗ₜ[k] d))) <|
    (((Matrix.ofLinearEquiv K') ≪≫ₗ Matrix.transposeLinearEquiv (Fin n) (Fin n) K' K')).symm,
    LinearEquiv.symm_symm, linearMap_eq]
  rw [LinearMap.det_pi (f := fun _ ↦ Matrix.toLin' (e (1 ⊗ₜ d)))]
  simp only [LinearMap.det_toLin', Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have h6: LinearMap.det (LinearMap.mulRight K' ((1 : K') ⊗ₜ[k] d)) =
    LinearMap.det (LinearMap.mulRight K' (e ((1 : K') ⊗ₜ d))) := by
    rw [← LinearMap.det_conj (LinearMap.mulRight _ _) e.toLinearEquiv, mulRight_conj]
    rfl
  rw [h6, ← LinearMap.det_conj (LinearMap.mulRight K' (e (1 ⊗ₜ[k] d))) <|
    (Matrix.ofLinearEquiv K').symm, LinearEquiv.symm_symm, linearMap_eq']
  rw [LinearMap.det_pi (f := fun _ ↦ Matrix.toLin' (e (1 ⊗ₜ d)).transpose)]
  simp

lemma IsSimpleRing.mulLeft_det_eq_mulRight_det' (d : Dˣ) :
    (LinearEquiv.mulLeft k d).det = (LinearEquiv.mulRight k d).det := by
  ext
  simp [mulLeft_det_eq_mulRight_det]
