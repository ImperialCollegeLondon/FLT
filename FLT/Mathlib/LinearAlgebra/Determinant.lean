/-
Copyright (c) 2025 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Yunzhou Xie
-/
import FLT.Mathlib.Algebra.Algebra.Bilinear
import Mathlib.Algebra.Azumaya.Basic
import Mathlib.Algebra.Central.Defs
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.LinearAlgebra.Charpoly.BaseChange
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.SimpleModule.IsAlgClosed

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

lemma mulLeft_conj_ofLinear (K : Type*) [Field K] (n : ℕ) [NeZero n] (N : Matrix (Fin n) (Fin n) K):
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

lemma mulRight_conj_ofLinear (K : Type*) [Field K] (n : ℕ) [NeZero n]
    (N : Matrix (Fin n) (Fin n) K) :
    ((Matrix.ofLinearEquiv K).symm.toLinearMap ∘ₗ
    LinearMap.mulRight K N ∘ₗ (Matrix.ofLinearEquiv K).toLinearMap :
    (Fin n → Fin n → K) →ₗ[K] (Fin n) → Fin n → K) =
    LinearMap.pi fun i ↦ ((fun _ ↦ Matrix.toLin' N.transpose) i).comp (LinearMap.proj i) := by
  apply LinearMap.ext
  intro M
  ext i j
  simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, mul_comm]

variable [Algebra.IsCentral k D] [IsSimpleRing D] [FiniteDimensional k D]

/-- this is instance is in a repo on brauergroup which will soon be PRed into mathlib. -/
instance (A B : Type*) [Ring A] [Ring B] [Algebra k A] [Algebra k B]
    [Algebra.IsCentral k B] [IsSimpleRing A] [IsSimpleRing B]: IsSimpleRing (A ⊗[k] B) := sorry

lemma IsSimpleRing.mulLeft_det_eq_mulRight_det (d : D) :
    (LinearMap.mulLeft k d).det = (LinearMap.mulRight k d).det := by
  let K' := AlgebraicClosure k
  obtain ⟨n, hn, ⟨e⟩⟩ := IsSimpleRing.exists_algEquiv_matrix_of_isAlgClosed K' (K' ⊗[k] D)
  have h1 : (LinearMap.mulLeft k d).baseChange K' = LinearMap.mulLeft K' ((1 : K') ⊗ₜ[k] d) := by
    ext; simp
  have h2 : (LinearMap.mulRight k d).baseChange K' = LinearMap.mulRight K' ((1 : K') ⊗ₜ[k] d) := by
    ext; simp
  apply FaithfulSMul.algebraMap_injective k K'
  rw [LinearMap.det_baseChange (LinearMap.mulLeft k d) |>.symm, LinearMap.det_baseChange
    (LinearMap.mulRight k d) |>.symm, h1, h2]
  have h5 : LinearMap.det (LinearMap.mulLeft K' ((1 : K') ⊗ₜ[k] d)) =
    LinearMap.det (LinearMap.mulLeft K' (e ((1 : K') ⊗ₜ d))) := by
    rw [← LinearMap.det_conj (LinearMap.mulLeft _ _) e.toLinearEquiv, mulLeft_conj]
    rfl
  have h6: LinearMap.det (LinearMap.mulRight K' ((1 : K') ⊗ₜ[k] d)) =
    LinearMap.det (LinearMap.mulRight K' (e ((1 : K') ⊗ₜ d))) := by
    rw [← LinearMap.det_conj (LinearMap.mulRight _ _) e.toLinearEquiv, mulRight_conj]
    rfl
  rw [h5, h6, ← LinearMap.det_conj (LinearMap.mulRight K' (e (1 ⊗ₜ[k] d))) <|
    (Matrix.ofLinearEquiv K').symm, LinearEquiv.symm_symm, mulRight_conj_ofLinear,
    LinearMap.det_pi, ← LinearMap.det_conj (LinearMap.mulLeft K' (e (1 ⊗ₜ[k] d))) <|
    (((Matrix.ofLinearEquiv K') ≪≫ₗ Matrix.transposeLinearEquiv (Fin n) (Fin n) K' K')).symm,
    LinearEquiv.symm_symm, mulLeft_conj_ofLinear, LinearMap.det_pi]
  simp [LinearMap.det_toLin', Finset.prod_const, Finset.card_univ, Fintype.card_fin]

lemma IsSimpleRing.mulLeft_det_eq_mulRight_det' (d : Dˣ) :
    (LinearEquiv.mulLeft k d).det = (LinearEquiv.mulRight k d).det := by
  ext
  simp [mulLeft_det_eq_mulRight_det]
