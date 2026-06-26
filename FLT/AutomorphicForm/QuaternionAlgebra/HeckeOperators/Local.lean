/-
Copyright (c) 2025 Bryan Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Wang, Andrew Yang
-/
module

public import FLT.QuaternionAlgebra.NumberField -- rigidifications of quat algs
public import FLT.Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import FLT.DedekindDomain.FiniteAdeleRing.LocalUnits
import FLT.DedekindDomain.AdicValuation

/-!
# Local computations for Hecke operators

Local lemmas at a finite place `v` for the Hecke operator `T_v` acting on
quaternionic automorphic forms: explicit double-coset decompositions of
`U₁(v) · diag(πᵥ, 1) · U₁(v)` inside `GL₂(F_v)`.
-/

@[expose] public section

open NumberField IsQuaternionAlgebra.NumberField IsDedekindDomain
open IsDedekindDomain.HeightOneSpectrum
open scoped TensorProduct
open scoped Pointwise

namespace TotallyDefiniteQuaternionAlgebra.WeightTwoAutomorphicForm.HeckeOperator

-- let F be a (totally real) number field
variable {F : Type*} [Field F] [NumberField F]

namespace Local

open scoped FLT

variable {v : HeightOneSpectrum (𝓞 F)}

variable (α : (v.adicCompletion F)ˣ)

open Matrix.GeneralLinearGroup.GL2

/- Some lemmas in this section could be placed somewhere else in greater generality. -/
namespace GL2

/-- The matrix element `diag[α, 1]`. -/
noncomputable def diag : (v.adicCompletion F)ˣ →* GL₂(adicCompletion F v) :=
  Units.map ⟨⟨(Matrix.diagonal ![·, 1]), by simp⟩, fun x y ↦ by simp⟩

-- Show that `unipotent t` is in `U1 v` for `t ∈ O_v`.
lemma unipotent_mem_localTameLevel (t : v.adicCompletion F) (ht : Valued.v t ≤ 1) :
    unipotent t ∈ GL2.localTameLevel v :=
  ⟨GL2.mem_localIwahoriLevel_iff_v.mpr (by simpa), by simp⟩

/-- The matrix element `(unipotent t) * (diag α hα) = !![α, t; 0, 1]`. -/
noncomputable def unipotentMulDiag (t : v.adicCompletion F) :
    GL₂(v.adicCompletion F) := unipotent t * diag α

lemma unipotentMulDiag_injective : Function.Injective (unipotentMulDiag α) := by
  intro a b h
  simpa [unipotentMulDiag, Matrix.mul_apply, unipotent_def, diag] using congr($h 0 1)

/-- `!![α t₁; 0 1]⁻¹ * [α t₂; 0 1] = [1 (t₂ - t₁) / α; 0 1]`. -/
lemma unipotentMulDiag_inv_mul_unipotentMulDiag (t₁ t₂ : v.adicCompletion F) :
    (unipotentMulDiag α t₁)⁻¹ * unipotentMulDiag α t₂ = unipotent (α.1⁻¹ * (t₂ - t₁)) := by
  trans (diag α)⁻¹ * unipotent (t₂ - t₁ : v.adicCompletion F) * diag α
  · simp [unipotentMulDiag, unipotent_inv, sub_eq_add_neg, ← unipotent_mul, mul_assoc]
  · simp only [← map_inv]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [unipotent_def, - map_inv, diag, Matrix.mul_apply]

end GL2

open GL2

/- We could use `TameLevel` instead of `U1` in the naming,
but not sure if we might want to generalise to more general `U_Δ` at some point. -/
namespace GL2.localPTameLevel

lemma conjBy_diag_mem_iff' (p : ℕ) (x) (hx : x ∈ GL2.localPTameLevel v p)
    (α : (v.adicCompletion F)ˣ) :
    (diag α)⁻¹ * x * diag α ∈ GL2.localPTameLevel v p ↔
      Valued.v (x 0 1) ≤ Valued.v α.1 ∧ Valued.v (x 1 0) * Valued.v α.1 < 1 := by
  simp only [mem_localPTameLevel, mem_localIwahoriLevel_iff_v, ne_eq, div_eq_zero_iff,
    not_or] at hx
  trans (Valued.v α.1)⁻¹ * Valued.v (x 0 1) ≤ 1 ∧ Valued.v (x 1 0) * Valued.v α.1 < 1
  · simp [mem_localPTameLevel, mem_localIwahoriLevel_iff_v,
      ← map_inv, Matrix.mul_apply, diag, mul_assoc, mul_left_comm (_⁻¹), hx]
  · simp [inv_mul_le_iff₀, Valuation.pos_iff]

lemma adicCompletionIntegers_dvd_iff
    {a b : v.adicCompletionIntegers F} : a ∣ b ↔ Valued.v b.1 ≤ Valued.v a.1 := by
  constructor
  · rintro ⟨b, rfl⟩; simpa using mul_le_of_le_one_right zero_le b.2
  · intro H
    by_cases ha : a.1 = 0
    · simp_all
    exact ⟨⟨b / a, by simpa [mem_adicCompletionIntegers] using div_le_one_of_le₀ H zero_le⟩,
      by ext; simp [← mul_div_assoc, ha]⟩

lemma conjBy_diag_mem_iff (p : ℕ) (x) (hx : x ∈ GL2.localPTameLevel v p)
    (α : v.adicCompletionIntegers F) (hα : α ≠ 0) :
    (diag (.mk0 α (by simpa)))⁻¹ * x * diag (.mk0 α (by simpa)) ∈ GL2.localPTameLevel v p ↔
      α ∣ ⟨(x 0 1), GL2.v_le_one_of_mem_localFullLevel _
        (GL2.localPTameLevel_le_localIwahoriLevel _ _ hx).1 _ _⟩ := by
  rw [conjBy_diag_mem_iff' (hx := hx)]
  simp only [mem_localPTameLevel, mem_localIwahoriLevel_iff_v, ne_eq, div_eq_zero_iff,
    not_or] at hx
  have : Valued.v (x 1 0) * Valued.v α.1 < 1 := by
    rw [← one_mul (1 : WithZero _)]
    exact mul_lt_mul_of_lt_of_le_of_nonneg_of_pos (by simp [hx]) α.2 zero_le zero_lt_one
  simp [this, adicCompletionIntegers_dvd_iff]

end GL2.localPTameLevel

open GL2.localPTameLevel FLT

section CosetDecomposition

variable (p : ℕ) (α : v.adicCompletionIntegers F) (hα : α ≠ 0)

variable (v) in
/-- For each `t ∈ O_v / αO_v`, the left coset `unipotentMulDiag U1`
for a lift of t to `O_v`. -/
noncomputable def unipotentMulDiagU1 (t : v.adicCompletionIntegers F ⧸ (Ideal.span {α})) :
    GL₂(adicCompletion F v) ⧸ GL2.localPTameLevel v p :=
  t.map (fun x ↦ by exact unipotentMulDiag (Units.mk0 α (by simpa)) x) <| by
    intro a b
    simp only [Submodule.quotientRel_def, QuotientGroup.leftRel_apply,
      unipotentMulDiag_inv_mul_unipotentMulDiag, Units.val_mk0, Ideal.mem_span_singleton]
    rw [dvd_sub_comm]
    rintro ⟨c, hc⟩
    simpa [← AddSubgroupClass.coe_sub, hc, inv_mul_cancel_left₀, hα] using
      GL2.localTameLevel_le_localPTameLevel _ _ (unipotent_mem_localTameLevel _ c.2)

/-- Distinct t give distinct `unipotent_mul_diagU1`, i.e. we have a disjoint union. -/
lemma unipotentMulDiagU1_injective :
    Function.Injective (unipotentMulDiagU1 v p α hα) := by
  rintro ⟨a⟩ ⟨b⟩ H
  refine Ideal.Quotient.eq.mpr ?_
  rw [Ideal.mem_span_singleton, dvd_sub_comm]
  refine ⟨⟨α.1⁻¹ * (b - a), ?_⟩, by ext; simp [hα]⟩
  have := QuotientGroup.eq.mp H
  simpa [unipotentMulDiag_inv_mul_unipotentMulDiag,
    mem_adicCompletionIntegers, unipotent_def] using
    (GL2.mem_localIwahoriLevel_iff_v.mp (localPTameLevel_le_localIwahoriLevel _ _ this)).2.1

/-- Each coset in `U1diagU1` is of the form `unipotent_mul_diagU1` for some `t ∈ O_v`. -/
lemma range_unipotentMulDiagU1 :
    Set.range (unipotentMulDiagU1 v p α hα) =
      QuotientGroup.mk '' (GL2.localPTameLevel v p *
        {diag (Units.mk0 α (by simpa))} : Set GL₂(v.adicCompletion F)) := by
  rw [← Set.image_univ, ← Ideal.Quotient.mk_surjective.range_eq, ← Set.range_comp]
  refine subset_antisymm (Set.range_subset_iff.mpr ?_) (Set.image_subset_iff.mpr ?_)
  · exact fun a ↦ ⟨_, Set.mul_mem_mul (GL2.localTameLevel_le_localPTameLevel _ _
      (unipotent_mem_localTameLevel _ a.2)) rfl, rfl⟩
  · simp only [Set.mul_singleton, Set.image_mul_right, Set.subset_def, Set.mem_preimage]
    intro x hx
    have H : Valued.v (x.1 0 0) = Valued.v α.1 ∧ Valued.v (x.1 0 1) ≤ 1 ∧
      Valued.v (x.1 1 0) < Valued.v α.1 ∧ Valued.v (x.1 1 1) = 1 := by
      simpa [diag, mul_inv_eq_iff_eq_mul₀, hα, mul_inv_lt_iff₀, Valuation.pos_iff] using
        GL2.mem_localIwahoriLevel_iff_v.mp (localPTameLevel_le_localIwahoriLevel _ _ hx)
    refine ⟨⟨x 0 1 / x 1 1, by simp [mem_adicCompletionIntegers, H]⟩, QuotientGroup.eq.mpr ?_⟩
    dsimp [unipotentMulDiag]
    convert (GL2.localPTameLevel.conjBy_diag_mem_iff _ _ (mul_mem (inv_mem
      (GL2.localTameLevel_le_localPTameLevel _ _ <|
      unipotent_mem_localTameLevel (x 0 1 / x 1 1) (by simp [H]))) hx) α hα).mpr ?_ using 1
    · group
    have h' : x 1 1 ≠ 0 := fun h ↦ by simp [h] at H
    simp only [← map_inv]
    simpa [unipotent_inv, Matrix.mul_apply, -map_inv, diag,
      unipotent_def, h', -dvd_zero] using! dvd_zero α

variable (v) in
/-- The double coset space `U1diagU1` is the disjoint union of
`unipotent_mul_diagU1` as t ranges over `O_v / αO_v`. -/
theorem bijOn_unipotentMulDiagU1 :
    Set.BijOn (unipotentMulDiagU1 v p α hα) Set.univ
      (QuotientGroup.mk '' (GL2.localPTameLevel v p * {diag (Units.mk0 α (by simpa))})) := by
  convert (unipotentMulDiagU1_injective p α hα).bijOn_image
  rw [Set.image_univ, range_unipotentMulDiagU1]

end CosetDecomposition

end Local

end TotallyDefiniteQuaternionAlgebra.WeightTwoAutomorphicForm.HeckeOperator
