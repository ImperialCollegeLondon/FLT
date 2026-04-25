/-
Copyright (c) 2025 Bryan Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Wang
-/
module

public import FLT.QuaternionAlgebra.NumberField -- rigidifications of quat algs
public import Mathlib.Data.Matrix.Reflection
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
public import FLT.Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

@[expose] public section

open NumberField IsQuaternionAlgebra.NumberField IsDedekindDomain
open IsDedekindDomain.HeightOneSpectrum
open scoped TensorProduct
open scoped Pointwise

namespace TotallyDefiniteQuaternionAlgebra.WeightTwoAutomorphicForm.HeckeOperator

-- let F be a (totally real) number field
variable {F : Type*} [Field F] [NumberField F]

namespace Local

variable {v : HeightOneSpectrum (𝓞 F)}

variable (α : v.adicCompletionIntegers F)

variable (hα : α ≠ 0)

variable (v) {α hα} in
/-- The subgroup `U1 v = GL2.localTameLevel v`. -/
noncomputable abbrev U1 : Subgroup (GL (Fin 2) (adicCompletion F v)) := GL2.localTameLevel v

open Matrix.GeneralLinearGroup.GL2

/- Some lemmas in this section could be placed somewhere else in greater generality. -/
namespace GL2

/-- The matrix element `diag[α, 1]`. -/
noncomputable abbrev diag : (GL (Fin 2) (adicCompletion F v)) :=
  Matrix.GeneralLinearGroup.diagonal (![⟨(α : v.adicCompletion F),
    (α : v.adicCompletion F)⁻¹, by
      rw [mul_inv_cancel₀]
      exact_mod_cast hα, by
      rw [inv_mul_cancel₀]
      exact_mod_cast hα⟩, 1])

lemma diag_def :
    (diag α hα : Matrix (Fin 2) (Fin 2) (adicCompletion F v))
    = !![↑α, 0; 0, 1] := by
  rw[diag, Matrix.GeneralLinearGroup.diagonal]
  ext i j; fin_cases i; all_goals fin_cases j
  all_goals simp

lemma conjBy_diag {a b c d : adicCompletion F v} :
    (diag α hα)⁻¹ * !![a, b; c, d] * diag α hα
    = !![a, (α : v.adicCompletion F)⁻¹ * b; c * α, d] := by
  simp only [Matrix.coe_units_inv, diag_def, Matrix.inv_def, Matrix.det_fin_two_of, mul_one,
    mul_zero, sub_zero, Ring.inverse_eq_inv', Matrix.adjugate_fin_two_of, neg_zero, Matrix.smul_of,
    Matrix.smul_cons, smul_eq_mul, Matrix.smul_empty, Matrix.cons_mul, Nat.succ_eq_add_one,
    Nat.reduceAdd, Matrix.vecMul_cons, Matrix.head_cons, Matrix.tail_cons, zero_smul,
    Matrix.empty_vecMul, add_zero, zero_add, Matrix.empty_mul, Equiv.symm_apply_apply,
    Matrix.add_cons, Matrix.empty_add_empty, EmbeddingLike.apply_eq_iff_eq]
  rw[inv_mul_cancel₀ ((Subtype.coe_ne_coe).mpr hα), one_mul, one_mul]
  ring_nf; rw[mul_inv_cancel₀ ((Subtype.coe_ne_coe).mpr hα), one_mul]

-- Show that `unipotent t` is in `U1 v` for `t ∈ O_v`.
lemma unipotent_mem_U1 (t : v.adicCompletionIntegers F) :
    unipotent ↑t ∈ (U1 v) := by
  unfold unipotent
  constructor
  · apply GL2.mem_localFullLevel_iff_v_le_one_and_v_det_eq_one.mpr
    constructor
    · intro i j
      fin_cases i; all_goals fin_cases j
      all_goals simp only [Matrix.unitOfDetInvertible, Fin.mk_one, Fin.isValue, Fin.zero_eta,
        val_unitOfInvertible, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
        Matrix.cons_val_fin_one, Matrix.cons_val_one, map_zero, zero_le', map_one, le_refl]
      apply (mem_adicCompletionIntegers _ _ _).mp
      simp
    simp [Matrix.unitOfDetInvertible]
  simp [Matrix.unitOfDetInvertible]

/-- The matrix element `(unipotent t) * (diag α hα) = !![α, t; 0, 1]`. -/
noncomputable def unipotent_mul_diag (t : v.adicCompletionIntegers F) :
    (GL (Fin 2) (adicCompletion F v)) :=
  (unipotent (t : adicCompletion F v)) * (diag α hα)

/-- `!![α t₁; 0 1]⁻¹ * [α t₂; 0 1] = [1 (t₂ - t₁) / α; 0 1]`. -/
lemma unipotent_mul_diag_inv_mul_unipotent_mul_diag (t₁ t₂ : v.adicCompletionIntegers F) :
    (unipotent_mul_diag α hα t₁)⁻¹ * unipotent_mul_diag α hα t₂
    = unipotent ((α : v.adicCompletion F)⁻¹ * ((t₂ + -t₁) : adicCompletion F v )) := by
  ext i j
  push_cast [unipotent_mul_diag, mul_inv_rev, unipotent_inv]
  rw [← mul_assoc]; nth_rw 2 [mul_assoc]
  rw_mod_cast [unipotent_mul]; push_cast [unipotent_def]
  rw_mod_cast [conjBy_diag]
  simp

end GL2

open GL2

/- We could use `TameLevel` instead of `U1` in the naming,
but not sure if we might want to generalise to more general `U_Δ` at some point. -/
namespace U1

variable {α hα}

variable {x : GL (Fin 2) (adicCompletion F v)}

variable (hx : x ∈ (U1 v))
include hx

lemma apply_mem_integer (i j : Fin 2) :
    (x i j) ∈ (adicCompletionIntegers F v) :=
  GL2.v_le_one_of_mem_localFullLevel _ hx.left _ _

lemma apply_zero_zero_sub_apply_one_one_mem_maximalIdeal :
    (⟨(x 0 0), apply_mem_integer hx _ _⟩ - ⟨(x 1 1), apply_mem_integer hx _ _⟩)
    ∈ IsLocalRing.maximalIdeal (adicCompletionIntegers F v) :=
  (mem_completionIdeal_iff _ v _).mpr hx.right.left

lemma apply_one_zero_mem_maximalIdeal :
    ⟨(x 1 0), apply_mem_integer hx _ _⟩
    ∈ IsLocalRing.maximalIdeal (adicCompletionIntegers F v) :=
  (mem_completionIdeal_iff _ v _).mpr hx.right.right

lemma apply_one_one_notMem_maximalIdeal :
    ⟨(x 1 1), apply_mem_integer hx _ _⟩
    ∉ IsLocalRing.maximalIdeal (adicCompletionIntegers F v) := by
  by_contra mem_maximalIdeal
  have det_mem_maximalIdeal :
      ⟨(x 0 0), apply_mem_integer hx _ _⟩ * ⟨(x 1 1), apply_mem_integer hx _ _⟩
      - ⟨(x 0 1), apply_mem_integer hx _ _⟩ * ⟨(x 1 0), apply_mem_integer hx _ _⟩
      ∈ IsLocalRing.maximalIdeal (adicCompletionIntegers F v) :=
    Ideal.sub_mem _
      (Ideal.mul_mem_left _ _ mem_maximalIdeal)
      (Ideal.mul_mem_left _ _ (apply_one_zero_mem_maximalIdeal hx))
  have v_det_lt_one :=
    ((mem_completionIdeal_iff _ v _).mp det_mem_maximalIdeal)
  push_cast at v_det_lt_one; rw[← Matrix.det_fin_two] at v_det_lt_one
  exact (ne_of_lt v_det_lt_one) (GL2.v_det_val_mem_localFullLevel_eq_one hx.left)

lemma isUnit_apply_one_one :
    IsUnit (⟨(x 1 1), apply_mem_integer hx _ _⟩ : adicCompletionIntegers F v) :=
  (IsLocalRing.notMem_maximalIdeal.mp (apply_one_one_notMem_maximalIdeal hx))

lemma conjBy_diag_mem_U1_iff_apply_zero_one_mem_ideal :
    (diag α hα)⁻¹ * x * diag α hα ∈ U1 v
    ↔ ⟨(x 0 1), apply_mem_integer hx _ _⟩ ∈ (Ideal.span {α}) := by
  let a : (adicCompletionIntegers F v) := ⟨_, apply_mem_integer hx 0 0⟩
  let b : (adicCompletionIntegers F v) := ⟨_, apply_mem_integer hx 0 1⟩
  let c : (adicCompletionIntegers F v) := ⟨_, apply_mem_integer hx 1 0 ⟩
  let d : (adicCompletionIntegers F v) := ⟨_, apply_mem_integer hx 1 1⟩
  have hx₁ : x = !![(a : adicCompletion F v), b; c, d] :=
    (Matrix.etaExpand_eq (x : Matrix (Fin 2) (Fin 2) (adicCompletion F v))).symm
  constructor
  · /- If `(diag α hα)⁻¹ * x * diag α hα ∈ U1 v`,
    then we have `((diag α hα)⁻¹ * x * diag α hα) 0 1 ∈ adicCompletionIntegers F v`,
    which after computing `(diag α hα)⁻¹ * x * diag α hα` gives the desired. -/
    intro h; have h₁ := apply_mem_integer h 0 1
    push_cast [hx₁] at h₁; rw_mod_cast [conjBy_diag] at h₁
    simp only [Fin.isValue, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one,
      Matrix.cons_val_fin_one, Matrix.cons_val_zero] at h₁
    apply Ideal.mem_span_singleton'.mpr
    use ⟨_, h₁⟩
    apply (Subtype.coe_inj).mp; push_cast
    ring_nf; rw[mul_inv_cancel₀ ((Subtype.coe_ne_coe).mpr hα), one_mul]
  /- Conversely, we show that `(diag α hα)⁻¹ * x * diag α hα ∈ U1 v`. -/
  intro h; obtain ⟨q, hq⟩ := Ideal.mem_span_singleton'.mp h
  constructor
  /- We first show that `(diag α hα)⁻¹ * x * diag α hα` is in `GL_2(O_v)`. -/
  · apply GL2.mem_localFullLevel_iff_v_le_one_and_v_det_eq_one.mpr
    push_cast [hx₁]; rw_mod_cast [conjBy_diag]
    constructor
    · intro i j; fin_cases i; all_goals fin_cases j
      all_goals simp only [Fin.zero_eta, Fin.isValue, Matrix.of_apply, Matrix.cons_val',
        Matrix.cons_val_zero, Matrix.cons_val_fin_one,
        Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_fin_one]
      · exact apply_mem_integer hx 0 0
      · unfold b; rw[← hq]; push_cast; ring_nf
        rw[mul_inv_cancel₀ ((Subtype.coe_ne_coe).mpr hα), one_mul]
        apply (mem_adicCompletionIntegers _ _ _).mp
        simp
      · exact_mod_cast le_of_lt
          ((mem_completionIdeal_iff _ v _).mp
          (Ideal.mul_mem_right _ _ (apply_one_zero_mem_maximalIdeal hx)))
      exact apply_mem_integer hx 1 1
    rw[Matrix.det_fin_two_of]; ring_nf
    rw[mul_inv_cancel₀ ((Subtype.coe_ne_coe).mpr hα), one_mul]
    rw[← Matrix.det_fin_two]
    exact GL2.v_det_val_mem_localFullLevel_eq_one hx.left
  /- Finally we show that `(diag α hα)⁻¹ * x * diag α hα`
  is in `GL2.localTameLevel`. -/
  push_cast [hx₁]; rw_mod_cast [conjBy_diag]
  simp only [Fin.isValue, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_fin_one, Matrix.cons_val_one]
  norm_cast
  exact ⟨hx.right.left,
    (mem_completionIdeal_iff _ v _).mp
    (Ideal.mul_mem_right _ _ (apply_one_zero_mem_maximalIdeal hx))⟩

end U1

open U1

section CosetDecomposition

variable (v) in
/-- The double coset space `U1 diag U1` as a set of left cosets. -/
noncomputable def U1diagU1 :
    Set ((GL (Fin 2) (adicCompletion F v)) ⧸ (U1 v)) :=
  (QuotientGroup.mk '' ((U1 v) * {diag α hα}))

variable (v) in
/-- For each `t ∈ O_v / αO_v`, the left coset `unipotent_mul_diag U1`
for a lift of t to `O_v`. -/
noncomputable def unipotent_mul_diagU1
    (t : ↑(adicCompletionIntegers F v) ⧸ (Ideal.span {α})) :
    ((GL (Fin 2) (adicCompletion F v)) ⧸ ↑(U1 v)) :=
  QuotientGroup.mk (unipotent_mul_diag α hα (Quotient.out t : adicCompletionIntegers F v))

/-- `unipotent_mul_diagU1` is contained in `U1diagU1` for all t. -/
lemma mapsTo_unipotent_mul_diagU1_U1diagU1 :
    Set.MapsTo (unipotent_mul_diagU1 v α hα) ⊤ (U1diagU1 v α hα) :=
  (fun t _ => Set.mem_image_of_mem QuotientGroup.mk
    (Set.mul_mem_mul (unipotent_mem_U1 (Quotient.out t)) rfl))

/-- Distinct t give distinct `unipotent_mul_diagU1`, i.e. we have a disjoint union. -/
lemma injOn_unipotent_mul_diagU1 :
    Set.InjOn (unipotent_mul_diagU1 v α hα) ⊤ := by
  intro t₁ h₁ t₂ h₂ h
  /- If `unipotent_mul_diagU1 t₁ = unipotent_mul_diagU1 t₂`,
  then `(unipotent_mul_diag t₁)⁻¹ * (unipotent_mul_diag t₂)` is in `U1 v`.
  Note `unipotent_mul_diag_inv_mul_unipotent_mul_diag` tells us that
  `(unipotent_mul_diag t₁)⁻¹ * (unipotent_mul_diag t₂)` is `unipotent`. -/
  have unipotent_mem_U1 :=
    (unipotent_mul_diag_inv_mul_unipotent_mul_diag α hα (Quotient.out t₁) (Quotient.out t₂)) ▸
      (QuotientGroup.eq.mp h)
  /- Then inspecting the top-right entry of `(unipotent_mul_diag t₁)⁻¹ * (unipotent_mul_diag t₂)`
  gives us `t₁ = t₂`. -/
  have unipotent_apply_zero_one_mem_integer := apply_mem_integer unipotent_mem_U1 0 1
  simp only [unipotent, Matrix.unitOfDetInvertible, Fin.isValue, val_unitOfInvertible,
    Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one, Matrix.cons_val_fin_one,
    Matrix.cons_val_zero] at unipotent_apply_zero_one_mem_integer
  rw [← (Submodule.Quotient.mk_out t₁), ← (Submodule.Quotient.mk_out t₂)]
  apply QuotientAddGroup.eq.mpr; apply Ideal.mem_span_singleton'.mpr
  use ⟨_, unipotent_apply_zero_one_mem_integer⟩
  apply (Subtype.coe_inj).mp; push_cast
  ring_nf; rw[mul_inv_cancel₀ ((Subtype.coe_ne_coe).mpr hα), one_mul, one_mul]

/-- Each coset in `U1diagU1` is of the form `unipotent_mul_diagU1` for some `t ∈ O_v`. -/
lemma surjOn_unipotent_mul_diagU1_U1diagU1 :
    Set.SurjOn (unipotent_mul_diagU1 v α hα) ⊤ (U1diagU1 v α hα) := by
  rintro _ ⟨_, ⟨x, hx, _, rfl, rfl⟩, rfl⟩
  /- Each element of `U1diagU1` can be written as `x * diag`,
  where `x = !![a,b;c,d]` is viewed as a matrix over `O_v`. -/
  let a : (adicCompletionIntegers F v) := ⟨_, apply_mem_integer hx 0 0⟩
  let b : (adicCompletionIntegers F v) := ⟨_, apply_mem_integer hx 0 1⟩
  let c : (adicCompletionIntegers F v) := ⟨_, apply_mem_integer hx 1 0⟩
  let d : (adicCompletionIntegers F v) := ⟨_, apply_mem_integer hx 1 1⟩
  have hx₁ : x = !![(a : adicCompletion F v), b; c, d] :=
    (Matrix.etaExpand_eq (x : Matrix (Fin 2) (Fin 2) (adicCompletion F v))).symm
  -- The desired t is `⅟d * b`.
  letI invertible_d := (isUnit_apply_one_one hx).invertible
  let t : ↥(adicCompletionIntegers F v) ⧸ (Ideal.span {α}) := (⅟d * b)
  use t
  have ht : (b + -Quotient.out t * d) ∈ Ideal.span {α} := by
    apply Ideal.mem_span_singleton'.mpr
    have t_def : (Ideal.Quotient.mk (Ideal.span {α})) (Quotient.out t) = (⅟d * b) := by
      simp only [Ideal.Quotient.mk_out]; rfl
    obtain ⟨q, hq⟩ :=
      Ideal.mem_span_singleton'.mp (Ideal.Quotient.eq.mp t_def)
    use - d * q
    rw[mul_assoc, hq]; ring_nf; simp
  /- The rest of the proof is devoted to showing that this t works.
  This means showing that `unipotent_mul_diag⁻¹ * x * diag` is in U. -/
  simp only [unipotent_mul_diagU1, Set.top_eq_univ, Set.mem_univ, true_and]
  apply QuotientGroup.eq.mpr
  unfold unipotent_mul_diag; rw[mul_inv_rev, ← mul_assoc, mul_assoc _ _ x]
  /- But `unipotent_mul_diag⁻¹ * x * diag = diag⁻¹ * (unipotent⁻¹ * x) * diag`,
  so we can apply `conjBy_diag_mem_U1_iff_apply_zero_one_mem_ideal`,
  and it suffices to show `(unipotent⁻¹ * x) 0 1 ∈ (Ideal.span {α})`.
  The choice of t guarantees this. -/
  apply (conjBy_diag_mem_U1_iff_apply_zero_one_mem_ideal
    (Subgroup.mul_mem _ (Subgroup.inv_mem _ (unipotent_mem_U1 _)) hx)).mpr
  simp only [Fin.isValue, Units.val_mul, Matrix.coe_units_inv, unipotent_def, Matrix.inv_def,
    Matrix.det_fin_two_of, mul_one, mul_zero, sub_zero, Ring.inverse_one,
    Matrix.adjugate_fin_two_of, neg_zero, one_smul, hx₁, Matrix.mul_apply, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_fin_one, Matrix.cons_val_zero, Matrix.cons_val_one,
    Fin.sum_univ_two, one_mul]
  exact_mod_cast ht

variable (v) in
/-- The double coset space `U1diagU1` is the disjoint union of
`unipotent_mul_diagU1` as t ranges over `O_v / αO_v`. -/
theorem bijOn_unipotent_mul_diagU1_U1diagU1 :
    Set.BijOn (unipotent_mul_diagU1 v α hα) ⊤ (U1diagU1 v α hα) :=
  ⟨mapsTo_unipotent_mul_diagU1_U1diagU1 α hα,
    injOn_unipotent_mul_diagU1 α hα,
    surjOn_unipotent_mul_diagU1_U1diagU1 α hα⟩

end CosetDecomposition

end Local

end TotallyDefiniteQuaternionAlgebra.WeightTwoAutomorphicForm.HeckeOperator
