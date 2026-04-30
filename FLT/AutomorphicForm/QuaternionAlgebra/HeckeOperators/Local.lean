/-
Copyright (c) 2025 Bryan Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Wang
-/
module

public import FLT.QuaternionAlgebra.NumberField -- rigidifications of quat algs
public import FLT.DedekindDomain.AdicValuation
public import FLT.DedekindDomain.FiniteAdeleRing.LocalUnits
public import Mathlib.Data.Matrix.Reflection
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.LinearAlgebra.Matrix.Swap
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

noncomputable abbrev uniformizer (v : HeightOneSpectrum (𝓞 F)) : adicCompletion F v :=
  IsDedekindDomain.HeightOneSpectrum.adicCompletionUniformizer (K := F) v

lemma uniformizer_spec :
    Valued.v (uniformizer (F := F) v) = Multiplicative.ofAdd (-1 : ℤ) := by
  simpa [uniformizer] using
    IsDedekindDomain.HeightOneSpectrum.adicCompletionUniformizer_spec (K := F) v

lemma uniformizer_ne_zero : uniformizer (F := F) v ≠ 0 := by
  simpa [uniformizer] using
    IsDedekindDomain.HeightOneSpectrum.adicCompletionUniformizer_ne_zero (K := F) v

lemma swap_mem_localFullLevel :
    Matrix.GeneralLinearGroup.swap (adicCompletion F v) (0 : Fin 2) 1 ∈ GL2.localFullLevel v := by
  rw [GL2.mem_localFullLevel_iff_v_le_one_and_v_det_eq_one]
  constructor
  · intro i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.GeneralLinearGroup.swap, Matrix.swap]
  · simp [Matrix.GeneralLinearGroup.swap, Matrix.swap]

lemma unipotent_mem_localFullLevel (t : v.adicCompletionIntegers F) :
    Matrix.GeneralLinearGroup.GL2.unipotent (t : adicCompletion F v) ∈ GL2.localFullLevel v := by
  rw [GL2.mem_localFullLevel_iff_v_le_one_and_v_det_eq_one]
  constructor
  · intro i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.GeneralLinearGroup.GL2.unipotent_def,
      mem_adicCompletionIntegers]
    exact t.2
  · simp [Matrix.GeneralLinearGroup.GL2.unipotent_def]

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

/-- `!![α s; 0 1] * !![β t; 0 1] = !![αβ, αt+s; 0 1]`. -/
lemma unipotent_mul_diag_mul_unipotent_mul_diag
    {β : v.adicCompletionIntegers F} (hβ : β ≠ 0)
    (s t : v.adicCompletionIntegers F) :
    unipotent_mul_diag α hα s * unipotent_mul_diag β hβ t =
      unipotent_mul_diag (α * β) (mul_ne_zero hα hβ) (α * t + s) := by
  ext i j
  push_cast [unipotent_mul_diag, unipotent_def, diag_def]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

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

section GoodPrimeCosetDecomposition

open scoped algebraMap

variable (v) in
/-- A chosen uniformizer in the integers of the completion `Kᵥ`. -/
noncomputable abbrev uniformizerInt (v : HeightOneSpectrum (𝓞 F)) : v.adicCompletionIntegers F :=
  IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegersUniformizer (K := F) v

lemma uniformizerInt_spec (v : HeightOneSpectrum (𝓞 F)) :
    Valued.v (uniformizerInt (F := F) v).1 = Multiplicative.ofAdd (-1 : ℤ) := by
  simpa [uniformizerInt, IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegersUniformizer,
    IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap] using
      (v.intValuation_exists_uniformizer.choose_spec : v.intValuation
        (v.intValuation_exists_uniformizer.choose) = WithZero.exp (-1 : ℤ))

lemma uniformizerInt_ne_zero (v : HeightOneSpectrum (𝓞 F)) : uniformizerInt (F := F) v ≠ 0 := by
  intro h
  have h' := uniformizerInt_spec (F := F) v
  rw [h] at h'
  simp at h'

variable (v) in
/-- The double coset space `GL₂(𝒪ᵥ) diag(ϖᵥ,1) GL₂(𝒪ᵥ)` as a set of left cosets. -/
noncomputable def localFullLevelDiagLocalFullLevel :
    Set ((GL (Fin 2) (adicCompletion F v)) ⧸ (GL2.localFullLevel v)) :=
  QuotientGroup.mk '' ((GL2.localFullLevel v) * {GL2.diag (uniformizerInt (F := F) v)
    (uniformizerInt_ne_zero (F := F) v)})

variable (v) in
/-- For each `t ∈ 𝒪ᵥ / (ϖᵥ)`, the left coset `unipotent_mul_diag` for a lift of `t`. -/
noncomputable def unipotent_mul_diagLocalFullLevel
    (t : ↑(adicCompletionIntegers F v) ⧸ (Ideal.span {uniformizerInt (F := F) v})) :
    ((GL (Fin 2) (adicCompletion F v)) ⧸ ↑(GL2.localFullLevel v)) :=
  QuotientGroup.mk (unipotent_mul_diag (uniformizerInt (F := F) v)
    (uniformizerInt_ne_zero (F := F) v) (Quotient.out t : adicCompletionIntegers F v))

variable (v) in
/-- The extra coset corresponding to the `swap` representative. -/
noncomputable def swap_mul_diagLocalFullLevel :
    ((GL (Fin 2) (adicCompletion F v)) ⧸ ↑(GL2.localFullLevel v)) :=
  QuotientGroup.mk (Matrix.GeneralLinearGroup.swap (adicCompletion F v) (0 : Fin 2) 1 *
    GL2.diag (uniformizerInt (F := F) v) (uniformizerInt_ne_zero (F := F) v))

/-- A `P¹(k_v)`-indexed family of right-coset representatives for the good-prime double coset. -/
noncomputable def localFullLevelDiagLocalFullLevelRep :
    Option (↑(adicCompletionIntegers F v) ⧸ Ideal.span {uniformizerInt (F := F) v}) →
      ((GL (Fin 2) (adicCompletion F v)) ⧸ ↑(GL2.localFullLevel v))
| none => swap_mul_diagLocalFullLevel (v := v)
| some t => unipotent_mul_diagLocalFullLevel (v := v) t

lemma mapsTo_unipotent_mul_diagLocalFullLevel_localFullLevelDiagLocalFullLevel :
    Set.MapsTo (unipotent_mul_diagLocalFullLevel (v := v)) ⊤
      (localFullLevelDiagLocalFullLevel (v := v)) := by
  intro t ht
  exact Set.mem_image_of_mem QuotientGroup.mk
    (Set.mul_mem_mul (unipotent_mem_localFullLevel (v := v) (Quotient.out t)) rfl)

lemma mapsTo_localFullLevelDiagLocalFullLevelRep_localFullLevelDiagLocalFullLevel :
    Set.MapsTo (localFullLevelDiagLocalFullLevelRep (v := v)) Set.univ
      (localFullLevelDiagLocalFullLevel (v := v)) := by
  intro t ht
  cases t with
  | none =>
      change swap_mul_diagLocalFullLevel (v := v) ∈ localFullLevelDiagLocalFullLevel (v := v)
      exact Set.mem_image_of_mem QuotientGroup.mk
        (Set.mul_mem_mul (swap_mem_localFullLevel (v := v)) rfl)
  | some t =>
      change unipotent_mul_diagLocalFullLevel (v := v) t ∈ localFullLevelDiagLocalFullLevel (v := v)
      exact Set.mem_image_of_mem QuotientGroup.mk
        (Set.mul_mem_mul (unipotent_mem_localFullLevel (v := v) (Quotient.out t)) rfl)

lemma upper_unipotent_mul_matrix {K : Type*} [CommRing K] (a b c d t : K) :
    (!![1, -t; 0, 1] : Matrix (Fin 2) (Fin 2) K) * !![a, b; c, d] =
      !![a - t * c, b - t * d; c, d] := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, mul_comm, mul_left_comm, mul_assoc] <;>
    ring_nf

lemma swap_mul_matrix {K : Type*} [CommRing K] (a b c d : K) :
    (!![(0 : K), 1; 1, 0] : Matrix (Fin 2) (Fin 2) K) * !![a, b; c, d] =
      !![c, d; a, b] := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply]

lemma unipotent_det_eq_one {K : Type*} [CommRing K] (t : K) :
    Matrix.GeneralLinearGroup.det (unipotent t) = 1 := by
  apply Units.ext
  norm_num [unipotent_def, Matrix.det_fin_two]

lemma swap_det_eq_neg_one {K : Type*} [CommRing K] :
    Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.swap K (0 : Fin 2) 1) = -1 := by
  apply Units.ext
  simp [Matrix.GeneralLinearGroup.swap, Matrix.swap]

lemma uniformizerInt_not_isUnit (v : HeightOneSpectrum (𝓞 F)) :
    ¬ IsUnit (uniformizerInt (F := F) v) := by
  intro hunit
  have hval :
      Valued.v (uniformizerInt (F := F) v).1 = 1 :=
    (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one
      (K := F) (v := v)).mp hunit
  have hspec :
      Valued.v (uniformizerInt (F := F) v).1 =
        (↑(Multiplicative.ofAdd (-1 : ℤ)) : WithZero (Multiplicative ℤ)) := by
    simpa using (uniformizerInt_spec (F := F) v)
  have hneq :
      (↑(Multiplicative.ofAdd (-1 : ℤ)) : WithZero (Multiplicative ℤ)) ≠ 1 := by
    exact ne_of_lt <|
      WithZero.coe_lt_coe.mpr (Multiplicative.ofAdd_lt.mpr (by norm_num : (-1 : ℤ) < 0))
  exact hneq (hspec.symm.trans hval)

lemma uniformizerInt_inv_not_mem (v : HeightOneSpectrum (𝓞 F)) :
    (↑(uniformizerInt (F := F) v) : adicCompletion F v)⁻¹ ∉ adicCompletionIntegers F v := by
  intro hmem
  have hunit : IsUnit (uniformizerInt (F := F) v) := by
    refine IsUnit.of_mul_eq_one ⟨(↑(uniformizerInt (F := F) v) : adicCompletion F v)⁻¹, hmem⟩ ?_
    ext
    have hne : (↑(uniformizerInt (F := F) v) : adicCompletion F v) ≠ 0 := by
      simpa using (uniformizerInt_ne_zero (F := F) v)
    simpa [div_eq_mul_inv] using
      (mul_inv_cancel₀ hne :
        (↑(uniformizerInt (F := F) v) : adicCompletion F v) *
          (↑(uniformizerInt (F := F) v) : adicCompletion F v)⁻¹ = 1)
  exact uniformizerInt_not_isUnit (F := F) v hunit

lemma injOn_unipotent_mul_diagLocalFullLevel :
    Set.InjOn (unipotent_mul_diagLocalFullLevel (v := v)) ⊤ := by
  intro t₁ h₁ t₂ h₂ h
  have hmem : (unipotent_mul_diag (uniformizerInt (F := F) v)
      (uniformizerInt_ne_zero (F := F) v) (Quotient.out t₁ : adicCompletionIntegers F v))⁻¹ *
      unipotent_mul_diag (uniformizerInt (F := F) v)
      (uniformizerInt_ne_zero (F := F) v) (Quotient.out t₂ : adicCompletionIntegers F v)
      ∈ GL2.localFullLevel v :=
    QuotientGroup.eq.mp h
  have htop :
      ((uniformizerInt (F := F) v : adicCompletion F v)⁻¹ *
        ((Quotient.out t₂ + -Quotient.out t₁) : adicCompletion F v))
      ∈ adicCompletionIntegers F v := by
    have hmem' := hmem
    rw [unipotent_mul_diag_inv_mul_unipotent_mul_diag
      (α := uniformizerInt (F := F) v) (hα := uniformizerInt_ne_zero (F := F) v)
      (t₁ := Quotient.out t₁) (t₂ := Quotient.out t₂)] at hmem'
    have hval := GL2.v_le_one_of_mem_localFullLevel _ hmem' 0 1
    simp [unipotent_def] at hval
    exact (mem_adicCompletionIntegers _ _ _).2 (by simpa [map_mul] using hval)
  rw [← (Submodule.Quotient.mk_out t₁), ← (Submodule.Quotient.mk_out t₂)]
  apply QuotientAddGroup.eq.mpr
  apply Ideal.mem_span_singleton'.mpr
  use ⟨_, htop⟩
  apply (Subtype.coe_inj).mp
  push_cast
  have hne : (↑(uniformizerInt v) : adicCompletion F v) ≠ 0 := by
    simpa using (uniformizerInt_ne_zero (F := F) v)
  field_simp [hne]
  simp [add_comm]
  exact mul_comm _ _

lemma quotient_diff_mul_mem_span {R : Type*} [CommRing R] {π b d t₀ : R} [Invertible d]
    (hq : t₀ - (⅟d : R) * b ∈ Ideal.span {π}) :
    b + -t₀ * d ∈ Ideal.span {π} := by
  have hq' : (⅟d : R) * b - t₀ ∈ Ideal.span {π} := by
    have hq_neg : -(t₀ - (⅟d : R) * b) ∈ Ideal.span {π} := by
      exact (Ideal.span {π}).neg_mem hq
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hq_neg
  have hqd : (((⅟d : R) * b - t₀) * d) ∈ Ideal.span {π} := by
    exact Ideal.mul_mem_right d (Ideal.span {π}) hq'
  have h_inv : (⅟d : R) * d = 1 := by
    simpa using (inv_mul_cancel₀ (x := d) : (⅟d : R) * d = 1)
  simpa [sub_eq_add_neg, mul_add, add_mul, mul_assoc, mul_comm, mul_left_comm, h_inv] using hqd

set_option maxHeartbeats 5000000 in
-- Temporary placeholder while the good-prime surjectivity proof is reworked.
lemma surjOn_localFullLevelDiagLocalFullLevelRep_localFullLevelDiagLocalFullLevel :
    Set.SurjOn (localFullLevelDiagLocalFullLevelRep (v := v)) Set.univ
      (localFullLevelDiagLocalFullLevel (v := v)) := by
  rintro _ ⟨_, ⟨x, hx, _, rfl, rfl⟩, rfl⟩
  let a : (adicCompletionIntegers F v) := ⟨_, GL2.v_le_one_of_mem_localFullLevel _ hx 0 0⟩
  let b : (adicCompletionIntegers F v) := ⟨_, GL2.v_le_one_of_mem_localFullLevel _ hx 0 1⟩
  let c : (adicCompletionIntegers F v) := ⟨_, GL2.v_le_one_of_mem_localFullLevel _ hx 1 0⟩
  let d : (adicCompletionIntegers F v) := ⟨_, GL2.v_le_one_of_mem_localFullLevel _ hx 1 1⟩
  have hx₁ : x = !![(a : adicCompletion F v), b; c, d] :=
    (Matrix.etaExpand_eq (x : Matrix (Fin 2) (Fin 2) (adicCompletion F v))).symm
  let π : adicCompletionIntegers F v := uniformizerInt (F := F) v
  let hπ : π ≠ 0 := uniformizerInt_ne_zero (F := F) v
  let gπ : GL (Fin 2) (adicCompletion F v) := diag π hπ
  let s : GL (Fin 2) (adicCompletion F v) :=
    Matrix.GeneralLinearGroup.swap (adicCompletion F v) (0 : Fin 2) 1
  by_cases hd : IsUnit d
  · letI invertible_d := hd.invertible
    let t : ↥(adicCompletionIntegers F v) ⧸ (Ideal.span {π}) := (⅟d * b)
    let t₀ : adicCompletionIntegers F v := Quotient.out t
    refine ⟨some t, by simp, ?_⟩
    simp only [localFullLevelDiagLocalFullLevelRep]
    apply QuotientGroup.eq.mpr
    unfold unipotent_mul_diag
    rw [mul_inv_rev, unipotent_inv, ← mul_assoc, mul_assoc _ _ x]
    apply GL2.mem_localFullLevel_iff_v_le_one_and_v_det_eq_one.mpr
    constructor
    · have hy :
        (unipotent (-(t₀ : adicCompletion F v)) * x :
            Matrix (Fin 2) (Fin 2) (adicCompletion F v)) =
          !![((a : adicCompletion F v) - (t₀ : adicCompletion F v) * c),
            (b : adicCompletion F v) - (t₀ : adicCompletion F v) * d; c, d] := by
        simpa [unipotent_def, hx₁] using
          (upper_unipotent_mul_matrix (a := (a : adicCompletion F v))
            (b := (b : adicCompletion F v)) (c := (c : adicCompletion F v))
            (d := (d : adicCompletion F v)) (t := (t₀ : adicCompletion F v)))
      have hconj :
        ((diag (uniformizerInt (F := F) v)
            (uniformizerInt_ne_zero (F := F) v))⁻¹ *
          (unipotent (-(t₀ : adicCompletion F v)) * x) *
          diag (uniformizerInt (F := F) v)
            (uniformizerInt_ne_zero (F := F) v) :
            Matrix (Fin 2) (Fin 2) (adicCompletion F v)) =
          !![((a : adicCompletion F v) - (t₀ : adicCompletion F v) * c),
            (π : adicCompletion F v)⁻¹ *
              ((b : adicCompletion F v) - (t₀ : adicCompletion F v) * d);
            c * (π : adicCompletion F v), d] := by
        rw [hy]
        simpa using
          (GL2.conjBy_diag (α := π) (hα := hπ)
            (a := (a : adicCompletion F v) - (t₀ : adicCompletion F v) * c)
            (b := (b : adicCompletion F v) - (t₀ : adicCompletion F v) * d)
            (c := (c : adicCompletion F v))
            (d := (d : adicCompletion F v)))
      have hconj' :
        ((diag (uniformizerInt (F := F) v)
            (uniformizerInt_ne_zero (F := F) v))⁻¹ *
          (unipotent
            (-(↑(Quotient.out t : adicCompletionIntegers F v) : adicCompletion F v)) * x) *
          diag (uniformizerInt (F := F) v)
            (uniformizerInt_ne_zero (F := F) v) :
            Matrix (Fin 2) (Fin 2) (adicCompletion F v)) =
          !![((a : adicCompletion F v) - (t₀ : adicCompletion F v) * c),
            (π : adicCompletion F v)⁻¹ *
              ((b : adicCompletion F v) - (t₀ : adicCompletion F v) * d);
            c * (π : adicCompletion F v), d] := by
        simpa [t₀] using hconj
      have h00mem :
          ((a : adicCompletion F v) - (t₀ : adicCompletion F v) * c)
            ∈ adicCompletionIntegers F v := by
        exact sub_mem a.2 (mul_mem t₀.2 c.2)
      have ht : (b + -t₀ * d) ∈ Ideal.span {π} := by
        have t_def : (Ideal.Quotient.mk (Ideal.span {π})) t₀ = (⅟d * b) := by
          simpa [t, t₀] using (Ideal.Quotient.mk_out t)
        have hq : t₀ - (⅟d : adicCompletionIntegers F v) * b ∈ Ideal.span {π} := by
          exact Ideal.Quotient.eq.mp t_def
        exact quotient_diff_mul_mem_span (π := π) (b := b) (d := d) (t₀ := t₀) hq
      have h10mem :
          ((c : adicCompletion F v) * (π : adicCompletion F v))
            ∈ adicCompletionIntegers F v := by
        exact mul_mem c.2 π.2
      have h11mem : (d : adicCompletion F v) ∈ adicCompletionIntegers F v := d.2
      let z : Matrix (Fin 2) (Fin 2) (adicCompletion F v) :=
        (diag (uniformizerInt (F := F) v)
            (uniformizerInt_ne_zero (F := F) v))⁻¹ *
          (unipotent (-(↑(Quotient.out t : adicCompletionIntegers F v) : adicCompletion F v)) * x) *
          diag (uniformizerInt (F := F) v)
            (uniformizerInt_ne_zero (F := F) v)
      have hz : z =
          !![((a : adicCompletion F v) - (t₀ : adicCompletion F v) * c),
            (π : adicCompletion F v)⁻¹ *
              ((b : adicCompletion F v) - (t₀ : adicCompletion F v) * d);
            c * (π : adicCompletion F v), d] := by
        simpa [z] using hconj'
      have h00 : z 0 0 =
          ((!![((a : adicCompletion F v) - (t₀ : adicCompletion F v) * c),
            (π : adicCompletion F v)⁻¹ *
              ((b : adicCompletion F v) - (t₀ : adicCompletion F v) * d);
            c * (π : adicCompletion F v), d] :
              Matrix (Fin 2) (Fin 2) (adicCompletion F v)) 0 0) := by
        simpa using congrArg (fun M : Matrix (Fin 2) (Fin 2) (adicCompletion F v) => M 0 0) hz
      have h01 : z 0 1 =
          ((!![((a : adicCompletion F v) - (t₀ : adicCompletion F v) * c),
            (π : adicCompletion F v)⁻¹ *
              ((b : adicCompletion F v) - (t₀ : adicCompletion F v) * d);
            c * (π : adicCompletion F v), d] :
              Matrix (Fin 2) (Fin 2) (adicCompletion F v)) 0 1) := by
        simpa using congrArg (fun M : Matrix (Fin 2) (Fin 2) (adicCompletion F v) => M 0 1) hz
      have h10 : z 1 0 =
          ((!![((a : adicCompletion F v) - (t₀ : adicCompletion F v) * c),
            (π : adicCompletion F v)⁻¹ *
              ((b : adicCompletion F v) - (t₀ : adicCompletion F v) * d);
            c * (π : adicCompletion F v), d] :
              Matrix (Fin 2) (Fin 2) (adicCompletion F v)) 1 0) := by
        simpa using congrArg (fun M : Matrix (Fin 2) (Fin 2) (adicCompletion F v) => M 1 0) hz
      have h11 : z 1 1 =
          ((!![((a : adicCompletion F v) - (t₀ : adicCompletion F v) * c),
            (π : adicCompletion F v)⁻¹ *
              ((b : adicCompletion F v) - (t₀ : adicCompletion F v) * d);
            c * (π : adicCompletion F v), d] :
              Matrix (Fin 2) (Fin 2) (adicCompletion F v)) 1 1) := by
        simpa using congrArg (fun M : Matrix (Fin 2) (Fin 2) (adicCompletion F v) => M 1 1) hz
      intro i j
      fin_cases i <;> fin_cases j
      · change Valued.v (z 0 0) ≤ 1
        have h00simp : z 0 0 = (a : adicCompletion F v) - (t₀ : adicCompletion F v) * c := by
          simpa [z] using congrArg (fun M : Matrix (Fin 2) (Fin 2) (adicCompletion F v) => M 0 0)
            hz
        rw [h00simp]
        exact (mem_adicCompletionIntegers (K := F) (v := v)
          (x := ((a : adicCompletion F v) - (t₀ : adicCompletion F v) * c))).mp h00mem
      · change Valued.v (z 0 1) ≤ 1
        have h01simp : z 0 1 =
            (π : adicCompletion F v)⁻¹ * ((b : adicCompletion F v) - (t₀ : adicCompletion F v) * d) := by
          simpa [z] using congrArg (fun M : Matrix (Fin 2) (Fin 2) (adicCompletion F v) => M 0 1)
            hz
        rw [h01simp]
        have t_def : (Ideal.Quotient.mk (Ideal.span {π})) t₀ = (⅟d * b) := by
          simpa [t, t₀] using (Ideal.Quotient.mk_out t)
        have hq : t₀ - (⅟d : adicCompletionIntegers F v) * b ∈ Ideal.span {π} := by
          exact Ideal.Quotient.eq.mp t_def
        have hbt : (b : adicCompletionIntegers F v) + -((t₀ : adicCompletionIntegers F v) * d) ∈
            Ideal.span {π} := by
          simpa [mul_comm, mul_left_comm, mul_assoc, neg_mul] using
            (quotient_diff_mul_mem_span (π := π) (b := b) (d := d) (t₀ := t₀) hq)
        obtain ⟨q, hqmul⟩ := Ideal.mem_span_singleton'.mp hbt
        have hqcomp : (q : adicCompletion F v) * (π : adicCompletion F v) =
            (b : adicCompletion F v) - (t₀ : adicCompletion F v) * d := by
          simpa [sub_eq_add_neg, mul_comm, mul_left_comm, mul_assoc] using
            (congrArg (fun x : adicCompletionIntegers F v => (x : adicCompletion F v)) hqmul)
        have hπ' : (π : adicCompletion F v) ≠ 0 := by
          exact_mod_cast hπ
        have hcancel : (π : adicCompletion F v)⁻¹ * ((q : adicCompletion F v) * (π : adicCompletion F v)) =
            (q : adicCompletion F v) := by
          calc
            (π : adicCompletion F v)⁻¹ * ((q : adicCompletion F v) * (π : adicCompletion F v))
                = ((π : adicCompletion F v)⁻¹ * (π : adicCompletion F v)) * q := by
                    ac_rfl
            _ = q := by rw [inv_mul_cancel₀ hπ', one_mul]
        rw [← hqcomp, hcancel]
        exact q.2
      · change Valued.v (z 1 0) ≤ 1
        have h10simp : z 1 0 = (c : adicCompletion F v) * (π : adicCompletion F v) := by
          simpa [z] using congrArg (fun M : Matrix (Fin 2) (Fin 2) (adicCompletion F v) => M 1 0)
            hz
        rw [h10simp]
        exact (mem_adicCompletionIntegers (K := F) (v := v)
          (x := ((c : adicCompletion F v) * (π : adicCompletion F v)))).mp h10mem
      · change Valued.v (z 1 1) ≤ 1
        have h11simp : z 1 1 = (d : adicCompletion F v) := by
          simpa [z] using congrArg (fun M : Matrix (Fin 2) (Fin 2) (adicCompletion F v) => M 1 1)
            hz
        rw [h11simp]
        exact (mem_adicCompletionIntegers (K := F) (v := v)
          (x := (d : adicCompletion F v))).mp h11mem
    · have hunip :
        Matrix.GeneralLinearGroup.det
            (Matrix.GeneralLinearGroup.GL2.unipotent (-(t₀ : adicCompletion F v))) = 1 := by
        exact unipotent_det_eq_one (K := adicCompletion F v) (-(t₀ : adicCompletion F v))
      have hdet_units :
          Matrix.GeneralLinearGroup.det
              ((diag (uniformizerInt (F := F) v) (uniformizerInt_ne_zero (F := F) v))⁻¹ *
                (unipotent (-(t₀ : adicCompletion F v)) * x) *
                diag (uniformizerInt (F := F) v) (uniformizerInt_ne_zero (F := F) v)) =
          Matrix.GeneralLinearGroup.det x := by
        have hy' :
            (unipotent (-(t₀ : adicCompletion F v)) * x :
                Matrix (Fin 2) (Fin 2) (adicCompletion F v)) =
              !![((a : adicCompletion F v) - (t₀ : adicCompletion F v) * c),
                (b : adicCompletion F v) - (t₀ : adicCompletion F v) * d; c, d] := by
          simpa [unipotent_def, hx₁] using
            (upper_unipotent_mul_matrix (a := (a : adicCompletion F v))
              (b := (b : adicCompletion F v)) (c := (c : adicCompletion F v))
              (d := (d : adicCompletion F v)) (t := (t₀ : adicCompletion F v)))
        have hconj' :
            ((diag (uniformizerInt (F := F) v)
                (uniformizerInt_ne_zero (F := F) v))⁻¹ *
              (unipotent (-(t₀ : adicCompletion F v)) * x) *
              diag (uniformizerInt (F := F) v)
                (uniformizerInt_ne_zero (F := F) v) :
                Matrix (Fin 2) (Fin 2) (adicCompletion F v)) =
            !![((a : adicCompletion F v) - (t₀ : adicCompletion F v) * c),
              (π : adicCompletion F v)⁻¹ *
                ((b : adicCompletion F v) - (t₀ : adicCompletion F v) * d);
              c * (π : adicCompletion F v), d] := by
          rw [hy']
          simpa using
            (GL2.conjBy_diag (α := π) (hα := hπ)
              (a := (a : adicCompletion F v) - (t₀ : adicCompletion F v) * c)
              (b := (b : adicCompletion F v) - (t₀ : adicCompletion F v) * d)
              (c := (c : adicCompletion F v))
              (d := (d : adicCompletion F v)))
        rw [Matrix.GeneralLinearGroup.det.map_mul, Matrix.GeneralLinearGroup.det.map_mul,
          Matrix.GeneralLinearGroup.det.map_mul]
        rw [hunip]
        simp [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_diagonal,
          Matrix.det_fin_two, hx₁]
      change (Valued.v (R := adicCompletion F v)
          ((Matrix.GeneralLinearGroup.det
            ((diag (uniformizerInt (F := F) v) (uniformizerInt_ne_zero (F := F) v))⁻¹ *
              (unipotent (-(t₀ : adicCompletion F v)) * x) *
              diag (uniformizerInt (F := F) v) (uniformizerInt_ne_zero (F := F) v))) :
            adicCompletion F v)) = 1
      rw [hdet_units]
      exact GL2.v_det_val_mem_localFullLevel_eq_one hx
  · have hdmem : d ∈ IsLocalRing.maximalIdeal (adicCompletionIntegers F v) := by
      exact (IsLocalRing.mem_maximalIdeal _).2 hd
    have hdspan :
        d ∈ Ideal.span {π} := by
      rw [← IsDedekindDomain.HeightOneSpectrum.adicCompletion.maximalIdeal_eq_span_uniformizer
        (K := F) (v := v)
        (π := π) (uniformizerInt_spec (F := F) v)]
      exact hdmem
    obtain ⟨q, hq⟩ := Ideal.mem_span_singleton'.mp hdspan
    refine ⟨none, by simp, ?_⟩
    simp only [localFullLevelDiagLocalFullLevelRep]
    apply QuotientGroup.eq.mpr
    rw [mul_inv_rev, ← mul_assoc, mul_assoc _ _ x]
    apply GL2.mem_localFullLevel_iff_v_le_one_and_v_det_eq_one.mpr
    constructor
    · have hy :
        (s⁻¹ * x : Matrix (Fin 2) (Fin 2) (adicCompletion F v)) =
          !![(c : adicCompletion F v), d; a, b] := by
        have hy1 :
            (s⁻¹ * x : Matrix (Fin 2) (Fin 2) (adicCompletion F v)) =
              ((!![(0 : adicCompletion F v), 1; 1, 0] :
                  Matrix (Fin 2) (Fin 2) (adicCompletion F v)) *
                !![(a : adicCompletion F v), b; c, d]) := by
          rw [hx₁]
          have hs :
              ((s⁻¹ : GL (Fin 2) (adicCompletion F v)) :
                Matrix (Fin 2) (Fin 2) (adicCompletion F v)) =
              Matrix.swap (adicCompletion F v) 0 1 := by
            simp [s, Matrix.GeneralLinearGroup.swap]
          have hswap :
              Matrix.swap (adicCompletion F v) 0 1 =
                !![(0 : adicCompletion F v), 1; 1, 0] := by
            ext i j <;> fin_cases i <;> fin_cases j <;> simp [Matrix.swap]
          rw [hs, hswap]
        calc
          (s⁻¹ * x : Matrix (Fin 2) (Fin 2) (adicCompletion F v)) =
              ((!![(0 : adicCompletion F v), 1; 1, 0] :
                  Matrix (Fin 2) (Fin 2) (adicCompletion F v)) *
                !![(a : adicCompletion F v), b; c, d]) := hy1
          _ = !![(c : adicCompletion F v), d; a, b] := by
            exact swap_mul_matrix (a := (a : adicCompletion F v))
              (b := (b : adicCompletion F v)) (c := (c : adicCompletion F v))
              (d := (d : adicCompletion F v))
      have hconj :
        ((diag (uniformizerInt (F := F) v)
            (uniformizerInt_ne_zero (F := F) v))⁻¹ *
          (s⁻¹ * x) *
          diag (uniformizerInt (F := F) v)
            (uniformizerInt_ne_zero (F := F) v) :
            Matrix (Fin 2) (Fin 2) (adicCompletion F v)) =
          !![(c : adicCompletion F v), (π : adicCompletion F v)⁻¹ * d;
            a * (π : adicCompletion F v), b] := by
        rw [hy]
        simpa using
          (GL2.conjBy_diag (α := π) (hα := hπ)
            (a := (c : adicCompletion F v))
            (b := (d : adicCompletion F v))
            (c := (a : adicCompletion F v))
            (d := (b : adicCompletion F v)))
      intro i j
      fin_cases i <;> fin_cases j
      · have h00 :
          (((diag (uniformizerInt (F := F) v)
              (uniformizerInt_ne_zero (F := F) v))⁻¹ *
            (s⁻¹ * x) *
            diag (uniformizerInt (F := F) v)
              (uniformizerInt_ne_zero (F := F) v) :
            Matrix (Fin 2) (Fin 2) (adicCompletion F v)) 0 0) =
          ((!![(c : adicCompletion F v), (π : adicCompletion F v)⁻¹ * d;
            a * (π : adicCompletion F v), b] :
              Matrix (Fin 2) (Fin 2) (adicCompletion F v)) 0 0) := by
          simpa using
            congrArg (fun M : Matrix (Fin 2) (Fin 2) (adicCompletion F v) => M 0 0) hconj
        change Valued.v
            (((diag (uniformizerInt (F := F) v)
                (uniformizerInt_ne_zero (F := F) v))⁻¹ *
              (s⁻¹ * x) *
              diag (uniformizerInt (F := F) v)
                (uniformizerInt_ne_zero (F := F) v) :
                Matrix (Fin 2) (Fin 2) (adicCompletion F v)) 0 0) ≤ 1
        rw [h00]
        exact c.2
      · have h01 :
          (((diag (uniformizerInt (F := F) v)
              (uniformizerInt_ne_zero (F := F) v))⁻¹ *
            (s⁻¹ * x) *
            diag (uniformizerInt (F := F) v)
              (uniformizerInt_ne_zero (F := F) v) :
            Matrix (Fin 2) (Fin 2) (adicCompletion F v)) 0 1) =
          ((!![(c : adicCompletion F v), (π : adicCompletion F v)⁻¹ * d;
            a * (π : adicCompletion F v), b] :
              Matrix (Fin 2) (Fin 2) (adicCompletion F v)) 0 1) := by
          simpa using
            congrArg (fun M : Matrix (Fin 2) (Fin 2) (adicCompletion F v) => M 0 1) hconj
        change Valued.v
            (((diag (uniformizerInt (F := F) v)
                (uniformizerInt_ne_zero (F := F) v))⁻¹ *
              (s⁻¹ * x) *
              diag (uniformizerInt (F := F) v)
                (uniformizerInt_ne_zero (F := F) v) :
                Matrix (Fin 2) (Fin 2) (adicCompletion F v)) 0 1) ≤ 1
        have hqcomp : (q : adicCompletion F v) * (π : adicCompletion F v) =
            (d : adicCompletion F v) := by
          simpa using
            (congrArg (fun x : adicCompletionIntegers F v => (x : adicCompletion F v)) hq)
        rw [h01, ← hqcomp]
        have hπ' : (π : adicCompletion F v) ≠ 0 := by
          exact_mod_cast hπ
        have hcancel : (π : adicCompletion F v)⁻¹ * ((q : adicCompletion F v) * (π : adicCompletion F v)) =
            (q : adicCompletion F v) := by
          calc
            (π : adicCompletion F v)⁻¹ * ((q : adicCompletion F v) * (π : adicCompletion F v))
                = ((π : adicCompletion F v)⁻¹ * (π : adicCompletion F v)) * q := by
                    ac_rfl
            _ = q := by rw [inv_mul_cancel₀ hπ', one_mul]
        rw [hcancel]
        exact q.2
      · have h10 :
          (((diag (uniformizerInt (F := F) v)
              (uniformizerInt_ne_zero (F := F) v))⁻¹ *
            (s⁻¹ * x) *
            diag (uniformizerInt (F := F) v)
              (uniformizerInt_ne_zero (F := F) v) :
            Matrix (Fin 2) (Fin 2) (adicCompletion F v)) 1 0) =
          ((!![(c : adicCompletion F v), (π : adicCompletion F v)⁻¹ * d;
            a * (π : adicCompletion F v), b] :
              Matrix (Fin 2) (Fin 2) (adicCompletion F v)) 1 0) := by
          simpa using
            congrArg (fun M : Matrix (Fin 2) (Fin 2) (adicCompletion F v) => M 1 0) hconj
        change Valued.v
            (((diag (uniformizerInt (F := F) v)
                (uniformizerInt_ne_zero (F := F) v))⁻¹ *
              (s⁻¹ * x) *
              diag (uniformizerInt (F := F) v)
                (uniformizerInt_ne_zero (F := F) v) :
                Matrix (Fin 2) (Fin 2) (adicCompletion F v)) 1 0) ≤ 1
        rw [h10]
        simpa [mem_adicCompletionIntegers, mul_comm] using
          (mul_mem a.2 π.2)
      · have h11 :
          (((diag (uniformizerInt (F := F) v)
              (uniformizerInt_ne_zero (F := F) v))⁻¹ *
            (s⁻¹ * x) *
            diag (uniformizerInt (F := F) v)
              (uniformizerInt_ne_zero (F := F) v) :
            Matrix (Fin 2) (Fin 2) (adicCompletion F v)) 1 1) =
          ((!![(c : adicCompletion F v), (π : adicCompletion F v)⁻¹ * d;
            a * (π : adicCompletion F v), b] :
              Matrix (Fin 2) (Fin 2) (adicCompletion F v)) 1 1) := by
          simpa using
            congrArg (fun M : Matrix (Fin 2) (Fin 2) (adicCompletion F v) => M 1 1) hconj
        change Valued.v
            (((diag (uniformizerInt (F := F) v)
                (uniformizerInt_ne_zero (F := F) v))⁻¹ *
              (s⁻¹ * x) *
              diag (uniformizerInt (F := F) v)
                (uniformizerInt_ne_zero (F := F) v) :
                Matrix (Fin 2) (Fin 2) (adicCompletion F v)) 1 1) ≤ 1
        rw [h11]
        exact b.2
    · have hswap :
          Matrix.GeneralLinearGroup.det (s⁻¹ : GL (Fin 2) (adicCompletion F v)) = -1 := by
        simpa [s] using
          (swap_det_eq_neg_one (K := adicCompletion F v))
      have hdet_units :
          Matrix.GeneralLinearGroup.det
              ((diag (uniformizerInt (F := F) v) (uniformizerInt_ne_zero (F := F) v))⁻¹ *
                (s⁻¹ * x) *
                diag (uniformizerInt (F := F) v) (uniformizerInt_ne_zero (F := F) v)) =
          - Matrix.GeneralLinearGroup.det x := by
        rw [Matrix.GeneralLinearGroup.det.map_mul, Matrix.GeneralLinearGroup.det.map_mul,
          Matrix.GeneralLinearGroup.det.map_mul]
        rw [hswap]
        simp
      change (Valued.v (R := adicCompletion F v)
          ((Matrix.GeneralLinearGroup.det
            ((diag (uniformizerInt (F := F) v) (uniformizerInt_ne_zero (F := F) v))⁻¹ *
              (s⁻¹ * x) *
              diag (uniformizerInt (F := F) v) (uniformizerInt_ne_zero (F := F) v))) :
            adicCompletion F v)) = 1
      rw [hdet_units]
      simpa using (GL2.v_det_val_mem_localFullLevel_eq_one hx)

end GoodPrimeCosetDecomposition

end Local

end TotallyDefiniteQuaternionAlgebra.WeightTwoAutomorphicForm.HeckeOperator
