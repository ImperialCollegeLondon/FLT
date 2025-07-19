/-
Copyright (c) 2025 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Bryan Wang
-/
import FLT.AutomorphicForm.QuaternionAlgebra.HeckeOperators.Abstract -- abstract Hecke ops
import FLT.AutomorphicForm.QuaternionAlgebra.Defs -- definitions of automorphic forms
import FLT.QuaternionAlgebra.NumberField -- rigidifications of quat algs
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
import Mathlib.Data.Matrix.Reflection
import FLT.DedekindDomain.FiniteAdeleRing.LocalUnits -- for (π 0; 0 1)
import FLT.Mathlib.Topology.Algebra.RestrictedProduct

open NumberField IsQuaternionAlgebra.NumberField IsDedekindDomain
open TotallyDefiniteQuaternionAlgebra
open IsDedekindDomain.HeightOneSpectrum
open scoped TensorProduct
open scoped Pointwise

namespace TotallyDefiniteQuaternionAlgebra.WeightTwoAutomorphicForm.HeckeOperator

-- let F be a totally real number field
variable (F : Type*) [Field F] [NumberField F]

-- Let D/F be a quaternion algebra
variable (D : Type*) [Ring D] [Algebra F D] [IsQuaternionAlgebra F D]

-- Let r be a rigidification of D, which is a collection of isomorphisms D ⊗ Fᵥ = M₂(Fᵥ)
-- for all finite places v of F, compatible with the adelic structure (i.e. inducing
-- an isomorphism D ⊗_F 𝔸_F^f = M₂(𝔸_F^f))
variable (r : Rigidification F D)

-- Let S be a finite set of finite places of F (the level)
variable (S : Finset (HeightOneSpectrum (𝓞 F)))

-- let P be a good prime
variable {P : HeightOneSpectrum (𝓞 F)} (hP : P ∉ S)

variable (R : Type*) [CommRing R]

namespace Local

variable (v : HeightOneSpectrum (𝓞 F))

variable (α : v.adicCompletionIntegers F)

variable (hα : α ≠ 0)

-- Not sure if this could be somewhere else.
variable {F α hα} in
lemma valuation_lt_one_iff_mem_maximalIdeal {t : adicCompletionIntegers F v} :
    Valued.v (t : adicCompletion F v) < 1
    ↔ t ∈ IsLocalRing.maximalIdeal (adicCompletionIntegers F v) :=
  Iff.trans
  (Valuation.isEquiv_iff_val_lt_one.mp
    (Valuation.isEquiv_valuation_valuationSubring Valued.v))
  (ValuationSubring.valuation_lt_one_iff (adicCompletionIntegers F v) _).symm

variable {F α hα} in
/-- The subgroup `U1 v = GL2.localTameLevel v`. -/
noncomputable abbrev U1 : Subgroup (GL (Fin 2) (adicCompletion F v)) := (GL2.localTameLevel v)

/- Some lemmas in this section could be placed somewhere else in greater generality. -/
namespace GL2

variable {F v} in
/-- The matrix element `diag[α, 1]`. -/
noncomputable abbrev diag : (GL (Fin 2) (adicCompletion F v)) :=
  Matrix.GeneralLinearGroup.diagonal (![⟨(α : v.adicCompletion F),
    (α : v.adicCompletion F)⁻¹, by
      rw [mul_inv_cancel₀]
      exact_mod_cast hα, by
      rw [inv_mul_cancel₀]
      exact_mod_cast hα⟩, 1])

variable {F v} in
lemma diag_def :
    (diag α hα : Matrix (Fin 2) (Fin 2) (adicCompletion F v))
    = !![↑α, 0; 0, 1] := by
  rw[diag, Matrix.GeneralLinearGroup.diagonal]
  ext i j; fin_cases i; all_goals fin_cases j
  all_goals simp

variable {F v} in
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

variable {F v} in
/-- The unipotent matrix element `!![1, t; 0, 1]`. -/
noncomputable def unipotent (t : v.adicCompletion F) : (GL (Fin 2) (adicCompletion F v)) :=
  letI detInv : Invertible !![1, t; 0, 1].det :=
  { invOf := 1,
    invOf_mul_self :=
      by simp only [Matrix.det_fin_two_of, mul_one, mul_zero, sub_zero],
    mul_invOf_self :=
      by simp only [Matrix.det_fin_two_of, mul_one, mul_zero, sub_zero] }
  Matrix.unitOfDetInvertible !![1, t; 0, 1]

variable {F v} in
lemma unipotent_def (t : v.adicCompletion F) :
    (unipotent t : Matrix (Fin 2) (Fin 2) (adicCompletion F v))
    = !![1, t; 0, 1] := by
  rw[unipotent]; rfl

variable {F v} in
lemma unipotent_inv (t : v.adicCompletion F) :
    (unipotent t)⁻¹ = unipotent (-t) := by
  ext; simp [unipotent_def, Matrix.inv_def]

variable {F v} in
lemma unipotent_mul (t₁ t₂ : v.adicCompletion F) :
    (unipotent t₂) * (unipotent t₁) = unipotent (t₁ + t₂) := by
  ext i j; fin_cases i; all_goals fin_cases j
  all_goals simp [unipotent_def]

-- Show that `unipotent t` is in `U1 v` for `t ∈ O_v`.
variable {F v} in
lemma unipotent_mem_U1 (t : v.adicCompletionIntegers F) :
    unipotent ↑t ∈ (U1 v) := by
  unfold unipotent
  constructor
  · let unipotentInt : ((Matrix (Fin 2) (Fin 2) ↥(adicCompletionIntegers F v))ˣ) :=
      letI detInv : Invertible !![1, t; 0, 1].det :=
      { invOf := 1,
        invOf_mul_self :=
        by simp only [Matrix.det_fin_two_of, mul_one, mul_zero, sub_zero],
        mul_invOf_self :=
        by simp only [Matrix.det_fin_two_of, mul_one, mul_zero, sub_zero] }
      Matrix.unitOfDetInvertible !![1, t; 0, 1]
    use unipotentInt; apply Units.eq_iff.mp
    simp only [unipotentInt, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe,
      RingHom.mapMatrix_apply, ValuationSubring.coe_subtype]
    ext i j
    fin_cases i; all_goals fin_cases j
    all_goals simp; rfl
  simp [Matrix.unitOfDetInvertible]

variable {F v} in
/-- The matrix element `(unipotent t) * (diag α hα) = !![α, t; 0, 1]`. -/
noncomputable def unipotent_mul_diag (t : v.adicCompletionIntegers F) :
    (GL (Fin 2) (adicCompletion F v)) :=
  (unipotent (t : adicCompletion F v)) * (diag α hα)

variable {F v} in
lemma unipotent_mul_diag_inv_mul_unipotent_mul_diag (t₁ t₂ : v.adicCompletionIntegers F) :
    (unipotent_mul_diag α hα t₁)⁻¹ * unipotent_mul_diag α hα t₂
    = unipotent ((α : v.adicCompletion F)⁻¹ * ((t₂ + -t₁) : adicCompletion F v )) := by
  ext i j
  push_cast [unipotent_mul_diag, mul_inv_rev, unipotent_inv]
  rw [← mul_assoc]; nth_rw 2 [mul_assoc]
  rw_mod_cast [unipotent_mul]; push_cast [unipotent_def]
  rw_mod_cast [conjBy_diag]
  fin_cases i; all_goals fin_cases j
  all_goals simp

end GL2

open GL2

namespace U1

variable (x : GL (Fin 2) (adicCompletion F v))

variable (hx : x ∈ (U1 v))
include hx

variable {F α hα} in
lemma apply_mem_integer (i j : Fin 2) :
    (x i j) ∈ (adicCompletionIntegers F v) := by
  have h : x i j = hx.left.choose i j := by
    conv_lhs => rw[← (Exists.choose_spec hx.left)]
    simp
  rw[h]; simp

variable {F α hα} in
lemma det_mem_integer :
    x.val.det ∈ (adicCompletionIntegers F v) := by
  rw[Matrix.det_fin_two]
  apply Subring.sub_mem
  all_goals apply Subring.mul_mem
  all_goals apply apply_mem_integer v x hx

variable {F α hα} in
lemma isUnit_det_integer :
    IsUnit (⟨x.val.det, det_mem_integer v x hx⟩ : adicCompletionIntegers F v) :=
  have h : ⟨x.val.det, det_mem_integer v x hx⟩ = hx.left.choose.val.det := by
    ext; push_cast
    conv_lhs => rw[← (Exists.choose_spec hx.left)]
    simp only [RingHom.toMonoidHom_eq_coe, Units.coe_map, MonoidHom.coe_coe,
      RingHom.mapMatrix_apply, ValuationSubring.coe_subtype]; rfl
  h ▸ (Matrix.isUnits_det_units hx.left.choose)

variable {F α hα} in
lemma det_integer_fin_two :
    (⟨x.val.det, det_mem_integer v x hx⟩ : adicCompletionIntegers F v)
    = ⟨(x 0 0), apply_mem_integer v x hx 0 0⟩ * ⟨(x 1 1), apply_mem_integer v x hx 1 1⟩
    - ⟨(x 0 1), apply_mem_integer v x hx 0 1⟩ * ⟨(x 1 0), apply_mem_integer v x hx 1 0⟩ := by
  ext; push_cast; rw[Matrix.det_fin_two]

variable {F α hα} in
lemma apply_zero_zero_sub_apply_one_one_mem_maximalIdeal :
    (⟨(x 0 0), apply_mem_integer v x hx 0 0⟩ - ⟨(x 1 1), apply_mem_integer v x hx 1 1⟩) ∈
    IsLocalRing.maximalIdeal (adicCompletionIntegers F v) :=
  (valuation_lt_one_iff_mem_maximalIdeal v).mp hx.right.left

variable {F α hα} in
lemma apply_one_zero_mem_maximalIdeal :
    ⟨(x 1 0), apply_mem_integer v x hx 1 0⟩ ∈
    IsLocalRing.maximalIdeal (adicCompletionIntegers F v) :=
  (valuation_lt_one_iff_mem_maximalIdeal v).mp hx.right.right

variable {F α hα} in
lemma apply_one_one_notMem_maximalIdeal :
    ⟨(x 1 1), apply_mem_integer v x hx 1 1⟩ ∉
    IsLocalRing.maximalIdeal (adicCompletionIntegers F v) := by
  by_contra mem_maximalIdeal
  have det_mem_maximalIdeal :
      ⟨x.val.det, det_mem_integer v x hx⟩ ∈
      IsLocalRing.maximalIdeal (adicCompletionIntegers F v) := by
    rw[det_integer_fin_two v x hx]
    exact Ideal.sub_mem _
      (Ideal.mul_mem_left _ _ mem_maximalIdeal)
      (Ideal.mul_mem_left _ _ (apply_one_zero_mem_maximalIdeal v x hx))
  exact (IsLocalRing.notMem_maximalIdeal.mpr (isUnit_det_integer v x hx)) det_mem_maximalIdeal

variable {F α hα} in
lemma isUnit_apply_one_one :
    IsUnit (⟨(x 1 1), apply_mem_integer v x hx 1 1⟩ : adicCompletionIntegers F v) :=
  (IsLocalRing.notMem_maximalIdeal.mp (apply_one_one_notMem_maximalIdeal v x hx))

variable {F v} in
lemma conjBy_diag_mem_U1_iff_apply_zero_one_mem_ideal :
    (diag α hα)⁻¹ * x * diag α hα ∈ U1 v
    ↔ ⟨(x 0 1), apply_mem_integer v x hx 0 1⟩ ∈ (Ideal.span {α}) := by
  let a : (adicCompletionIntegers F v) := ⟨ _ , apply_mem_integer v x hx 0 0 ⟩
  let b : (adicCompletionIntegers F v) := ⟨ _ , apply_mem_integer v x hx 0 1 ⟩
  let c : (adicCompletionIntegers F v) := ⟨ _ , apply_mem_integer v x hx 1 0 ⟩
  let d : (adicCompletionIntegers F v) := ⟨ _ , apply_mem_integer v x hx 1 1 ⟩
  have hx₁ : x = !![(a : adicCompletion F v), b; c, d] :=
    (Matrix.etaExpand_eq (x : Matrix (Fin 2) (Fin 2) (adicCompletion F v))).symm

  constructor
  · /- If `(diag α hα)⁻¹ * x * diag α hα ∈ U1 v`,
    then we have `((diag α hα)⁻¹ * x * diag α hα) 0 1 ∈ adicCompletionIntegers F v`,
    which after computing `(diag α hα)⁻¹ * x * diag α hα` gives the desired. -/
    intro h; have h₁ := apply_mem_integer _ _ h 0 1
    push_cast [hx₁] at h₁; rw_mod_cast [conjBy_diag] at h₁
    simp only [Fin.isValue, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one,
      Matrix.cons_val_fin_one, Matrix.cons_val_zero] at h₁
    apply Ideal.mem_span_singleton'.mpr
    use ⟨ _ , h₁ ⟩
    apply (Subtype.coe_inj).mp; push_cast
    ring_nf; rw[mul_inv_cancel₀ ((Subtype.coe_ne_coe).mpr hα), one_mul]

  /- Conversely, we show that `(diag α hα)⁻¹ * x * diag α hα ∈ U1 v`.
  We compute the product explicitly and denote the result by `conjBy_diag_explicit`. -/
  intro h; obtain ⟨ q, hq ⟩ := Ideal.mem_span_singleton'.mp h
  let conjBy_diag_explicit : Matrix (Fin 2) (Fin 2) (adicCompletionIntegers F v) :=
    !![a, q; c * α, d]
  /- We first need to show that `conjBy_diag_explicit` is in `GL_2(O_v)`.
  Note this is not a priori obvious, as even `diag` itself need not be
  in `GL_2(O_v)` (`α` need not be a unit). -/
  have det_eq :
      conjBy_diag_explicit.det = ⟨x.val.det, det_mem_integer v x hx⟩ := by
    unfold conjBy_diag_explicit
    rw[Matrix.det_fin_two_of, mul_comm _ α, ← mul_assoc, hq]
    exact (det_integer_fin_two v x hx).symm
  have isUnit_conjBy_diag_explicit :=
    ((Matrix.isUnit_iff_isUnit_det _).mpr (det_eq ▸ isUnit_det_integer v x hx))
  /- Now we show that `(diag α hα)⁻¹ * x * diag α hα = conjBy_diag_explicit`,
  hence `(diag α hα)⁻¹ * x * diag α hα` is in `GL_2(O_v)`. -/
  constructor
  · use isUnit_conjBy_diag_explicit.unit
    ext i j
    push_cast [hx₁]; rw_mod_cast [conjBy_diag]
    fin_cases i; all_goals fin_cases j
    all_goals simp only [RingHom.toMonoidHom_eq_coe, Fin.mk_one, Fin.isValue, Fin.zero_eta,
      Units.coe_map, IsUnit.unit_spec, MonoidHom.coe_coe, RingHom.mapMatrix_apply,
      ValuationSubring.coe_subtype, Matrix.map_apply, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_fin_one, Matrix.cons_val_one, MulMemClass.coe_mul,
      conjBy_diag_explicit]
    unfold b; rw[← hq]; push_cast; ring_nf
    rw[mul_inv_cancel₀ ((Subtype.coe_ne_coe).mpr hα), one_mul]
  /- Finally we show that `(diag α hα)⁻¹ * x * diag α hα`
  is in `GL2.localTameLevel`. -/
  push_cast [hx₁]; rw_mod_cast [conjBy_diag]
  simp only [Fin.isValue, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_fin_one, Matrix.cons_val_one]
  norm_cast
  exact ⟨ hx.right.left ,
    (valuation_lt_one_iff_mem_maximalIdeal v).mpr
    (Ideal.mul_mem_right _ _ (apply_one_zero_mem_maximalIdeal v x hx)) ⟩

end U1

open U1

section CosetDecomposition

variable {F v} in
/-- The double coset space `U1 diag U1` as a set of left cosets. -/
noncomputable def U1diagU1 :
    Set ((GL (Fin 2) (adicCompletion F v)) ⧸ (U1 v)) :=
  (QuotientGroup.mk '' ((U1 v) * {diag α hα}))

variable {F v} in
/-- For each `t ∈ O_v / αO_v`, the left coset `unipotent_mul_diag U1`
for a lift of t to `O_v`. -/
noncomputable def unipotent_mul_diagU1
    (t : ↑(adicCompletionIntegers F v) ⧸ (Ideal.span {α})) :
    ((GL (Fin 2) (adicCompletion F v)) ⧸ ↑(U1 v)) :=
  QuotientGroup.mk (unipotent_mul_diag α hα (Quotient.out t : adicCompletionIntegers F v))

variable {F v} in
/-- `unipotent_mul_diagU1` is contained in `U1diagU1` for all t. -/
lemma mapsTo_unipotent_mul_diagU1_U1diagU1 :
    Set.MapsTo (unipotent_mul_diagU1 α hα) ⊤ (U1diagU1 α hα) :=
  (fun t _ => Set.mem_image_of_mem QuotientGroup.mk
    (Set.mul_mem_mul (unipotent_mem_U1 (Quotient.out t)) rfl))

variable {F v} in
/-- Distinct t give distinct `unipotent_mul_diagU1`, i.e. we have a disjoint union. -/
lemma injOn_unipotent_mul_diagU1 :
    Set.InjOn (unipotent_mul_diagU1 α hα) ⊤ := by
  intro t₁ h₁ t₂ h₂ h
  -- If `unipotent_mul_diagU1 t₁ = unipotent_mul_diagU1 t₂`,
  -- then `(unipotent_mul_diag t₁)⁻¹ * (unipotent_mul_diag t₂)` is in `U1 v`.
  have unipotent_mem_U1 :=
    (unipotent_mul_diag_inv_mul_unipotent_mul_diag α hα (Quotient.out t₁) (Quotient.out t₂)) ▸
      (QuotientGroup.eq.mp h)
  -- But inspecting the top-right entry of `(unipotent_mul_diag t₁)⁻¹ * (unipotent_mul_diag t₂)`
  -- gives us `t₁ = t₂`.
  have unipotent_apply_zero_one_mem_integer := apply_mem_integer v _ unipotent_mem_U1 0 1
  simp only [unipotent, Matrix.unitOfDetInvertible, Fin.isValue, val_unitOfInvertible,
    Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one, Matrix.cons_val_fin_one,
    Matrix.cons_val_zero] at unipotent_apply_zero_one_mem_integer
  rw[← (QuotientAddGroup.out_eq' t₁), ← (QuotientAddGroup.out_eq' t₂)]
  apply QuotientAddGroup.eq.mpr; apply Ideal.mem_span_singleton'.mpr
  use ⟨ _ , unipotent_apply_zero_one_mem_integer ⟩
  apply (Subtype.coe_inj).mp; push_cast
  ring_nf; rw[mul_inv_cancel₀ ((Subtype.coe_ne_coe).mpr hα), one_mul, one_mul]

variable {F v} in
/-- Each coset in `U1diagU1` is of the form `unipotent_mul_diagU1` for some `t ∈ O_v`. -/
lemma surjOn_unipotent_mul_diagU1_U1diagU1 :
    Set.SurjOn (unipotent_mul_diagU1 α hα) ⊤ (U1diagU1 α hα) := by
  rintro _ ⟨ _, ⟨ x, hx, _, rfl, rfl ⟩ , rfl ⟩
  -- Each element of `U1diagU1` can be written as `x * diag`,
  -- where `x = !![a,b;c,d]` is viewed as a matrix over `O_v`.
  let a : (adicCompletionIntegers F v) := ⟨ _ , apply_mem_integer v x hx 0 0 ⟩
  let b : (adicCompletionIntegers F v) := ⟨ _ , apply_mem_integer v x hx 0 1 ⟩
  let c : (adicCompletionIntegers F v) := ⟨ _ , apply_mem_integer v x hx 1 0 ⟩
  let d : (adicCompletionIntegers F v) := ⟨ _ , apply_mem_integer v x hx 1 1 ⟩
  have hx₁ : x = !![(a : adicCompletion F v), b; c, d] :=
    (Matrix.etaExpand_eq (x : Matrix (Fin 2) (Fin 2) (adicCompletion F v))).symm
  -- The desired t is `⅟d * b`.
  letI invertible_d := (isUnit_apply_one_one v x hx).invertible
  let t : ↥(adicCompletionIntegers F v) ⧸ (Ideal.span {α}) := (⅟d * b)
  use t
  have ht : (b + -Quotient.out t * d) ∈ Ideal.span {α} := by
    apply Ideal.mem_span_singleton'.mpr
    have t_def : (Ideal.Quotient.mk (Ideal.span {α})) (Quotient.out t) = (⅟d * b) := by
      simp only [Ideal.Quotient.mk_out]; rfl
    obtain ⟨ q, hq ⟩ :=
      Ideal.mem_span_singleton'.mp (Ideal.Quotient.eq.mp t_def)
    use - d * q
    rw[mul_assoc, hq]; ring_nf; simp
  /- The rest of the proof is devoted to showing that this t works.
  This means showing that `unipotent_mul_diag⁻¹ * x * diag` is in U.
  -/
  simp only [unipotent_mul_diagU1, Set.top_eq_univ, Set.mem_univ, true_and]
  apply QuotientGroup.eq.mpr
  unfold unipotent_mul_diag; rw[mul_inv_rev, ← mul_assoc, mul_assoc _ _ x]
  /- But `unipotent_mul_diag⁻¹ * x * diag = diag⁻¹ * (unipotent⁻¹ * x) * diag`,
  so it suffices to show `(unipotent⁻¹ * x) 0 1 ∈ (Ideal.span {α})`.
  -/
  apply (conjBy_diag_mem_U1_iff_apply_zero_one_mem_ideal _ _ _
    (Subgroup.mul_mem _ (Subgroup.inv_mem _ (unipotent_mem_U1 _)) hx)).mpr
  simp only [Fin.isValue, Units.val_mul, Matrix.coe_units_inv, unipotent_def, Matrix.inv_def,
    Matrix.det_fin_two_of, mul_one, mul_zero, sub_zero, Ring.inverse_one,
    Matrix.adjugate_fin_two_of, neg_zero, one_smul, hx₁, Matrix.mul_apply, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_fin_one, Matrix.cons_val_zero, Matrix.cons_val_one,
    Fin.sum_univ_two, one_mul]
  exact_mod_cast ht

variable {F v} in
/-- The double coset space `U1diagU1` is the disjoint union of
`unipotent_mul_diagU1` as t ranges over `O_v / αO_v`. -/
theorem bijOn_unipotent_mul_diagU1_U1diagU1 :
    Set.BijOn (unipotent_mul_diagU1 α hα) ⊤ (U1diagU1 α hα) :=
  ⟨ mapsTo_unipotent_mul_diagU1_U1diagU1 α hα,
    injOn_unipotent_mul_diagU1 α hα,
    surjOn_unipotent_mul_diagU1_U1diagU1 α hα ⟩

end CosetDecomposition

end Local

end TotallyDefiniteQuaternionAlgebra.WeightTwoAutomorphicForm.HeckeOperator
