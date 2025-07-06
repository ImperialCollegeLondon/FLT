/-
Copyright (c) 2025 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Andrew Yang, Matthew Jasper
-/
import FLT.AutomorphicForm.QuaternionAlgebra.HeckeOperators.Abstract -- abstract Hecke ops
import FLT.AutomorphicForm.QuaternionAlgebra.Defs -- definitions of automorphic forms
import FLT.QuaternionAlgebra.NumberField -- rigidifications of quat algs
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
import FLT.DedekindDomain.FiniteAdeleRing.LocalUnits -- for (π 0; 0 1)
import FLT.Mathlib.Topology.Algebra.RestrictedProduct

open NumberField IsQuaternionAlgebra.NumberField IsDedekindDomain
open TotallyDefiniteQuaternionAlgebra
open IsDedekindDomain.HeightOneSpectrum
open scoped TensorProduct
open scoped Pointwise

namespace TotallyDefiniteQuaternionAlgebra.WeightTwoAutomorphicForm.HeckeOperator

-- let F be a totally real number field
variable (F : Type*) [Field F] [NumberField F] [IsTotallyReal F]

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

variable {F α hα} in
/-- The subgroup `U1 = GL2.localTameLevel`. -/
noncomputable abbrev U1v : Subgroup (GL (Fin 2) (adicCompletion F v)) := (GL2.localTameLevel v)

variable {F v} in
/-- The matrix element `g = diag[α, 1]`. -/
noncomputable def g : (GL (Fin 2) (adicCompletion F v)) :=
  Matrix.GeneralLinearGroup.diagonal (![⟨(α : v.adicCompletion F),
    (α : v.adicCompletion F)⁻¹, by
      rw [mul_inv_cancel₀]
      exact_mod_cast hα, by
      rw [inv_mul_cancel₀]
      exact_mod_cast hα⟩, 1])

set_option synthInstance.maxHeartbeats 0 in
-- double coset space
variable {F v} in
/-- The double coset space `U1 g U1` as a set of left cosets. -/
noncomputable def U1gU1 :
  Set ((GL (Fin 2) (adicCompletion F v)) ⧸ ↑(U1v v)) :=
  (QuotientGroup.mk '' ((U1v v) * g α hα • ↑(U1v v) ))

variable {F v} in
/-- The matrix element `gt = !![α, t; 0, 1]`. -/
noncomputable def gt (t : v.adicCompletionIntegers F) :
  (GL (Fin 2) (adicCompletion F v)) := by
  let gtInv : Invertible !![(α : v.adicCompletion F), t; 0, 1].det :=
  { invOf := (α : v.adicCompletion F)⁻¹,
    invOf_mul_self :=
      by simp only [Matrix.det_fin_two_of,
        mul_one, mul_zero, sub_zero]; rw [inv_mul_cancel₀]; exact_mod_cast hα,
    mul_invOf_self :=
      by simp only [Matrix.det_fin_two_of,
        mul_one, mul_zero, sub_zero]; rw [mul_inv_cancel₀]; exact_mod_cast hα }
  exact Matrix.unitOfDetInvertible !![(α : v.adicCompletion F), t; 0, 1]

variable {F v} in
/-- For each `t ∈ O_v / αO_v`, the left coset `gt U1`
for a lift of t to `O_v`. -/
noncomputable def gtU1
  (t : ↑(adicCompletionIntegers F v) ⧸ (AddSubgroup.map (AddMonoidHom.mulLeft α)
    (⊤ : AddSubgroup ↑(adicCompletionIntegers F v)))) :
  ((GL (Fin 2) (adicCompletion F v)) ⧸ ↑(U1v v)) := by
  let tLift : ↑(adicCompletionIntegers F v) := Quotient.out t
  exact QuotientGroup.mk (gt α hα tLift)

set_option maxHeartbeats 600000 in
-- long explicit matrix coset computations
variable {F v} in
omit [IsTotallyReal F] in
/-- The double coset space `U1gU1` is the disjoint union of `gtU1`
as t ranges over `O_v / αO_v`. -/
lemma U1gU1_cosetDecomposition : Set.BijOn (gtU1 α hα) ⊤ (U1gU1 α hα) := by
  have r (A : Matrix (Fin 2) (Fin 2) (adicCompletion F v)) [Invertible A.det] :
    (↑(A.unitOfDetInvertible) : Matrix (Fin 2) (Fin 2) (adicCompletion F v)) = A := rfl
  have valEquiv : Valued.v.IsEquiv (adicCompletionIntegers F v).valuation := by
    apply Valuation.isEquiv_valuation_valuationSubring
  let ht (t : v.adicCompletion F) : (GL (Fin 2) (adicCompletion F v)) := by
    let htInv : Invertible !![1, t; 0, 1].det :=
    { invOf := 1,
      invOf_mul_self :=
        by simp only [Matrix.det_fin_two_of, mul_one, mul_zero, sub_zero],
      mul_invOf_self :=
        by simp only [Matrix.det_fin_two_of, mul_one, mul_zero, sub_zero] }
    exact Matrix.unitOfDetInvertible !![1, t; 0, 1]

  constructor
  · -- Show that `gtU1` is contained in `U1gU1` for all t.
    intro t h
    -- We have `gt = ht * g`.
    have m : (gt α hα (Quotient.out t)) =  ht ↑(Quotient.out t) * g α hα := by
        have r₁ : (g α hα : Matrix (Fin 2) (Fin 2) (adicCompletion F v))
          = !![↑α, 0; 0, 1] := by
          rw[g]; ext i j
          rw[Matrix.GeneralLinearGroup.diagonal]
          fin_cases i
          · fin_cases j
            · simp
            simp
          fin_cases j
          · simp
          simp
        ext i j; push_cast
        rw[gt]; unfold ht; rw[r₁, r, r, Matrix.mul_apply]
        simp only [Fin.sum_univ_two, Fin.isValue]
        fin_cases i
        · fin_cases j
          · simp
          simp
        simp
    rw[gtU1, m, U1gU1]
    use (ht ↑(Quotient.out t) * g α hα)
    constructor
    · use ht ↑(Quotient.out t)
      constructor
      · -- Show that `ht` is in `U1`.
        unfold ht
        constructor
        · let htInt : ((Matrix (Fin 2) (Fin 2) ↥(adicCompletionIntegers F v))ˣ) := by
            let htInv : Invertible !![1, (Quotient.out t); 0, 1].det :=
            { invOf := 1,
              invOf_mul_self :=
              by simp only [Matrix.det_fin_two_of, mul_one, mul_zero, sub_zero],
              mul_invOf_self :=
              by simp only [Matrix.det_fin_two_of, mul_one, mul_zero, sub_zero] }
            exact Matrix.unitOfDetInvertible !![1, (Quotient.out t); 0, 1]
          use htInt; refine Units.eq_iff.mp ?_; rw[r]
          have hr : (htInt = !![1, (Quotient.out t); 0, 1]) := rfl
          rw[Units.coe_map, hr]
          simp only [RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, RingHom.mapMatrix_apply,
            ValuationSubring.coe_subtype]
          ext i j
          fin_cases i
          · fin_cases j
            · simp
            simp
          fin_cases j
          · simp
          simp
        rw[r]; simp
      use g α hα
      simp only [and_true]
      use (1 : GL (Fin 2) (adicCompletion F v))
      simp only [SetLike.mem_coe, smul_eq_mul, mul_one, and_true]
      exact Subgroup.one_mem (U1v v)
    rfl

  constructor
  · -- Show that distinct t give distinct `gtU1`, i.e. we have a disjoint union.
    intro t₁ h₁ t₂ h₂ h
    rw[gtU1, gtU1] at h
    have h₀ := QuotientGroup.eq.mp h
    -- If `gtU1 t₁ = gtU1 t₂`, then `(gt t₁)⁻¹ * (gt t₂)` is in `U1v`.
    have m : (gt α hα (Quotient.out t₁))⁻¹ * gt α hα (Quotient.out t₂)
      = ht ((α : v.adicCompletion F)⁻¹ *
        (( - (Quotient.out t₁) + (Quotient.out t₂)) : adicCompletion F v )) := by
        apply inv_mul_eq_iff_eq_mul.mpr
        rw [gt, gt]; unfold ht
        ext i j; push_cast
        rw[r, r, r, Matrix.mul_apply]
        simp only [Fin.sum_univ_two, Fin.isValue]
        fin_cases i
        · fin_cases j
          · simp
          simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one, Matrix.of_apply, Matrix.cons_val',
            Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.cons_val_zero, mul_one]
          rw[← mul_assoc, mul_inv_cancel₀, one_mul]; ring
          exact (Subtype.coe_ne_coe.mpr hα)
        simp
    rw[m] at h₀
    obtain ⟨ ⟨ x, y ⟩ , z ⟩ := h₀
    -- But inspecting the top-right entry of `(gt t₁)⁻¹ * (gt t₂)`
    -- gives us `t₁ = t₂`.
    apply_fun (fun (A : (Matrix (Fin 2) (Fin 2) (adicCompletion F v))ˣ) ↦ A 0 1) at y
    unfold ht at y
    simp only [RingHom.toMonoidHom_eq_coe, Fin.isValue, Units.coe_map, MonoidHom.coe_coe,
      RingHom.mapMatrix_apply, ValuationSubring.coe_subtype, Matrix.map_apply] at y
    have w : ((x 0 1) : adicCompletion F v) = (α : v.adicCompletion F)⁻¹ *
        (( - (Quotient.out t₁) + (Quotient.out t₂)) : adicCompletion F v ) := by
        rw[y]; rfl
    conv_lhs =>
      apply Eq.symm (QuotientAddGroup.out_eq' t₁)
    conv_rhs =>
      apply Eq.symm (QuotientAddGroup.out_eq' t₂)
    apply QuotientAddGroup.eq.mpr
    use (x 0 1)
    constructor
    · simp
    simp only [Fin.isValue, AddMonoidHom.coe_mulLeft]
    apply (Subtype.coe_inj).mp; push_cast
    rw[w, ← mul_assoc, mul_inv_cancel₀, one_mul]
    exact (Subtype.coe_ne_coe.mpr hα)

  -- Show that each coset in `U1gU1` is of the form `gtU1` for some t.
  -- This is the more involved part.
  intro co h
  obtain ⟨ co₀, ⟨ ⟨ co₁, h₁, ⟨ l, ⟨ ⟨ co₂, ⟨ h₂, z ⟩ ⟩ , hl ⟩ ⟩ ⟩ , h₀ ⟩ ⟩ := h
  have hp : co₀ = co₁ * (g α hα) * co₂ := by
    rw[← hl, ← z]; simp only [smul_eq_mul]; rw[mul_assoc]
  -- Each element of `U1gU1` can be written as
  -- `x * gU1`, where `x = !![a,b;c,d]`
  -- is viewed as a matrix over `O_v`.
  obtain ⟨ ⟨ x , y ⟩ , z ⟩ := h₁
  have xdetunit :
      IsUnit (x : Matrix (Fin 2) (Fin 2) ↥(adicCompletionIntegers F v)).det :=
      Matrix.isUnits_det_units x
  let a : (adicCompletionIntegers F v) := (x 0 0)
  let b : (adicCompletionIntegers F v) := (x 0 1)
  let c : (adicCompletionIntegers F v) := (x 1 0)
  let d : (adicCompletionIntegers F v) := (x 1 1)
  have h11 : c * (x.inv 0 1) + d * (x.inv 1 1) = 1 := by calc
    _ = (x 1 0) * (x.inv 0 1) + (x 1 1) * (x.inv 1 1) := rfl
    _ = (x * x.inv) 1 1 := by rw[Matrix.mul_apply]; simp
    _ = 1 := by rw[x.val_inv]; simp
  have valc : Valued.v (c : adicCompletion F v) < 1 := by
    unfold c
    apply_fun (fun (A : (Matrix (Fin 2) (Fin 2) (adicCompletion F v))ˣ) ↦ A 1 0) at y
    simp only [RingHom.toMonoidHom_eq_coe, Fin.isValue, Units.coe_map, MonoidHom.coe_coe,
      RingHom.mapMatrix_apply, ValuationSubring.coe_subtype, Matrix.map_apply] at y
    rw[y]
    apply z.right
  have maxc : c ∈ IsLocalRing.maximalIdeal (adicCompletionIntegers F v) := by
    apply (ValuationSubring.valuation_lt_one_iff (adicCompletionIntegers F v) c).mpr
    apply (Valuation.isEquiv_iff_val_lt_one.mp valEquiv).mp
    exact valc
  have maxd : d ∉ IsLocalRing.maximalIdeal (adicCompletionIntegers F v) := by
    by_contra maxd₁
    have max1 : c * (x.inv 0 1) + d * (x.inv 1 1)
      ∈ IsLocalRing.maximalIdeal (adicCompletionIntegers F v) := by
      apply Ideal.add_mem
      repeat
        apply Ideal.mul_mem_right
        assumption
    rw[h11] at max1
    have nonunit : 1 ∈ nonunits ↥(adicCompletionIntegers F v) :=
      (IsLocalRing.mem_maximalIdeal 1).mp max1
    exact one_notMem_nonunits nonunit
  have dunit : IsUnit d := by
    by_contra dnotunit
    have dnonunit : d ∈ nonunits ↥(adicCompletionIntegers F v) := mem_nonunits_iff.mpr dnotunit
    have dmax : d ∈ IsLocalRing.maximalIdeal (adicCompletionIntegers F v) :=
      (IsLocalRing.mem_maximalIdeal d).mpr dnonunit
    exact maxd dmax
  obtain ⟨ dinv, dval_inv, dinv_val ⟩ := isUnit_iff_exists.mp dunit
  /- In the above, we show that d is a unit,
  because c is a non-unit (by assumption on U).
  This is necessary because the desired t
  is `b * d⁻¹`.
  The rest of the proof is devoted to showing
  that this t works.
  This means showing that `gt⁻¹ * x * g` is in U,
  which boils down to explicit matrix computations.
  -/
  let t : ↥(adicCompletionIntegers F v) ⧸ AddSubgroup.map (AddMonoidHom.mulLeft α) ⊤ := b * dinv
  use t
  simp only [Set.top_eq_univ, Set.mem_univ, true_and]; rw[gtU1, ← h₀]
  apply QuotientGroup.eq.mpr; rw[hp, ← mul_assoc]
  have ht : t = b * dinv := rfl
  rw[← QuotientAddGroup.out_eq' t] at ht
  have ht₁ := QuotientAddGroup.eq.mp ht
  obtain ⟨q, hq⟩ := ht₁
  simp only [AddSubgroup.coe_top, Set.mem_univ, AddMonoidHom.coe_mulLeft, true_and] at hq
  have hq₁ : Quotient.out t = b * dinv - α * q := by rw[hq]; ring
  -- We have `t = b * dinv - α * q` for some `q ∈ O_v`.
  -- Now we compute `m := gt⁻¹ * x * g` explicitly,
  -- and denote the resulting matrix by `mMatrix`.
  apply Subgroup.mul_mem
  · let m : GL (Fin 2) (adicCompletion F v) := (gt α hα (Quotient.out t))⁻¹ * (co₁ * g α hα)
    have hmr : m = (gt α hα (Quotient.out t))⁻¹ * (co₁ * g α hα) := rfl
    let mMatrix : Matrix (Fin 2) (Fin 2) (adicCompletion F v) :=
      !![a - (Quotient.out t) * c, (α : adicCompletion F v)⁻¹ * (b - (Quotient.out t) * d);
        c * α, d]
    have hm : m = mMatrix := by
      have hp1 : (gt α hα (Quotient.out t))⁻¹
        = !![(α : adicCompletion F v)⁻¹, -(α : adicCompletion F v)⁻¹ * (Quotient.out t); 0, 1] := by
        rw[gt]; push_cast; rw[r, Matrix.inv_def]
        simp only [Matrix.det_fin_two_of, mul_one, mul_zero, sub_zero, Ring.inverse_eq_inv',
          Matrix.adjugate_fin_two_of, neg_zero, Matrix.smul_of, Matrix.smul_cons, smul_eq_mul,
          mul_neg, Matrix.smul_empty, neg_mul, EmbeddingLike.apply_eq_iff_eq]
        rw [inv_mul_cancel₀]; exact_mod_cast hα
      have hp2 : co₁ = !![(a : adicCompletion F v), b; c, d] := by
        rw[← y]; ext i j
        simp only [RingHom.toMonoidHom_eq_coe, Matrix.of_apply, Matrix.cons_val',
          Matrix.cons_val_fin_one]
        fin_cases i
        · fin_cases j
          · simp; rfl
          simp; rfl
        fin_cases j
        · simp; rfl
        simp; rfl
      have hp3 : g α hα = !![(α : adicCompletion F v), 0; 0, 1] := by
        rw[g]; ext i j
        simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_fin_one]
        fin_cases i
        · fin_cases j
          · simp; rfl
          simp; rfl
        fin_cases j
        · simp; rfl
        simp; rfl
      rw[hmr]; push_cast; rw[hp2, hp3]; norm_cast; rw[hp1]
      unfold mMatrix
      simp only [neg_mul, Matrix.cons_mul, Nat.succ_eq_add_one, Nat.reduceAdd, Matrix.vecMul_cons,
        Matrix.head_cons, Matrix.smul_cons, smul_eq_mul, mul_zero, Matrix.smul_empty,
        Matrix.tail_cons, mul_one, Matrix.empty_vecMul, add_zero, Matrix.add_cons, zero_add,
        Matrix.empty_add_empty, Matrix.empty_mul, Equiv.symm_apply_apply, neg_smul, Matrix.neg_cons,
        Matrix.neg_empty, zero_smul, one_smul, EmbeddingLike.apply_eq_iff_eq]
      ring_nf
      ext i j
      fin_cases i
      · fin_cases j
        · simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.zero_eta, Fin.isValue,
          Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one]
          rw [mul_inv_cancel₀]
          · simp
          exact_mod_cast hα
        simp
      fin_cases j
      · simp
      simp
    rw[← hmr]
    -- First we show that `m = mMatrix` is in `GL_2(O_v)`.
    -- Note this is not a priori obvious,
    -- as even `g` itself need not be in `GL_2(O_v)`
    -- (`α` need not be a unit).
    let mMatrixInt : Matrix (Fin 2) (Fin 2) (adicCompletionIntegers F v) :=
      !![a - (Quotient.out t) * c, q * d; c * α, d]
    have intdet : mMatrixInt.det = x.val.det := by
      unfold mMatrixInt
      rw[Matrix.det_fin_two_of, hq₁]; ring_nf
      rw[mul_assoc b dinv c, mul_comm dinv c, mul_assoc, mul_assoc, dinv_val]; ring_nf
      rw[Matrix.det_fin_two]
    rw[← intdet] at xdetunit
    have mMatrixIntUnit : IsUnit mMatrixInt :=
      (Matrix.isUnit_iff_isUnit_det mMatrixInt).mpr xdetunit
    obtain ⟨ mMatrixIntUnitval , hmMatrixIntUnitval ⟩ := mMatrixIntUnit
    have inteq : (Units.map (RingHom.mapMatrix ((v.adicCompletionIntegers F).subtype)).toMonoidHom)
      mMatrixIntUnitval = m := by
      simp only [RingHom.toMonoidHom_eq_coe]
      ext i j; rw[hm]; unfold mMatrix
      simp only [Units.coe_map, MonoidHom.coe_coe, RingHom.mapMatrix_apply,
        ValuationSubring.coe_subtype, Matrix.map_apply, Matrix.of_apply, Matrix.cons_val',
        Matrix.cons_val_fin_one]
      rw[hmMatrixIntUnitval]; unfold mMatrixInt
      fin_cases i
      · fin_cases j
        · simp
        simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one, Matrix.of_apply, Matrix.cons_val',
          Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.cons_val_zero, MulMemClass.coe_mul]
        rw[hq₁]
        ring_nf; push_cast
        rw[mul_sub_left_distrib]
        rw[mul_assoc (d : adicCompletion F v) (α : adicCompletion F v)⁻¹
          ((α : adicCompletion F v) * (q : adicCompletion F v))]
        rw[← mul_assoc (α : adicCompletion F v)⁻¹ (α : adicCompletion F v) (q : adicCompletion F v)]
        rw[inv_mul_cancel₀]
        · rw[mul_comm (d : adicCompletion F v) (α : adicCompletion F v)⁻¹]
          rw[mul_comm (b : adicCompletion F v) (dinv : adicCompletion F v)]
          rw[mul_assoc, ← mul_assoc
            (d : adicCompletion F v) (dinv : adicCompletion F v) (b : adicCompletion F v)]
          norm_cast; rw[dval_inv]
          push_cast; ring_nf
        exact_mod_cast hα
      fin_cases j
      · simp
      simp
    constructor
    · use mMatrixIntUnitval
    -- Next we show that `m = mMatrix` is in `GL2.localTameLevel`.
    rw[hm]; unfold mMatrix
    simp only [Fin.isValue, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_fin_one, Matrix.cons_val_one]
    norm_cast
    constructor
    · have valad : Valued.v ((a - d) : adicCompletion F v) < 1 := by
        unfold a d
        have va : (x 0 0) = co₁ 0 0 := by
          apply_fun (fun (A : (Matrix (Fin 2) (Fin 2) (adicCompletion F v))ˣ) ↦ A 0 0) at y
          simp only [RingHom.toMonoidHom_eq_coe, Fin.isValue] at y
          exact y
        have vd : (x 1 1) = co₁ 1 1 := by
          apply_fun (fun (A : (Matrix (Fin 2) (Fin 2) (adicCompletion F v))ˣ) ↦ A 1 1) at y
          simp only [RingHom.toMonoidHom_eq_coe, Fin.isValue] at y
          exact y
        rw[va, vd]
        apply z.left
      norm_cast at valad
      have maxad : (a - d) ∈ IsLocalRing.maximalIdeal (adicCompletionIntegers F v) := by
        apply (ValuationSubring.valuation_lt_one_iff (adicCompletionIntegers F v) (a-d)).mpr
        apply (Valuation.isEquiv_iff_val_lt_one.mp valEquiv).mp
        exact valad
      rw[sub_right_comm]
      have maxadc : (a - d - Quotient.out t * c)
        ∈ IsLocalRing.maximalIdeal (adicCompletionIntegers F v) := by
        apply Ideal.sub_mem
        · assumption
        apply Ideal.mul_mem_left
        assumption
      apply (Valuation.isEquiv_iff_val_lt_one.mp valEquiv).mpr
      exact (ValuationSubring.valuation_lt_one_iff (adicCompletionIntegers F v) _).mp maxadc
    have maxcα : c * α ∈ IsLocalRing.maximalIdeal ↥(adicCompletionIntegers F v) := by
      exact Ideal.mul_mem_right α (IsLocalRing.maximalIdeal ↥(adicCompletionIntegers F v)) maxc
    apply (Valuation.isEquiv_iff_val_lt_one.mp valEquiv).mpr
    exact (ValuationSubring.valuation_lt_one_iff (adicCompletionIntegers F v) (c*α)).mp maxcα
  assumption

end Local

end TotallyDefiniteQuaternionAlgebra.WeightTwoAutomorphicForm.HeckeOperator
