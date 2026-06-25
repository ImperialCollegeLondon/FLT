/-
Copyright (c) 2026 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

/-! # Bound of degree of splitting field -/

@[expose] public section

open Polynomial IntermediateField

lemma Polynomial.IsSplittingField.finrank_le_factorial_aux.{u}
  {F K : Type u} [Field F] [Field K] [Algebra F K]
    (p : Polynomial F) [p.IsSplittingField F K] :
    Module.finrank F K ≤ p.natDegree.factorial := by
  induction hp : p.natDegree generalizing F with
  | zero =>
    obtain ⟨a, rfl⟩ := natDegree_eq_zero.mp hp
    have : Module.finrank F K = 1 := by
      simpa [Subalgebra.bot_eq_top_iff_finrank_eq_one] using
        IsSplittingField.adjoin_rootSet K (C a)
    simp [this]
  | succ n IH =>
    obtain ⟨x, hx⟩ := (IsSplittingField.splits K p).exists_eval_eq_zero
      (by simpa using! degree_ne_of_natDegree_ne (by simp [hp]))
    rw [eval_map_algebraMap] at hx
    obtain ⟨q, hq⟩ : X - C (AdjoinSimple.gen F x) ∣ p.map (algebraMap F F⟮x⟯) := by
      convert X_sub_C_dvd_sub_C_eval (p := p.map (algebraMap F F⟮x⟯))
      suffices aeval (AdjoinSimple.gen F x) p = 0 by simp [this]
      ext1
      exact (aeval_algHom_apply F⟮x⟯.val ..).symm.trans (by simpa)
    have hp0 : p ≠ 0 := by rintro rfl; simp_all
    have hq0 : q ≠ 0 := by rintro rfl; simp_all
    have hqn : q.natDegree = n := by
      refine Nat.add_right_cancel (m := 1) ?_
      convert congr(($hq).natDegree).symm
      · simp [natDegree_mul, hq0, X_sub_C_ne_zero, add_comm]
      · simp [hp]
    have : IsSplittingField F⟮x⟯ K q := by
      refine ⟨.of_dvd (IsSplittingField.splits K p) (by simp [hp0]) ?_, ?_⟩
      · rw [IsScalarTower.algebraMap_eq F F⟮x⟯ K, ← Polynomial.map_map]
        exact map_dvd _ ⟨_, hq.trans (mul_comm _ _)⟩
      · have : Module.Finite F K := Polynomial.IsSplittingField.finiteDimensional _ p
        refine Algebra.adjoin_eq_top_of_intermediateField (fun a ha ↦
          ⟨q, hq0, by simpa [hq0, mem_rootSet] using ha⟩) ?_
        apply IntermediateField.restrictScalars_injective F
        apply IntermediateField.toSubalgebra_injective
        rw [IntermediateField.adjoin_adjoin_left, restrictScalars_top,
          Set.singleton_union, adjoin_toSubalgebra, top_toSubalgebra,
          ← IsSplittingField.adjoin_rootSet K p]
        congr
        ext a
        simp [hq0, hp0, mem_rootSet, - aeval_map_algebraMap, ← aeval_map_algebraMap F⟮x⟯ _ p,
          hq, sub_eq_zero]
    rw [← Module.finrank_mul_finrank _ F⟮x⟯, Nat.factorial_succ]
    refine Nat.mul_le_mul ?_ (IH (F := IntermediateField.adjoin F {x}) _ hqn)
    rw [IntermediateField.adjoin.finrank]
    · grw [natDegree_le_of_dvd (minpoly.dvd F x hx) hp0, hp]
    · exact IsAlgebraic.isIntegral ⟨p, hp0, hx⟩

lemma Polynomial.IsSplittingField.finrank_le_factorial
    {F K : Type*} [Field F] [Field K] [Algebra F K]
    (p : Polynomial F) [p.IsSplittingField F K] :
    Module.finrank F K ≤ p.natDegree.factorial := by
  simpa using IsSplittingField.finrank_le_factorial_aux (F := (⊥ : IntermediateField F K)) (K := K)
    (p.map (algebraMap _ _))
