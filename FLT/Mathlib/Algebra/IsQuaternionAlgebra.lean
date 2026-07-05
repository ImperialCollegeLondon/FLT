/-
Copyright (c) 2025 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/
module

public import Mathlib.Analysis.Quaternion -- for *notation* ℍ only!
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic

import Mathlib.RingTheory.SimpleModule.WedderburnArtin
import Mathlib.LinearAlgebra.Matrix.Unique

/-!
# Is Quaternion Algebra

Material destined for Mathlib.
-/

@[expose] public section

open Algebra Polynomial in
/-- The surjective algebra morphism `R[X]/(minpoly R x) → R[x]`.
If `R` is an integrally closed domain and `x` is integral, this is an isomorphism,
see `minpoly.equivAdjoin`. -/
noncomputable
def Minpoly.toAdjoin' (R : Type*) {S : Type*} [CommRing R] [Ring S] [Algebra R S] (x : S) :
    AdjoinRoot (minpoly R x) →ₐ[R] adjoin R ({x} : Set S) :=
  AdjoinRoot.liftAlgHom _ (Algebra.ofId R <| adjoin R {x}) ⟨x, self_mem_adjoin_singleton R x⟩
    (by change aeval _ _ = _; simp [← Subalgebra.coe_eq_zero, aeval_subalgebra_coe])

open Algebra Polynomial in
lemma Minpoly.toAdjoin'_surjective
    (R : Type*) {S : Type*} [CommRing R] [Ring S] [Algebra R S] (x : S) :
    Function.Surjective (Minpoly.toAdjoin' R x) := by
  rw [← AlgHom.range_eq_top, _root_.eq_top_iff, ← adjoin_adjoin_coe_preimage]
  exact adjoin_le fun ⟨y₁, y₂⟩ h ↦ ⟨AdjoinRoot.mk (minpoly R x) X,
    by simpa [Minpoly.toAdjoin'] using h.symm⟩

open AdjoinRoot in
/-- If `p` is the minimal polynomial of `a` over `F` then `F[a] ≃ₐ[F] F[x]/(p)` -/
noncomputable
def AlgEquiv.adjoinSingletonEquivAdjoinRootMinpoly' (F : Type*) {R : Type*} [Field F]
    [Ring R] [Algebra F R] (x : R) :
    Algebra.adjoin F ({x} : Set R) ≃ₐ[F] AdjoinRoot (minpoly F x) :=
  AlgEquiv.symm <| AlgEquiv.ofBijective (Minpoly.toAdjoin' F x) <| by
    refine ⟨(injective_iff_map_eq_zero _).2 fun P₁ hP₁ ↦ ?_, Minpoly.toAdjoin'_surjective F x⟩
    obtain ⟨P, rfl⟩ := mk_surjective P₁
    refine AdjoinRoot.mk_eq_zero.mpr (minpoly.dvd F x ?_)
    simpa [Minpoly.toAdjoin', ← Subalgebra.coe_eq_zero, ← Polynomial.aeval_def] using hP₁

/-- `IsQuaternionAlgebra F D` says that `D` is a quaternion algebra over the field `F`,
i.e. a four-dimensional central simple `F`-algebra. -/
class IsQuaternionAlgebra (F : Type*) [Field F] (D : Type*) [Ring D] [Algebra F D] : Prop where
  isSimpleRing : IsSimpleRing D
  isCentral : Algebra.IsCentral F D
  dim_four : Module.rank F D = 4

namespace IsQuaternionAlgebra

attribute [instance low] isSimpleRing isCentral

variable (F : Type*) [Field F] (D : Type*) [Ring D] [Algebra F D] [IsQuaternionAlgebra F D]

instance : Module.Finite F D := FiniteDimensional.of_rank_eq_nat dim_four

lemma finrank_eq_four : Module.finrank F D = 4 :=
  Module.finrank_eq_of_rank_eq IsQuaternionAlgebra.dim_four

open scoped IsMulCommutative in
include F in
lemma not_isMulCommutative : ¬ IsMulCommutative D := by
  intro H
  by_cases h : (⊥ : Subalgebra F D) = ⊤
  · simp [Subalgebra.bot_eq_top_iff_finrank_eq_one, IsQuaternionAlgebra.finrank_eq_four] at h
  · rw [← Algebra.IsCentral.center_eq_bot F D, Subalgebra.center_eq_top] at h; contradiction

set_option backward.isDefEq.respectTransparency false in
lemma nomepty_algEquiv_matrix_or_forall_isUnit :
    (Nonempty (D ≃ₐ[F] Matrix (Fin 2) (Fin 2) F)) ∨ (∀ a : D, a ≠ 0 → IsUnit a) := by
  have := IsArtinianRing.of_finite F D
  obtain ⟨n, hn, K, _, _, ⟨e⟩⟩ := IsSimpleRing.exists_algEquiv_matrix_divisionRing F D
  have := finrank_eq_four F D
  rw [e.toLinearEquiv.finrank_eq, Module.finrank_matrix, Fintype.card_fin] at this
  obtain (_|_|_|n) := n
  · simp at this
  · let e' := e.trans (by convert Matrix.uniqueAlgEquiv (m := Fin 1))
    exact .inr fun a ha ↦ .of_map e' _ (isUnit_iff_ne_zero.mpr (by simpa))
  · have : Module.finrank F K = 1 := by simpa using this
    let e' : F ≃ₐ[F] K := .ofBijective (Algebra.ofId F K)
      (Algebra.finrank_eq_one_iff_bijective_algebraMap.mp this)
    refine .inl ⟨e.trans e'.mapMatrix.symm⟩
  · cases Nat.eq_zero_or_pos (Module.finrank F K) <;> lia

lemma Algebra.finrank_adjoin_singleton (F : Type*) {A : Type*} [Field F] [Ring A]
    [Algebra F A] (x : A) (hx : IsIntegral F x) :
    Module.finrank F (Algebra.adjoin F {x}) = (minpoly F x).natDegree := by
  rw [(AlgEquiv.adjoinSingletonEquivAdjoinRootMinpoly' F x).toLinearEquiv.finrank_eq,
    (AdjoinRoot.powerBasis (minpoly.ne_zero hx)).finrank, AdjoinRoot.powerBasis_dim]

-- bad proof. Should be something something reduced char poly.
variable {D} in
lemma natDegree_minpoly_le_two (x : D) : (minpoly F x).natDegree ≤ 2 := by
  obtain ⟨⟨e⟩⟩ | H := nomepty_algEquiv_matrix_or_forall_isUnit F D
  · rw [← minpoly.algHom_eq e.toAlgHom e.injective]
    refine (Polynomial.natDegree_le_of_dvd (Matrix.minpoly_dvd_charpoly _) ?_).trans ?_
    · intro a; have := Matrix.charpoly_degree_eq_dim (e x); simp_all
    · simp
  · let : DivisionRing D := .ofIsUnitOrEqZero fun a ↦ or_iff_not_imp_right.mpr (H a)
    have : IsDomain (Algebra.adjoin F {x}) :=
      Function.Injective.isDomain ((Algebra.adjoin F {x}).val) Subtype.val_injective
    have : IsField (Algebra.adjoin F {x}) := isField_of_isIntegral_of_isField' (Field.toIsField F)
    let := this.toField
    have hrank := Module.finrank_mul_finrank F (Algebra.adjoin F {x}) D
    rw [Algebra.finrank_adjoin_singleton _ _ (Algebra.IsIntegral.isIntegral _),
      finrank_eq_four] at hrank
    suffices H : 1 < Module.finrank (Algebra.adjoin F {x}) D by
      by_contra! H'
      rw [← Nat.add_one_le_iff] at H H'
      have := (Nat.mul_le_mul H' H).trans_eq hrank
      lia
    have : Module.Finite (Algebra.adjoin F {x}) D := .of_restrictScalars_finite F _ _
    by_contra! H
    replace H := H.antisymm (Nat.add_one_le_iff.mpr (Module.finrank_pos_iff.mpr inferInstance))
    have : Function.Surjective (Algebra.adjoin F {x}).val :=
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (by rw [Algebra.finrank_adjoin_singleton _ _ (Algebra.IsIntegral.isIntegral _),
        finrank_eq_four, ← hrank, H, mul_one])
      (f := (Algebra.adjoin F {x}).val.toLinearMap)).mp Subtype.val_injective
    rw [← AlgHom.range_eq_top, Subalgebra.range_val] at this
    let e := (Subalgebra.equivOfEq _ _ this).trans Subalgebra.topEquiv
    exact not_isMulCommutative F D ⟨⟨fun x y ↦ e.symm.injective (by simp [mul_comm])⟩⟩

variable [NumberField F]

open NumberField InfinitePlace

open scoped TensorProduct Quaternion

/-- A quaternion algebra `D` over a number field `F` is totally definite if
`D ⊗[F, v] ℝ` is isomorphic to the Hamilton quaternions ℍ for all real places `v` (that is,
for all ring homomorphisms `F → ℝ`). -/
class IsTotallyDefinite : Prop where
  cond (v : InfinitePlace F) (hv : v.IsReal) :
    letI : Algebra F ℝ := (embedding_of_isReal hv).toAlgebra
    Nonempty (ℝ ⊗[F] D ≃ₐ[ℝ] ℍ)

end IsQuaternionAlgebra
