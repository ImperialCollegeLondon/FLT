/-
Copyright (c) 2025 Norbert Voelker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Norbert Voelker
-/

import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.Haar.Unique

import FLT.HaarMeasure.HaarChar.Ring
import FLT.Mathlib.Topology.Algebra.Module.Equiv
import FLT.Mathlib.LinearAlgebra.Determinant
import Mathlib.Topology.Algebra.Module.ModuleTopology

/-!

# Haar character scaling under linear automorphisms

This file proves FLT blueprint lemma 9.18
(`addEquivAddHaarChar_eq_ringHaarChar_det`) regarding Haar measure scaling for
invertible linear maps on a finite-dimensional vector space V over a locally
compact field F. The proof assumes [SecondCountableTopology F].


We proceed by:
1. Proving the scaling property for diagonal matrices.
2. Showing that transvections preserve Haar measure.
3. Extending to arbitrary matrices using induction on diagonal/transvection decomposition.
4. Proving the result for automorphisms on `(ι → F)`
5. Deducing the general result for `V`

## Main results:

* `addEquivAddHaarChar_eq_ringHaarChar_det_diagonal`
* `transvections_preserve_addHaar_pi`
* `addEquivAddHaarChar_eq_ringHaarChar_det_matrix_pi`
* `addEquivAddHaarChar_eq_ringHaarChar_det_pi`
* `addEquivAddHaarChar_eq_ringHaarChar_det`

## TODO

* Reivew material in auxiliary sections (LinearEquiv, ContinousLinearEquiv, pi)
  and move it to other files as appropriate

* Review [SecondCountableTopology F] assumption as Mathlib measure theory
  evolves.
-/

/-!
### Auxiliary lemmas about linear equivalences and matrices
-/
section LinearEquiv

variable {F : Type*} [Field F]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {V : Type*} [AddCommGroup V] [Module F V]

lemma LinearEquiv.det_ne_zero
  {F : Type*} [Field F] {V : Type*} [AddCommGroup V] [Module F V]
  (e : V ≃ₗ[F] V) : e.toLinearMap.det ≠ 0 := isUnit_iff_ne_zero.mp (isUnit_det' e)

lemma Matrix.toLinearEquiv_toLinearMap
    (b : Module.Basis ι F V) (M : Matrix ι ι F) (h : IsUnit M.det) :
    (Matrix.toLinearEquiv b M h).toLinearMap = Matrix.toLin b b M := rfl

lemma LinearEquiv.det_of_toLinarEquiv
    (b : Module.Basis ι F V) {M : Matrix ι ι F} (h : IsUnit M.det) :
    LinearEquiv.det (M.toLinearEquiv b h) = Units.mk0 M.det (isUnit_iff_ne_zero.mp h) := by
  refine Units.val_inj.mp ?_
  simp [Matrix.toLinearEquiv_toLinearMap]

end LinearEquiv

/-!
### Continuous linear equivalences
-/
section ContinousLinearEquiv

variable {F : Type*} [Field F] [TopologicalSpace F]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {V : Type*} [AddCommGroup V] [Module F V] [TopologicalSpace V]
variable [IsModuleTopology F V] [ContinuousAdd V]

lemma ContinuousLinearEquiv.toMatrix_det_ne_zero
 {F : Type*} [Field F] {V : Type*} [AddCommGroup V] [Module F V] [TopologicalSpace V]
    (b : Module.Basis ι F V) (ρ : V ≃L[F] V) :
      (ρ.toLinearMap.toMatrix b b).det ≠ 0 := by
      simp[LinearEquiv.det_ne_zero]

lemma ContinuousLinearEquiv.toContinuousAddEquiv_trans
    {R : Type*} {E : Type*} [Semiring R] [AddCommMonoid E] [Module R E]
    [TopologicalSpace E] [AddGroup E] [IsTopologicalAddGroup E] {e f : E ≃L[R] E} :
    (e.trans f).toContinuousAddEquiv =
      e.toContinuousAddEquiv.trans f.toContinuousAddEquiv := rfl

namespace Matrix

noncomputable def toContinuousLinearEquiv
  (M : Matrix ι ι F) (b : Module.Basis ι F V) (h : M.det ≠ 0) : V ≃L[F] V :=
  let e := Matrix.toLinearEquiv b M (Ne.isUnit h)
  have ce : Continuous e :=
    IsModuleTopology.continuous_of_linearMap e.toLinearMap
  have ce_inv : Continuous e.symm :=
    IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap
  ⟨e, ce, ce_inv⟩

@[simp]
lemma toContinousLinearEquiv_apply
  (M : Matrix ι ι F) (b : Module.Basis ι F V) (h : M.det ≠ 0) (x : V) :
  (M.toContinuousLinearEquiv b h) x = toLin b b M x := rfl

@[simp]
lemma toContinuousLinearEquiv_toLin_coe
  (M : Matrix ι ι F) (b : Module.Basis ι F V) (h : M.det ≠ 0) :
  ⇑(M.toContinuousLinearEquiv b h) = ⇑(toLin b b M) := rfl

@[simp]
lemma toContinuousLinearEquiv_toLinearEquiv
  (b : Module.Basis ι F V) (M : Matrix ι ι F) (h : M.det ≠ 0) :
  (M.toContinuousLinearEquiv b h).toLinearEquiv = Matrix.toLinearEquiv b M (Ne.isUnit h) := rfl

@[simp]
lemma toContinousLinearEquiv_toMatrix
    (b : Module.Basis ι F V) (M : Matrix ι ι F) (h : M.det ≠ 0) :
    (M.toContinuousLinearEquiv b h ).toLinearMap.toMatrix b b = M := by
  exact (LinearEquiv.eq_symm_apply (LinearMap.toMatrix b b)).mp rfl

lemma toContinousLinearEquiv_prod
    (b : Module.Basis ι F V)
    (A : Matrix ι ι F) (hA : A.det ≠ 0) (B : Matrix ι ι F) (hB : B.det ≠ 0) :
    have h_ne : (A * B).det ≠ 0 := by
      rw[Matrix.det_mul ]; exact (mul_ne_zero_iff_right hB).mpr hA
    (A * B).toContinuousLinearEquiv b h_ne =
    (B.toContinuousLinearEquiv b hB).trans (A.toContinuousLinearEquiv b hA) := by
  ext x
  simp[ContinuousLinearEquiv.trans_apply, Matrix.toLin_mul b b]

lemma ContinuousLinearEquiv.toMatrix_toContinousLinearEquiv
    (b : Module.Basis ι F V) (ρ : V ≃L[F] V) :
    (ρ.toLinearEquiv.toMatrix b b).toContinuousLinearEquiv b
    (ContinuousLinearEquiv.toMatrix_det_ne_zero b ρ ) = ρ := by
  apply ContinuousLinearEquiv.ext
  simp[]

end Matrix

end ContinousLinearEquiv

section pi

variable {ι : Type*} {H : ι → Type*} [Π i, Group (H i)] [Π i, TopologicalSpace (H i)]
    [∀ i, IsTopologicalGroup (H i)] [∀ i, LocallyCompactSpace (H i)]
    [∀ i, MeasurableSpace (H i)] [∀ i, BorelSpace (H i)]

/-- A version of `mulEquivAddHaarChar_piCongrRight` that works under the ambient
  `[BorelSpace (Π i, H i)]` instance, avoiding instance mismatch problems. -/
@[to_additive]
lemma MeasureTheory.mulEquivHaarChar_piCongrRight' [Fintype ι] [MeasurableSpace (Π i, H i)]
    [BorelSpace (Π i, H i)] (ψ : Π i, (H i) ≃ₜ* (H i)) :
    mulEquivHaarChar (ContinuousMulEquiv.piCongrRight ψ) = ∏ i, mulEquivHaarChar (ψ i) := by
  borelize (Π i, (H i))
  exact mulEquivHaarChar_piCongrRight ψ

end pi

/-!
### Haar measure scaling lemmas
-/

section HaarMeasureScaling

namespace MeasureTheory

open Matrix Measure

variable {F : Type*} [Field F] [MeasurableSpace F] [TopologicalSpace F] [BorelSpace F]
  [IsTopologicalRing F] [LocallyCompactSpace F]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A diagonal matrix scales addHaar with its determinant
-/
lemma addEquivAddHaarChar_eq_ringHaarChar_det_diagonal
    [BorelSpace (ι → F)]
    (ρ : (ι → F) ≃L[F] (ι → F)) {D : ι → F}
    (h : ρ.toLinearMap.toMatrix' = Matrix.diagonal D) :
  addEquivAddHaarChar ρ.toContinuousAddEquiv
    = ringHaarChar ρ.toLinearEquiv.det := by
  classical
  -- 1) determinant computations
  let f := ρ.toLinearMap
  have f_eq : f = Matrix.toLin' (Matrix.diagonal D) := by
    rw [← h, Matrix.toLin'_toMatrix']
  have f_det: f.det = (∏ i, D i) := by
    simp only [f_eq, LinearMap.det_toLin', det_diagonal]
  have det_ne : f.det ≠ 0 := by
  -- we know det(ρ) is a unit, so nonzero
    have := LinearEquiv.coe_det ρ.toLinearEquiv
    simpa [this] using Units.ne_zero (ρ.toLinearEquiv.det)
  have prod_ne : (∏ i, D i) ≠ 0 := by
    -- det(diagonal D) = ∏ i, D i
    simp [← f_det, det_ne]
  have D_ne : ∀ i, D i ≠ 0 :=
    fun i => (Finset.prod_ne_zero_iff.mp prod_ne) i (by simp)
  have det_equiv :
      (↑(ρ.toLinearEquiv.det) : F) = ∏ i, D i := by
      have: ↑(ρ.toLinearEquiv.det) = f.det := LinearEquiv.coe_det ρ.toLinearEquiv
      simp [this, f_det]
  -- 2) identify ρ with coordinatewise scalings x ↦ (i ↦ D i * x i)
  have hρDi : ∀ (x : ι → F) (i : ι), ρ.toContinuousAddEquiv x i = D i * x i := by
    intro x i
    calc
      ρ.toContinuousAddEquiv x i = f x i := rfl
      _ = toLin' (diagonal D) x i := by rw [f_eq]
      _ = D i * x i := by exact mulVec_diagonal D x i
  -- 3) LHS: compute via `piCongrRight`
  let ψ : ι → ContinuousAddEquiv F F :=
    fun i => ContinuousAddEquiv.mulLeft (Units.mk0 (D i) (D_ne i))
  have h_pi :
      addEquivAddHaarChar ρ.toContinuousAddEquiv
        = ∏ i, ringHaarChar (Units.mk0 (D i) (D_ne i)) := by
    have : ρ.toContinuousAddEquiv = ContinuousAddEquiv.piCongrRight ψ := by
      ext x i; simp [ψ, hρDi x i]; rfl
    rw[this]
    exact MeasureTheory.addEquivAddHaarChar_piCongrRight' ψ
  -- 4) RHS: compute `ringHaarChar det ρ` as the same product
  have det_units :
      ρ.toLinearEquiv.det = Units.mk0 (∏ i, D i) prod_ne :=
      Units.val_inj.mp det_equiv
  have h_det :
      ringHaarChar ρ.toLinearEquiv.det
        = ∏ i, ringHaarChar (Units.mk0 (D i) (D_ne i)) := by
      have: Units.mk0 (∏ i, D i) prod_ne = ∏ i, Units.mk0 (D i) (D_ne i) := by ext; simp
      simp only [det_units, this, map_prod]
  -- 4) Conclude.
  exact h_pi.trans h_det.symm

/-- A transvection preserves addHaar on `ι → F`.
-/
lemma transvections_preserve_addHaar_pi [SecondCountableTopology F]
    (t : Matrix.TransvectionStruct ι F) :
    MeasurePreserving (⇑(Matrix.toLin' t.toMatrix)) addHaar addHaar := by
  -- Step 1: replace `addHaar` by the product Haar measure `μ`.
  --         By uniqueness of Haar measures, they differ by a scalar, and
  --         measure-preservation is unaffected by scaling.
  let μ := Measure.pi fun _ : ι => (addHaar : Measure F)
  suffices  MeasurePreserving (⇑(toLin' t.toMatrix)) μ μ by
    rw[isAddLeftInvariant_eq_smul_of_regular addHaar μ]
    apply MeasurePreserving.smul_measure this
  -- Step 2: prove invariance for the product Haar `μ`.
  --         This is the analogue of `Real.volume_preserving_transvectionStruct`.
  have hc: Continuous (toLin' t.toMatrix) := LinearMap.continuous_on_pi (toLin' t.toMatrix)
  have hm: Measurable (toLin' t.toMatrix) := hc.measurable
  refine ⟨hm, ?_⟩
  -- Step 3: reduce to checking the map preserves measure of rectangles.
  refine (pi_eq fun s hs ↦ ?_).symm
  have h2s : MeasurableSet (Set.univ.pi s) :=  MeasurableSet.univ_pi hs
  simp_rw [← pi_pi, ← lintegral_indicator_one h2s]
  rw [lintegral_map (measurable_one.indicator h2s) hm]
   -- Step 4: reduce further to the one-dimensional marginal on coordinate i.
  refine lintegral_eq_of_lmarginal_eq {t.i}
    ((measurable_one.indicator h2s).comp hm)
    (measurable_one.indicator h2s) ?_
  simp_rw [lmarginal_singleton]
  ext x
  -- Step 5: explicit computation for a transvection.
  -- On the j-th coordinate, the transvection acts as a translation,
  -- and Haar measure is invariant under translations.
  cases t with
  | mk i j hij c =>
    simp [transvection, single_mulVec, hij.symm, ← Function.update_add,
          lintegral_add_right_eq_self
            (fun xᵢ ↦ Set.indicator (Set.univ.pi s) 1 (Function.update x i xᵢ))]

/-- Haar measure scaling on `(ι → F)` for continuous linear equivalences generated by a matrix -/
lemma addEquivAddHaarChar_eq_ringHaarChar_det_matrix_pi [SecondCountableTopology F]
    (M : Matrix ι ι F) (hM : M.det ≠ 0) :
    let b := Pi.basisFun F ι
    let f := M.toContinuousLinearEquiv b hM
    addEquivAddHaarChar (f.toContinuousAddEquiv) = ringHaarChar f.toLinearEquiv.det := by
  classical
  intro b f
  let P : Matrix ι ι F → Prop :=
    fun A =>
      ∀ hA : A.det ≠ 0,
        addEquivAddHaarChar ( A.toContinuousLinearEquiv b hA).toContinuousAddEquiv
          = ringHaarChar (A.toContinuousLinearEquiv b hA).toLinearEquiv.det
  apply diagonal_transvection_induction_of_det_ne_zero P M hM
  · -- diagonal case
    intro D h_ne hA
    set ρ : (ι → F) ≃L[F] (ι → F) := (diagonal D).toContinuousLinearEquiv b  h_ne
    have hρ : ρ.toLinearMap.toMatrix' = diagonal D := by
      simp only[ρ]; exact toContinousLinearEquiv_toMatrix b (diagonal D) h_ne
    rw[addEquivAddHaarChar_eq_ringHaarChar_det_diagonal ρ hρ]
  · -- transvection case
    intro t hT
    let e := t.toMatrix.toContinuousLinearEquiv b hT
    have lhs_eq_one:
      addEquivAddHaarChar e.toContinuousAddEquiv = 1 := by
        have: ⇑e.toContinuousAddEquiv = ⇑(toLin' t.toMatrix) := by rfl
        simp [addEquivAddHaarChar, this, (transvections_preserve_addHaar_pi t).map_eq]
    have rhs_eq_one:
      ringHaarChar (LinearEquiv.det e.toLinearEquiv) = 1 := by
        simp [e, toContinuousLinearEquiv_toLinearEquiv, LinearEquiv.det_of_toLinarEquiv,
          TransvectionStruct.det t, Units.mk0_one, map_one MeasureTheory.ringHaarChar]
    rw [lhs_eq_one, rhs_eq_one]
  · -- product case
    intro A B hA hB IHA IHB hAB
    let Ae := A.toContinuousLinearEquiv b hA
    let Be := B.toContinuousLinearEquiv b hB
    set ABe := (A * B).toContinuousLinearEquiv b hAB
    have hCL : ABe = Be.trans Ae := toContinousLinearEquiv_prod b A hA B hB
    have hL :
        addEquivAddHaarChar ABe.toContinuousAddEquiv
          = addEquivAddHaarChar Be.toContinuousAddEquiv
          * addEquivAddHaarChar Ae.toContinuousAddEquiv := by
      simp[hCL, ContinuousLinearEquiv.toContinuousAddEquiv_trans,
            addEquivAddHaarChar_trans]
    have hR :
        ringHaarChar ABe.toLinearEquiv.det
        = ringHaarChar Ae.toLinearEquiv.det
        * ringHaarChar Be.toLinearEquiv.det := by
      simp[ABe, Ae, Be, LinearEquiv.det_of_toLinarEquiv]
    rw[hL, hR, IHA hA, IHB hB, CommMonoid.mul_comm]

/-- Haar measure scaling for linear maps on (ι → F) -/
lemma addEquivAddHaarChar_eq_ringHaarChar_det_pi [SecondCountableTopology F]
    (ρ : (ι → F) ≃L[F] (ι → F)) :
    addEquivAddHaarChar ρ.toContinuousAddEquiv = ringHaarChar ρ.toLinearEquiv.det := by
  let e := ρ.toLinearEquiv
  let b := Pi.basisFun F ι
  let M := e.toMatrix b b
  have h_ne : det M ≠ 0 := by simp [M,e, LinearEquiv.det_ne_zero]
  -- identify ρ with the matrix-induced equivalence
  have hρ : ρ = (M.toContinuousLinearEquiv b h_ne) :=
    (ContinuousLinearEquiv.toMatrix_toContinousLinearEquiv b ρ).symm
  rw [hρ]
  exact addEquivAddHaarChar_eq_ringHaarChar_det_matrix_pi M h_ne

variable {V : Type*} [AddCommGroup V] [TopologicalSpace V] [MeasurableSpace V] [BorelSpace V]
    [Module F V] [FiniteDimensional F V] [IsModuleTopology F V]
    [IsTopologicalAddGroup V]
    [LocallyCompactSpace V] -- this can be proved from the preceding hypos
                            -- but typeclass inference can't find it because it
                            -- can't find V

open Module

/-- Haar measure scaling for invertible linear maps on a finite-dimensional vector space
    over a field F assuming [SecondCountableTopology F] (FLT#517) -/
theorem addEquivAddHaarChar_eq_ringHaarChar_det
    (ρ : V ≃L[F] V) [SecondCountableTopology F] :
  addEquivAddHaarChar ρ.toContinuousAddEquiv
    = ringHaarChar ρ.toLinearEquiv.det := by
  classical
  let b  := finBasis F V
  let ι  := Fin (finrank F V)
  let e  : V ≃ₗ[F] ι → F := Basis.equivFun b
  have he : Continuous e := IsModuleTopology.continuous_of_linearMap e.toLinearMap
  have he_inv : Continuous e.symm := IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap
  let ec : V ≃L[F] (ι → F) := ⟨e, he, he_inv⟩
  let f  := ec.toContinuousAddEquiv
  let ρ' : (ι → F) ≃ₜ+ (ι → F) := (f.symm.trans (ρ.toContinuousAddEquiv)).trans f
  have hComm: ∀ x, f (ρ.toContinuousAddEquiv x) = ρ' (f x) := by
    simp [f, ρ', ContinuousAddEquiv.trans_apply, ContinuousAddEquiv.symm_apply_apply]
  let h_eq := addEquivAddHaarChar_eq_addEquivAddHaarChar_of_continuousAddEquiv f
                ρ.toContinuousAddEquiv ρ' hComm
  have: (ec.toContinuousAddEquiv.symm.trans
        ρ.toContinuousAddEquiv).trans ec.toContinuousAddEquiv =
        ((ec.symm.trans ρ).trans ec).toContinuousAddEquiv := by exact rfl
  simp[h_eq, ρ', f, this, addEquivAddHaarChar_eq_ringHaarChar_det_pi]

end MeasureTheory
end HaarMeasureScaling
