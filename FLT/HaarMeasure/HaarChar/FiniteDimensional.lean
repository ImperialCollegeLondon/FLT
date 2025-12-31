/-
Copyright (c) 2025 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Norbert Voelker
-/
import FLT.HaarMeasure.HaarChar.Ring
import FLT.Mathlib.Topology.Algebra.Module.Equiv
import FLT.Mathlib.LinearAlgebra.Determinant
import Mathlib.Topology.Algebra.Module.ModuleTopology
import FLT.Mathlib.Topology.Algebra.Module.Equiv

namespace MeasureTheory

open Measure

section HaarMeasureScaling

/-!

# Haar character scaling under linear automorphisms

We prove that a linear isomorphism on a finite-dimensional vector space
`V` over a locally compact field `F` scales Haar measure by its determinant. The
proof assumes `[SecondCountableTopology F]`.

We proceed by:
1. Proving the scaling property for diagonal matrices.
2. Showing that transvections preserve Haar measure.
3. Extending to arbitrary matrices using induction on diagonal/transvection decomposition.
4. Proving the result for automorphisms on `(ι → F)`
5. Deducing the general result for `V`

## Main result:

* `addEquivAddHaarChar_eq_ringHaarChar_det`

## TODO

* Review `[SecondCountableTopology F]` assumption
* Consider generalisation to commutative rings

-/

open Matrix Measure

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

variable {F : Type*} [MeasurableSpace F] [TopologicalSpace F]
    [BorelSpace F] [LocallyCompactSpace F]

section commring

variable [CommRing F] [IsTopologicalRing F]

/-- A diagonal matrix scales addHaar with its determinant
-/
lemma addEquivAddHaarChar_eq_ringHaarChar_det_diagonal [SecondCountableTopology F]
    (ρ : (ι → F) ≃L[F] (ι → F)) {D : ι → F}
    (h : ρ.toLinearMap.toMatrix' = Matrix.diagonal D) :
    addEquivAddHaarChar ρ.toContinuousAddEquiv = ringHaarChar ρ.toLinearEquiv.det := by
  -- 1) determinant computations
  let f := ρ.toLinearMap
  have f_eq : f = Matrix.toLin' (Matrix.diagonal D) := by
    rw [← h, Matrix.toLin'_toMatrix']
  have f_det : f.det = (∏ i, D i) := by
    simp only [f_eq, LinearMap.det_toLin', det_diagonal]
  have det_isUnit : IsUnit (f.det) := by
  -- we know det(ρ) is a unit, so nonzero
    exact LinearEquiv.isUnit_det' ρ.toLinearEquiv
  have prod_isUnit : IsUnit (∏ i, D i) := by
    -- det(diagonal D) = ∏ i, D i
    simp [← f_det, det_isUnit]
  have D_isUnit : ∀ i, IsUnit (D i) := by
    -- product of things is a unit => they're all units
    rwa [← IsUnit.prod_univ_iff]
  have det_equiv : (↑(ρ.toLinearEquiv.det) : F) = ∏ i, D i := by
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
    fun i => ContinuousAddEquiv.mulLeft (D_isUnit i).unit
  have h_pi :
      addEquivAddHaarChar ρ.toContinuousAddEquiv
        = ∏ i, ringHaarChar (D_isUnit i).unit := by
    have : ρ.toContinuousAddEquiv = ContinuousAddEquiv.piCongrRight ψ := by
      ext x i; simp only [ψ, hρDi x i]; rfl
    rw [this]
    exact addEquivAddHaarChar_piCongrRight ψ
  -- 4) RHS: compute `ringHaarChar det ρ` as the same product
  have det_units :
    ρ.toLinearEquiv.det = prod_isUnit.unit := Units.val_inj.mp det_equiv
  have h_det :
    ringHaarChar ρ.toLinearEquiv.det = ∏ i, ringHaarChar (D_isUnit i).unit := by
      have: prod_isUnit.unit = ∏ i, (D_isUnit i).unit := by ext; simp
      simp only [det_units, this, map_prod]
  -- 4) Conclude.
  exact h_pi.trans h_det.symm

/-- A transvection preserves addHaar on `ι → F`.
-/
lemma Matrix.TransvectionStruct.measurePreserving [SecondCountableTopology F]
    (t : Matrix.TransvectionStruct ι F) :
    MeasurePreserving (⇑(Matrix.toLin' t.toMatrix)) addHaar addHaar := by
  -- Step 1: replace `addHaar` by the product Haar measure `μ`.
  --         By uniqueness of Haar measures, they differ by a scalar, and
  --         measure-preservation is unaffected by scaling.
  let μ := Measure.pi fun _ : ι => (addHaar : Measure F)
  suffices MeasurePreserving (⇑(toLin' t.toMatrix)) μ μ by
    rw [isAddLeftInvariant_eq_smul_of_regular addHaar μ]
    apply MeasurePreserving.smul_measure this
  -- Step 2: prove invariance for the product Haar `μ`.
  --         This is the analogue of `Real.volume_preserving_transvectionStruct`.
  have hc: Continuous (toLin' t.toMatrix) := LinearMap.continuous_on_pi (toLin' t.toMatrix)
  have hm: Measurable (toLin' t.toMatrix) := hc.measurable
  refine ⟨hm, ?_⟩
  -- Step 3: reduce to checking the map preserves measure of rectangles.
  refine (pi_eq fun s hs ↦ ?_).symm
  have h2s : MeasurableSet (Set.univ.pi s) := MeasurableSet.univ_pi hs
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

end commring

section field

variable [Field F] [IsTopologicalRing F]

--#check Matrix.diagonal_transvection_induction_of_det_ne_zero -- needs field

/-- Haar measure scaling on `(ι → F)` for continuous linear equivalences generated by a matrix -/
lemma addEquivAddHaarChar_eq_ringHaarChar_det_matrix_pi [SecondCountableTopology F]
    (M : Matrix ι ι F) (h : IsUnit M.det) :
    let b := Pi.basisFun F ι
    let f := M.toContinuousLinearEquiv b h
    addEquivAddHaarChar (f.toContinuousAddEquiv) = ringHaarChar f.toLinearEquiv.det := by
  intro b f
  let P : Matrix ι ι F → Prop :=
    fun A =>
      ∀ hA : IsUnit A.det,
        addEquivAddHaarChar ( A.toContinuousLinearEquiv b hA).toContinuousAddEquiv
          = ringHaarChar (A.toContinuousLinearEquiv b hA).toLinearEquiv.det
  apply diagonal_transvection_induction_of_det_ne_zero P M h.ne_zero
  · -- diagonal case
    intro D h_ne hA
    set ρ : (ι → F) ≃L[F] (ι → F) := (diagonal D).toContinuousLinearEquiv b hA
    have hρ : ρ.toLinearMap.toMatrix' = diagonal D := by
      simp only[ρ]; exact toContinousLinearEquiv_toMatrix b (diagonal D) hA
    rw [addEquivAddHaarChar_eq_ringHaarChar_det_diagonal ρ hρ]
  · -- transvection case
    intro t hT
    let e := t.toMatrix.toContinuousLinearEquiv b hT
    have lhs_eq_one: addEquivAddHaarChar e.toContinuousAddEquiv = 1 := by
        have: ⇑e.toContinuousAddEquiv = ⇑(toLin' t.toMatrix) := by rfl
        simp [addEquivAddHaarChar, this, (Matrix.TransvectionStruct.measurePreserving t).map_eq]
    have rhs_eq_one: ringHaarChar (LinearEquiv.det e.toLinearEquiv) = 1 := by
        simp [e, toContinuousLinearEquiv_toLinearEquiv, LinearEquiv.det_toLinearEquiv,
          TransvectionStruct.det t, map_one MeasureTheory.ringHaarChar]
    rw [lhs_eq_one, rhs_eq_one]
  · -- product case
    intro A B hA hB IHA IHB hAB
    let hA' := isUnit_iff_ne_zero.mpr hA
    let hB' := isUnit_iff_ne_zero.mpr hB
    have hAB': hAB.unit = hA'.unit * hB'.unit := by ext; simp
    set Ae := A.toContinuousLinearEquiv b hA'
    set Be := B.toContinuousLinearEquiv b hB'
    set ABe := (A * B).toContinuousLinearEquiv b hAB
    have hCL : ABe = Be.trans Ae := toContinousLinearEquiv_mul b A hA' B hB'
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
      simp only [ABe, Ae, Be, toContinuousLinearEquiv_toLinearEquiv,
        LinearEquiv.det_toLinearEquiv, hAB',
        MulHomClass.map_mul ringHaarChar hA'.unit hB'.unit ]
    rw [hL, hR, IHA hA', IHB hB', CommMonoid.mul_comm]

omit [DecidableEq ι] in
/-- Haar measure scaling for linear maps on (ι → F) -/
lemma addEquivAddHaarChar_eq_ringHaarChar_det_pi [SecondCountableTopology F]
    (ρ : (ι → F) ≃L[F] (ι → F)) :
    addEquivAddHaarChar ρ.toContinuousAddEquiv = ringHaarChar ρ.toLinearEquiv.det := by
  classical
  let e := ρ.toLinearEquiv
  let b := Pi.basisFun F ι
  let M := e.toMatrix b b
  have hM : IsUnit M.det := by simp [M, e, LinearEquiv.det_ne_zero]
  -- identify ρ with the matrix-induced equivalence
  have hρ : ρ = (M.toContinuousLinearEquiv b hM) :=
    (ContinuousLinearEquiv.toMatrix_toContinousLinearEquiv b ρ).symm
  rw [hρ]
  exact addEquivAddHaarChar_eq_ringHaarChar_det_matrix_pi M hM

variable {V : Type*} [AddCommGroup V] [TopologicalSpace V] [MeasurableSpace V] [BorelSpace V]
    [Module F V] [FiniteDimensional F V] [IsModuleTopology F V]
    [IsTopologicalAddGroup V]
    [LocallyCompactSpace V] -- this can be proved from the preceding hypos
                            -- but typeclass inference can't find it because it
                            -- can't find V

open Module

/-- Haar measure scaling for invertible linear maps on a finite-dimensional vector space
over a field F assuming `[SecondCountableTopology F]`. -/
theorem addEquivAddHaarChar_eq_ringHaarChar_det [SecondCountableTopology F] (ρ : V ≃L[F] V) :
    addEquivAddHaarChar ρ.toContinuousAddEquiv = ringHaarChar ρ.toLinearEquiv.det := by
  let b := finBasis F V
  let ι := Fin (finrank F V)
  let e : V ≃ₗ[F] ι → F := Basis.equivFun b
  have he : Continuous e := IsModuleTopology.continuous_of_linearMap e.toLinearMap
  have he_inv : Continuous e.symm := IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap
  let ec : V ≃L[F] (ι → F) := ⟨e, he, he_inv⟩
  let f := ec.toContinuousAddEquiv
  let ρ' : (ι → F) ≃ₜ+ (ι → F) := (f.symm.trans (ρ.toContinuousAddEquiv)).trans f
  have hComm: ∀ x, f (ρ.toContinuousAddEquiv x) = ρ' (f x) := by
    simp [f, ρ', ContinuousAddEquiv.trans_apply, ContinuousAddEquiv.symm_apply_apply]
  let h_eq := addEquivAddHaarChar_eq_addEquivAddHaarChar_of_continuousAddEquiv f
    ρ.toContinuousAddEquiv ρ' hComm
  have : (ec.toContinuousAddEquiv.symm.trans
      ρ.toContinuousAddEquiv).trans ec.toContinuousAddEquiv =
      ((ec.symm.trans ρ).trans ec).toContinuousAddEquiv := rfl
  simp [h_eq, ρ', f, this, addEquivAddHaarChar_eq_ringHaarChar_det_pi]

end field

end HaarMeasureScaling

variable {F : Type*} [Field F] [MeasurableSpace F] [TopologicalSpace F] [BorelSpace F]
  [IsTopologicalRing F] [LocallyCompactSpace F]

section needs_PRing

variable (R : Type*) [CommSemiring R]

variable {A : Type*} [Ring A] [TopologicalSpace A] [IsTopologicalRing A]

variable [Algebra R A]

-- needs PRing
/--
Multiplication on the left by a unit of an F-algebra which is a topological
ring, is a continuous F-linear homeomorphism.
-/
def _root_.ContinuousLinearEquiv.mulLeft (u : Aˣ) : A ≃L[R] A where
  __ := LinearEquiv.mulLeft R u
  continuous_toFun := continuous_mul_left _
  continuous_invFun := continuous_mul_left _

-- needs PRing
/--
Multiplication on the right by a unit of an F-algebra which is a topological
ring, is a continuous F-linear homeomorphism.
-/
def _root_.ContinuousLinearEquiv.mulRight (u : Aˣ) : A ≃L[R] A where
  __ := LinearEquiv.mulRight R u
  continuous_toFun := continuous_mul_right _
  continuous_invFun := continuous_mul_right _

end needs_PRing

section ring

variable {A : Type*} [Ring A] [TopologicalSpace A]
    [Algebra F A] [FiniteDimensional F A] [IsModuleTopology F A]
    [IsTopologicalRing A] -- can be deduced from previous assumptions but only using F
    [LocallyCompactSpace A] -- can also be proved but only using F
    [MeasurableSpace A] [BorelSpace A]
    [SecondCountableTopology F]

variable (F) in
lemma algebra_ringHaarChar_eq_ringHaarChar_det (u : Aˣ) :
    ringHaarChar u = ringHaarChar (LinearEquiv.mulLeft F u).det :=
  addEquivAddHaarChar_eq_ringHaarChar_det (ContinuousLinearEquiv.mulLeft F u)

end ring

section issimplering

variable {D : Type*} [Ring D] [TopologicalSpace D]
    [Algebra F D] [FiniteDimensional F D] [IsSimpleRing D]
    [IsModuleTopology F D]
    [Algebra.IsCentral F D] -- could be removed if necessary by proving
    -- `IsSimpleRing.mulLeft_det_eq_mulRight_det` with tensoring over the center of `D`
    -- instead of `k`.
    [IsTopologicalRing D] -- can be deduced from previous assumptions but only using F
    [LocallyCompactSpace D] -- can also be proved but only using F
    [MeasurableSpace D] [BorelSpace D]
    [SecondCountableTopology F]

include F in
lemma _root_.IsSimpleRing.ringHaarChar_eq_addEquivAddHaarChar_mulRight (u : Dˣ) :
    ringHaarChar u = addEquivAddHaarChar (ContinuousAddEquiv.mulRight u) := by
  rw [algebra_ringHaarChar_eq_ringHaarChar_det F u]
  rw [IsSimpleRing.mulLeft_det_eq_mulRight_det']
  symm
  exact addEquivAddHaarChar_eq_ringHaarChar_det (ContinuousLinearEquiv.mulRight F u)

end issimplering

end MeasureTheory
