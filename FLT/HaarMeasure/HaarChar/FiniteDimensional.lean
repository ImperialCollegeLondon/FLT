import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.Haar.Unique

import FLT.HaarMeasure.HaarChar.Ring
import FLT.Mathlib.Topology.Algebra.Module.Equiv
import FLT.Mathlib.LinearAlgebra.Determinant
import Mathlib.Topology.Algebra.Module.ModuleTopology

-- TODO: split off material that belongs to other files
-- TODO: review definition of `toContinousLinearEquiv'`
-- TODO: review `SecondCountableTopology` assumption

section LinearEquiv

variable {F : Type*} [Field F]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma LinearEquiv.det_of_toLinarEquiv' {M : Matrix ι ι F} (h : M.det ≠ 0) :
    LinearEquiv.det (M.toLinearEquiv' (M.invertibleOfIsUnitDet (Ne.isUnit h))) =
      Units.mk0 M.det h := by
  refine Units.val_inj.mp ?_
  simp [LinearEquiv.coe_det, Units.val_mk0]

end LinearEquiv

section ContinousLinearEquiv

lemma ContinuousLinearEquiv.toContinuousAddEquiv_trans
    {R : Type*} {E : Type*} [Semiring R] [AddCommMonoid E] [Module R E]
    [TopologicalSpace E] [AddGroup E] [IsTopologicalAddGroup E] {e f : E ≃L[R] E} :
    (e.trans f).toContinuousAddEquiv = e.toContinuousAddEquiv.trans f.toContinuousAddEquiv := rfl

end ContinousLinearEquiv

section toContinousLinearEquiv'

variable {F : Type*} [Field F] [TopologicalSpace F]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable [IsModuleTopology F (ι → F)] [ContinuousAdd (ι → F)]

namespace Matrix

noncomputable def toContinuousLinearEquiv'
   (M : Matrix ι ι F) (h : M.det ≠ 0) : (ι → F) ≃L[F] (ι → F) :=
  have: Invertible M := Matrix.invertibleOfIsUnitDet M (Ne.isUnit h)
  let e := Matrix.toLinearEquiv' M this
  have ce : Continuous e :=
    IsModuleTopology.continuous_of_linearMap e.toLinearMap
  have ce_inv : Continuous e.symm :=
    IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap
  ⟨e, ce, ce_inv⟩

@[simp]
lemma toContinousLinearEquiv'_apply
    (M : Matrix ι ι F) (h : M.det ≠ 0) (x : ι → F) :
     (M.toContinuousLinearEquiv' h) x = toLin' M x := rfl

@[simp]
lemma toContinuousLinearEquiv'_toLin'_coe
    (M : Matrix ι ι F) (h : M.det ≠ 0) : ⇑(M.toContinuousLinearEquiv' h) = ⇑(toLin' M) := rfl

lemma toContinuousLinearEquiv'_toLinearEquiv (M : Matrix ι ι F) (h : M.det ≠ 0) :
    (M.toContinuousLinearEquiv' h).toLinearEquiv =
    Matrix.toLinearEquiv' M (Matrix.invertibleOfIsUnitDet M (Ne.isUnit h)) := rfl

@[simp]
lemma toContinousLinearEquiv'_toMatrix' (M : Matrix ι ι F) (h : M.det ≠ 0) :
    (M.toContinuousLinearEquiv' h ).toLinearMap.toMatrix' = M := by
  exact (LinearEquiv.eq_symm_apply LinearMap.toMatrix').mp rfl

lemma toContinousLinearEquiv'_prod
    (A : Matrix ι ι F) (hA : A.det ≠ 0) (B : Matrix ι ι F) (hB : B.det ≠ 0) :
    have h_ne : (A * B).det ≠ 0 := by
        rw[Matrix.det_mul ]; exact (mul_ne_zero_iff_right hB).mpr hA
    (A * B).toContinuousLinearEquiv' h_ne =
    (B.toContinuousLinearEquiv' hB).trans (A.toContinuousLinearEquiv' hA) := by
  ext x
  simp[ContinuousLinearEquiv.trans_apply, Matrix.toLin'_mul]

end Matrix

lemma ContinuousLinearEquiv.toMatrix'_toContinousLinearEquiv' (ρ : (ι → F) ≃L[F] (ι → F))
    (h_ne : ρ.toLinearEquiv.toMatrix'.det ≠ 0) :
    (ρ.toLinearEquiv.toMatrix').toContinuousLinearEquiv' h_ne = ρ := by
   ext; simp []

end toContinousLinearEquiv'

namespace MeasureTheory

section pi

variable {ι : Type*} {H : ι → Type*} [Π i, Group (H i)] [Π i, TopologicalSpace (H i)]
    [∀ i, IsTopologicalGroup (H i)] [∀ i, LocallyCompactSpace (H i)]
    [∀ i, MeasurableSpace (H i)] [∀ i, BorelSpace (H i)]

open Classical ContinuousMulEquiv MeasureTheory in

/-- Variation of mulEquivHaarChar_piCongrRight -/
@[to_additive]
lemma mulEquivHaarChar_piCongrRight' [Fintype ι] [MeasurableSpace (Π i, H i)]
    [BorelSpace (Π i, H i)] (ψ : Π i, (H i) ≃ₜ* (H i)) :
    mulEquivHaarChar (ContinuousMulEquiv.piCongrRight ψ) = ∏ i, mulEquivHaarChar (ψ i) := by
  borelize (Π i, (H i))
  exact mulEquivHaarChar_piCongrRight ψ

end pi

variable {F : Type*} [Field F] [MeasurableSpace F] [TopologicalSpace F] [BorelSpace F]
  [IsTopologicalRing F] [LocallyCompactSpace F]

section addequiv

open Matrix MeasureTheory Measure

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- ringHaarChar computation of the determinant of a diagonal matrix -/
lemma ringHaarChar_diagonal_matrix {D : ι → F} (h : ∀ i, D i ≠ 0) (hd : (diagonal D).det ≠ 0) :
    ringHaarChar (Units.mk0 (diagonal D).det hd) = ∏ i, ringHaarChar (Units.mk0 (D i) (h i)) := by
  have hp : ∏ i, D i ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => h i
  have hu: Units.mk0 (diagonal D).det hd = Units.mk0 (∏ i, D i) hp := by simp [det_diagonal]
  have: Units.mk0 (∏ i, D i) hp = ∏ i, Units.mk0 (D i) (h i) := by ext; simp
  rw [hu, this, map_prod]

/-- Haar measure scaling on (ι → F) (diagonal matrix) -/
lemma addEquivAddHaarChar_eq_ringHaarChar_det_diagonal [BorelSpace (ι → F)]
    (ρ : (ι → F) ≃L[F] (ι → F)) {D : ι → F}
    (h : ρ.toLinearMap.toMatrix' = diagonal D) :
    addEquivAddHaarChar ρ.toContinuousAddEquiv = ringHaarChar ρ.toLinearEquiv.det := by
  let f := ρ.toLinearMap
  have h0: ↑(ρ.toLinearEquiv.det) = f.det := LinearEquiv.coe_det ρ.toLinearEquiv
  -- determinants and elements of the diagonal
  have det_f : f.det = ∏ i, D i := by rw [← LinearMap.det_toMatrix', h, det_diagonal]
  have det_ne : f.det ≠ 0 := by rw [← h0]; exact Units.ne_zero (ρ.toLinearEquiv.det)
  have det_eq : ρ.toLinearEquiv.det = Units.mk0 f.det det_ne := Units.val_inj.mp h0
  have prod_ne : ∏ i, D i ≠ 0 := by rw[← det_f]; exact det_ne
  have D_ne : ∀ i, D i ≠ 0 := by intro i; apply Finset.prod_ne_zero_iff.mp prod_ne; simp
  -- relate determinants to the diagonal matrix itself
  have diag_det_ne : (diagonal D).det ≠ 0 := by
    rw[← h, LinearMap.det_toMatrix', det_f]; exact prod_ne
  have det_match : ρ.toLinearEquiv.det = Units.mk0 (diagonal D).det diag_det_ne := by
    refine Units.val_inj.mp ?_; simp [det_eq, det_f]
  -- express ρ as a product of coordinatewise scalings
  have f_eq : f = toLin' (diagonal D) := by rw [← h, Matrix.toLin'_toMatrix']
  have hρDi : ∀ (x : ι → F) (i : ι), ρ.toContinuousAddEquiv x i = D i * x i := by
    intro x i; calc
      ρ.toContinuousAddEquiv x i = f x i := rfl
      _ = toLin' (diagonal D) x i := by rw [f_eq]
      _ = D i * x i := by exact mulVec_diagonal D x i
  let ψ := fun i ↦ ContinuousAddEquiv.mulLeft (Units.mk0 (D i) (D_ne i))
  have : ρ.toContinuousAddEquiv = ContinuousAddEquiv.piCongrRight ψ := by
    ext x i; simp only [ψ, hρDi]; rfl
  rw [det_match, ringHaarChar_diagonal_matrix D_ne diag_det_ne,
      this, addEquivAddHaarChar_piCongrRight' ψ]
  rfl

/-- A transvection preserves the product of addHaar on `ι → F`. The proof is
      a transcription of the proof of theorem volume_preserving_transvectionStruct.
-/
lemma transvections_preserve_addHaar_pi_product_measure
  [SigmaCompactSpace F] [BorelSpace (ι → F)] (t : Matrix.TransvectionStruct ι F) :
    MeasurePreserving (⇑(Matrix.toLin' t.toMatrix))
      (Measure.pi fun _ : ι => addHaar) (Measure.pi fun _ : ι => addHaar) := by
  have hc: Continuous (toLin' t.toMatrix) := LinearMap.continuous_on_pi (toLin' t.toMatrix)
  have hm: Measurable (toLin' t.toMatrix) := hc.measurable
  refine ⟨hm, ?_⟩
  refine (pi_eq fun s hs ↦ ?_).symm
  have h2s : MeasurableSet (Set.univ.pi s) :=  MeasurableSet.univ_pi hs
  simp_rw [← pi_pi, ← lintegral_indicator_one h2s]
  rw [lintegral_map (measurable_one.indicator h2s) hm]
  refine lintegral_eq_of_lmarginal_eq {t.i}
    ((measurable_one.indicator h2s).comp hm)
    (measurable_one.indicator h2s) ?_
  simp_rw [lmarginal_singleton]
  ext x
  cases t with
  | mk i j hij c =>
    -- the key: on the j–th coordinate the map is a translation
    simp [transvection, single_mulVec, hij.symm, ← Function.update_add,
          lintegral_add_right_eq_self
            (fun xᵢ ↦ Set.indicator (Set.univ.pi s) 1 (Function.update x i xᵢ))]

/-- Corresponding theorem for addHaar -/
lemma transvections_preserve_addHaar_pi [SecondCountableTopology F]
    (t : Matrix.TransvectionStruct ι F) :
    MeasurePreserving (⇑(Matrix.toLin' t.toMatrix)) addHaar addHaar := by
  let μ := Measure.pi fun _ : ι => (addHaar : Measure F)
  rw[ isAddLeftInvariant_eq_smul_of_regular addHaar μ]
  apply MeasurePreserving.smul_measure (transvections_preserve_addHaar_pi_product_measure t)

/-- Haar measure scaling on (ι → F) for continuous linear equivalences generated by a matrix -/
lemma addEquivAddHaarChar_eq_ringHaarChar_det_matrix_pi [SecondCountableTopology F]
    (M : Matrix ι ι F) (hM : M.det ≠ 0) :
    let f := M.toContinuousLinearEquiv' hM
    addEquivAddHaarChar (f.toContinuousAddEquiv) = ringHaarChar f.toLinearEquiv.det := by
  let P : Matrix ι ι F → Prop :=
    fun A =>
      ∀ hA : A.det ≠ 0,
        addEquivAddHaarChar ( A.toContinuousLinearEquiv' hA).toContinuousAddEquiv
          = ringHaarChar (A.toContinuousLinearEquiv' hA).toLinearEquiv.det
  apply diagonal_transvection_induction_of_det_ne_zero P M hM
  any_goals (simp only [P])
  · intro D h_ne hA
    set ρ : (ι → F) ≃L[F] (ι → F) := (diagonal D).toContinuousLinearEquiv'  h_ne
    have hρ : ρ.toLinearMap.toMatrix' = diagonal D := by
      simp only[ρ]; exact toContinousLinearEquiv'_toMatrix' (diagonal D) h_ne
    rw[addEquivAddHaarChar_eq_ringHaarChar_det_diagonal ρ hρ]
  · intro t hT
    have lhs_eq_one:
      addEquivAddHaarChar (t.toMatrix.toContinuousLinearEquiv' hT).toContinuousAddEquiv = 1 := by
      have: ⇑(t.toMatrix.toContinuousLinearEquiv' hT).toContinuousAddEquiv =
         ⇑(toLin' t.toMatrix) := by rfl
      simp_rw [addEquivAddHaarChar, this, (transvections_preserve_addHaar_pi t).map_eq]
      exact addHaarScalarFactor_self addHaar
    have rhs_eq_one:
      ringHaarChar (LinearEquiv.det
        (t.toMatrix.toContinuousLinearEquiv' hT).toLinearEquiv) = 1 := by
      simp_rw [ toContinuousLinearEquiv'_toLinearEquiv]
      rw[LinearEquiv.det_of_toLinarEquiv' hT]
      simp only [TransvectionStruct.det t]
      rw[Units.mk0_one, map_one MeasureTheory.ringHaarChar]
    rw[lhs_eq_one, rhs_eq_one]
  · intro A B hA hB IHA IHB h_ne
    have hdet : (A * B).det = A.det * B.det := Matrix.det_mul _ _
    have h_ne' : A.det * B.det ≠ 0 := by exact (mul_ne_zero_iff_right hB).mpr hA
    have ring_mul :
      ringHaarChar (Units.mk0 (A.det * B.det) h_ne') =
        ringHaarChar (Units.mk0 A.det hA) * ringHaarChar (Units.mk0 B.det hB) := by
      simp [Units.mk0_mul]
    have det_trans :
      LinearEquiv.det ((B.toContinuousLinearEquiv' hB).trans
        (A.toContinuousLinearEquiv' hA)).toLinearEquiv = Units.mk0 (A.det * B.det) h_ne' := by
        simp[toContinuousLinearEquiv'_toLinearEquiv, LinearEquiv.det_of_toLinarEquiv' hA,
            LinearEquiv.det_of_toLinarEquiv' hB]
    rw[toContinousLinearEquiv'_prod A hA B hB]
    rw[ContinuousLinearEquiv.toContinuousAddEquiv_trans]
    rw[addEquivAddHaarChar_trans, IHA hA, IHB hB]
    rw[det_trans, ring_mul]
    rw[Matrix.toContinuousLinearEquiv'_toLinearEquiv, LinearEquiv.det_of_toLinarEquiv' hB]
    rw[Matrix.toContinuousLinearEquiv'_toLinearEquiv, LinearEquiv.det_of_toLinarEquiv' hA]
    exact
      CommMonoid.mul_comm
        (ringHaarChar (Units.mk0 B.det hB))
        (ringHaarChar (Units.mk0 A.det hA))

/-- Haar measure scaling for linear maps on (ι → F) -/
lemma addEquivAddHaarChar_eq_ringHaarChar_det_pi [SecondCountableTopology F]
    (ρ : (ι → F) ≃L[F] (ι → F)) :
    addEquivAddHaarChar ρ.toContinuousAddEquiv = ringHaarChar ρ.toLinearEquiv.det := by
  let e := ρ.toLinearEquiv
  let M := e.toMatrix'
  have: LinearEquiv.det e = det M := by
    simp only [M, LinearMap.det_toMatrix']; exact LinearEquiv.coe_det e
  have h_ne : det M ≠ 0 := by
    rw[← this, ← isUnit_iff_ne_zero]; exact Units.isUnit (LinearEquiv.det e)
  rw[← ContinuousLinearEquiv.toMatrix'_toContinousLinearEquiv' ρ h_ne]
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
theorem addEquivAddHaarChar_eq_ringHaarChar_det (ρ : V ≃L[F] V) [SecondCountableTopology F] :
    addEquivAddHaarChar ρ.toContinuousAddEquiv = ringHaarChar ρ.toLinearEquiv.det := by
  let b := finBasis F V
  let ι := Fin (finrank F V)
  let e : V ≃ₗ[F] ι → F := Basis.equivFun b
  have he: Continuous e :=
    IsModuleTopology.continuous_of_linearMap e.toLinearMap
  have he_inv : Continuous e.symm :=
    IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap
  let ec : V ≃L[F] (ι → F) := ⟨e, he, he_inv⟩
  let f := ec.toContinuousAddEquiv
  let ρ' : (ι → F) ≃ₜ+ (ι → F) := (f.symm.trans (ρ.toContinuousAddEquiv)).trans f
  have hComm: ∀ x, f (ρ.toContinuousAddEquiv x) = ρ' (f x) := by
    simp [f, ρ', ContinuousAddEquiv.trans_apply, ContinuousAddEquiv.symm_apply_apply]
  let h_eq := addEquivAddHaarChar_eq_addEquivAddHaarChar_of_continuousAddEquiv f
                ρ.toContinuousAddEquiv ρ' hComm
  have: (ec.toContinuousAddEquiv.symm.trans
        ρ.toContinuousAddEquiv).trans ec.toContinuousAddEquiv =
        ((ec.symm.trans ρ).trans ec).toContinuousAddEquiv := by exact rfl
  simp[h_eq, ρ', f, this, addEquivAddHaarChar_eq_ringHaarChar_det_pi]

end addequiv

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

variable (F) in
lemma algebra_ringHaarChar_eq_ringHaarChar_det [SecondCountableTopology F] (u : Aˣ) :
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

include F in
lemma _root_.IsSimpleRing.ringHaarChar_eq_addEquivAddHaarChar_mulRight [SecondCountableTopology F]
  (u : Dˣ) :
    ringHaarChar u = addEquivAddHaarChar (ContinuousAddEquiv.mulRight u) := by
  rw [algebra_ringHaarChar_eq_ringHaarChar_det F u]
  rw [IsSimpleRing.mulLeft_det_eq_mulRight_det']
  symm
  exact addEquivAddHaarChar_eq_ringHaarChar_det (ContinuousLinearEquiv.mulRight F u)

end issimplering

end MeasureTheory
