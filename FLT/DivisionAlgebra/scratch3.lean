import FLT.HaarMeasure.HaarChar.Ring
import Mathlib

variable (R : Type*) [Ring R] [Nontrivial R] [Algebra ℝ R] [Module.Finite ℝ R] [Module.Free ℝ R]
  [TopologicalSpace R] [IsModuleTopology ℝ R]
-- Want algebra not module for the smul later...

def basis_non_zero_in_one : ∃ i, (Module.finBasis ℝ R).coord i 1 ≠ 0 := by
  by_contra t
  have h : ∀ x, ((Module.finBasis ℝ R).coord x) 0 = 0 := by
    exact fun x ↦ LinearMap.map_zero ((Module.finBasis ℝ R).coord x)
  simp only [Module.Basis.coord_apply, ne_eq, not_exists, Decidable.not_not] at t h
  have w : ∀ a b, (∀ x, ((Module.finBasis ℝ R).coord x) a = ((Module.finBasis ℝ R).coord x) b) →
      (a = b) := by
    intro a b
    exact (Module.Basis.ext_elem_iff (Module.finBasis ℝ R)).mpr
  specialize w 1 0
  have : ∀ x, ((Module.finBasis ℝ R).coord x) 1 = ((Module.finBasis ℝ R).coord x) 0 := by
    intro x
    simp only [Module.Basis.coord_apply, map_zero]
    exact t x
  apply w at this
  contrapose this
  have : (1 : R) ≠ 0 := by
    exact one_ne_zero
  exact this

omit [Nontrivial R] [TopologicalSpace R] [IsModuleTopology ℝ R] in
lemma ex : ∃ a : R, ∑ x, (Module.finBasis ℝ R) x = a := exists_eq'

-- need to work on how to show this is a basis... (in Lean, done on paper)

def basis_map : Module.Basis (Fin (Module.finrank ℝ R)) ℝ R →
    Module.Basis (Fin (Module.finrank ℝ R)) ℝ R :=
    sorry
  /-
  fun a (i : (Fin (Module.finrank ℝ R))) => if
    (i : (Fin (Module.finrank ℝ R))).val = Classical.choose (basis_non_zero_in_one R) then a i =
    a i - ((Classical.choose (ex R)) + 1)
                                            else a i = a i
                                          -/

lemma basis_existance' : ∃ b : Module.Basis (Fin (Module.finrank ℝ R)) ℝ R, ∑ x, b x = 1 := by

  -- use basis_map R (Module.finBasis ℝ R)

  sorry

lemma basis_existance : ∃ b : Module.Basis (Fin (Module.finrank ℝ R)) ℝ R,
    ∑ x, b x = 1 := by
  have : ∃ a : R, ∑ x, (Module.finBasis ℝ R) x = a := by
    simp only [exists_eq']
  -- now just want to argue that we can manipulate this basis
  -- definitely will need that Module.finrank ℝ R is not 0... else we have an empty(?) basis.
  sorry

noncomputable
abbrev iso : R ≃ₗ[ℝ] (Fin (Module.finrank ℝ R) → ℝ) := by
  exact Module.Basis.equivFun
    (ι := Fin (Module.finrank ℝ R)) (R := ℝ) (M := R) (Classical.choose (basis_existance R))

-- I think the maps will be continuous need to explicitely check

local instance : TopologicalSpace (Fin (Module.finrank ℝ R) → ℝ) := by
  exact Pi.topologicalSpace

local instance : IsModuleTopology ℝ (Fin (Module.finrank ℝ R) → ℝ) := by
  exact IsModuleTopology.instPi

noncomputable
abbrev iso' : R ≃ₜ+ (Fin (Module.finrank ℝ R) → ℝ) where
  toFun := iso R
  invFun := (iso R).symm
  map_add' := fun x y ↦ LinearEquiv.map_add (iso R) x y
  left_inv _ := LinearEquiv.symm_apply_apply _ _
  right_inv _ := LinearEquiv.apply_symm_apply _ _
  continuous_toFun := IsModuleTopology.continuous_of_linearMap _
  continuous_invFun := by
    convert IsModuleTopology.continuous_of_linearMap _
    all_goals try infer_instance
    exact IsModuleTopology.toContinuousAdd ℝ R

variable [IsTopologicalRing R] [LocallyCompactSpace R] [MeasurableSpace R] [BorelSpace R]

lemma ringHaarChar_eq1' (y : (Fin (Module.finrank ℝ R) → ℝ)ˣ)
    (hy : ∃ a : ℝ, y.val = algebraMap ℝ (Fin (Module.finrank ℝ R) → ℝ) a)
    (hy' : IsUnit ((iso R).symm y)) :
    MeasureTheory.ringHaarChar y = MeasureTheory.ringHaarChar (IsUnit.unit hy') := by
  apply MeasureTheory.addEquivAddHaarChar_eq_addEquivAddHaarChar_of_continuousAddEquiv
    (iso' R).symm
  intro x
  simp only [ContinuousAddEquiv.mulLeft_apply, IsUnit.unit_spec]
  have h1 : (iso' R).symm x = ∑ j, x j • (Classical.choose (basis_existance R)) j :=
    Module.Basis.equivFun_symm_apply _ _
    -- need to fix imports, as this should just be immediate
  have h2 : (iso' R).symm (↑y * x) =
      ∑ j, (↑y * x) j • (Classical.choose (basis_existance R)) j :=
    Module.Basis.equivFun_symm_apply _ _
  rw [h1, h2, Module.Basis.equivFun_symm_apply]
  obtain ⟨a, ha⟩ := hy
  simp_rw [ha, Pi.mul_apply, Pi.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
  have : a • (∑ x, (Classical.choose (basis_existance R)) x) =
      (∑ x, a • (Classical.choose (basis_existance R)) x) := Finset.smul_sum
  simp only [← this, Algebra.smul_mul_assoc, Classical.choose_spec (basis_existance R), one_mul,
    Finset.smul_sum, ← IsScalarTower.smul_assoc, smul_eq_mul]
