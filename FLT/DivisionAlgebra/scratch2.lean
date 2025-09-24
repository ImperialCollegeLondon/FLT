import FLT.HaarMeasure.HaarChar.Ring

variable (R : Type*) [Ring R] [Module ℝ R] [Module.Finite ℝ R]
  [Module.Free ℝ R]

local instance : TopologicalSpace R :=
  moduleTopology ℝ R

noncomputable
abbrev iso : R ≃ₗ[ℝ] (Fin (Module.finrank ℝ R) → ℝ) := by
  exact Module.Basis.equivFun
    (ι := Fin (Module.finrank ℝ R)) (R := ℝ) (M := R) (Module.finBasis ℝ R)

-- I think the maps will be continuous need to explicitely check

noncomputable
abbrev iso' : R ≃ₜ+ (Fin (Module.finrank ℝ R) → ℝ) where
  toFun := iso R
  invFun := (iso R).symm
  map_add' := by
    exact fun x y ↦ LinearEquiv.map_add (iso R) x y
  left_inv a := by
    exact LinearEquiv.symm_apply_apply (iso R) a
  right_inv a := by
    exact LinearEquiv.apply_symm_apply (iso R) a
  continuous_toFun := by

    sorry
  continuous_invFun := by

    sorry

local instance : IsTopologicalRing (Fin (Module.finrank ℝ R) →  ℝ) := by

  sorry


local instance : LocallyCompactSpace (Fin (Module.finrank ℝ R) → ℝ) := by

  sorry

local instance : BorelSpace (Fin (Module.finrank ℝ R) → ℝ) := by

  sorry

local instance : Algebra ℝ R := by -- this is basically what I need for the end of the proof
  refine Algebra.ofModule' ?_ ?_
  · intro r x

    sorry
  · intro r x

    sorry

variable [IsTopologicalRing R] [LocallyCompactSpace R] [MeasurableSpace R] [BorelSpace R]

lemma ringHaarChar_eq1' (y : (Fin (Module.finrank ℝ R) → ℝ)ˣ)
    (hy : ∃ a : ℝ, y.val = algebraMap ℝ (Fin (Module.finrank ℝ R) → ℝ) a)
    (hy' : IsUnit ((iso R).symm y)) :
    MeasureTheory.ringHaarChar y = MeasureTheory.ringHaarChar (R := R) (IsUnit.unit hy') := by
  apply MeasureTheory.addEquivAddHaarChar_eq_addEquivAddHaarChar_of_continuousAddEquiv
    (iso' R).symm
  intro x
  simp only [ContinuousAddEquiv.mulLeft_apply, IsUnit.unit_spec]
  have : (iso' R).symm x = ∑j, x j • (Module.finBasis ℝ R) j := by
    exact Module.Basis.equivFun_symm_apply ((Module.finBasis ℝ R)) x
    -- I should be importing this file so that it works :/ but Kevins Mathlib is fucked
  rw [this]
  simp only [Module.Basis.equivFun_symm_apply]
  refine (ContinuousAddEquiv.symm_apply_eq (iso' R)).mpr ?_
  simp only [ContinuousAddEquiv.coe_mk, AddEquiv.coe_mk, Equiv.coe_fn_mk,
    Module.Basis.equivFun_apply]
  ext i
  obtain ⟨a, ha⟩ := hy
  simp_rw [ha]
  simp only [Pi.mul_apply] -- why is it not likeing tho simplify with the algebra instance??

  sorry
