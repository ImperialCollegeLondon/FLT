import FLT.HaarMeasure.HaarChar.Ring

variable (R : Type*) [Ring R] [Algebra ℝ R] [Module.Finite ℝ R] [Module.Free ℝ R]

-- Want algebra not module for the smul later...

local instance : TopologicalSpace R :=
  moduleTopology ℝ R

def basis_map : Module.Basis (Fin (Module.finrank ℝ R)) ℝ R →
    Module.Basis (Fin (Module.finrank ℝ R)) ℝ R :=
  fun a (i : (Fin (Module.finrank ℝ R))) => if
    (i : (Fin (Module.finrank ℝ R))).val = 0 then a i =
    a i - ((Classical.choose ((∃ a : R, ∑ x, (Module.finBasis ℝ R) x = a) (by simp only [exists_eq']))) + 1)
                                            else a i = a i

lemma basis_existance' (h : Module.finrank ℝ R > 0) :
    ∃ b : Module.Basis (Fin (Module.finrank ℝ R)) ℝ R, ∑ x, b x = 1 := by
  have : ∃ a : R, ∑ x, (Module.finBasis ℝ R) x = a := by
    simp only [exists_eq']

  -- now just want to argue that we can manipulate this basis
  -- definitely will need that Module.finrank ℝ R is not 0... else we have an empty(?) basis.

  -- Is this possible... a is sum of some basis elements, then replace one of its constituent parts
  -- with
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

variable [IsTopologicalRing R] [LocallyCompactSpace R] [MeasurableSpace R] [BorelSpace R]

lemma ringHaarChar_eq1' (y : (Fin (Module.finrank ℝ R) → ℝ)ˣ)
    (hy : ∃ a : ℝ, y.val = algebraMap ℝ (Fin (Module.finrank ℝ R) → ℝ) a)
    (hy' : IsUnit ((iso R).symm y)) :
    MeasureTheory.ringHaarChar y = MeasureTheory.ringHaarChar (R := R) (IsUnit.unit hy') := by
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
