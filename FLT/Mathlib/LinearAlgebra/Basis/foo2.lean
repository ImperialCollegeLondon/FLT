import Mathlib
import FLT.HaarMeasure.HaarChar.Ring

variable (T R : Type*) [Field T] [Ring R] [Algebra T R] [Module.Finite T R]
    [TopologicalSpace T] [TopologicalSpace R] [IsTopologicalRing R] [IsModuleTopology T R]
    [LocallyCompactSpace R] [MeasurableSpace R] [BorelSpace R]
    [IsTopologicalRing T] [LocallyCompactSpace T]
    (t : Tˣ)

/-- This is still the homeomorphism I constructed. But I think this should be fine. -/
noncomputable
abbrev Module.Basis.equivFun_homeo :
    R ≃ₜ+ (Fin (Module.finrank T R) → T) where
  toFun := Module.Basis.equivFun (Module.finBasisOfFinrankEq T R (rfl))
  invFun := (Module.Basis.equivFun (Module.finBasisOfFinrankEq T R (rfl))).symm
  map_add' _ _ := LinearEquiv.map_add _ _ _
  left_inv _ := LinearEquiv.symm_apply_apply _ _
  right_inv _ := LinearEquiv.apply_symm_apply _ _
  continuous_toFun := by
    convert IsModuleTopology.continuous_of_linearMap _
    all_goals infer_instance
  continuous_invFun := by
    convert IsModuleTopology.continuous_of_linearMap _
    all_goals try infer_instance

instance : MeasurableSpace (Fin (Module.finrank T R) → T) := by
  exact borel (Fin (Module.finrank T R) → T)

instance : BorelSpace (Fin (Module.finrank T R) → T) := by
  exact { measurable_eq := rfl }

theorem foo_ext1 :
    MeasureTheory.ringHaarChar (Units.map (algebraMap T R).toMonoidHom t) =
    MeasureTheory.ringHaarChar (R := (Fin (Module.finrank T R) → T))
      (Units.map (algebraMap T (Fin (Module.finrank T R) → T)).toMonoidHom t) := by
  apply MeasureTheory.addEquivAddHaarChar_eq_addEquivAddHaarChar_of_continuousAddEquiv
    (Module.Basis.equivFun_homeo T R)
  intro x
  simp only [RingHom.toMonoidHom_eq_coe, ContinuousAddEquiv.mulLeft_apply, Units.coe_map,
    MonoidHom.coe_coe, ContinuousAddEquiv.coe_mk, AddEquiv.coe_mk, Equiv.coe_fn_mk,
    Module.Basis.equivFun_apply]
  ext i
  simp only [Pi.mul_apply, Pi.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
    Module.Basis.repr_smul']

-- turned out to be much easier... the main difference to my previous work is that we are using
-- equivFun_homeo and not equivFun_homeo.symm

variable [MeasurableSpace T] [BorelSpace T]

theorem foo :
    MeasureTheory.ringHaarChar (Units.map (algebraMap T R).toMonoidHom t) =
    (MeasureTheory.ringHaarChar t) ^ (Module.finrank T R) := by
  rw [foo_ext1 T R t]
  simpa using MeasureTheory.ringHaarChar_pi (ι := Fin (Module.finrank T R))
      (A := fun _ : Fin (Module.finrank T R) => T) (fun (i : Fin (Module.finrank T R)) ↦ t)
