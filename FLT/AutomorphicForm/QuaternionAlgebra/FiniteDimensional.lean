/-
Copyright (c) 2024 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/
module

public import FLT.AutomorphicForm.QuaternionAlgebra.Basic
public import Mathlib.Algebra.Central.Defs
public import FLT.DivisionAlgebra.Finiteness
import Mathlib.RingTheory.PicardGroup
import FLT.Mathlib.GroupTheory.DoubleCoset

/-!
# Finite-dimensionality of spaces of weight-2 automorphic forms

We prove that the space of weight-2 automorphic forms on a totally definite
quaternion algebra over a totally real number field, of fixed level `U`,
is a finitely generated `R`-module.

## Main results

* `WeightTwoAutomorphicForm.finiteDimensional`: the space of weight-2 forms
  is module-finite over the coefficient ring.
-/

@[expose] public section
namespace TotallyDefiniteQuaternionAlgebra

open IsDedekindDomain NumberField IsQuaternionAlgebra.NumberField
open scoped TensorProduct TensorProduct.RightActions Adele

-- let F be a number field
variable {F : Type*} [Field F] [NumberField F]
    -- and let D be a finite-dimensional division ring over F
    {D : Type*} [DivisionRing D] [Algebra F D] [Module.Finite F D]
    [Algebra.IsCentral F D]
-- Let K be a coefficient field
variable (R : Type*) [CommRing R]
    [WithRigidification F D]
    -- and let U, the level, be a subgroup of `(D ⊗ 𝔸_F^∞)ˣ`
    -- (which will be open in the theorem)
    {U : Subgroup (GL (Fin 2) (FiniteAdeleRing (𝓞 F) F))}

open TotallyDefiniteQuaternionAlgebra

open scoped FLT

variable (D) in
/-- For any open `U ⊆ GL₂(𝔸_F)`, `Dˣ\GL₂(𝔸_F)/U` is finite.
(where `Dˣ` is viewed as a subgroup of `GL₂(𝔸_F)` under the identification `M₂(𝔸_F) ≃ D ⊗ 𝔸_F`) -/
lemma finite_doubleCoset
    (hU : IsOpen (U : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)))) :
    Finite (Dˣ＼GL₂(𝔸 F)／U) :=
  (NumberField.FiniteAdeleRing.DivisionAlgebra.finiteDoubleCoset F D
    (U := U.comap (Units.map (WithRigidification.algEquiv ..).toMonoidHom))
    (hU.preimage (Units.continuous_map (by
      exact IsModuleTopology.continuous_of_linearMap
        (WithRigidification.algEquiv F D).toLinearMap)))).of_equiv _
  (DoubleCoset.quotientEquiv _ _ _ _
    (Units.mapEquiv (WithRigidification.algEquiv ..).toMulEquiv) (by
      rw [← MulEquiv.coe_toEquiv, Equiv.preimage_eq_iff_eq_image, ← Set.range_comp]
      dsimp
      congr 1
      ext x : 2
      simp [WithRigidification.algEquiv]) rfl)

instance (ℒ : WeightTwoAutomorphicForm.LevelStruct F R) : ℒ.IsFinite D :=
  finite_doubleCoset _ (Subgroup.isOpen_mono le_sup_left ℒ.isOpen_U)

end TotallyDefiniteQuaternionAlgebra
