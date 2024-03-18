/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.CategoryTheory.Monoidal.Transport
import FLT.Proj3.CommAlgebraCat.Basic
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Mathlib.RingTheory.TensorProduct

/-!
# The monoidal category structure on R-algebras
-/

open CategoryTheory
open scoped MonoidalCategory

universe v u

variable {R : Type u} [CommRing R]

namespace CommAlgebraCat

noncomputable section

namespace instMonoidalCategory

open scoped TensorProduct

/-- Auxiliary definition used to fight a timeout when building
`CommAlgebraCat.instMonoidalCategory`. -/
@[simps!]
noncomputable abbrev tensorObj (X Y : CommAlgebraCat.{u} R) : CommAlgebraCat.{u} R :=
  of R (X ⊗[R] Y)

/-- Auxiliary definition used to fight a timeout when building
`CommAlgebraCat.instMonoidalCategory`. -/
noncomputable abbrev tensorHom {W X Y Z : CommAlgebraCat.{u} R} (f : W ⟶ X) (g : Y ⟶ Z) :
    tensorObj W Y ⟶ tensorObj X Z :=
  Algebra.TensorProduct.map f g

open MonoidalCategory

end instMonoidalCategory

open instMonoidalCategory

instance : MonoidalCategoryStruct (CommAlgebraCat.{u} R) where
  tensorObj := instMonoidalCategory.tensorObj
  whiskerLeft X _ _ f := tensorHom (𝟙 X) f
  whiskerRight {X₁ X₂} (f : X₁ ⟶ X₂) Y := tensorHom f (𝟙 Y)
  tensorHom := tensorHom
  tensorUnit := of R R
  associator X Y Z := (Algebra.TensorProduct.assoc R X Y Z).toCommAlgebraIso
  leftUnitor X := (Algebra.TensorProduct.lid R X).toCommAlgebraIso
  rightUnitor X := (Algebra.TensorProduct.rid R R X).toCommAlgebraIso

theorem forget₂_map_associator_hom (X Y Z : CommAlgebraCat.{u} R) :
    (forget₂ (CommAlgebraCat R) (ModuleCat R)).map (α_ X Y Z).hom =
      (α_
        (forget₂ _ (ModuleCat R) |>.obj X)
        (forget₂ _ (ModuleCat R) |>.obj Y)
        (forget₂ _ (ModuleCat R) |>.obj Z)).hom := by
  rfl

set_option maxHeartbeats 800000 in
theorem forget₂_map_associator_inv (X Y Z : CommAlgebraCat.{u} R) :
    (forget₂ (CommAlgebraCat R) (ModuleCat R)).map (α_ X Y Z).inv =
      (α_
        (forget₂ _ (ModuleCat R) |>.obj X)
        (forget₂ _ (ModuleCat R) |>.obj Y)
        (forget₂ _ (ModuleCat R) |>.obj Z)).inv := by
  rfl

set_option maxHeartbeats 800000 in
noncomputable instance instMonoidalCategory : MonoidalCategory (CommAlgebraCat.{u} R) :=
  Monoidal.induced
    (forget₂ (CommAlgebraCat R) (ModuleCat R))
    { μIso := fun X Y => Iso.refl _
      εIso := Iso.refl _
      associator_eq := fun X Y Z => by
        dsimp only [forget₂_module_obj, forget₂_map_associator_hom]
        simp only [eqToIso_refl, Iso.refl_trans, Iso.refl_symm, Iso.trans_hom, tensorIso_hom,
          Iso.refl_hom, MonoidalCategory.tensor_id]
        erw [Category.id_comp, Category.comp_id, MonoidalCategory.tensor_id, Category.id_comp]
      leftUnitor_eq := fun X => by
        dsimp only [forget₂_module_obj, forget₂_module_map, Iso.refl_symm, Iso.trans_hom,
          Iso.refl_hom, tensorIso_hom]
        erw [Category.id_comp, MonoidalCategory.tensor_id, Category.id_comp]
        rfl
      rightUnitor_eq := fun X => by
        dsimp
        erw [Category.id_comp, MonoidalCategory.tensor_id, Category.id_comp]
        exact congr_arg LinearEquiv.toLinearMap <|
          TensorProduct.AlgebraTensorModule.rid_eq_rid R X }

variable (R) in
/-- `forget₂ (CommAlgebraCat R) (ModuleCat R)` as a monoidal functor. -/
def toModuleCatMonoidalFunctor : MonoidalFunctor (CommAlgebraCat.{u} R) (ModuleCat.{u} R) := by
  unfold instMonoidalCategory
  exact Monoidal.fromInduced (forget₂ (CommAlgebraCat R) (ModuleCat R)) _

instance : Faithful (toModuleCatMonoidalFunctor R).toFunctor :=
  forget₂_faithful _ _

end

end CommAlgebraCat
