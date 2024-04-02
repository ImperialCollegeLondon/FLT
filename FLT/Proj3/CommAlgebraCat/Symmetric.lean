/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import FLT.Proj3.CommAlgebraCat.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric

/-!
# The monoidal structure on `CommAlgebraCat` is symmetric.

In this file we show:

* `CommAlgebraCat.instSymmetricCategory : SymmetricCategory (CommAlgebraCat.{u} R)`
-/
open CategoryTheory


noncomputable section

universe v u

variable {R : Type u} [CommRing R]

namespace CommAlgebraCat

instance : BraidedCategory (CommAlgebraCat.{u} R) :=
  braidedCategoryOfFaithful (toModuleCatMonoidalFunctor R)
    (fun X Y => (Algebra.TensorProduct.comm R X Y).toCommAlgebraIso)
    (by aesop_cat)

variable (R) in
/-- `forget₂ (CommAlgebraCat R) (ModuleCat R)` as a braided functor. -/
@[simps toMonoidalFunctor]
def toModuleCatBraidedFunctor : BraidedFunctor (CommAlgebraCat.{u} R) (ModuleCat.{u} R) where
  toMonoidalFunctor := toModuleCatMonoidalFunctor R

instance : Faithful (toModuleCatBraidedFunctor R).toFunctor :=
  forget₂_faithful _ _

instance instSymmetricCategory : SymmetricCategory (CommAlgebraCat.{u} R) :=
  symmetricCategoryOfFaithful (toModuleCatBraidedFunctor R)

end CommAlgebraCat
