/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.CategoryTheory.Elementwise
public import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal
public import Mathlib.Data.Set.Lattice.Image
public import Mathlib.CategoryTheory.Subfunctor.Basic

/-!
# Subfunctors

Basic constructions for subfunctors of functors valued in `Type`, including
the subfunctor cut out by a subset of the value at a terminal object.
-/

@[expose] public section

universe w v u

open Opposite CategoryTheory

namespace CategoryTheory
namespace Subfunctor

variable {C : Type u} [Category.{v} C] (F : C ⥤ Type w)

/-- The subfunctor defined by pulling back a subset of the terminal component. -/
def ofIsTerminal {X : C} (hX : Limits.IsTerminal X) (s : Set (F.obj X)) :
    Subfunctor F where
  obj U := F.map (hX.from U) ⁻¹' s
  map {U V} i := by
    simp only [← Set.preimage_comp, ← hX.comp_from i, F.map_comp]
    rfl

end Subfunctor
end CategoryTheory
