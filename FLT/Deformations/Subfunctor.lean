module

public import Mathlib.CategoryTheory.Elementwise
public import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal
public import Mathlib.Data.Set.Lattice.Image
public import Mathlib.CategoryTheory.Subfunctor.Basic

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
