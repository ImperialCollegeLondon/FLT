import FLT.Deformations.Lift
import mathlib

def Deformation := _root_.Quotient <| Lift.isIso ρbar A

omit A in
def Deformation.functor_onMap {A B : 𝓒 𝓞} (f : A ⟶ B) : Deformation ρbar A → Deformation ρbar B :=
  sorry

variable (𝓞) in
def Deformation.functor : CategoryTheory.Functor (𝓒 𝓞) (Type (u+1)) where
  obj A := Deformation ρbar A
  map f := Deformation.functor_onMap ρbar f

theorem Deformation.functor_isCorepresentable : (Deformation.functor 𝓞 ρbar).IsCorepresentable  := sorry
