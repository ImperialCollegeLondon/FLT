import Mathlib

universe u v

instance CategoryTheory.Under.instConcreteCategory {C : Type u} [CategoryTheory.Category.{v, u} C]
  {X : C} [CategoryTheory.ConcreteCategory C] : CategoryTheory.ConcreteCategory (CategoryTheory.Under X) := sorry
