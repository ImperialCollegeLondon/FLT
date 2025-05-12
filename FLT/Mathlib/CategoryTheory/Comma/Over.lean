import Mathlib

open CategoryTheory

section Under

universe u v

instance Subtype.instFunLike {F : Type*} {X Y} [DFunLike F X Y] (P : F → Prop) :
    DFunLike (Subtype P) X Y where
  coe f := f
  coe_injective' _ _ h := Subtype.coe_injective (DFunLike.coe_injective h)

instance Under.instConcreteCategory {C : Type u} [CategoryTheory.Category.{v, u} C]
    {FC : C → C → Type*} {CC : C → Type*} [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)]
    {X : C} [ConcreteCategory C FC] :
    ConcreteCategory (CategoryTheory.Under X) fun X Y => {f : FC X.right Y.right | ∀ x, f (X.hom x) = Y.hom x} where
  hom f := ⟨ConcreteCategory.hom f.right, sorry⟩
  ofHom f := Under.homMk (ConcreteCategory.ofHom f) (w := sorry)

end Under
