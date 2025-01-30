import Mathlib
import FLT.Mathlib.CategoryTheory.Comma.Over

open CategoryTheory

section CommRingCat

def CommRingCat.quotient {A : CommRingCat} (a : Ideal A) : CommRingCat where
  α := A ⧸ a

end CommRingCat

section CommAlgCat

-- TODO: Need to update Mathlib first! (maybe concrete cat change is not in the last stable yet)
-- section Under

-- universe u v

-- instance Subtype.instFunLike {F : Type*} {X Y} [DFunLike F X Y] (P : F → Prop) :
--     DFunLike (Subtype P) X Y where
--   coe f := f
--   coe_injective' _ _ h := Subtype.coe_injective (DFunLike.coe_injective h)

-- instance Under.instConcreteCategory {C : Type u} [CategoryTheory.Category.{v, u} C]
--     {FC : C → C → Type*} {CC : C → Type*} [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)]
--     {X : C} [ConcreteCategory C FC] :
--     ConcreteCategory (CategoryTheory.Under X) fun X Y => {f : FC X.right Y.right | ∀ x, f (X.hom x) = Y.hom x} where
--   hom f := ⟨ConcreteCategory.hom f.right, sorry⟩
--   ofHom f := Under.homMk (ConcreteCategory.ofHom f) (w := sorry)

-- end Under

variable (𝓞 : Type*) [CommRing 𝓞]

def CommAlgCat := Under (CommRingCat.of 𝓞)

instance : Category (CommAlgCat 𝓞) := by unfold CommAlgCat; infer_instance

instance : ConcreteCategory (CommAlgCat 𝓞) := by unfold CommAlgCat; infer_instance

instance : CoeOut (CommAlgCat 𝓞) (CommRingCat) where coe A := A.right

instance : CoeSort (CommAlgCat 𝓞) (Type _) where coe A := A.right

instance (A B : CommAlgCat 𝓞) : CoeFun (A ⟶ B) fun _ ↦ (A → B) :=
  sorry

variable (A : CommAlgCat 𝓞)

instance : Algebra 𝓞 A := A.hom.toAlgebra

instance (A B : CommAlgCat 𝓞) : FunLike (A ⟶ B) A B where
  coe f := sorry
  coe_injective' := sorry

instance (A B : CommAlgCat 𝓞) : AlgHomClass (A ⟶ B) 𝓞 A B where
  map_mul := sorry
  map_one := sorry
  map_add := sorry
  map_zero := sorry
  commutes := sorry

def CommAlgCat.quotient {A : CommAlgCat 𝓞} (a : Ideal A) : CommAlgCat 𝓞 where
  left := ⟨⟨⟩⟩
  right := CommRingCat.quotient a
  hom := by simp; exact CommRingCat.ofHom (algebraMap _ _)

end CommAlgCat
