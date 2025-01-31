import Mathlib
import FLT.Mathlib.Algebra.Category.Ring.Basic
import FLT.Mathlib.CategoryTheory.Comma.Over

open CategoryTheory

section CommAlgCat

universe u v

variable (R : Type u) [CommRing R]

def CommAlgCat := Under (CommRingCat.of R)

instance : Category (CommAlgCat R) := by unfold CommAlgCat; infer_instance

instance : CoeOut (CommAlgCat R) (CommRingCat) where
  coe A := A.right

instance : CoeSort (CommAlgCat R) (Type _) where
  coe A := A.right

instance (A : CommAlgCat R) : Algebra R A := (ConcreteCategory.hom A.hom).toAlgebra

instance : ConcreteCategory (CommAlgCat R) (· →ₐ[R] ·) where
  hom := sorry
  ofHom := sorry

instance (A B : CommAlgCat R) : FunLike (A ⟶ B) A B := sorry

def CommAlgCat.quotient {A : CommAlgCat R} (a : Ideal A) : CommAlgCat R where
  left := ⟨⟨⟩⟩
  right := CommRingCat.quotient a
  hom := by simp; exact CommRingCat.ofHom (algebraMap _ _)

end CommAlgCat
