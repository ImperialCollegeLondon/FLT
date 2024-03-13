import FLT.Proj3.CommAlgebraCat.Monoidal
import FLT.for_mathlib.HopfAlgebra.Basic
import Mathlib.CategoryTheory.Yoneda


open CategoryTheory Opposite
open scoped MonoidalCategory

variable (k A : Type) [CommRing k] [CommRing A] [Bialgebra k A]

variable (Δ :  CommAlgebraCat.of k A ⟶ CommAlgebraCat.of k A ⊗ CommAlgebraCat.of k A)
variable (ε : CommAlgebraCat.of k A ⟶ CommAlgebraCat.of k k)


variable {k} in
@[simps]
def square (F : CommAlgebraCat k ⥤ Type) [F.Corepresentable] :
    CommAlgebraCat k ⥤ Type where
  obj A := (F.obj A) × (F.obj A)
  map f x := ⟨F.map f x.1, F.map f x.2⟩

local notation "*" => (coyoneda.obj <| op (CommAlgebraCat.of k k))

class AffineMonoid (F : CommAlgebraCat k ⥤ Type) [F.Corepresentable] where
m : square F ⟶ F
e : * ⟶ F

variable (F : CommAlgebraCat k ⥤ Type) [F.Corepresentable]

/-
instance (A : CommAlgebraCat k) [Bialgebra k A] : Monoid (F.obj A) where
  mul x y := AffineMonoid.m (F := F) |>.app A ⟨x, y⟩
  mul_assoc := sorry
  one := AffineMonoid.e (F := F) |>.app A <| CommAlgebraCat.ofHom <| Algebra.ofId k A
  one_mul := sorry
  mul_one := sorry
-/

-- lemma ex1 [AffineMonoid k F] : Bialgebra k A := sorry
-- #check Points.mul1

-- instance [Bialgebra k A] {X : CommAlgebraCat k}
--   (f : A →ₐ[k] X) : (Points (R := k) (A := A) (L := X)) f := sorry

instance : Bialgebra k ↑(op (CommAlgebraCat.of k A)).unop :=
  inferInstanceAs <| Bialgebra k A

def ex2 [Bialgebra k A]  :
    AffineMonoid k (coyoneda.obj <| op <| CommAlgebraCat.of k A) where
  m :=
  { app := fun X xx => AlgHomPoint.mul xx.1 xx.2
    naturality := by
      intros X Y f
      ext ⟨(x1 : A →ₐ[k] X), (x2 : A →ₐ[k] X)⟩
      simp only [coyoneda_obj_obj, unop_op, square_obj, CommAlgebraCat.coe_of, types_comp_apply,
        square_map, coyoneda_obj_map]
      sorry }
  e := _

-- variable (g : A →ₐ[k] A) [Bialgebra k A]

-- lemma sidjao :  (A →ₐ[k] A) = (Points (R := k) (A := A) (L := A)) := rfl
