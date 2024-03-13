import Mathlib.Algebra.Category.CommAlgebraCat.Monoidal
import Mathlib.CategoryTheory.Yoneda
import Mathlib.Proj2

open CategoryTheory Opposite
open scoped MonoidalCategory

variable (k : Type) [CommRing k]

variable (A : CommAlgebraCat.{0} k)

variable (Δ :  A ⟶ A ⊗ A) (ε : A ⟶ CommAlgebraCat.of k k)


variable {k} in
def square (F : CommAlgebraCat k ⥤ Type) [F.Corepresentable] : CommAlgebraCat k ⥤ Type where
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

lemma ex1 [AffineMonoid k F] : Bialgebra k A := sorry
-- #check Points.mul1

@[simp]
def coyonedaToAlgHom {X : CommAlgebraCat k} (f : (coyoneda.obj <| op A).obj X) :
  A →ₐ[k] X := f

def algHomToCoyoneda {X : CommAlgebraCat k} (f : A →ₐ[k] X) :
  (coyoneda.obj <| op A).obj X := f

open Points
variable {k A} in
set_option tactic.skipAssignedInstances false
-- def asPoint [Bialgebra k A] {X : CommAlgebraCat k} (f : A →ₐ[k] X) :
--     Points.Points (R := k) (A := A) (L := X) where
--       toFun := _
--       map_one' := _
--       map_mul' := _
--       map_zero' := _
--       map_add' := _
--       commutes' := _

instance [Bialgebra k A] {X : CommAlgebraCat k}
  (f : A →ₐ[k] X) : (Points (R := k) (A := A) (L := X)) f := sorry

def ex2 [Bialgebra k A]  : AffineMonoid k (coyoneda.obj <| op A) where
    m :=
    { app := fun X xx => algHomToCoyoneda k A <| _

        -- Points.mul1 (R := k) (A := A) (L := X)
        -- -- _ _
        --   (asPoint <| coyonedaToAlgHom k A xx.1) (asPoint <| coyonedaToAlgHom k A xx.2)
    -- by
    --     have x1 : A ⟶ X := xx.1
    --     have x2 : A ⟶ X := xx.2

        -- let y1 : F.coreprX ⟶ X := F.coreprW.symm.hom.app X xx.1

        -- let y2 : F.coreprX ⟶ X := F.coreprW.symm.hom.app X xx.2
        -- let h := y1 ⊗ y2
      naturality := _ }
    e := _

variable (g : A →ₐ[k] A) [Bialgebra k A]

lemma sidjao :  (A →ₐ[k] A) = (Points (R := k) (A := A) (L := A)) := rfl
