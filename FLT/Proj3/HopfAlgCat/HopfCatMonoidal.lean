import FLT.for_mathlib.Coalgebra.Monoid
import FLT.for_mathlib.Coalgebra.Sweedler
import FLT.for_mathlib.Coalgebra.TensorProduct
import FLT.for_mathlib.HopfAlgebra.Basic
import FLT.for_mathlib.Coalgebra.TensorProduct
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.CategoryTheory.Comma.Over
import Mathlib.Algebra.Category.AlgebraCat.Monoidal
import Mathlib.RingTheory.TensorProduct
import Mathlib.Algebra.Algebra.Basic
import Mathlib.LinearAlgebra.TensorProduct
import Mathlib.CategoryTheory.Monoidal.Category
import FLT.Proj3.HopfAlgCat.CoalgHom
import FLT.Proj3.HopfAlgCat.BialgHom
import FLT.Proj3.HopfAlgCat.CoalgEquiv
import FLT.Proj3.HopfAlgCat.BialgEquiv
import FLT.Proj3.HopfAlgCat.HopfCat

open Opposite
open CategoryTheory
open scoped TensorProduct
open HopfAlgebra
open Coalgebra
set_option synthInstance.maxHeartbeats 50000

universe u
variable (R : Type u) [CommRing R]
variable (H1 H2 : Type u)[CommRing H1][CommRing H2][HopfAlgebra R H1][HopfAlgebra R H2]
variable (A B C D: Type u) [CommRing A] [CommRing B] [CommRing C] [CommRing D] [HopfAlgebra R A]
    [HopfAlgebra R B] [HopfAlgebra R C] [HopfAlgebra R D]

-- This file we are going to prove the monoidal structure on the category of Hopf algebras
-- The first is to define tensor object.
variable {X₁ X₂ : Type u}
@[simps!]
noncomputable abbrev tensorObj (A B : HopfAlgCat R) : HopfAlgCat R := HopfAlgCat.of R (A ⊗[R] B)

-- We need to define an ext here for later uses.
@[ext]
theorem ext {f g : H1 →bi[R] H2} (h : ∀ a, f a = g a) : f = g :=
  DFunLike.ext _ _ h

-- We prove that HopfAlgCat is a ConcreteCategory, with a forgetful functor sending a morphism
-- to its underlying function. This forgetful functor is faithful.
instance: ConcreteCategory (HopfAlgCat R) where
  forget :=
    { obj := fun M => M
      map := fun f => f.toFun}
  forget_faithful := ⟨fun h => ext _ _ _ (by intros x; dsimp at h; exact congrFun h x)⟩

-- Implicitly coerce HopfAlgCat to type u.
instance : CoeSort (HopfAlgCat R) (Type u) :=
  ⟨HopfAlgCat.carrier⟩

-- Instance funlike property
instance {M N : HopfAlgCat R} : FunLike (M ⟶ N) M N :=
  BialgHom.funLike

--Instance of the algebra hom class
instance {M N : HopfAlgCat R} : AlgHomClass (M ⟶ N) R M N :=
  BialgHom.algHomClass

-- def the isomorphism of two hopf algebra category.
-- This is refered from toAlgebraIso, with is a useful tool to define isomorphism of two algebra category,
-- and useful in proving monoidal category structure of algebra category.
@[simps!]
def toHopfAlgebraIso {X₁ X₂ : Type u} {g₁ : CommRing X₁} {g₂ : CommRing X₂} {m₁ : HopfAlgebra R X₁} {m₂ : HopfAlgebra R X₂}
    (e : X₁ ≃bi[R] X₂) : HopfAlgCat.of R X₁ ≅ HopfAlgCat.of R X₂ where
  -- homomorphism of the isomorphism part
  hom := e.toBialgHom
  -- inverse homomorphism of the isomorphism part
  inv := BialgEquiv.symm X₁ X₂ e |>.toBiAlgHom
  hom_inv_id := by ext x; exact e.left_inv x
  inv_hom_id := by ext x; exact e.right_inv x

-- TensorHom in monoidal category
noncomputable abbrev tensorHom {W X Y Z : HopfAlgCat R} (f : W ⟶ X) (g : Y ⟶ Z) :
    tensorObj R W Y ⟶ tensorObj R X Z :=
  Bialgebra.TensorProduct.map f g

open BigOperators
-- To prove that the comul is preserved under associativity condition.
lemma comul_comp_assoc :
  TensorProduct.map (TensorProduct.assoc R A B C) (TensorProduct.assoc R A B C) ∘ₗ comul =
  comul (R := R) (A := A ⊗[R] B ⊗[R] C) ∘ₗ
  (TensorProduct.assoc R A B C).toLinearMap := by
    ext x y z
    simp only [TensorProduct.AlgebraTensorModule.curry_apply, TensorProduct.curry_apply,
      LinearMap.coe_restrictScalars, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
      TensorProduct.assoc_tmul]
    obtain ⟨Ix, x1, x2, hx⟩ := Coalgebra.exists_repr (R := R) x
    obtain ⟨Iy, y1, y2, hy⟩ := Coalgebra.exists_repr (R := R) y
    obtain ⟨Iz, z1, z2, hz⟩ := Coalgebra.exists_repr (R := R) z
    have comul_xy' : comul (x ⊗ₜ y) = ∑ i in Ix, ∑ j in Iy, (x1 i ⊗ₜ y1 j) ⊗ₜ[R] (x2 i ⊗ₜ y2 j) :=
      TensorProduct.comul_apply_repr (a := x) (b := y) (repr_a := hx) (repr_b := hy)
    rw [← Finset.sum_product'] at comul_xy'
    have comul_yz' : comul (y ⊗ₜ z) = ∑ i in Iy, ∑ j in Iz, (y1 i ⊗ₜ z1 j) ⊗ₜ[R] (y2 i ⊗ₜ z2 j) :=
      TensorProduct.comul_apply_repr (a := y) (b := z) (repr_a := hy) (repr_b := hz)
    rw [← Finset.sum_product'] at comul_yz'
    have comul_xy_z : comul ((x ⊗ₜ y) ⊗ₜ z) = _ :=
      TensorProduct.comul_apply_repr (a := x ⊗ₜ y) (b := z) (repr_a := comul_xy') (repr_b := hz)
    rw [← Finset.sum_product'] at comul_xy_z
    have comul_x_yz : comul (x ⊗ₜ (y ⊗ₜ z)) = _ :=
      TensorProduct.comul_apply_repr (a := x) (b := y ⊗ₜ z) (repr_a := hx) (repr_b := comul_yz')
    simp only [comul_xy_z, map_sum, TensorProduct.map_tmul, LinearEquiv.coe_coe,
      TensorProduct.assoc_tmul, comul_x_yz]
    erw [← Finset.sum_product']
    refine Finset.sum_bij'
      (fun x _ ↦ (x.1.1, (x.1.2, x.2)))
      (fun x _ ↦ ((x.1, x.2.1), x.2.2)) ?_ ?_ ?_ ?_ ?_ <;> aesop

-- To prove that the counit is preserved under associativity condition.
lemma counit_comp_assoc :
  counit (R := R) (A := A ⊗[R] B ⊗[R] C) ∘ₗ (TensorProduct.assoc R A B C).toLinearMap =
  counit (R := R) (A := (A ⊗[R] B) ⊗[R] C) := by
  ext x y z
  simp only [TensorProduct.AlgebraTensorModule.curry_apply, TensorProduct.curry_apply,
    LinearMap.coe_restrictScalars, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    TensorProduct.assoc_tmul]
  rw[Coalgebra.TensorProduct.counit_def, Coalgebra.TensorProduct.counit_def, Coalgebra.TensorProduct.counit_def, Coalgebra.TensorProduct.counit_def]
  simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, TensorProduct.map_tmul,
    TensorProduct.lid_tmul, smul_eq_mul]
  rw [Mathlib.Tactic.RingNF.mul_assoc_rev]


set_option maxHeartbeats 1000000 in
-- For associator, we use the "comul_comp_assoc" and "counit_comp_assoc" that already proved
noncomputable def assoc : (A ⊗[R] B) ⊗[R] C ≃bi[R] A ⊗[R] B ⊗[R] C where
  __ := Algebra.TensorProduct.assoc R A B C
  __ := _root_.TensorProduct.assoc R A B C
  comul_comp' := comul_comp_assoc R A B C
  counit_comp' := counit_comp_assoc R A B C


open BigOperators

-- For left unitor
noncomputable def lid : R ⊗[R] A ≃bi[R] A :=
{
    Algebra.TensorProduct.lid R A with
  comul_comp' := by
    ext x
    simp only [AlgEquiv.toEquiv_eq_coe, Equiv.toFun_as_coe, EquivLike.coe_coe,
      TensorProduct.AlgebraTensorModule.curry_apply, TensorProduct.curry_apply,
      LinearMap.coe_restrictScalars, LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_mk,
      AddHom.coe_mk, Algebra.TensorProduct.lid_tmul, one_smul]
    obtain ⟨I1, x1, x2, hx⟩ := Coalgebra.exists_repr (R := R) x
    have repr_a : comul (1 : R) = ∑ i in {1}, (1 : R) ⊗ₜ[R] (1 : R) := rfl
    rw [TensorProduct.comul_apply_repr (a := 1) (b := x) (repr_a := repr_a) (repr_b := hx)]
    simp only [Finset.sum_const, Finset.card_singleton, one_smul, map_sum, TensorProduct.map_tmul,
      LinearMap.coe_mk, AddHom.coe_mk, Algebra.TensorProduct.lid_tmul]
    exact hx.symm
  counit_comp' := by
    ext x
    rw [TensorProduct.counit_def]
    simp
  map_smul' := by simp
}

-- For right unitor
noncomputable def rid: A ⊗[R] R ≃bi[R] A :=
{
    Algebra.TensorProduct.rid R R A with
  comul_comp' := by
    ext x
    simp
    obtain ⟨I1, x1, x2, hx⟩ := Coalgebra.exists_repr (R := R) x
    have repr_b : comul (1 : R) = ∑ i in {1}, (1 : R) ⊗ₜ[R] (1 : R) := rfl
    rw [TensorProduct.comul_apply_repr (a := x) (b := 1) (repr_a := hx) (repr_b := repr_b)]
    simp only [Finset.sum_const, Finset.card_singleton, one_smul, map_sum, TensorProduct.map_tmul,
      LinearMap.coe_mk, AddHom.coe_mk, Algebra.TensorProduct.rid_tmul]
    exact hx.symm
  counit_comp' := by
    ext x
    rw [TensorProduct.counit_def]
    simp
  map_smul' := by simp
}

-- Monoidal Structure of HopfAlgCat
noncomputable instance : MonoidalCategoryStruct (HopfAlgCat R) where
  tensorObj := tensorObj R
  whiskerLeft X _ _ f :=  tensorHom R (𝟙 X) f
  whiskerRight {X₁ X₂} (f : X₁ ⟶ X₂) Y := tensorHom R f (𝟙 Y)
  tensorHom := tensorHom R
  tensorUnit := HopfAlgCat.of R R
  associator X Y Z := toHopfAlgebraIso R (assoc R X Y Z)
  leftUnitor X := toHopfAlgebraIso R (lid R X)
  rightUnitor X := toHopfAlgebraIso R (rid R X)

open BialgHom
-- Basicly extend from algebracat to hopfalgcat
-- Use Monoidal structure that mentioned above to finish each proof
noncomputable instance : MonoidalCategory (HopfAlgCat R) where
  tensorHom_def {X₁ X₂ Y₁ Y₂} (f : _ →bi[R] _) (g : _ →bi[R] _) := by
    have := @MonoidalCategory.tensorHom_def (AlgebraCat R) _ _
      (.of R X₁) (.of R X₂) (.of R Y₁) (.of R Y₂)
      (AlgebraCat.ofHom <| BialgHom.toAlgHom f)
      (AlgebraCat.ofHom <| BialgHom.toAlgHom g)
    change (_ : _ →bi[R] _) = (_ : _ →bi[R] _)
    refine DFunLike.ext _ _ fun x ↦ ?_
    exact congr($this x)
  tensor_id {X₁ X₂}:= by
    have := @MonoidalCategory.tensor_id (AlgebraCat R) _ _ (.of R X₁) (.of R X₂)
    change (_ : _ →bi[R] _) = (_ : _ →bi[R] _)
    refine DFunLike.ext _ _ fun x ↦ ?_
    exact congr($this x)
  tensor_comp {X₁ X₂ Y₁ Y₂ Z₁ Z₂} (f₁ : _ →bi[R] _) (f₂ : _ →bi[R] _) (g₁ : _ →bi[R] _)
    (g₂ : _ →bi[R] _) := by
    have := @MonoidalCategory.tensor_comp (AlgebraCat R) _ _ (.of R X₁) (.of R X₂)
      (.of R Y₁) (.of R Y₂) (.of R Z₁) (.of R Z₂)
      (AlgebraCat.ofHom <| BialgHom.toAlgHom f₁) (AlgebraCat.ofHom <| BialgHom.toAlgHom f₂)
      (AlgebraCat.ofHom <| BialgHom.toAlgHom g₁) (AlgebraCat.ofHom <| BialgHom.toAlgHom g₂)
    change (_ : _ →bi[R] _) = (_ : _ →bi[R] _)
    refine DFunLike.ext _ _ fun x ↦ ?_
    exact congr($this x)
  whiskerLeft_id {X Y} := by
    have := @MonoidalCategory.whiskerLeft_id (AlgebraCat R) _ _ (.of R X) (.of R Y)
    change (_ : _ →bi[R] _) = (_ : _ →bi[R] _)
    refine DFunLike.ext _ _ fun x ↦ ?_
    exact congr($this x)
  id_whiskerRight {X Y}:= by
    have := @MonoidalCategory.id_whiskerRight (AlgebraCat R) _ _ (.of R X) (.of R Y)
    change (_ : _ →bi[R] _) = (_ : _ →bi[R] _)
    refine DFunLike.ext _ _ fun x ↦ ?_
    exact congr($this x)
  associator_naturality {X₁ X₂ X₃ Y₁ Y₂ Y₃} (f₁ : _ →bi[R] _) (f₂ : _ →bi[R] _)
    (f₃ : _ →bi[R] _) := by
    have := @MonoidalCategory.associator_naturality (AlgebraCat R) _ _ (.of R X₁) (.of R X₂)
      (.of R X₃) (.of R Y₁) (.of R Y₂) (.of R Y₃)
      (AlgebraCat.ofHom <| BialgHom.toAlgHom f₁) (AlgebraCat.ofHom <| BialgHom.toAlgHom f₂)
      (AlgebraCat.ofHom <| BialgHom.toAlgHom f₃)
    change (_ : _ →bi[R] _) = (_ : _ →bi[R] _)
    refine DFunLike.ext _ _ fun x ↦ ?_
    exact congr($this x)
  leftUnitor_naturality {X Y} (f : _ →bi[R] _) := by
    have := @MonoidalCategory.leftUnitor_naturality (AlgebraCat R) _ _ (.of R X) (.of R Y)
      (AlgebraCat.ofHom <| BialgHom.toAlgHom f)
    change (_ : _ →bi[R] _) = (_ : _ →bi[R] _)
    refine DFunLike.ext _ _ fun x ↦ ?_
    exact congr($this x)
  rightUnitor_naturality {X Y} (f : _ →bi[R] _) := by
    have := @MonoidalCategory.rightUnitor_naturality (AlgebraCat R) _ _ (.of R X) (.of R Y)
      (AlgebraCat.ofHom <| BialgHom.toAlgHom f)
    change (_ : _ →bi[R] _) = (_ : _ →bi[R] _)
    refine DFunLike.ext _ _ fun x ↦ ?_
    exact congr($this x)
  pentagon {W X Y Z} := by
    have := @MonoidalCategory.pentagon (AlgebraCat R) _ _ (.of R W) (.of R X) (.of R Y) (.of R Z)
    change (_ : _ →bi[R] _) = (_ : _ →bi[R] _)
    refine DFunLike.ext _ _ fun x ↦ ?_
    exact congr($this x)
  triangle {X Y} := by
    have := @MonoidalCategory.triangle (AlgebraCat R) _ _ (.of R X) (.of R Y)
    change (_ : _ →bi[R] _) = (_ : _ →bi[R] _)
    refine DFunLike.ext _ _ fun x ↦ ?_
    exact congr($this x)
