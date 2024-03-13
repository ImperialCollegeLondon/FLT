/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Algebra.FreeAlgebra
import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.Algebra.Category.ModuleCat.Basic

#align_import algebra.category.Algebra.basic from "leanprover-community/mathlib"@"79ffb5563b56fefdea3d60b5736dad168a9494ab"

/-!
# Category instance for algebras over a commutative ring

We introduce the bundled category `CommAlgebraCat` of algebras over a fixed commutative ring `R` along
with the forgetful functors to `RingCat` and `ModuleCat`. We furthermore show that the functor
associating to a type the free `R`-algebra on that type is left adjoint to the forgetful functor.
-/

set_option linter.uppercaseLean3 false

open CategoryTheory

open CategoryTheory.Limits

universe v u

variable (R : Type u) [CommRing R]

/-- The category of R-algebras and their morphisms. -/
structure CommAlgebraCat where
  carrier : Type v
  [isRing : CommRing carrier]
  [isAlgebra : Algebra R carrier]

-- Porting note: typemax hack to fix universe complaints
/-- An alias for `CommAlgebraCat.{max u₁ u₂}`, to deal around unification issues.
Since the universe the ring lives in can be inferred, we put that last. -/
@[nolint checkUnivs]
abbrev CommAlgebraCatMax.{v₁, v₂, u₁} (R : Type u₁) [CommRing R] := CommAlgebraCat.{max v₁ v₂} R

attribute [instance] CommAlgebraCat.isRing CommAlgebraCat.isAlgebra

initialize_simps_projections CommAlgebraCat (-isRing, -isAlgebra)

namespace CommAlgebraCat

instance : CoeSort (CommAlgebraCat R) (Type v) :=
  ⟨CommAlgebraCat.carrier⟩

attribute [coe] CommAlgebraCat.carrier

instance : Category (CommAlgebraCat.{v} R) where
  Hom A B := A →ₐ[R] B
  id A := AlgHom.id R A
  comp f g := g.comp f

instance {M N : CommAlgebraCat.{v} R} : FunLike (M ⟶ N) M N :=
  AlgHom.funLike

instance {M N : CommAlgebraCat.{v} R} : AlgHomClass (M ⟶ N) R M N :=
  AlgHom.algHomClass

instance : ConcreteCategory.{v} (CommAlgebraCat.{v} R) where
  forget :=
    { obj := fun R => R
      map := fun f => f.toFun }
  forget_faithful := ⟨fun h => AlgHom.ext (by intros x; dsimp at h; rw [h])⟩

instance {S : CommAlgebraCat.{v} R} : Ring ((forget (CommAlgebraCat R)).obj S) :=
  (inferInstance : Ring S.carrier)

instance {S : CommAlgebraCat.{v} R} : Algebra R ((forget (CommAlgebraCat R)).obj S) :=
  (inferInstance : Algebra R S.carrier)

instance hasForgetToRing : HasForget₂ (CommAlgebraCat.{v} R) RingCat.{v} where
  forget₂ :=
    { obj := fun A => RingCat.of A
      map := fun f => RingCat.ofHom f.toRingHom }
#align Algebra.has_forget_to_Ring CommAlgebraCat.hasForgetToRing

instance hasForgetToModule : HasForget₂ (CommAlgebraCat.{v} R) (ModuleCat.{v} R) where
  forget₂ :=
    { obj := fun M => ModuleCat.of R M
      map := fun f => ModuleCat.ofHom f.toLinearMap }
#align Algebra.has_forget_to_Module CommAlgebraCat.hasForgetToModule

@[simp]
lemma forget₂_module_obj (X : CommAlgebraCat.{v} R) :
    (forget₂ (CommAlgebraCat.{v} R) (ModuleCat.{v} R)).obj X = ModuleCat.of R X :=
  rfl

@[simp]
lemma forget₂_module_map {X Y : CommAlgebraCat.{v} R} (f : X ⟶ Y) :
    (forget₂ (CommAlgebraCat.{v} R) (ModuleCat.{v} R)).map f = ModuleCat.ofHom f.toLinearMap :=
  rfl

/-- The object in the category of R-algebras associated to a type equipped with the appropriate
typeclasses. -/
def of (X : Type v) [CommRing X] [Algebra R X] : CommAlgebraCat.{v} R :=
  ⟨X⟩
/-- Typecheck a `AlgHom` as a morphism in `CommAlgebraCat R`. -/
def ofHom {R : Type u} [CommRing R] {X Y : Type v} [CommRing X] [Algebra R X] [CommRing Y] [Algebra R Y]
    (f : X →ₐ[R] Y) : of R X ⟶ of R Y :=
  f
#align Algebra.of_hom CommAlgebraCat.ofHom

@[simp]
theorem ofHom_apply {R : Type u} [CommRing R] {X Y : Type v} [CommRing X] [Algebra R X] [CommRing Y]
    [Algebra R Y] (f : X →ₐ[R] Y) (x : X) : ofHom f x = f x :=
  rfl
#align Algebra.of_hom_apply CommAlgebraCat.ofHom_apply

instance : Inhabited (CommAlgebraCat R) :=
  ⟨of R R⟩

@[simp]
theorem coe_of (X : Type u) [CommRing X] [Algebra R X] : (of R X : Type u) = X :=
  rfl
#align Algebra.coe_of CommAlgebraCat.coe_of

variable {R}

/-- Forgetting to the underlying type and then building the bundled object returns the original
algebra. -/
@[simps]
def ofSelfIso (M : CommAlgebraCat.{v} R) : CommAlgebraCat.of R M ≅ M where
  hom := 𝟙 M
  inv := 𝟙 M
#align Algebra.of_self_iso CommAlgebraCat.ofSelfIso

variable {M N U : ModuleCat.{v} R}

@[simp]
theorem id_apply (m : M) : (𝟙 M : M → M) m = m :=
  rfl
#align Algebra.id_apply CommAlgebraCat.id_apply

@[simp]
theorem coe_comp (f : M ⟶ N) (g : N ⟶ U) : (f ≫ g : M → U) = g ∘ f :=
  rfl

-- variable (R)

-- /-- The "free algebra" functor, sending a type `S` to the free algebra on `S`. -/
-- @[simps!]
-- def free : Type u ⥤ CommAlgebraCat.{u} R where
--   obj S :=
--     { carrier := FreeAlgebra R S
--       isRing := Algebra.commSemiringToCommRing R }
--   map f := FreeAlgebra.lift _ <| FreeAlgebra.ι _ ∘ f
--   -- Porting note: `apply FreeAlgebra.hom_ext` was `ext1`.
--   map_id := by intro X; apply FreeAlgebra.hom_ext; simp only [FreeAlgebra.ι_comp_lift]; rfl
--   map_comp := by
--   -- Porting note: `apply FreeAlgebra.hom_ext` was `ext1`.
--     intros; apply FreeAlgebra.hom_ext; simp only [FreeAlgebra.ι_comp_lift]; ext1
--     -- Porting node: this ↓ `erw` used to be handled by the `simp` below it
--     erw [CategoryTheory.coe_comp]
--     simp only [CategoryTheory.coe_comp, Function.comp_apply, types_comp_apply]
--     -- Porting node: this ↓ `erw` and `rfl` used to be handled by the `simp` above
--     erw [FreeAlgebra.lift_ι_apply, FreeAlgebra.lift_ι_apply]
--     rfl
-- #align Algebra.free CommAlgebraCat.free

-- /-- The free/forget adjunction for `R`-algebras. -/
-- def adj : free.{u} R ⊣ forget (CommAlgebraCat.{u} R) :=
--   Adjunction.mkOfHomEquiv
--     { homEquiv := fun X A => (FreeAlgebra.lift _).symm
--       -- Relying on `obviously` to fill out these proofs is very slow :(
--       homEquiv_naturality_left_symm := by
--         -- Porting note: `apply FreeAlgebra.hom_ext` was `ext1`.
--         intros; apply FreeAlgebra.hom_ext; simp only [FreeAlgebra.ι_comp_lift]; ext1
--         simp only [free_map, Equiv.symm_symm, FreeAlgebra.lift_ι_apply, CategoryTheory.coe_comp,
--           Function.comp_apply, types_comp_apply]
--         -- Porting node: this ↓ `erw` and `rfl` used to be handled by the `simp` above
--         erw [FreeAlgebra.lift_ι_apply, CategoryTheory.comp_apply, FreeAlgebra.lift_ι_apply,
--           Function.comp_apply, FreeAlgebra.lift_ι_apply]
--         rfl
--       homEquiv_naturality_right := by
--         intros; ext
--         simp only [CategoryTheory.coe_comp, Function.comp_apply,
--           FreeAlgebra.lift_symm_apply, types_comp_apply]
--         -- Porting note: proof used to be done after this ↑ `simp`; added ↓ two lines
--         erw [FreeAlgebra.lift_symm_apply, FreeAlgebra.lift_symm_apply]
--         rfl }
-- #align Algebra.adj CommAlgebraCat.adj

-- instance : IsRightAdjoint (forget (CommAlgebraCat.{u} R)) :=
--   ⟨_, adj R⟩

end CommAlgebraCat

variable {R}

variable {X₁ X₂ : Type u}

/-- Build an isomorphism in the category `CommAlgebraCat R` from a `AlgEquiv` between `Algebra`s. -/
@[simps]
def AlgEquiv.toAlgebraIso {g₁ : CommRing X₁} {g₂ : CommRing X₂} {m₁ : Algebra R X₁} {m₂ : Algebra R X₂}
    (e : X₁ ≃ₐ[R] X₂) : CommAlgebraCat.of R X₁ ≅ CommAlgebraCat.of R X₂ where
  hom := (e : X₁ →ₐ[R] X₂)
  inv := (e.symm : X₂ →ₐ[R] X₁)
  hom_inv_id := by ext x; exact e.left_inv x
  inv_hom_id := by ext x; exact e.right_inv x
#align alg_equiv.to_Algebra_iso AlgEquiv.toAlgebraIso

namespace CategoryTheory.Iso

/-- Build a `AlgEquiv` from an isomorphism in the category `CommAlgebraCat R`. -/
@[simps]
def toAlgEquiv {X Y : CommAlgebraCat R} (i : X ≅ Y) : X ≃ₐ[R] Y where
  toFun := i.hom
  invFun := i.inv
  left_inv x := by
    -- Porting note: was `by tidy`
    change (i.hom ≫ i.inv) x = x
    simp only [hom_inv_id]
    -- This used to be `rw`, but we need `erw` after leanprover/lean4#2644
    erw [id_apply]
  right_inv x := by
    -- Porting note: was `by tidy`
    change (i.inv ≫ i.hom) x = x
    simp only [inv_hom_id]
    -- This used to be `rw`, but we need `erw` after leanprover/lean4#2644
    erw [id_apply]
  map_add' := by aesop
  map_mul' := by aesop
  commutes' := i.hom.commutes -- Porting note: was `by tidy`
#align category_theory.iso.to_alg_equiv CategoryTheory.Iso.toAlgEquiv

end CategoryTheory.Iso

/-- Algebra equivalences between `Algebra`s are the same as (isomorphic to) isomorphisms in
`CommAlgebraCat`. -/
@[simps]
def algEquivIsoAlgebraIso {X Y : Type u} [CommRing X] [CommRing Y] [Algebra R X] [Algebra R Y] :
    (X ≃ₐ[R] Y) ≅ CommAlgebraCat.of R X ≅ CommAlgebraCat.of R Y where
  hom e := e.toAlgebraIso
  inv i := i.toAlgEquiv
#align alg_equiv_iso_Algebra_iso algEquivIsoAlgebraIso

-- Porting note: changed to `CoeOut`
instance (X : Type u) [CommRing X] [Algebra R X] : CoeOut (Subalgebra R X) (CommAlgebraCat R) :=
  ⟨fun N => CommAlgebraCat.of R N⟩

instance CommAlgebraCat.forget_reflects_isos : ReflectsIsomorphisms (forget (CommAlgebraCat.{u} R)) where
  reflects {X Y} f _ := by
    let i := asIso ((forget (CommAlgebraCat.{u} R)).map f)
    let e : X ≃ₐ[R] Y := { f, i.toEquiv with }
    exact ⟨(IsIso.of_iso e.toAlgebraIso).1⟩
#align Algebra.forget_reflects_isos CommAlgebraCat.forget_reflects_isos
