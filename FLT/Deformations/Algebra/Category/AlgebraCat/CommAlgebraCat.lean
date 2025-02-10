/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Algebra.FreeAlgebra
import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.RingTheory.Ideal.Defs
import FLT.Mathlib.Algebra.Algebra.Defs

/-!
# Category instance for algebras over a commutative ring

We introduce the bundled category `CommAlgebraCat` of commutative algebras over a fixed commutative ring `R` along
with the forgetful functors to `CommRingCat` and `ModuleCat`.
-/

open CategoryTheory Limits

universe v u

variable (R : Type u) [CommRing R]

/-- The category of R-algebras and their morphisms. -/
structure CommAlgebraCat where
  private mk ::
  /-- The underlying type. -/
  carrier : Type v
  [isCommRing : CommRing carrier]
  [isAlgebra : Algebra R carrier]

-- Porting note: typemax hack to fix universe complaints
/-- An alias for `CommAlgebraCat.{max u₁ u₂}`, to deal around unification issues.
Since the universe the ring lives in can be inferred, we put that last. -/
@[nolint checkUnivs]
abbrev CommAlgebraCatMax.{v₁, v₂, u₁} (R : Type u₁) [CommRing R] := CommAlgebraCat.{max v₁ v₂} R

attribute [instance] CommAlgebraCat.isCommRing CommAlgebraCat.isAlgebra

initialize_simps_projections CommAlgebraCat (-isCommRing, -isAlgebra)

namespace CommAlgebraCat

instance : CoeSort (CommAlgebraCat R) (Type v) :=
  ⟨CommAlgebraCat.carrier⟩

attribute [coe] CommAlgebraCat.carrier

/-- The object in the category of commutative R-algebras associated to a type equipped with the appropriate
typeclasses. This is the preferred way to construct a term of `CommAlgebraCat R`. -/
abbrev of (X : Type v) [CommRing X] [Algebra R X] : CommAlgebraCat.{v} R :=
  ⟨X⟩

lemma coe_of (X : Type v) [CommRing X] [Algebra R X] : (of R X : Type v) = X :=
  rfl

variable {R} in
/-- The type of morphisms in `CommAlgebraCat R`. -/
@[ext]
structure Hom (A B : CommAlgebraCat.{v} R) where
  private mk ::
  /-- The underlying algebra map. -/
  hom' : A →ₐ[R] B

instance : Category (CommAlgebraCat.{v} R) where
  Hom A B := Hom A B
  id A := ⟨AlgHom.id R A⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩

instance : ConcreteCategory (CommAlgebraCat.{v} R) (· →ₐ[R] ·) where
  hom := Hom.hom'
  ofHom := Hom.mk

variable {R} in
/-- Turn a morphism in `CommAlgebraCat` back into an `AlgHom`. -/
abbrev Hom.hom {A B : CommAlgebraCat.{v} R} (f : Hom A B) :=
  ConcreteCategory.hom (C := CommAlgebraCat R) f

variable {R} in
/-- Typecheck an `AlgHom` as a morphism in `CommAlgebraCat`. -/
abbrev ofHom {A B : Type v} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B] (f : A →ₐ[R] B) :
    of R A ⟶ of R B :=
  ConcreteCategory.ofHom (C := CommAlgebraCat R) f

variable {R} in
/-- Use the `ConcreteCategory.hom` projection for `@[simps]` lemmas. -/
def Hom.Simps.hom (A B : CommAlgebraCat.{v} R) (f : Hom A B) :=
  f.hom

initialize_simps_projections Hom (hom' → hom)

/-!
The results below duplicate the `ConcreteCategory` simp lemmas, but we can keep them for `dsimp`.
-/

@[simp]
lemma hom_id {A : CommAlgebraCat.{v} R} : (𝟙 A : A ⟶ A).hom = AlgHom.id R A := rfl

/- Provided for rewriting. -/
lemma id_apply (A : CommAlgebraCat.{v} R) (a : A) :
    (𝟙 A : A ⟶ A) a = a := by simp

@[simp]
lemma hom_comp {A B C : CommAlgebraCat.{v} R} (f : A ⟶ B) (g : B ⟶ C) :
    (f ≫ g).hom = g.hom.comp f.hom := rfl

/- Provided for rewriting. -/
lemma comp_apply {A B C : CommAlgebraCat.{v} R} (f : A ⟶ B) (g : B ⟶ C) (a : A) :
    (f ≫ g) a = g (f a) := by simp

@[ext]
lemma hom_ext {A B : CommAlgebraCat.{v} R} {f g : A ⟶ B} (hf : f.hom = g.hom) : f = g :=
  Hom.ext hf

@[simp]
lemma hom_ofHom {R : Type u} [CommRing R] {X Y : Type v} [CommRing X] [Algebra R X] [CommRing Y]
    [Algebra R Y] (f : X →ₐ[R] Y) : (ofHom f).hom = f := rfl

@[simp]
lemma ofHom_hom {A B : CommAlgebraCat.{v} R} (f : A ⟶ B) :
    ofHom (Hom.hom f) = f := rfl

@[simp]
lemma ofHom_id {X : Type v} [CommRing X] [Algebra R X] : ofHom (AlgHom.id R X) = 𝟙 (of R X) := rfl

@[simp]
lemma ofHom_comp {X Y Z : Type v} [CommRing X] [CommRing Y] [CommRing Z] [Algebra R X] [Algebra R Y]
    [Algebra R Z] (f : X →ₐ[R] Y) (g : Y →ₐ[R] Z) :
    ofHom (g.comp f) = ofHom f ≫ ofHom g :=
  rfl

lemma ofHom_apply {R : Type u} [CommRing R] {X Y : Type v} [CommRing X] [Algebra R X] [CommRing Y]
    [Algebra R Y] (f : X →ₐ[R] Y) (x : X) : ofHom f x = f x := rfl

@[simp]
lemma inv_hom_apply {A B : CommAlgebraCat.{v} R} (e : A ≅ B) (x : A) : e.inv (e.hom x) = x := by
  rw [← comp_apply]
  simp

@[simp]
lemma hom_inv_apply {A B : CommAlgebraCat.{v} R} (e : A ≅ B) (x : B) : e.hom (e.inv x) = x := by
  rw [← comp_apply]
  simp

instance : Inhabited (CommAlgebraCat R) :=
  ⟨of R R⟩

lemma forget_obj {A : CommAlgebraCat.{v} R} : (forget (CommAlgebraCat.{v} R)).obj A = A := rfl

lemma forget_map {A B : CommAlgebraCat.{v} R} (f : A ⟶ B) :
    (forget (CommAlgebraCat.{v} R)).map f = f :=
  rfl

instance {S : CommAlgebraCat.{v} R} : CommRing ((forget (CommAlgebraCat R)).obj S) :=
  (inferInstance : CommRing S.carrier)

instance {S : CommAlgebraCat.{v} R} : Algebra R ((forget (CommAlgebraCat R)).obj S) :=
  (inferInstance : Algebra R S.carrier)

instance hasForgetToCommRing : HasForget₂ (CommAlgebraCat.{v} R) CommRingCat.{v} where
  forget₂ :=
    { obj := fun A => CommRingCat.of A
      map := fun f => CommRingCat.ofHom f.hom.toRingHom }

instance hasForgetToModule : HasForget₂ (CommAlgebraCat.{v} R) (ModuleCat.{v} R) where
  forget₂ :=
    { obj := fun M => ModuleCat.of R M
      map := fun f => ModuleCat.ofHom f.hom.toLinearMap }

@[simp]
lemma forget₂_module_obj (X : CommAlgebraCat.{v} R) :
    (forget₂ (CommAlgebraCat.{v} R) (ModuleCat.{v} R)).obj X = ModuleCat.of R X :=
  rfl

@[simp]
lemma forget₂_module_map {X Y : CommAlgebraCat.{v} R} (f : X ⟶ Y) :
    (forget₂ (CommAlgebraCat.{v} R) (ModuleCat.{v} R)).map f = ModuleCat.ofHom f.hom.toLinearMap :=
  rfl

variable {R} in
/-- Forgetting to the underlying type and then building the bundled object returns the original
algebra. -/
@[simps]
def ofSelfIso (M : CommAlgebraCat.{v} R) : CommAlgebraCat.of R M ≅ M where
  hom := 𝟙 M
  inv := 𝟙 M

variable {R} in
def quotient {X : CommAlgebraCat.{v} R} (a : Ideal X)
    : CommAlgebraCat.{v} R := of R (X ⧸ a)

end CommAlgebraCat

variable {R}
variable {X₁ X₂ : Type u}

/-- Build an isomorphism in the category `CommAlgebraCat R` from a `AlgEquiv` between `Algebra`s. -/
@[simps]
def AlgEquiv.toCommAlgebraIso {g₁ : CommRing X₁} {g₂ : CommRing X₂} {m₁ : Algebra R X₁} {m₂ : Algebra R X₂}
    (e : X₁ ≃ₐ[R] X₂) : CommAlgebraCat.of R X₁ ≅ CommAlgebraCat.of R X₂ where
  hom := CommAlgebraCat.ofHom (e : X₁ →ₐ[R] X₂)
  inv := CommAlgebraCat.ofHom (e.symm : X₂ →ₐ[R] X₁)

namespace CategoryTheory.Iso

/-- Build a `AlgEquiv` from an isomorphism in the category `CommAlgebraCat R`. -/
@[simps]
def toCommAlgEquiv {X Y : CommAlgebraCat R} (i : X ≅ Y) : X ≃ₐ[R] Y :=
  { i.hom.hom with
    toFun := i.hom
    invFun := i.inv
    left_inv := fun x ↦ by simp
    right_inv := fun x ↦ by simp }

end CategoryTheory.Iso

/-- Algebra equivalences between `CommAlgebra`s are the same as (isomorphic to) isomorphisms in
`CommAlgebraCat`. -/
@[simps]
def commAlgEquivIsoCommAlgebraIso {X Y : Type u} [CommRing X] [CommRing Y] [Algebra R X] [Algebra R Y] :
    (X ≃ₐ[R] Y) ≅ CommAlgebraCat.of R X ≅ CommAlgebraCat.of R Y where
  hom e := e.toCommAlgebraIso
  inv i := i.toCommAlgEquiv

instance CommAlgebraCat.forget_reflects_isos : (forget (CommAlgebraCat.{u} R)).ReflectsIsomorphisms where
  reflects {X Y} f _ := by
    let i := asIso ((forget (CommAlgebraCat.{u} R)).map f)
    let e : X ≃ₐ[R] Y := { f.hom, i.toEquiv with }
    exact e.toCommAlgebraIso.isIso_hom
