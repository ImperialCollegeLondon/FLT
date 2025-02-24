import FLT.Deformation.Algebra.Category.AlgebraCat.CommAlgebraCat
import FLT.Deformation.Proartinian
import FLT.Deformation.ResidueAlgebra
import FLT.Mathlib.Algebra.Group.Units.Hom

set_option linter.unusedSectionVars false

universe v u

open CategoryTheory Function Limits

namespace Deformation

variable (𝓞 : Type u)
  [CommRing 𝓞] [IsLocalRing 𝓞] [IsNoetherianRing 𝓞]

scoped notation3:max "𝓴" 𝓞 => (IsLocalRing.ResidueField 𝓞)

structure BaseCat where
  private mk ::
  carrier : Type v
  [isCommRing : CommRing carrier]
  [isAlgebra : Algebra 𝓞 carrier]
  [isLocalRing : IsLocalRing carrier]
  [isLocalHom : IsLocalHom (algebraMap 𝓞 carrier)]
  [isResidueAlgebra : IsResidueAlgebra 𝓞 carrier]
  [isProartinian : IsProartinian carrier]

scoped notation3:max "𝓒" 𝓞 => BaseCat 𝓞

-- Porting note: typemax hack to fix universe complaints
/-- An alias for `BaseCat.{max u₁ u₂}`, to deal around unification issues.
Since the universe the ring lives in can be inferred, we put that last. -/
@[nolint checkUnivs]
abbrev BaseCatMax.{v₁, v₂, u₁} (𝓞 : Type u₁) [CommRing 𝓞] [IsLocalRing 𝓞] [IsNoetherianRing 𝓞] :=
  BaseCat.{max v₁ v₂} 𝓞

attribute [instance] BaseCat.isCommRing BaseCat.isAlgebra BaseCat.isLocalRing BaseCat.isLocalHom
  BaseCat.isResidueAlgebra BaseCat.isProartinian

initialize_simps_projections BaseCat (-isCommRing, -isAlgebra, -isLocalRing, -isLocalHom,
  -isResidueAlgebra, -isProartinian)

namespace BaseCat

instance : CoeSort (BaseCat 𝓞) (Type v) :=
  ⟨BaseCat.carrier⟩

attribute [coe] BaseCat.carrier

abbrev of (X : Type v) [CommRing X] [Algebra 𝓞 X] [IsLocalRing X] [IsLocalHom (algebraMap 𝓞 X)]
  [IsResidueAlgebra 𝓞 X] [IsProartinian X] : BaseCat.{v} 𝓞 :=
  ⟨X⟩

lemma coe_of (X : Type v) [CommRing X] [Algebra 𝓞 X] [IsLocalRing X] [IsLocalHom (algebraMap 𝓞 X)]
  [IsResidueAlgebra 𝓞 X] [IsProartinian X] : (of 𝓞 X : Type v) = X := rfl

variable {𝓞} in
/-- The type of morphisms in `BaseCat 𝓞`. -/
@[ext]
structure Hom (A B : BaseCat.{v} 𝓞) where
  private mk ::
  /-- The underlying algebra map. -/
  hom' : A →A[𝓞] B

instance : Category (BaseCat.{v} 𝓞) where
  Hom A B := Hom A B
  id A := ⟨ContinuousAlgHom.id 𝓞 A⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩

instance : ConcreteCategory (BaseCat.{v} 𝓞) (· →A[𝓞] ·) where
  hom := Hom.hom'
  ofHom := Hom.mk

variable {𝓞} in
/-- Turn a morphism in `BaseCat` back into an `ContinuousAlgHom`. -/
abbrev Hom.hom {A B : BaseCat.{v} 𝓞} (f : Hom A B) :=
  ConcreteCategory.hom (C := BaseCat 𝓞) f

variable {𝓞} in
/-- Typecheck an `ContinuousAlgHom` as a morphism in `BaseCat`. -/
abbrev ofHom {A B : Type v}
  [CommRing A] [Algebra 𝓞 A] [IsLocalRing A] [IsLocalHom (algebraMap 𝓞 A)]
  [IsResidueAlgebra 𝓞 A] [IsProartinian A]
  [CommRing B] [Algebra 𝓞 B] [IsLocalRing B] [IsLocalHom (algebraMap 𝓞 B)]
  [IsResidueAlgebra 𝓞 B] [IsProartinian B]
  (f : A →A[𝓞] B) :
    of 𝓞 A ⟶ of 𝓞 B :=
  ConcreteCategory.ofHom (C := BaseCat 𝓞) f

variable {𝓞} in
/-- Use the `ConcreteCategory.hom` projection for `@[simps]` lemmas. -/
def Hom.Simps.hom (A B : BaseCat.{v} 𝓞) (f : Hom A B) :=
  f.hom

initialize_simps_projections Hom (hom' → hom)

------------------------------------------------------------
variable {𝓞}

variable {X Y Z : Type v}
  [CommRing X] [Algebra 𝓞 X] [IsLocalRing X] [IsLocalHom (algebraMap 𝓞 X)]
  [IsResidueAlgebra 𝓞 X] [IsProartinian X]
  [CommRing Y] [Algebra 𝓞 Y] [IsLocalRing Y] [IsLocalHom (algebraMap 𝓞 Y)]
  [IsResidueAlgebra 𝓞 Y] [IsProartinian Y]
  [CommRing Z] [Algebra 𝓞 Z] [IsLocalRing Z] [IsLocalHom (algebraMap 𝓞 Z)]
  [IsResidueAlgebra 𝓞 Z] [IsProartinian Z]

variable {A B C : BaseCat.{v} 𝓞}

@[simp]
lemma hom_id : (𝟙 A : A ⟶ A).hom = ContinuousAlgHom.id 𝓞 A := rfl

/- Provided for rewriting. -/
lemma id_apply (a : A) : (𝟙 A : A ⟶ A) a = a := by simp

@[simp]
lemma hom_comp (f : A ⟶ B) (g : B ⟶ C) : (f ≫ g).hom = g.hom.comp f.hom := rfl

/- Provided for rewriting. -/
lemma comp_apply (f : A ⟶ B) (g : B ⟶ C) (a : A) :
    (f ≫ g) a = g (f a) := by simp

@[ext]
lemma hom_ext {f g : A ⟶ B} (hf : f.hom = g.hom) : f = g :=
  Hom.ext hf

@[simp]
lemma hom_ofHom (f : X →A[𝓞] Y) : (ofHom f).hom = f := rfl

@[simp]
lemma ofHom_hom (f : A ⟶ B) : ofHom (Hom.hom f) = f := rfl

@[simp]
lemma ofHom_id : ofHom (ContinuousAlgHom.id 𝓞 X) = 𝟙 (of 𝓞 X) := rfl

@[simp]
lemma ofHom_comp (f : X →A[𝓞] Y) (g : Y →A[𝓞] Z) :
    ofHom (g.comp f) = ofHom f ≫ ofHom g :=
  rfl

lemma ofHom_apply (f : X →A[𝓞] Y) (x : X) : ofHom f x = f x := rfl

@[simp]
lemma inv_hom_apply (e : A ≅ B) (x : A) : e.inv (e.hom x) = x := by
  rw [← comp_apply]
  simp

@[simp]
lemma hom_inv_apply (e : A ≅ B) (x : B) : e.hom (e.inv x) = x := by
  rw [← comp_apply]
  simp

-- TODO(jlcontreras): why is 𝓞 in BaseCat 𝓞
-- instance : Inhabited (BaseCat 𝓞) := ⟨of 𝓞 𝓞⟩

lemma forget_obj : (forget (BaseCat.{v} 𝓞)).obj A = A := rfl

lemma forget_map (f : A ⟶ B) : (forget (BaseCat.{v} 𝓞)).map f = f := rfl

instance : CommRing ((forget (BaseCat 𝓞)).obj A) := (inferInstance : CommRing A.carrier)

instance : Algebra 𝓞 ((forget (BaseCat 𝓞)).obj A) := (inferInstance : Algebra 𝓞 A.carrier)

instance hasForgetToCommRing : HasForget₂ (BaseCat.{v} 𝓞) CommRingCat.{v} where
  forget₂ :=
    { obj := fun A => CommRingCat.of A
      map := fun f => CommRingCat.ofHom f.hom.toRingHom }

instance hasForgetToModule : HasForget₂ (BaseCat.{v} 𝓞) (ModuleCat.{v} 𝓞) where
  forget₂ :=
    { obj := fun M => ModuleCat.of 𝓞 M
      map := fun f => ModuleCat.ofHom f.hom.toLinearMap }

@[simp]
lemma forget₂_module_obj :
    (forget₂ (BaseCat.{v} 𝓞) (ModuleCat.{v} 𝓞)).obj A = ModuleCat.of 𝓞 A :=
  rfl

@[simp]
lemma forget₂_module_map (f : A ⟶ B) :
    (forget₂ (BaseCat.{v} 𝓞) (ModuleCat.{v} 𝓞)).map f = ModuleCat.ofHom f.hom.toLinearMap :=
  rfl

/-- Forgetting to the underlying type and then building the bundled object returns the original
algebra. -/
@[simps]
def ofSelfIso : of 𝓞 A ≅ A where
  hom := 𝟙 A
  inv := 𝟙 A

def quotient (a : Ideal A) [a.NeqTop] : BaseCat.{v} 𝓞 where
  carrier := A ⧸ a
  isCommRing := by infer_instance
  isAlgebra := by infer_instance
  isLocalRing := isLocalRing_of_quotient a
  isLocalHom := by sorry -- isLocalHom_of_quotient (algebraMap 𝓞 A) a
  isResidueAlgebra := by infer_instance
  isProartinian := by infer_instance

end BaseCat

variable {𝓞}
variable {X Y : Type u}
  [CommRing X] [Algebra 𝓞 X] [IsLocalRing X] [IsLocalHom (algebraMap 𝓞 X)]
  [IsResidueAlgebra 𝓞 X] [IsProartinian X]
  [CommRing Y] [Algebra 𝓞 Y] [IsLocalRing Y] [IsLocalHom (algebraMap 𝓞 Y)]
  [IsResidueAlgebra 𝓞 Y] [IsProartinian Y]
variable {A B : BaseCat 𝓞}

/-- Build an isomorphism in the category `BaseCat R` from a `ContinuousAlgEquiv` between `Algebra`s. -/
@[simps]
def _root_.ContinuousAlgEquiv.toContinuousAlgebraIso (e : X ≃A[𝓞] Y) : BaseCat.of 𝓞 X ≅ BaseCat.of 𝓞 Y where
  hom := BaseCat.ofHom (e : X →A[𝓞] Y)
  inv := BaseCat.ofHom (e.symm : Y →A[𝓞] X)

/-- Build a `ContinuousAlgEquiv` from an isomorphism in the category `BaseCat R`. -/
@[simps]
def _root_.CategoryTheory.Iso.toContinuousAlgEquiv (i : A ≅ B) : A ≃A[𝓞] B :=
  {i.hom.hom  with
    toFun := i.hom
    invFun := i.inv
    left_inv := fun x ↦ by simp
    right_inv := fun x ↦ by simp
    continuous_toFun := by continuity}

/-- Continuous Algebra equivalences between `Algebra`s are the same as (isomorphic to) isomorphisms in
`BaseCat`. -/
@[simps]
def _root_.continuousAlgEquivIsoContinuousAlgebraIso : (X ≃A[𝓞] Y) ≅ BaseCat.of 𝓞 X ≅ BaseCat.of 𝓞 Y where
  hom e := e.toContinuousAlgebraIso
  inv i := i.toContinuousAlgEquiv

instance BaseCat.forget_reflects_isos : (forget (BaseCat.{u} 𝓞)).ReflectsIsomorphisms where
  reflects {X Y} f _ := by
    let i := asIso ((forget (BaseCat.{u} 𝓞)).map f)
    let e : X ≃A[𝓞] Y := {
        f.hom, i.toEquiv with
        continuous_invFun := by
          simp
          sorry
      }
    exact e.toContinuousAlgebraIso.isIso_hom

section Noetherian -- Proposition 2.4 of Smit&Lenstra

variable (A : 𝓒 𝓞) [IsNoetherianRing A]

instance noetherian_topology
    : IsAdic (IsLocalRing.maximalIdeal A) := by
  exact IsProartinian.noetherian_topology A

instance noetherian_isAdic
    : IsAdicComplete (IsLocalRing.maximalIdeal A) A := by
  exact IsProartinian.noetherian_isAdic A

lemma noetherian_continuous (A' : 𝓒 𝓞) (f : A →ₐ[𝓞] A')
    : Continuous f := by
  exact IsProartinian.noetherian_continuous A A' f

end Noetherian

end Deformation
