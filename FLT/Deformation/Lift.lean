import FLT.Deformation.BaseCat
import FLT.Deformation.IsResidueAlgebra
import FLT.Deformation.RepresentationTheory.RepresentationEquiv
import FLT.Mathlib.RepresentationTheory.Basic
import FLT.Mathlib.Algebra.Module.Equiv.Defs
import FLT.Deformation.ContinuousRepresentation.TopologicalModule
import FLT.Deformation.ContinuousRepresentation.FreeFiniteModuleTopology
import FLT.Deformation.ContinuousRepresentation.Basic

universe u

open CategoryTheory Function
open scoped TensorProduct Deformation

namespace Deformation

variable {𝓞 : Type u}
  [CommRing 𝓞] [IsLocalRing 𝓞] [IsNoetherianRing 𝓞]

variable {V : Type u}
  [AddCommGroup V] [Module (𝓴 𝓞) V] [Module.Free (𝓴 𝓞) V] [Module.Finite (𝓴 𝓞) V]

variable {G : Type u} [Group G] [TopologicalSpace G] [TopologicalGroup G]

variable (ρbar : @ContinuousRepresentation (𝓴 𝓞) _ ⊥ (by sorry) G _ _ _ V _ _ ⊥ (by sorry))

variable {ι : Type*} [Fintype ι]

section Definitions

variable (A : 𝓒 𝓞)
  [Module (𝓴 A) V] [IsScalarTower (𝓴 A) (𝓴 𝓞) V]
  [Module A V] [IsScalarTower A (𝓴 A) V]

variable {W: Type u} [AddCommGroup W] [Module A W] [Module.Free A W] [Module.Finite A W]
  [TopologicalSpace W] [TopologicalModule A W]

variable (reduction : ((𝓴 A) ⊗[A] W) ≃ₛₗ[algebraMap (𝓴 A) (𝓴 𝓞)] V)

variable (ρ: ContinuousRepresentation A G W)

variable (W V) in
noncomputable def extend_ctts : W →ₗ[A] ((𝓴 A) ⊗[A] W) :=
  (TensorProduct.mk A (𝓴 A) W) (1 : (𝓴 A))

variable (V W) in
noncomputable def mod_ctts : ((𝓴 A) ⊗[A] W) →ₗ[A] V where
  toFun kaw := reduction kaw
  map_add' := by simp
  map_smul' := by
    simp only [RingHom.id_apply]
    rintro m x
    sorry
    -- rw [LinearEquiv.map_smulₛₗ reduction]

variable (W V) in
noncomputable def representation_mod : W →ₗ[A] V :=
  (mod_ctts V A W reduction).comp (extend_ctts A W)

end Definitions

section Lift

variable (A : 𝓒 𝓞)

structure Lift : Type _ where
  W: Type _
  -- Basic structure on carrier
  [addCommGroup : AddCommGroup W]
  [module : Module A W]
  [free : Module.Free A W]
  [finite : Module.Finite A W]
  -- Topology W
  [topo : TopologicalSpace W]
  [topo_module : TopologicalModule A W]
  -- Reduction
  reduction : ((𝓴 A) ⊗[A] W) ≃ₛₗ[algebraMap (𝓴 A) (𝓴 𝓞)] V
  -- Scalar products on V. This is saying that V has A-module some structure
  -- and this "some" is precisely the obvious one via algebraMap A kA algebraMap kA kO
  [module_A : Module A V]
  [module_𝓴A : Module (𝓴 A) V]
  [isScalarTower_𝓴A : IsScalarTower (𝓴 A) (𝓴 𝓞) V]
  [isScalarTower_A : IsScalarTower A (𝓴 A) V]
  -- G-Representation on W as A-module
  ρ: ContinuousRepresentation A G W
  -- Lift property
  is_lift: ∀ g : G, ∀ w : W, ρbar g (representation_mod V A W reduction w)
      = representation_mod V A W reduction (ρ g w)

attribute [instance] Lift.addCommGroup Lift.module Lift.free Lift.finite

def Lift.isIso : Setoid (Lift ρbar A) where
  r l l' := Representation.IsRepresentationEquiv (l.ρ : Representation A G l.W) (l'.ρ : Representation A G l'.W)
  iseqv := {
    refl := by
      unfold Representation.IsRepresentationEquiv
      rintro l
      use LinearEquiv.id l.W
      rintro g
      unfold LinearEquiv.id
      aesop
    symm := by
      unfold Representation.IsRepresentationEquiv
      rintro x y ⟨φ, φ_prop⟩
      use φ.symm
      rintro g
      sorry
    trans := by
      unfold Representation.IsRepresentationEquiv
      rintro x y z ⟨φ, φ_prop⟩ ⟨φ', φ'_prop⟩
      use LinearEquiv.comp' φ φ'
      sorry
  }

end Lift

section UnrestrictedFunctor

def Lift.functor_onMap {A B : 𝓒 𝓞} (f : A ⟶ B) (l : Lift ρbar A) : Lift ρbar B where
  W := letI : Algebra A B := f.hom.toAlgebra; l.W ⊗[A] B
  addCommGroup := sorry
  module := sorry
  free := sorry
  finite := sorry
  topo := sorry
  topo_module := sorry
  reduction := sorry
  module_A := sorry
  module_𝓴A := sorry
  isScalarTower_𝓴A := sorry
  isScalarTower_A := sorry
  ρ := sorry
  is_lift := sorry

variable (𝓞) in
def Lift.functor : CategoryTheory.Functor (𝓒 𝓞) (Type (u+1)) where
  obj A := Lift ρbar A
  map f l := Lift.functor_onMap ρbar f l
  map_id := sorry
  map_comp := sorry

theorem Lift.functor_isCorepresentable : (Lift.functor 𝓞 ρbar).IsCorepresentable := sorry

end UnrestrictedFunctor

end Deformation
