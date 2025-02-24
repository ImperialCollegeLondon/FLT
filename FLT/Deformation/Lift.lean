import FLT.Deformation.BaseCat
import FLT.Deformation.IsResidueAlgebra
import FLT.Deformation.RepresentationTheory.RepresentationEquiv
import FLT.Mathlib.RepresentationTheory.Basic
import FLT.Mathlib.Algebra.Module.Equiv.Defs
import FLT.Deformation.ContinuousRepresentation.TopologicalModule
import FLT.Deformation.ContinuousRepresentation.FreeFiniteModuleTopology
import FLT.Deformation.ContinuousRepresentation.Basic

open CategoryTheory Function
open scoped TensorProduct Deformation

namespace Deformation

variable {𝓞 : Type*}
  [CommRing 𝓞] [IsLocalRing 𝓞] [IsNoetherianRing 𝓞]

variable (V : Type*)
  [AddCommGroup V] [Module (𝓴 𝓞) V] [Module.Free (𝓴 𝓞) V] [Module.Finite (𝓴 𝓞) V]

variable {G : Type*} [Group G] [TopologicalSpace G] [TopologicalGroup G]

def 𝓴𝓞_topology : TopologicalSpace (𝓴 𝓞) := ⊥

def 𝓴𝓞_discrete : @DiscreteTopology (𝓴 𝓞) 𝓴𝓞_topology := by
  letI : TopologicalSpace (𝓴 𝓞) := 𝓴𝓞_topology
  exact {
    eq_bot := rfl
  }

def 𝓴𝓞_topologicalRing : @TopologicalRing (𝓴 𝓞) 𝓴𝓞_topology _ := by
  letI : TopologicalSpace (𝓴 𝓞) := 𝓴𝓞_topology
  letI := 𝓴𝓞_discrete (𝓞 := 𝓞)
  exact DiscreteTopology.topologicalRing

variable {V} in
def V_topology : TopologicalSpace V := ⊥

variable {V} in
def V_discrete : @DiscreteTopology V V_topology := by
  letI : TopologicalSpace V := V_topology
  exact {
    eq_bot := rfl
  }

variable {V} in
def V_topologicalModule : @TopologicalModule (𝓴 𝓞) _ 𝓴𝓞_topology 𝓴𝓞_topologicalRing V _ _ V_topology := by
  letI : TopologicalSpace (𝓴 𝓞) := 𝓴𝓞_topology
  letI := 𝓴𝓞_topologicalRing (𝓞 := 𝓞)
  letI := 𝓴𝓞_discrete (𝓞 := 𝓞)
  letI := V_topology (V := V)
  letI := V_discrete (V := V)
  exact {
    continuous_smul := by continuity
    continuous_add := by continuity
  }

variable (ρbar : @ContinuousRepresentation (𝓴 𝓞) _ ⊥ 𝓴𝓞_topologicalRing
  G _ _ _ V _ _ V_topology V_topologicalModule)

variable {ι : Type*} [Fintype ι]
section Definitions

variable (A : 𝓒 𝓞) [Module (𝓴 A) V] [IsScalarTower (𝓴 𝓞) (𝓴 A) V]
  [Module A V] [IsScalarTower A (𝓴 A) V]

variable (W: Type*) [AddCommGroup W] [Module A W] [Module.Free A W] [Module.Finite A W]
  [TopologicalSpace W] [TopologicalModule A W]

variable (reduction : ((𝓴 A) ⊗[A] W) ≃ₛₗ[(IsResidueAlgebra.ringEquiv 𝓞 A).symm.toRingHom] V)

variable (ρ: ContinuousRepresentation A G W)

noncomputable def extend_ctts : W →ₗ[A] ((𝓴 A) ⊗[A] W) :=
  (TensorProduct.mk A (𝓴 A) W) (1 : (𝓴 A))

noncomputable def mod_ctts : ((𝓴 A) ⊗[A] W) →ₗ[A] V where
  toFun kaw := reduction kaw
  map_add' := by simp
  map_smul' := by
    simp only [RingHom.id_apply]
    rintro a x
    change reduction (algebraMap A (𝓴 A) a • x) = a • reduction x
    have h : ∀ v : V, a • v = algebraMap (𝓴 A) (𝓴 𝓞) (algebraMap A (𝓴 A) a) • v := by
      intro v
      have : a • v = ((a • (1 : 𝓴 A)) • (1 : 𝓴 𝓞)) • v := by
        rw [smul_assoc, one_smul, smul_assoc, one_smul]
      have : algebraMap A (𝓴 A) a = a • (1 : 𝓴 A) := by
        unfold HSMul.hSMul instHSMul SMul.smul Algebra.toSMul
        simp [IsLocalRing.ResidueField.algebra, IsLocalRing.residue]
        sorry -- This is probably a mathlib issue, AFAIK this whole "have" should just be rfl, right?
      rw [this]
      aesop
    rw [h (reduction x), LinearEquiv.map_smulₛₗ reduction]

noncomputable def representation_mod : W →ₗ[A] V :=
  (mod_ctts V A W reduction).comp (extend_ctts A W)

end Definitions

section Lift

variable (A : 𝓒 𝓞)
variable {V}

structure Lift : Type _ where
  carrier: Type _
  -- Basic structure on carrier
  [addCommGroup : AddCommGroup carrier]
  [module : Module A carrier]
  [free : Module.Free A carrier]
  [finite : Module.Finite A carrier]
  -- Reduction
  reduction : ((𝓴 A) ⊗[A] carrier) ≃ₛₗ[algebraMap (𝓴 A) (𝓴 𝓞)] V
  -- Scalar products on V. This is saying that V has A-module some structure
  -- and this "some" is precisely the obvious one via algebraMap A kA algebraMap kA kO
  [module_A : Module A V]
  [module_𝓴A : Module (𝓴 A) V]
  [isScalarTower_𝓴A : IsScalarTower (𝓴 A) (𝓴 𝓞) V]
  [isScalarTower_A : IsScalarTower A (𝓴 A) V]
  -- G-Representation on carrier as A-module
  ρ: @ContinuousRepresentation A _ _ _ G _ _ _ carrier _ _
      (freeFiniteModuleProductTopology A carrier) (freeFiniteModuleProductTopology_topologicalModule)
  -- Lift property
  is_lift: ∀ g : G, ∀ w : carrier, ρbar g (representation_mod V A carrier reduction w)
      = representation_mod V A carrier reduction (ρ g w)

attribute [instance] Lift.addCommGroup Lift.module Lift.free Lift.finite

def Lift.isIso : Setoid (Lift ρbar A) where
  r l l' := Representation.IsRepresentationEquiv (l.ρ : Representation A G l.carrier) (l'.ρ : Representation A G l'.carrier)
  iseqv := {
    refl := by
      unfold Representation.IsRepresentationEquiv
      rintro l
      use LinearEquiv.id l.carrier
      rintro g
      unfold LinearEquiv.id
      aesop
    symm := by
      unfold Representation.IsRepresentationEquiv
      rintro x y ⟨φ, φ_prop⟩
      use φ.symm
      rintro g
      ext x
      sorry
    trans := by
      unfold Representation.IsRepresentationEquiv
      rintro x y z ⟨φ, φ_prop⟩ ⟨φ', φ'_prop⟩
      use LinearEquiv.comp' φ φ'
      sorry
  }

end Lift

section UnrestrictedFunctor

variable {V}

noncomputable def Lift.functor_onMap {A B : 𝓒 𝓞} (f : A ⟶ B) (l : Lift ρbar A) : Lift ρbar B where
  carrier := letI : Algebra A B := f.hom.toAlgebra; B ⊗[A] l.carrier
  addCommGroup := by infer_instance
  module := by infer_instance
  free := by infer_instance
  finite := by infer_instance
  reduction := sorry
  module_A := sorry
  module_𝓴A := sorry
  isScalarTower_𝓴A := sorry
  isScalarTower_A := sorry
  ρ := sorry
  is_lift := sorry

variable (𝓞) in
noncomputable def Lift.functor : CategoryTheory.Functor (𝓒 𝓞) (Type _) where
  obj A := Lift ρbar A
  map f l := Lift.functor_onMap ρbar f l
  map_id := sorry
  map_comp := sorry

theorem Lift.functor_isCorepresentable : (Lift.functor 𝓞 ρbar).IsCorepresentable := sorry

end UnrestrictedFunctor

end Deformation
