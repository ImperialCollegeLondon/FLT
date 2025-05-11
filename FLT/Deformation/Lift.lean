import FLT.Deformation.BaseCat
import FLT.Deformation.RepresentationTheory.RepresentationEquiv
import FLT.Mathlib.RepresentationTheory.Basic
import FLT.Mathlib.Algebra.Module.Equiv.Defs
import FLT.Deformation.ContinuousRepresentation.IsTopologicalModule

open CategoryTheory Function
open scoped TensorProduct Deformation

namespace Deformation

/-!
# The Lift Functor
- `G` is a topological group
- `𝓴 X` is notation for the residue field of `{X : Type*} [CommRing X] [IsLocalRing X]`
- `𝓞` is a `CommRing, IsLocalRing, IsNoetherianRing` and represents the Witt Vectors of `(𝓴 𝓞) = k`, `k` is topologized discretely
- `V` is a continuous `k`-representation of `G`, represented in `ρbar`, topologized discretely
- `A` is an object of the category `BaseCat 𝓞` which makes it
  - `CommRing`
  - `Algebra 𝓞`
  - `IsLocalRing A`
  - `IsLocalHom (algebraMap A (𝓴 A))`
  - `IsResidueAlgebra 𝓞` (meaning its residue field is isomorphic to `k` via the canonical algebraMap)
  - `IsProartinianRing` (meaning its isomorphic, via the diagonal map, to the inverse limit of its artinian quotients, and gets topologized by induced topology over this isomorphism, where the RHS is topologized as the InverseLimit topology where each quotient is topologized discretely)
- `W` is a continuous `A`-representation of `G`, represented in `ρ`, topologized with the ProArtinian topology
- `reduction` is the isomorphism between `W` after extending constants to `𝓴 A` and `V`
!-/

variable {𝓞 : Type*}
  [CommRing 𝓞] [IsLocalRing 𝓞] [IsNoetherianRing 𝓞]

variable (V : Type*)
  [AddCommGroup V] [Module (𝓴 𝓞) V] [Module.Free (𝓴 𝓞) V] [Module.Finite (𝓴 𝓞) V]
  [Module 𝓞 V] [IsScalarTower 𝓞 (𝓴 𝓞) V]

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

def 𝓴𝓞_topology : TopologicalSpace (𝓴 𝓞) := ⊥

def 𝓴𝓞_discrete : @DiscreteTopology (𝓴 𝓞) 𝓴𝓞_topology :=
  letI : TopologicalSpace (𝓴 𝓞) := 𝓴𝓞_topology
  {
    eq_bot := rfl
  }

def 𝓴𝓞_isTopologicalRing : @IsTopologicalRing (𝓴 𝓞) 𝓴𝓞_topology _ :=
  letI : TopologicalSpace (𝓴 𝓞) := 𝓴𝓞_topology
  letI := 𝓴𝓞_discrete (𝓞 := 𝓞)
  DiscreteTopology.topologicalRing

variable {V} in
def V_topology : TopologicalSpace V := ⊥

variable {V} in
def V_discrete : @DiscreteTopology V V_topology :=
  letI : TopologicalSpace V := V_topology
  {
    eq_bot := rfl
  }

variable {V} in
def V_isTopologicalModule : @IsTopologicalModule (𝓴 𝓞) _ 𝓴𝓞_topology 𝓴𝓞_isTopologicalRing V _ _ V_topology :=
  letI : TopologicalSpace (𝓴 𝓞) := 𝓴𝓞_topology
  letI := 𝓴𝓞_isTopologicalRing (𝓞 := 𝓞)
  letI := 𝓴𝓞_discrete (𝓞 := 𝓞)
  letI := V_topology (V := V)
  letI := V_discrete (V := V)
  DiscreteTopology.isTopologicalModule

variable (ρbar : @ContinuousRepresentation (𝓴 𝓞) _ 𝓴𝓞_topology 𝓴𝓞_isTopologicalRing
  G _ _ _ V _ _ V_topology V_isTopologicalModule)

variable {ι : Type*} [Fintype ι]
section Definitions

variable (A : 𝓒 𝓞)

variable (W: Type*) [AddCommGroup W] [Module A W] [Module.Free A W] [Module.Finite A W]
  [TopologicalSpace W] [IsTopologicalModule A W]
  [Module 𝓞 W] [IsScalarTower 𝓞 A W]

variable (reduction : ((𝓴 A) ⊗[A] W) ≃ₗ[𝓞] V)

variable (ρ: ContinuousRepresentation A G W)

noncomputable def extend_ctts : W →ₗ[𝓞] ((𝓴 A) ⊗[A] W) :=
  (TensorProduct.mk A (𝓴 A) W) (1 : (𝓴 A))

noncomputable def representation_mod : W →ₗ[𝓞] V :=
  (reduction).comp (extend_ctts A W)

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
  reduction : ((𝓴 A) ⊗[A] carrier) ≃ₗ[𝓞] V
  [module_carrier : Module 𝓞 carrier]
  [isScalarTower_carrier : IsScalarTower 𝓞 A carrier]
  -- G-Representation on carrier as A-module
  ρ: @ContinuousRepresentation A _ _ _ G _ _ _ carrier _ _
      (freeFiniteModuleProductTopology A carrier) (freeFiniteModuleProductTopology_topologicalModule)
  -- Lift property
  is_lift: ∀ g : G, ∀ w : carrier, ρbar g (representation_mod V A carrier reduction w)
      = representation_mod V A carrier reduction (ρ g w)

attribute [instance] Lift.addCommGroup Lift.module Lift.free Lift.finite
  Lift.module_carrier Lift.isScalarTower_carrier

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
      rintro l l' ⟨φ, φ_prop⟩
      use φ.symm
      rintro g
      calc
        φ.symm ∘ (l'.ρ g) = φ.symm ∘ (l'.ρ g) ∘ (φ ∘ φ.symm) := by aesop
        _ = φ.symm ∘ ((l'.ρ g) ∘ φ) ∘ φ.symm := by aesop
        _ = φ.symm ∘ (φ ∘ (l.ρ g)) ∘ φ.symm := by erw [← φ_prop g]; rfl
        _ = (φ.symm ∘ φ) ∘ (l.ρ g) ∘ φ.symm := by aesop
        _ = (l.ρ g) ∘ φ.symm := by aesop
    trans := by
      unfold Representation.IsRepresentationEquiv
      rintro x y z ⟨φ, φ_prop⟩ ⟨φ', φ'_prop⟩
      use LinearEquiv.comp' φ φ'
      rintro g
      calc
        _ = φ' ∘ (φ ∘ (x.ρ g)) := by aesop
        _ = φ' ∘ ((y.ρ g) ∘ φ) := by erw [φ_prop g]; rfl
        _ = (φ' ∘ (y.ρ g)) ∘ φ := by aesop
        _ = ((z.ρ g) ∘ φ') ∘ φ := by erw [φ'_prop g]; rfl
        _ = (z.ρ g) ∘ (φ' ∘ φ) := by aesop
        _ = _ := by aesop
    }

end Lift

section UnrestrictedLiftFunctor

variable {V ρbar}
variable {A B : 𝓒 𝓞} (f : A ⟶ B) (l : Lift ρbar A)

def onMap_reduction' :
    letI : Algebra A B := f.hom.toAlgebra;
    letI : IsLocalHom (algebraMap A B) := f.isLocalHom
    letI : IsScalarTower 𝓞 A B := .of_algHom f.hom.toAlgHom
    letI : IsResidueAlgebra A B := IsResidueAlgebra.of_restrictScalars (𝓞 := 𝓞)
    (𝓴 B) ⊗[B] (B ⊗[A] l.carrier) ≃ₗ[A] ((𝓴 B) ⊗[B] B) ⊗[A] l.carrier := sorry
    -- this should be a general fact: extension of scalar twice

variable (B) in
def onMap_reduction'' :
    (𝓴 B) ⊗[B] B ≃ₗ[B] 𝓴 B := sorry
  -- this should be a general fact: tensoring by the constants does nothing

noncomputable def onMap_reduction :
    letI : Algebra A B := f.hom.toAlgebra;
    letI : IsLocalHom (algebraMap A B) := f.isLocalHom
    letI : IsScalarTower 𝓞 A B := .of_algHom f.hom.toAlgHom
    letI : IsResidueAlgebra A B := IsResidueAlgebra.of_restrictScalars (𝓞 := 𝓞)
    (𝓴 B) ⊗[B] (B ⊗[A] l.carrier) ≃ₗ[A] (𝓴 A) ⊗[A] l.carrier :=
  letI : Algebra A B := f.hom.toAlgebra;
  letI : IsLocalHom (algebraMap A B) := f.isLocalHom
  letI : IsScalarTower 𝓞 A B := .of_algHom f.hom.toAlgHom
  letI : IsResidueAlgebra A B := IsResidueAlgebra.of_restrictScalars (𝓞 := 𝓞)
  let ekBB_kB : (𝓴 B) ⊗[B] B ≃ₗ[A] (𝓴 B) := (onMap_reduction'' B).restrictScalars A
  let ekB_kA : (𝓴 B) ≃ₗ[A] (𝓴 A) := (IsResidueAlgebra.algEquiv A B).symm.toLinearEquiv
  onMap_reduction' f l ≪≫ₗ (ekBB_kB ≪≫ₗ ekB_kA).rTensor l.carrier

noncomputable def onMap_ρ :
    letI : Algebra A B := f.hom.toAlgebra;
    letI : TopologicalSpace (B ⊗[A] l.carrier) := freeFiniteModuleProductTopology B (B ⊗[A] l.carrier)
    letI : IsTopologicalModule B (B ⊗[A] l.carrier) := freeFiniteModuleProductTopology_topologicalModule
    ContinuousRepresentation B G (B ⊗[A] l.carrier) :=
  letI : Algebra A B := f.hom.toAlgebra;
  letI : TopologicalSpace (B ⊗[A] l.carrier) := freeFiniteModuleProductTopology B (B ⊗[A] l.carrier)
  letI : IsTopologicalModule B (B ⊗[A] l.carrier) := freeFiniteModuleProductTopology_topologicalModule
  {
    toFun g := LinearMap.baseChange B ((l.ρ : Representation _ _ _) g)
    map_one' := by aesop
    map_mul' := by aesop
    continuous := by sorry
  }

noncomputable def Lift.functor_onMap : Lift ρbar B :=
  letI : Algebra A B := f.hom.toAlgebra;
  letI : IsLocalHom (algebraMap A B) := f.isLocalHom
  letI : IsScalarTower 𝓞 A B := .of_algHom f.hom.toAlgHom
  letI : IsResidueAlgebra A B := IsResidueAlgebra.of_restrictScalars (𝓞 := 𝓞)
  letI : TopologicalSpace (B ⊗[A] l.carrier) := freeFiniteModuleProductTopology B (B ⊗[A] l.carrier)
  letI : IsTopologicalModule B (B ⊗[A] l.carrier) := freeFiniteModuleProductTopology_topologicalModule
  {
    carrier := B ⊗[A] l.carrier
    addCommGroup := by infer_instance
    module := by infer_instance
    free := by infer_instance
    finite := by infer_instance
    reduction := LinearEquiv.trans ((onMap_reduction f l).restrictScalars 𝓞) l.reduction
    module_carrier := by infer_instance
    isScalarTower_carrier := by infer_instance
    ρ := onMap_ρ f l
    is_lift g w := by sorry
  }

variable (𝓞 ρbar) in
noncomputable def Lift.functor : CategoryTheory.Functor (𝓒 𝓞) (Type _) where
  obj A := Lift ρbar A
  map {A B} f (l : Lift ρbar A) := ((Lift.functor_onMap f l) : Lift ρbar B)
  map_id A := by
    ext l
    simp at l
    sorry
  map_comp {A B C} f g := by
    ext l
    simp at l
    sorry

end UnrestrictedLiftFunctor

end Deformation
