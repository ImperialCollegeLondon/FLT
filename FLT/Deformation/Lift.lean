import FLT.Deformation.BaseCat
import FLT.Deformation.RepresentationTheory.RepresentationEquiv
import FLT.Mathlib.RepresentationTheory.Basic
import FLT.Mathlib.Algebra.Module.Equiv.Defs
import FLT.Deformation.ContinuousRepresentation.IsTopologicalModule
import FLT.Deformation.ContinuousRepresentation.FreeFiniteModuleTopology
import FLT.Deformation.ContinuousRepresentation.Basic

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

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

def 𝓴𝓞_topology : TopologicalSpace (𝓴 𝓞) := ⊥

def 𝓴𝓞_discrete : @DiscreteTopology (𝓴 𝓞) 𝓴𝓞_topology := by
  letI : TopologicalSpace (𝓴 𝓞) := 𝓴𝓞_topology
  exact {
    eq_bot := rfl
  }

def 𝓴𝓞_isTopologicalRing : @IsTopologicalRing (𝓴 𝓞) 𝓴𝓞_topology _ := by
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
def V_isTopologicalModule : @IsTopologicalModule (𝓴 𝓞) _ 𝓴𝓞_topology 𝓴𝓞_isTopologicalRing V _ _ V_topology := by
  letI : TopologicalSpace (𝓴 𝓞) := 𝓴𝓞_topology
  letI := 𝓴𝓞_isTopologicalRing (𝓞 := 𝓞)
  letI := 𝓴𝓞_discrete (𝓞 := 𝓞)
  letI := V_topology (V := V)
  letI := V_discrete (V := V)
  exact DiscreteTopology.isTopologicalModule

variable (ρbar : @ContinuousRepresentation (𝓴 𝓞) _ 𝓴𝓞_topology 𝓴𝓞_isTopologicalRing
  G _ _ _ V _ _ V_topology V_isTopologicalModule)

variable {ι : Type*} [Fintype ι]
section Definitions

variable (A : 𝓒 𝓞)

noncomputable abbrev modMapInv := (IsResidueAlgebra.ringEquiv 𝓞 A).symm.toRingHom

variable [Module (𝓴 A) V] [IsScalarTower (𝓴 A) (𝓴 𝓞) V]
  [Module A V] [IsScalarTower A (𝓴 A) V]

variable (W: Type*) [AddCommGroup W] [Module A W] [Module.Free A W] [Module.Finite A W]
  [TopologicalSpace W] [IsTopologicalModule A W]

variable (reduction : ((𝓴 A) ⊗[A] W) ≃ₛₗ[modMapInv A] V)

variable (ρ: ContinuousRepresentation A G W)

noncomputable def extend_ctts : W →ₗ[A] ((𝓴 A) ⊗[A] W) :=
  (TensorProduct.mk A (𝓴 A) W) (1 : (𝓴 A))

noncomputable def mod_ctts : ((𝓴 A) ⊗[A] W) →ₗ[A] V where
  toFun kaw := reduction kaw
  map_add' := by simp
  map_smul' := by
    simp only [RingHom.id_apply]
    rintro a x
    change reduction (algebraMap A (𝓴 A) a • x) = _
    have h_tower1 (a : A) (v : V) : a • v = algebraMap A (𝓴 A) a • v := by
      exact algebra_compatible_smul (𝓴 A) a v
    have h_tower2 (ka : 𝓴 A) (v : V) : ka • v = (ka • (1 : (𝓴 𝓞))) • v := by
      exact Eq.symm (smul_one_smul (𝓴 𝓞) ka v)
    have h_tower3 (ka : 𝓴 A) : (ka • (1 : 𝓴 𝓞)) = (IsResidueAlgebra.ringEquiv 𝓞 A).symm ka * (1 : 𝓴 𝓞) := rfl
    rw [LinearEquiv.map_smulₛₗ reduction, h_tower1, h_tower2, h_tower3]
    simp

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
  reduction : ((𝓴 A) ⊗[A] carrier) ≃ₛₗ[modMapInv A] V
  -- Scalar products on V. This is saying that V has A-module some structure
  -- and this "some" is precisely the obvious one via algebraMap A kA algebraMap kA kO
  [module_𝓴A : Module (𝓴 A) V]
  [isScalarTower_𝓴A : IsScalarTower (𝓴 A) (𝓴 𝓞) V]
  [module_A : Module A V]
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

section UnrestrictedFunctor

variable {V}
variable {A B : 𝓒 𝓞} (f : A ⟶ B) (l : Lift ρbar A)

noncomputable def relModMap (f : A ⟶ B) : (𝓴 A) ≃+* (𝓴 B) := .ofBijective
  (IsLocalRing.ResidueField.map f.hom) ⟨sorry, sorry⟩

noncomputable abbrev relModMapInv := (Deformation.relModMap f).symm.toRingHom

instance relModMap_ringHomInvPair₁ : RingHomInvPair (relModMap f).toRingHom (relModMapInv f) :=
  RingHomInvPair.of_ringEquiv (relModMap f)

instance relModMap_ringHomInvPair₂ : RingHomInvPair (relModMapInv f) (relModMap f).toRingHom :=
  RingHomInvPair.of_ringEquiv (relModMap f).symm

variable {ρbar l} in
def onMap_reduction :
  letI : Algebra A B := f.hom.toAlgebra;
  (𝓴 B) ⊗[B] (B ⊗[A] l.carrier) ≃ₛₗ[relModMapInv f] (𝓴 A) ⊗[A] l.carrier := sorry

instance : RingHomCompTriple (relModMapInv f) (modMapInv A) (modMapInv B) := sorry

instance : RingHomCompTriple (IsResidueAlgebra.ringEquiv 𝓞 A).toRingHom (relModMap f).toRingHom
    (IsResidueAlgebra.ringEquiv 𝓞 B).toRingHom := sorry

noncomputable def Lift.functor_onMap : Lift ρbar B :=
  letI : Algebra A B := f.hom.toAlgebra
  letI : TopologicalSpace (B ⊗[A] l.carrier) := freeFiniteModuleProductTopology B (B ⊗[A] l.carrier)
  letI : IsTopologicalModule B (B ⊗[A] l.carrier) := freeFiniteModuleProductTopology_topologicalModule
  {
    carrier := B ⊗[A] l.carrier
    addCommGroup := by infer_instance
    module := by infer_instance
    free := by infer_instance
    finite := by infer_instance
    reduction := LinearEquiv.trans (onMap_reduction f) l.reduction
    module_A := Module.compHom V (RingHom.comp (modMapInv B) (IsLocalRing.residue B))
    module_𝓴A := Module.compHom V (modMapInv B)
    isScalarTower_𝓴A := sorry
    isScalarTower_A := sorry
    ρ := {
      toFun g := TensorProduct.lift _
      map_one' := sorry
      map_mul' := sorry
      continuous := sorry
    }
    is_lift := sorry
  }

variable (𝓞) in
noncomputable def Lift.functor : CategoryTheory.Functor (𝓒 𝓞) (Type _) where
  obj A := Lift ρbar A
  map f l := Lift.functor_onMap ρbar f l
  map_id := sorry
  map_comp := sorry

theorem Lift.functor_isCorepresentable : (Lift.functor 𝓞 ρbar).IsCorepresentable := sorry

end UnrestrictedFunctor

end Deformation
