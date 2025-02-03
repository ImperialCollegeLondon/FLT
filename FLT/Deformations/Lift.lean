import FLT.Deformations.BaseCategory
import FLT.Deformations.RepresentationTheory.RepresentationEquiv
import FLT.Mathlib.RepresentationTheory.Basic
import FLT.Mathlib.Algebra.Module.Equiv.Defs

universe u

open CategoryTheory Function
open scoped TensorProduct

variable {𝓞 : Type u}
  [CommRing 𝓞] [IsLocalRing 𝓞] [IsNoetherianRing 𝓞]

local notation3:max "𝓴" 𝓞 => (IsLocalRing.ResidueField 𝓞)

variable {V : Type u}
  [AddCommMonoid V] [Module (𝓴 𝓞) V] [Module.Free (𝓴 𝓞) V] [Module.Finite (𝓴 𝓞) V]

variable {G : Type u} [Group G] [TopologicalSpace G] [TopologicalGroup G]

variable (ρbar : Representation (𝓴 𝓞) G V)

variable (A : 𝓒 𝓞)
variable [Module (𝓴 A) V] [IsScalarTower (𝓴 A) (𝓴 𝓞) V]
variable [Module A V] [IsScalarTower A (𝓴 A) V]

variable {W: Type u} [AddCommMonoid W] [Module A W] [Module.Free A W] [Module.Finite A W]

variable {ι : Type*} [Fintype ι]

variable (reduction : LinearEquiv
  (algebraMap (𝓴 A) (𝓴 𝓞))
  ((𝓴 A) ⊗[A] W)
  V)

variable (ρ: Representation A G W)

section Definition

variable (W V) in
noncomputable def extend_ctts : W →ₗ[A] ((𝓴 A) ⊗[A] W) :=
  (TensorProduct.mk A (𝓴 A) W) (1 : (𝓴 A))

variable (V W) in
noncomputable def mod_ctts : ((𝓴 A) ⊗[A] W) →ₗ[A] V where
  toFun kaw := reduction kaw
  map_add' := by simp
  map_smul' := by
    simp
    rintro m x
    sorry -- TODO: why is rw [LinearEquiv.map_smulₛₗ reduction] not matching?

variable (W V) in
noncomputable def representation_mod : W →ₗ[A] V :=
  (mod_ctts V A W reduction).comp (extend_ctts A W)

instance {A W : Type*} [CommRing A] [TopologicalSpace A] [TopologicalRing A]
    [AddCommMonoid W] [Module A W] [Module.Free A W] [Module.Finite A W] [TopologicalSpace W]
    [is_prod_topo : Nonempty (W ≃ₜ (Module.Free.ChooseBasisIndex A W → A))]
  : TopologicalSpace (W →ₗ[A] W) := sorry

omit W reduction in
structure Lift : Type _ where
  W: Type _
  -- Basic structure on carrier
  [addCommMonoid : AddCommMonoid W]
  [module : Module A W]
  [free : Module.Free A W]
  [finite : Module.Finite A W]
  -- Topology W
  [topo : TopologicalSpace W]
  [is_prod_topo : Nonempty (W ≃ₜ (Module.Free.ChooseBasisIndex A W → A.obj))]
  -- Reduction
  reduction : ((𝓴 A) ⊗[A] W) ≃ₛₗ[algebraMap (𝓴 A) (𝓴 𝓞)] V
  -- Scalar products on W
  [module_A : Module A V]
  [module_𝓴A : Module (𝓴 A) V]
  [isScalarTower_𝓴A : IsScalarTower (𝓴 A) (𝓴 𝓞) V]
  [isScalarTower_A : IsScalarTower A (𝓴 A) V]
  -- G-Representation on W as A-module
  ρ: Representation A G W
  is_cont: Continuous ρ
  -- Lift property
  is_lift: ∀ g : G, ∀ w : W, ρbar g (representation_mod V A W reduction w)
      = representation_mod V A W reduction (ρ g w)

attribute [instance] Lift.addCommMonoid Lift.module Lift.free Lift.finite

def Lift.isIso : Setoid (Lift ρbar A) where
  r l l' := Representation.IsRepresentationEquiv l.ρ l'.ρ
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

end Definition
section UnrestrictedFunctor

omit A in
def Lift.functor_onMap {A B : 𝓒 𝓞} (f : A ⟶ B) (l : Lift ρbar A) : Lift ρbar B where
  W := letI : Algebra A B := f.hom.toAlgebra; l.W ⊗[A] B
  addCommMonoid := sorry
  module := sorry
  free := sorry
  finite := sorry
  topo := sorry
  is_prod_topo := sorry
  reduction := sorry
  module_A := sorry
  module_𝓴A := sorry
  isScalarTower_𝓴A := sorry
  isScalarTower_A := sorry
  ρ := sorry
  is_cont := sorry
  is_lift := sorry

variable (𝓞) in
def Lift.functor : CategoryTheory.Functor (𝓒 𝓞) (Type (u+1)) where
  obj A := Lift ρbar A
  map f l := Lift.functor_onMap ρbar f l
  map_id := sorry
  map_comp := sorry

theorem Lift.functor_isCorepresentable : (Lift.functor 𝓞 ρbar).IsCorepresentable := sorry

end UnrestrictedFunctor
