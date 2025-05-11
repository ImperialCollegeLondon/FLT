import FLT.Deformation.BaseCat
import FLT.Deformation.RepresentationTheory.RepresentationEquiv
import FLT.Mathlib.RepresentationTheory.Basic
import FLT.Mathlib.Algebra.Module.Equiv.Defs
import FLT.Deformation.ContinuousRepresentation.IsTopologicalModule
import FLT.Deformation.Lift
import FLT.Deformation.Topology.Algebra.OpenIdeal

open CategoryTheory Function
open scoped TensorProduct Deformation

namespace Deformation

/-!
# The Deformation Functor
- Setting is the same as for the Lift functor
- Deformation functor is the Lift functor quotiented by ≃ᵣ
!-/

variable {𝓞 : Type*}
  [CommRing 𝓞] [IsLocalRing 𝓞] [IsNoetherianRing 𝓞]

variable {V : Type*}
  [AddCommGroup V] [Module (𝓴 𝓞) V] [Module.Free (𝓴 𝓞) V] [Module.Finite (𝓴 𝓞) V]
  [Module 𝓞 V] [IsScalarTower 𝓞 (𝓴 𝓞) V]

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

variable (ρbar : @ContinuousRepresentation (𝓴 𝓞) _ 𝓴𝓞_topology 𝓴𝓞_isTopologicalRing
  G _ _ _ V _ _ V_topology V_isTopologicalModule)

variable (A : 𝓒 𝓞)

def _root_.Deformation := Quotient (Lift.isIso ρbar A)
section UnrestrictedDeformationFunctor -- Theorem 2.3 of Smit&Lenstra

omit A in
def functor_onMap {A B : 𝓒 𝓞} (f : A ⟶ B) (D : Deformation ρbar A) : Deformation ρbar B :=
  sorry

variable (𝓞) in
def functor : CategoryTheory.Functor (𝓒 𝓞) (Type _) where
  obj A := Deformation ρbar A
  map f := Deformation.functor_onMap ρbar f
  map_id := sorry
  map_comp := sorry

end UnrestrictedDeformationFunctor

section RestrictedDeformationFunctor -- Section 6 of Smit&Lenstra

variable {A ρbar} in
def quotient (D : Deformation ρbar A) (a : OpenIdeal A) [Nontrivial (A ⧸ a.1)]: Deformation ρbar (A.quotient a) := sorry

variable {A ρbar} in
def tensorProduct (D : Deformation ρbar A) (R : 𝓒 𝓞) [Algebra A R] : Deformation ρbar R := sorry

class IsValidDeformationRestriction (res : (R : 𝓒 𝓞) → Set (Deformation ρbar R)) : Prop where
  cond1 : ∀ A : 𝓒 𝓞, ∀ D : Deformation ρbar A,
    (D ∈ res A) ↔ (∀ a : OpenIdeal A, ∀ _ : Nontrivial (A ⧸ a.1), (D.quotient a) ∈ res (A.quotient a))
  cond2 : ∀ A : 𝓒 𝓞, ∀ D : Deformation ρbar A, ∀ a b : OpenIdeal A,
    ∀ _ : Nontrivial (A ⧸ a.1), ∀ _ : Nontrivial (A ⧸ b.1), ∀ _ : Nontrivial (A ⧸ (a ⊓ b).1),
    ((D.quotient a) ∈ res (A.quotient a) ∧ (D.quotient b) ∈ res (A.quotient b) →
      D.quotient (a ⊓ b)  ∈ res (A.quotient (a ⊓ b)))
  cond3 : ∀ A A' : 𝓒 𝓞, ∀ ι : A  →+* A', ∃ _ : Function.Injective ι,
    ∃ _ : IsArtinianRing A, ∃ _ : IsArtinianRing A',
    ∀ D : Deformation ρbar A, (D ∈ res A) ↔ ((D.tensorProduct A) ∈ res A)

variable (res : (R : 𝓒 𝓞) → Set (Deformation ρbar R))
variable [IsValidDeformationRestriction ρbar res]

omit A in
def restrictedFunctor_onMap {A B : 𝓒 𝓞} (f : A ⟶ B) (D : res A) : (res B) :=
  ⟨Deformation.functor_onMap ρbar f D, sorry⟩

variable (𝓞) in
def restrictedFunctor : CategoryTheory.Functor (𝓒 𝓞) (Type _) where
  obj A := res A
  map f := Deformation.restrictedFunctor_onMap ρbar res f
  map_id X := sorry
  map_comp := sorry

end RestrictedDeformationFunctor

end Deformation
