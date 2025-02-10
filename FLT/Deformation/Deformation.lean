import Mathlib
import FLT.Deformation.BaseCategory
import FLT.Deformation.Lift

universe u

open scoped TensorProduct Deformation

namespace Deformation

variable {𝓞 : Type u}
  [CommRing 𝓞] [IsLocalRing 𝓞] [IsNoetherianRing 𝓞]

variable {V : Type u}
  [AddCommMonoid V] [Module (𝓴 𝓞) V] [Module.Free (𝓴 𝓞) V] [Module.Finite (𝓴 𝓞) V]

variable {G : Type u} [Group G] [TopologicalSpace G] [TopologicalGroup G]

variable (ρbar : Representation (𝓴 𝓞) G V)

variable (A : 𝓒 𝓞)

def Deformation := Quotient <| Lift.isIso ρbar A

def OpenIdeal := {a : Ideal A // IsOpen a.carrier}

instance : Coe (OpenIdeal A) (Ideal A) where
  coe a := a.1

variable {A ρbar} in
def Deformation.quotient (D : Deformation ρbar A) (a : Ideal A) : Deformation ρbar (A.quotient a) := sorry

variable {A ρbar} in
def Deformation.tensorProduct (D : Deformation ρbar A) (R : 𝓒 𝓞) [Algebra A R] : Deformation ρbar R := sorry

section UnrestrictedFunctor -- Theorem 2.3 of Smit&Lenstra

omit A in
def Deformation.functor_onMap {A B : 𝓒 𝓞} (f : A ⟶ B) (D :  Deformation ρbar A) : Deformation ρbar B :=
  sorry

variable (𝓞) in
def Deformation.functor : CategoryTheory.Functor (𝓒 𝓞) (Type _) where
  obj A := Deformation ρbar A
  map f := Deformation.functor_onMap ρbar f
  map_id := sorry
  map_comp := sorry

-- Theorem 2.3
theorem Deformation.functor_isCorepresentable : (Deformation.functor 𝓞 ρbar).IsCorepresentable  := sorry

end UnrestrictedFunctor

section RestrictedFunctor -- Section 6 of Smit&Lenstra

class IsValidDeformationRestriction (res : (R : 𝓒 𝓞) → Set (Deformation ρbar R)) : Prop where
  cond1 : ∀ A : 𝓒 𝓞, ∀ D : Deformation ρbar A,
    (D ∈ res A) ↔ (∀ a : OpenIdeal A, (D.quotient a) ∈ res (A.quotient a))
  cond2 : ∀ A : 𝓒 𝓞, ∀ D : Deformation ρbar A, ∀ a b : OpenIdeal A,
    ∃ _: (a : Ideal A) ≠ ⊤, ∃ _: (b : Ideal A) ≠ ⊤,
    ((D.quotient a) ∈ res (A.quotient a) ∧ (D.quotient b) ∈ res (A.quotient b) →
      D.quotient (a ⊓ b) ∈ res (A.quotient (a ⊓ b)))
  cond3 : ∀ A A' : 𝓒 𝓞, ∀ ι : A  →+* A', ∃ _ : Function.Injective ι,
    ∃ _ : IsArtinianRing A, ∃ _ : IsArtinianRing A',
    ∀ D : Deformation ρbar A, (D ∈ res A) ↔ ((D.tensorProduct A) ∈ res A)

variable (res : (R : 𝓒 𝓞) → Set (Deformation ρbar R))
variable [IsValidDeformationRestriction ρbar res]

omit A in
def Deformation.restrictedFunctor_onMap {A B : 𝓒 𝓞} (f : A ⟶ B) (D : res A) : (res B) :=
  ⟨Deformation.functor_onMap ρbar f D, sorry⟩

variable (𝓞) in
def Deformation.restrictedFunctor : CategoryTheory.Functor (𝓒 𝓞) (Type _) where
  obj A := res A
  map f := Deformation.restrictedFunctor_onMap ρbar res f
  map_id := sorry
  map_comp := sorry

-- Theorem 2.3
theorem Deformation.restrictedFunctor_isCorepresentable :
    (Deformation.restrictedFunctor 𝓞 ρbar res).IsCorepresentable :=
  sorry

end RestrictedFunctor

end Deformation
