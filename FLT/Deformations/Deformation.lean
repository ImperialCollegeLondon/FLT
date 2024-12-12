import Mathlib
import FLT.Deformations.Lift

universe u

open scoped TensorProduct

variable {𝓞 : Type u}
  [CommRing 𝓞] [IsLocalRing 𝓞] [IsNoetherianRing 𝓞]
local notation3:max "𝓴" 𝓞 => (IsLocalRing.ResidueField 𝓞)
variable {V : Type u}
  [AddCommMonoid V] [Module (𝓴 𝓞) V] [Module.Free (𝓴 𝓞) V] [Module.Finite (𝓴 𝓞) V]
variable {G : Type u}
  [Group G] [TopologicalSpace G] [TopologicalGroup G]
variable (ρbar : Representation (𝓴 𝓞) G V)

variable (A : 𝓒 𝓞)

def Deformation := Quotient <| Lift.isIso ρbar A

def OpenIdeal := {a : Ideal A // IsOpen a.carrier}

instance : Coe (OpenIdeal A) (Ideal A) where
  coe a := a.1

variable {A} in
def CommRingCat.quotient (a : Ideal A) : CommRingCat where
  α := A ⧸ a

variable {A} in
def CommAlgCat.quotient (a : Ideal A) : CommAlgCat 𝓞 where
  left := sorry
  right := CommRingCat.quotient a
  hom := sorry

variable {A} in
def 𝓒.quotient (a : Ideal A) : 𝓒 𝓞 where
  obj := CommAlgCat.quotient a
  property := sorry

variable {A ρbar} in
def Deformation.quotient (D : Deformation ρbar A) (a : Ideal A) : Deformation ρbar (A.quotient a) := sorry

variable {A ρbar} in
def Deformation.tensorProduct (D : Deformation ρbar A) (R : 𝓒 𝓞) [Algebra A R] : Deformation ρbar R := sorry

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
def Deformation.functor_onMap {A B : 𝓒 𝓞} (f : A ⟶ B) : Deformation ρbar A → Deformation ρbar B :=
  sorry

variable (𝓞) in
def Deformation.functor : CategoryTheory.Functor (𝓒 𝓞) (Type (u+1)) where
  obj A := Deformation ρbar A
  map f := sorry -- Deformation.functor_onMap ρbar f

-- Proposition 2.3
theorem Deformation.functor_isCorepresentable : (Deformation.functor 𝓞 ρbar).IsCorepresentable  := sorry
