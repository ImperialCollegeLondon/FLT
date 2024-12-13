import Mathlib.RepresentationTheory.Basic
import FLT.Mathlib.RepresentationTheory.Basic

variable {G : Type*} [Group G]

variable {A : Type*} [CommRing A]

variable {W : Type*} [AddCommMonoid W] [Module A W]

class Representation.Irreducible (ρ : Representation A G W) : Prop :=
  sorry

class Representation.AbsolutelyIrreducible (ρ : Representation A G W) : Prop where
  absolutelyIrreducible:
    ∀ A', ∃ _ : CommRing A', ∀ ι : A  →+* A', ∃ _ : Function.Injective ι,
    Irreducible (Representation.tprod' W A')
