module

public import Mathlib.RepresentationTheory.Subrepresentation
public import Mathlib.RepresentationTheory.Irreducible
public import FLT.Mathlib.RepresentationTheory.Basic

@[expose] public section

universe u

namespace Representation

variable {G : Type*} [Group G]

variable {k : Type*} [Field k]

variable {W : Type*} [AddCommMonoid W] [Module k W]

/-!
  `IsAbsolutelyIrreducible ρ` states that a given Representation ρ over a field k
  is absolutely irreducible, meaning that all the possible base change extensions are irreducible.
-/
class IsAbsolutelyIrreducible (ρ : Representation k G W) : Prop where
  absolutelyIrreducible :
    ∀ k' : Type u, ∀ _ : Field k', ∀ _ : Algebra k k', IsIrreducible (k' ⊗ᵣ' ρ)

end Representation
