import FLT.Deformations.RepresentationTheory.Subrepresentation
import FLT.Mathlib.RepresentationTheory.Basic

namespace Representation

variable {G : Type*} [Group G]

variable {k : Type*} [Field k]

variable {W : Type*} [AddCommMonoid W] [Module k W]

/-!
  IsIrreducible predicates that a given Representation ρ is irreducible (also known as simple),
  meaning that any subrepresentation must be either the full one (⊤) or zero (⊥)

  This notion is only well behaved when the representation is over a field k. If it were defined over
  a ring A with a nontrivial ideal J, the subrepresentation JW would be a non trivial subrepresentation,
  so ρ would never be irreducible.
-/
class IsIrreducible (ρ : Representation k G W) : Prop where
  irreducible : IsSimpleOrder (Subrepresentation ρ)

/-!
  IsAbsolutelyIrreducible predicates that a given Representation ρ over a field k
  is absolutely irreducible, meaning that all the possible base change extensions are irreducible.

  This notion is only well behaved when the representation is over a field k. If it were defined over
  a ring A with a nontrivial ideal J, the subrepresentation JW would be a non trivial subrepresentation,
  so ρ would never be absolutely irreducible.
-/
class IsAbsolutelyIrreducible (ρ : Representation k G W) : Prop where
  absolutelyIrreducible : ∀ k', ∀ _ : Field k', ∀ _ : Algebra k k', IsIrreducible (k' ⊗ᵣ' ρ)

end Representation
