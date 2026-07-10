module

public import Mathlib.RepresentationTheory.Subrepresentation

@[expose] public section

variable {k G V : Type*} [Semiring k] [Monoid G] [AddCommMonoid V] [Module k V]
  (ρ : Representation k G V)

namespace Subrepresentation

@[simp]
lemma toRepresentation_apply_mk {ρ' : Subrepresentation ρ} {g : G} {v w : V} {hv : v ∈ ρ'}
    {hw : w ∈ ρ'}
    : ρ'.toRepresentation g ⟨v, hv⟩ = ⟨w, hw⟩ ↔ ρ g v = w := by
  rw [Subtype.ext_iff]; rfl

lemma toRepresentation_apply_coe {ρ' : Subrepresentation ρ} {g : G} {v w : ρ'.toSubmodule}
    : ρ'.toRepresentation g v = w ↔ ρ g v.1 = w.1 := by
  rw [Subtype.ext_iff]; rfl

section quotient

variable {A G W : Type*} [Ring A] [Group G] [AddCommGroup W] [Module A W]

/-- The quotient representation associated to a subrepresentation. -/
def quotient {ρ : Representation A G W} (ρ' : Subrepresentation ρ) :
    Representation A G (W ⧸ ρ'.toSubmodule) :=
  ρ.quotient ρ'.toSubmodule (fun g _ hw => ρ'.apply_mem_toSubmodule g hw)

lemma quotient_apply_mk {ρ : Representation A G W} (ρ' : Subrepresentation ρ)
    (g : G) (w : W) :
    ρ'.quotient g ⟦w⟧ = ⟦ρ g w⟧ := by
  rfl

end quotient

end Subrepresentation

end
