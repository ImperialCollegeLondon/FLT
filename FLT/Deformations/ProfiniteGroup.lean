import Mathlib
import FLT.Deformations.Lift

universe u
namespace Deformations

variable {𝓞 : Type u} [CommRing 𝓞] [IsLocalRing 𝓞] [IsNoetherianRing 𝓞]

variable {V : Type u} [AddCommMonoid V] [Module (𝓴 𝓞) V] [Module.Free (𝓴 𝓞) V] [Module.Finite (𝓴 𝓞) V]

section G_profinite -- Section 3.2 Smit & Lenstra

variable {G : ProfiniteGrp}

variable (ρbar : Representation (𝓴 𝓞) G V)

abbrev G_decomposition_index : Set (Subgroup G) :=
  setOf fun (Gi : Subgroup G) ↦
    Gi.Normal ∧ Nonempty (Fintype (G ⧸ Gi)) ∧ ∀ gi ∈ Gi, ρbar gi = 1

def group_of_hi (Gi : Subgroup G) (h : Gi ∈ G_decomposition_index ρbar) : Group (G ⧸ Gi) := by
  simp at h
  obtain ⟨hn, _, _⟩ := h
  infer_instance

abbrev G_decomposition_obj (Gi : Subgroup G) : Type _ := G ⧸ Gi

abbrev G_decomposition_map (Gi Gj : G_decomposition_index ρbar) (h : Gi ≤ Gj) :
   GroupHom (instGroup := group_of_hi Gi) (G_decomposition_obj Gi) (G_decomposition_obj Gj) :=
    groupHomOfQuot_of_le (ideal_le_of_artinianQuotientIdeal_le h)


def G_decomposition_topology := sorry


-- Proposition 2.5 in G Profinite
theorem Lift.functor_isCorepresentable_profinite :
    (Lift.functor 𝓞 ρbar).IsCorepresentable := by
  sorry
end G_profinite

end Deformations
