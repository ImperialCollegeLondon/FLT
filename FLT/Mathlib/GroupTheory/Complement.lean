import Mathlib.GroupTheory.Complement

open Set
open scoped Pointwise

namespace Subgroup
variable {G : Type*} [Group G] {s t : Set G}

@[to_additive (attr := simp)]
lemma not_isComplement_empty_left : ¬ IsComplement ∅ t :=
  fun h ↦ by simpa [eq_comm (a := ∅)] using h.mul_eq

@[to_additive (attr := simp)]
lemma not_isComplement_empty_right : ¬ IsComplement s ∅ :=
  fun h ↦ by simpa [eq_comm (a := ∅)] using h.mul_eq

@[to_additive]
lemma IsComplement.nonempty_of_left (hst : IsComplement s t) : s.Nonempty := by
  contrapose! hst; simp [hst]

@[to_additive]
lemma IsComplement.nonempty_of_right (hst : IsComplement s t) : t.Nonempty := by
  contrapose! hst; simp [hst]

@[to_additive] lemma IsComplement.pairwiseDisjoint_smul (hst : IsComplement s t) :
    s.PairwiseDisjoint (· • t) := fun a ha b hb hab ↦ disjoint_iff_forall_ne.2 <| by
  rintro _ ⟨c, hc, rfl⟩ _ ⟨d, hd, rfl⟩
  exact hst.1.ne (a₁ := (⟨a, ha⟩, ⟨c, hc⟩)) (a₂:= (⟨b, hb⟩, ⟨d, hd⟩)) (by simp [hab])

@[to_additive]
lemma not_empty_mem_leftTransversals : ∅ ∉ leftTransversals s := not_isComplement_empty_left

@[to_additive]
lemma not_empty_mem_rightTransversals : ∅ ∉ rightTransversals s := not_isComplement_empty_right

@[to_additive]
lemma nonempty_of_mem_leftTransversals (hst : s ∈ leftTransversals t) : s.Nonempty :=
  hst.nonempty_of_left

@[to_additive]
lemma nonempty_of_mem_rightTransversals (hst : s ∈ rightTransversals t) : s.Nonempty :=
  hst.nonempty_of_right

variable {H : Subgroup G} [H.FiniteIndex]

@[to_additive]
lemma finite_of_mem_leftTransversals (hs : s ∈ leftTransversals H) : s.Finite :=
  Nat.finite_of_card_ne_zero <| by rw [card_left_transversal hs]; exact FiniteIndex.finiteIndex

@[to_additive]
lemma finite_of_mem_rightTransversals (hs : s ∈ rightTransversals H) : s.Finite :=
  Nat.finite_of_card_ne_zero <| by rw [card_right_transversal hs]; exact FiniteIndex.finiteIndex

end Subgroup
