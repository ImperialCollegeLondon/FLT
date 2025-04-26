import Mathlib.GroupTheory.Complement

/-!
# TODO

Replace `IsComplement.card_left` by a new lemma `IsComplement.ncard_left`.
-/

open Function Set
open scoped Pointwise

namespace Subgroup
variable {G : Type*} [Group G] {H K : Subgroup G} {S T : Set G}

@[to_additive]
lemma IsComplement.encard_left [H.FiniteIndex] (h : IsComplement S H) : S.encard = H.index := by
  rw [← h.finite_left.cast_ncard_eq, ← Set.Nat.card_coe_set_eq, h.card_left]
