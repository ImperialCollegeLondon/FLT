import Mathlib.Data.Set.Card

@[deprecated Nat.card_coe_set_eq (since := "2025-09-16")]
lemma Nat.card_set_eq_ncard {α : Type*} (s : Set α) : Nat.card s = s.ncard := rfl

-- TODO: deprecate in favour of ENat.card_coe_set_eq after
-- https://github.com/leanprover-community/mathlib4/pull/29716
@[simp]
lemma ENat.card_set_eq_encard {α : Type*} (s : Set α) : ENat.card s = s.encard := rfl
