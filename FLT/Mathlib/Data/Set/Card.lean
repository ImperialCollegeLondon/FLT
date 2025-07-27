import Mathlib.Data.Set.Card

@[simp] lemma Nat.card_set_eq_ncard {α : Type*} (s : Set α) : Nat.card s = s.ncard := rfl

@[simp] lemma ENat.card_set_eq_encard {α : Type*} (s : Set α) : ENat.card s = s.encard := rfl
