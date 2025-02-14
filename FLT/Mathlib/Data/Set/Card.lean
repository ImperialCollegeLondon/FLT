import Mathlib.Data.Set.Card

-- TODO: This really should be defeq. Replace `Set.Nat.card_coe_set_eq`
@[simp] lemma Nat.card_set_eq_ncard {α : Type*} (s : Set α) : Nat.card s = s.ncard :=
  Set.Nat.card_coe_set_eq _

@[simp] lemma ENat.card_set_eq_encard {α : Type*} (s : Set α) : ENat.card s = s.encard := rfl
