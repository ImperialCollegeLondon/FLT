/-
Copyright (c) 2025 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McCarthy
-/
module

public import Mathlib.SetTheory.Cardinal.Finite

@[expose] public section

namespace Fintype

/--
Rewrite a finite sum with an `if` condition as a sum over the subtype where the
condition holds
-/
lemma sum_dite_eq_sum_subtype
    {α : Type*} [Fintype α]
    {β : Type*} [AddCommMonoid β]
    (P : α → Prop) [DecidablePred P]
    (f : (a : α) → P a → β) :
    (∑ a : α, if h : P a then f a h else 0)
      =
    ∑ a : {a : α // P a}, f a.1 a.2 := by
  symm
  refine Finset.sum_bij_ne_zero (fun a _ _ ↦ a.val) ?_ ?_ ?_ ?_
  · intro a _ _
    exact Finset.mem_univ _
  · intro a₁ _ _ a₂ _ _ h
    exact Subtype.ext h
  · intro b _ hb
    split_ifs at hb with h
    · exact ⟨⟨b, h⟩, Finset.mem_univ _, hb, rfl⟩
    · exact False.elim (hb rfl)
  · intro a _ _
    exact (dif_pos a.prop).symm

end Fintype

namespace One
/--
A finite type with a `1` element has nonzero cardinality.
-/
lemma natCard_ne_zero_of_finite
    (H : Type*) [One H] [Finite H] :
    Nat.card H ≠ 0 := by
  exact Nat.card_ne_zero.mpr ⟨⟨1⟩, inferInstance⟩

/--
In characteristic zero, the cardinality of a finite type with a `1` element
is nonzero in any semiring.
-/
lemma natCast_natCard_ne_zero_of_finite
    (H : Type*) [One H] [Finite H]
    (k : Type*) [Semiring k] [CharZero k] :
    (Nat.card H : k) ≠ 0 := by
  intro h
  exact One.natCard_ne_zero_of_finite H (Nat.cast_eq_zero.mp h)

end One
