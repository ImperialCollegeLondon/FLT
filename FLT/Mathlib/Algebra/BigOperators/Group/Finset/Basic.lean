import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Pi

theorem Fintype.sum_pi_single_pi {α : Type*} {β : α → Type*} [DecidableEq α] [Fintype α]
    [(a : α) → AddCommMonoid (β a)] (f : (a : α) → β a) :
    ∑ (a : α), Pi.single a (f a) = f := by
  simp_rw [funext_iff, Fintype.sum_apply]
  exact fun _ => Fintype.sum_pi_single _ _
