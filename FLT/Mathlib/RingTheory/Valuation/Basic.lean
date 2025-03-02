import Mathlib.RingTheory.Valuation.Basic

variable {R : Type*} {Γ₀ : Type*} [Ring R] [LinearOrderedCommMonoidWithZero Γ₀]
  (v : Valuation R Γ₀)

theorem Valuation.map_sub_lt {x y : R} {g : Γ₀} (hx : v x < g) (hy : v y < g) : v (x - y) < g := by
  rw [sub_eq_add_neg]
  apply Valuation.map_add_lt _ hx ?_
  rw [Valuation.map_neg]
  exact hy
