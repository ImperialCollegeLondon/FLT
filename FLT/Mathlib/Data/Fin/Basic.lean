import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Logic.Pairwise

theorem Fin.castPred_ne_zero {n : ℕ} {j : Fin (n + 2)} (h₁ : j ≠ Fin.last (n + 1)) (h₂ : j ≠ 0) :
    Fin.castPred j h₁ ≠ 0 := by
  contrapose! h₂
  rwa [← Fin.castPred_zero, Fin.castPred_inj] at h₂

theorem Fin.pairwise_forall_two {n : ℕ} {r : Fin (n + 2) → Fin (n + 2) → Prop} (h : Pairwise r) :
    Pairwise (r.onFun ![0, Fin.last _]) := by
  apply Pairwise.comp_of_injective h
  simp [Function.Injective, Fin.forall_fin_two]
