module

public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Logic.Pairwise

@[expose] public section

theorem Fin.pairwise_forall_two {n : ℕ} {r : Fin (n + 2) → Fin (n + 2) → Prop} (h : Pairwise r) :
    Pairwise (r.onFun ![0, Fin.last _]) := by
  apply Pairwise.comp_of_injective h
  simp [Function.Injective, Fin.forall_fin_two]
