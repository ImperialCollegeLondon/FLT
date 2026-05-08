/-
Copyright (c) 2025 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri, Kevin Buzzard
-/
module

public import Mathlib.Data.Fin.VecNotation

/-!
# Basic

Material destined for Mathlib.
-/

@[expose] public section

theorem Fin.pairwise_forall_two {n : ℕ} {r : Fin (n + 2) → Fin (n + 2) → Prop} (h : Pairwise r) :
    Pairwise (r.onFun ![0, Fin.last _]) := by
  apply Pairwise.comp_of_injective h
  simp [Function.Injective, Fin.forall_fin_two]
