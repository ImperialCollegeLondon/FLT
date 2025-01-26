import Mathlib.Data.Finset.Lattice.Fold

 theorem Finset.le_sup_dite_pos {α β : Type*} [SemilatticeSup α] [OrderBot α] {s : Finset β}
    (p : β → Prop) [DecidablePred p] {f : (b : β) → p b → α} {g : (b : β) → ¬p b → α} {b : β}
    (h₀ : b ∈ s) (h₁ : p b) :
    f b h₁ ≤ s.sup fun i => if h : p i then f i h else g i h := by
  have : f b h₁ = (fun i => if h : p i then f i h else g i h) b := by simp [h₁]
  rw [this]
  apply Finset.le_sup h₀

  theorem Finset.le_sup_dite_neg {α β : Type*} [SemilatticeSup α] [OrderBot α] {s : Finset β}
    (p : β → Prop) [DecidablePred p] {f : (b : β) → p b → α} {g : (b : β) → ¬p b → α} {b : β}
    (h₀ : b ∈ s) (h₁ : ¬p b) :
    g b h₁ ≤ s.sup fun i => if h : p i then f i h else g i h := by
  have : g b h₁ = (fun i => if h : p i then f i h else g i h) b := by simp [h₁]
  rw [this]
  apply Finset.le_sup h₀
