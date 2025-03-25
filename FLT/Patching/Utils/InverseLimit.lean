import FLT.Patching.Utils.Lemmas
import Mathlib.CategoryTheory.CofilteredSystem
import Mathlib.Data.Finset.Order

variable {ι : Type*} [Preorder ι] [Nonempty ι] [IsDirected ι (· ≥ ·)]
variable (α : ι → Type*) (f : ∀ i j, i ≤ j → α i → α j)

section Topology

variable [∀ i, TopologicalSpace (α i)]
variable (hf : ∀ i j h, Continuous (f i j h))

include hf in
lemma dense_inverseLimit_of_forall_image_dense
    (s : Set { v : Π i, α i // ∀ i j (h : i ≤ j), f i j h (v i) = v j })
    (hs : ∀ i, Dense ((fun x ↦ (Subtype.val x) i) '' s)) : Dense s := by
  classical
  rw [dense_iff_inter_open]
  rintro U ⟨t, ht, rfl⟩ ⟨x, hx⟩
  obtain ⟨I, u, hu₁, hu₂⟩ := isOpen_pi_iff.mp ht _ hx
  obtain ⟨i, hi⟩ := Finset.exists_le (α := ιᵒᵈ) I
  let U : Set (α i) := ⋂ (j : I), (f _ _ (hi j.1 j.2)) ⁻¹' u _
  have hU : IsOpen U := isOpen_iInter_of_finite fun j ↦ (hu₁ j.1 j.2).1.preimage (hf ..)
  obtain ⟨_, hz₁, z, hz₂, rfl⟩ := dense_iff_inter_open.mp (hs i) U hU
    ⟨x.1 _, by simp [U, x.2, hu₁]⟩
  exact ⟨z, hu₂ (by simpa [U, z.2] using hz₁), hz₂⟩

include hf in
lemma denseRange_inverseLimit {β}
    (g : β → { v : Π i, α i // ∀ i j (h : i ≤ j), f i j h (v i) = v j })
    (hg : ∀ i, DenseRange (fun x ↦ (g x).1 i)) : DenseRange g := by
  refine dense_inverseLimit_of_forall_image_dense α f hf _ fun i ↦ ?_
  rw [← Set.range_comp]
  exact hg _

end Topology

section MittagLeffler

variable (hf₀ : ∀ i, f i i le_rfl = id)
variable (hf : ∀ i j k (hij : i ≤ j) (hjk : j ≤ k), f j k hjk ∘ f i j hij = f i k (hij.trans hjk))
variable {l : ℕ → ι} (hl : Antitone l) (hl' : ∀ x, ∃ n, l n ≤ x)

open CategoryTheory
omit [Nonempty ι] [IsDirected ι (· ≥ ·)] in
include hf₀ hf hl hl' in
theorem nonempty_inverseLimit_of_finite [∀ i, Finite (α i)] [∀ i, Nonempty (α i)] :
    Nonempty { v : Π i, α i // ∀ i j (h : i ≤ j), f i j h (v i) = v j } := by
  let f' : ιᵒᵈᵒᵖ ⥤ Type _ :=
  { obj i := α i.1,
    map e := f _ _ e.unop.le,
    map_id i := by ext; simp [hf₀],
    map_comp f g := by ext; simp [← hf _ _ _ f.unop.le g.unop.le] }
  have : IsDirected ιᵒᵈ (· ≤ ·) := by
    constructor
    intros i j
    obtain ⟨i', hi'⟩ := hl' i
    obtain ⟨j', hj'⟩ := hl' j
    refine ⟨l (max i' j'), le_trans hi' (hl (le_max_left _ _)), le_trans hj' (hl (le_max_right _ _))⟩
  obtain ⟨x, hx⟩ := nonempty_sections_of_finite_inverse_system f'
  exact ⟨⟨fun i ↦ x ⟨i⟩, fun i j e ↦ hx (homOfLE e).op⟩⟩

end MittagLeffler
