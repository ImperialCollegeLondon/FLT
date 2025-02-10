import FLT.Deformation.Algebra.InverseLimit.Basic
import Mathlib.Order.CompletePartialOrder

namespace Group.InverseLimit

section Topology

variable {ι : Type*} [instLinearOrder : LinearOrder ι] [nonempty : Nonempty ι]
  {obj : (i : ι) → Type*} [∀ i : ι, Group (obj i)] [∀ i, Finite (obj i)]
  (func : ∀ {i j}, i ≤ j → obj j →* obj i)

instance : TopologicalSpace (InverseLimit obj func) :=
  .generateFrom <| setOf fun V ↦ ∃ (i : ι) (W : Set (obj i)), V = (toComponent func i) ⁻¹' W

instance : TopologicalSpace.IsTopologicalBasis
    <| setOf fun V ↦ ∃ (i : ι) (W : Set (obj i)), V = (toComponent func i) ⁻¹' W where
  exists_subset_inter := by
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.subset_inter_iff, and_imp,
      forall_exists_index]
    rintro V₁ i₁ W₁ h₁ V₂ i₂ W₂ h₂ x₁ hx₁ hx₂
    have h_le₁ : i₁ ≤ i₁ ⊔ i₂ := by simp
    have h_le₂ : i₂ ≤ i₁ ⊔ i₂ := by simp
    let R₁ := func h_le₁ ⁻¹' W₁
    let R₂ := func h_le₂ ⁻¹' W₂
    use (toComponent func (i₁ ⊔ i₂)) ⁻¹' R₁ ∩ (toComponent func (i₁ ⊔ i₂)) ⁻¹' R₂
    use ⟨i₁ ⊔ i₂, R₁ ∩ R₂, ?_⟩
    have h_f₁ : .comp (func h_le₁) (toComponent func (i₁ ⊔ i₂)) = (toComponent func i₁) := by simp
    have h_f₂ : .comp (func h_le₂) (toComponent func (i₁ ⊔ i₂)) = (toComponent func i₂) := by simp
    have h_antiimage₁ : V₁ = (toComponent func (i₁ ⊔ i₂)) ⁻¹' R₁ := by
      unfold R₁
      rw [h₁, ← h_f₁]
      simp [Set.preimage_comp_eq, -func_toComponent]
    have h_antiimage₂ : V₂ = (toComponent func (i₁ ⊔ i₂)) ⁻¹' R₂ := by
      unfold R₂
      rw [h₂, ← h_f₂]
      simp [Set.preimage_comp_eq, -func_toComponent]
    aesop
    rfl
  sUnion_eq := by
    change _ = ⊤
    rw [← top_le_iff]
    rintro x hx
    rw [Set.mem_sUnion]
    use ⊤
    simp only [Set.top_eq_univ, Set.mem_setOf_eq, Set.mem_univ, and_true]
    use Classical.choice nonempty
    use ⊤
    aesop
  eq_generateFrom := rfl

instance : TopologicalGroup (InverseLimit obj func) where
  continuous_mul := sorry
  continuous_inv := sorry

end Topology

namespace Group.InverseLimit
