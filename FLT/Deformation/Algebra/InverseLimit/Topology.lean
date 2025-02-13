import FLT.Deformation.Algebra.InverseLimit.Basic
import FLT.Mathlib.Order.Defs.Unbundled
import Mathlib.Order.CompletePartialOrder

namespace Group.InverseLimit

section Topology

variable {ι : Type*} [instPreorder : Preorder ι] [nonempty : Nonempty ι]
  {obj : (i : ι) → Type*} [∀ i : ι, Group (obj i)]
  [∀ i : ι, TopologicalSpace (obj i)]
  (func : ∀ {i j}, i ≤ j → obj j →* obj i)
  (cont : {i j : ι} → (h : i ≤ j) → Continuous (func h))

def minimumOpens : Set (Set (InverseLimit obj func)) :=
    setOf fun V ↦ ∃ (i : ι) (W : Set (obj i)), IsOpen W ∧ V = (toComponent func i) ⁻¹' W

instance : TopologicalSpace (InverseLimit obj func) := .generateFrom <| minimumOpens func

instance [DecidableRel LE.le (α := ι)] [instIsLinearOrder : IsLinearOrder ι LE.le]
    : TopologicalSpace.IsTopologicalBasis <| minimumOpens func where
  exists_subset_inter := by
    unfold minimumOpens
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.subset_inter_iff, and_imp,
      forall_exists_index]
    rintro V₁ i₁ W₁ ho₁ h₁ V₂ i₂ W₂ ho₂ h₂ x hx₁ hx₂
    have h_le₁ : i₁ ≤ i₁ ⊔ i₂ := by simp
    have h_le₂ : i₂ ≤ i₁ ⊔ i₂ := by simp
    let R₁ := func h_le₁ ⁻¹' W₁
    let R₂ := func h_le₂ ⁻¹' W₂
    have hoR₁ : IsOpen R₁ := by exact (cont h_le₁).isOpen_preimage W₁ ho₁
    have hoR₂ : IsOpen R₂ := by exact (cont h_le₂).isOpen_preimage W₂ ho₂
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
    subst h_antiimage₁ h₂
    simp_all only [func_toComponent, Set.mem_preimage, Set.mem_inter_iff, and_self, Set.inter_subset_left,
      Set.inter_subset_right, R₁, R₂]
    split_ands
    . exact IsOpen.inter hoR₁ hoR₂
    . aesop
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

lemma map_of_maps_continuous {G' : Type*} [Group G'] [TopologicalSpace G'] [TopologicalGroup G']
  (maps : (i : ι) → G' →* obj i)
  (comm : _)
  (maps_cont : (i : ι) → Continuous (maps i))
    : Continuous (map_of_maps func maps comm) := sorry

instance [∀ i : ι, TopologicalGroup (obj i)] : TopologicalGroup (InverseLimit obj func) where
  continuous_mul := by
    let G := InverseLimit obj func
    let G' := G × G
    let mul : G × G → G := sorry
    let maps : (i : ι) → G' →* obj i:= sorry -- fun (i : ι) ↦ .comp (toComponent func i) Mul.mul
    sorry
  continuous_inv := by
    sorry

end Topology

namespace Group.InverseLimit
