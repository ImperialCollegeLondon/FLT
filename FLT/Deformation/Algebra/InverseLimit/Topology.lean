import FLT.Deformation.Algebra.InverseLimit.Basic
import FLT.Mathlib.Order.Defs.Unbundled
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.Defs.Unbundled

open TopologicalSpace

variable {ι : Type*} [instPreorder : Preorder ι]
  {obj : (i : ι) → Type*}

namespace Module.InverseLimit

variable {R : Type*} [Ring R] [∀ i : ι, AddCommGroup (obj i)] [∀ i : ι, Module R (obj i)]
  [∀ i : ι, TopologicalSpace (obj i)]
  (func : ∀ {i j}, i ≤ j → obj j →ₗ[R] obj i)
  (cont : {i j : ι} → (h : i ≤ j) → Continuous (func h))

def minimumOpens : Set (Set (InverseLimit obj func)) :=
    setOf fun V ↦ ∃ (i : ι) (W : Set (obj i)), IsOpen W ∧ V = (toComponent func i) ⁻¹' W

instance : TopologicalSpace (InverseLimit obj func) := .generateFrom <| minimumOpens func

end Module.InverseLimit

namespace Ring.InverseLimit

variable [∀ i : ι, Ring (obj i)]
  [∀ i : ι, TopologicalSpace (obj i)]
  (func : ∀ {i j}, i ≤ j → obj j →+* obj i)
  (cont : {i j : ι} → (h : i ≤ j) → Continuous (func h))

def minimumOpens : Set (Set (InverseLimit obj func)) :=
    setOf fun V ↦ ∃ (i : ι) (W : Set (obj i)), IsOpen W ∧ V = (toComponent func i) ⁻¹' W

instance : TopologicalSpace (InverseLimit obj func) := .generateFrom <| minimumOpens func

end Ring.InverseLimit

namespace Group.InverseLimit

variable [∀ i : ι, Group (obj i)]
  [∀ i : ι, TopologicalSpace (obj i)]
  (func : ∀ {i j}, i ≤ j → obj j →* obj i)
  (cont : {i j : ι} → (h : i ≤ j) → Continuous (func h))

def minimumOpens : Set (Set (InverseLimit obj func)) :=
    setOf fun V ↦ ∃ (i : ι) (W : Set (obj i)), IsOpen W ∧ V = (toComponent func i) ⁻¹' W

instance : TopologicalSpace (InverseLimit obj func) := .generateFrom <| minimumOpens func

instance instBasis [nonempty : Nonempty ι] [DecidableLE ι] [IsLinearOrder ι LE.le]
    : IsTopologicalBasis <| minimumOpens func where
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

@[continuity]
lemma map_of_maps_continuous {X : Type*} [TopologicalSpace X]
  (maps : (i : ι) → X → obj i) (comm : _) (maps_cont : (i : ι) → Continuous (maps i))
    : Continuous (map_of_maps func maps comm) := by
  refine continuous_generateFrom_iff.mpr ?_
  unfold minimumOpens
  intro V hV
  let i := hV.choose
  let R := hV.choose_spec.choose
  have hRo := hV.choose_spec.choose_spec.1
  have hR := hV.choose_spec.choose_spec.2
  rw [hR]
  have hcomp : (toComponent func i) ∘ (map_of_maps func maps comm) = maps i := by
    ext x
    simp
  rw [← Set.preimage_comp, hcomp]
  exact (maps_cont i).isOpen_preimage (Exists.choose_spec hV).choose hRo

lemma minimumOpens_isOpen {s : Set (InverseLimit obj func)} : s ∈ minimumOpens func → IsOpen s :=
  GenerateOpen.basic s

@[continuity]
lemma toComponent_continuous (i : ι) : Continuous (toComponent func i) where
  isOpen_preimage R hR := by
    refine minimumOpens_isOpen func ?_
    unfold minimumOpens
    simp only [Set.mem_setOf_eq]
    use i, R

instance [∀ i : ι, TopologicalGroup (obj i)] : TopologicalGroup (InverseLimit obj func) where
  continuous_mul := by
    refine continuous_generateFrom_iff.mpr ?_
    rintro V hV
    unfold minimumOpens at hV
    let i := hV.choose
    let R := hV.choose_spec.choose
    have hRo := hV.choose_spec.choose_spec.1
    have hR := hV.choose_spec.choose_spec.2
    rw [hR]
    rw [← Set.preimage_comp]
    let G := InverseLimit obj func
    let Rinvadd := ((fun ⟨x, y⟩ ↦ x * y) : obj i × obj i → obj i) ⁻¹' R
    let hRinvaddo : IsOpen (Rinvadd) := by
      exact (continuous_mul (M := obj i)).isOpen_preimage R hRo
    have hcomm : ((toComponent func i) ∘ (fun ⟨x, y⟩ ↦ x * y) : G × G → obj i) =
      (fun ⟨x, y⟩ ↦ x * y) ∘ (fun ⟨x, y⟩ ↦ (⟨toComponent func i x, toComponent func i y⟩ : obj i × obj i))  := by
      ext x
      simp
    rw [hcomm, Set.preimage_comp]
    simp only
    have hcont : Continuous (fun (⟨x, y⟩ : G × G) ↦
      (⟨toComponent func i x, toComponent func i y⟩ : obj i × obj i)) := by
      continuity
    exact hcont.isOpen_preimage ((fun x ↦ x.1 * x.2) ⁻¹' (Exists.choose_spec hV).choose) hRinvaddo
  continuous_inv := by
    refine continuous_generateFrom_iff.mpr ?_
    rintro V hV
    unfold minimumOpens at hV
    let i := hV.choose
    let R := hV.choose_spec.choose
    have hRo := hV.choose_spec.choose_spec.1
    have hR := hV.choose_spec.choose_spec.2
    rw [hR]
    rw [← Set.preimage_comp]
    have hRinvo : IsOpen (R⁻¹) := by exact IsOpen.inv hRo
    have hcomm : (toComponent func i) ∘ (fun x ↦ x⁻¹) = (fun x ↦ x⁻¹) ∘ (toComponent func i) := by
      ext x
      simp
    rw [hcomm]
    simp only [Set.inv_preimage]
    exact (toComponent_continuous func i).isOpen_preimage R⁻¹ hRinvo

namespace Group.InverseLimit
