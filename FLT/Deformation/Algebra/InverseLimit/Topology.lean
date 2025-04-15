import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.Defs.Unbundled
import FLT.Deformation.ContinuousRepresentation.IsTopologicalModule
import FLT.Deformation.Algebra.InverseLimit.Basic

open TopologicalSpace

variable {ι : Type*}
  [instSemilatticeSup : SemilatticeSup ι]
  [instOrderBot : OrderBot ι]
  {obj : (i : ι) → Type*}
namespace Module.InverseLimit

variable {R : Type*} [Ring R] [∀ i : ι, AddCommGroup (obj i)] [∀ i : ι, Module R (obj i)]
  [∀ i : ι, TopologicalSpace (obj i)]
  (func : ∀ {i j}, i ≤ j → obj j →ₗ[R] obj i)
  {cont : ∀ {i j}, (h : i ≤ j) → Continuous (func h)}

instance instTopologicalSpace : TopologicalSpace (InverseLimit obj func) :=
  induced (fun (x : InverseLimit obj func) ↦ x.val)
    (Pi.topologicalSpace (ι := ι) (Y := fun x ↦ obj x)
      (t₂ := fun _ ↦ generateFrom {U | IsOpen U}))

abbrev minimumOpens : Set (Set (InverseLimit obj func)) :=
    {V | ∃ (i : ι) (W : Set (obj i)), IsOpen W ∧ V = (toComponent func i) ⁻¹' W}

-- TODO: Why is cont not automatically added? Is this a Lean bug or am I unaware of something?
lemma minimumOpens_isSubbasis {cont : ∀ {i j}, (h : i ≤ j) → Continuous (func h)} :
    instTopologicalSpace func = generateFrom (minimumOpens func) := by
  unfold instTopologicalSpace minimumOpens toComponent
  rw [pi_generateFrom_eq, induced_generateFrom_eq]
  congr
  ext X
  simp only [Set.mem_setOf_eq, Set.mem_image, LinearMap.coe_mk, AddHom.coe_mk]
  apply Iff.intro
  . intro ⟨Y, ⟨⟨side, index, ⟨hY₁, hY₂⟩⟩, hY₃⟩⟩
    let index_sup := (index.sup (fun x ↦ x))
    use index_sup
    have h_le {j : ι} (h : j ∈ index) : j ≤ index_sup := Finset.le_sup (f := fun x ↦ x) h
    let side_sup {j : ι} (h : j ∈ index) : Set (obj index_sup) := (func (h_le h)) ⁻¹' (side j)
    let W := ⋂ (j : index), side_sup j.2
    use W
    split_ands
    . apply isOpen_iInter_of_finite
      intro ⟨j, j_in⟩
      exact IsOpen.preimage (cont (h_le j_in)) (hY₁ j j_in)
    . simp_rw [← hY₃, W, side_sup, hY₂, Set.pi_def, Set.preimage_iInter, ← Set.preimage_comp,
          Finset.mem_coe, Set.iInter_subtype]
      have comp_eq_comp (j : ι) (h : j ∈ index) : (Function.eval j) ∘ (fun (x : InverseLimit obj func) ↦ x.1)
          = (func (h_le h)) ∘ (toComponent func index_sup) := by
        ext x
        simp_rw [func_toComponent]
        aesop
      aesop
  . intro ⟨i, W, ⟨hW₁, hW₂⟩⟩
    let side := (fun (j : ι) ↦ by
      by_cases h : i = j
      . rw [h] at W; exact W
      . exact ⊥
    )
    use (Set.pi { i } side)
    split_ands
    . use side
      use { i }
      aesop
    . aesop

@[continuity]
lemma map_of_maps_continuous {cont : ∀ {i j}, (h : i ≤ j) → Continuous (func h)}
  {X : Type*} [TopologicalSpace X]
  (maps : (i : ι) → X → obj i) (comm : _) (maps_cont : (i : ι) → Continuous (maps i)) :
    Continuous (map_of_maps func maps comm) := by
  rw [minimumOpens_isSubbasis (cont := cont)]
  refine continuous_generateFrom_iff.mpr ?_
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

lemma minimumOpens_isOpen {cont : ∀ {i j}, (h : i ≤ j) → Continuous (func h)}
    {s : Set (InverseLimit obj func)} (h : s ∈ minimumOpens func) : IsOpen s := by
  rw [minimumOpens_isSubbasis (cont := cont)]
  exact isOpen_generateFrom_of_mem h

@[continuity]
lemma toComponent_continuous {cont : ∀ {i j}, (h : i ≤ j) → Continuous (func h)} (i : ι) :
    Continuous (toComponent func i) where
  isOpen_preimage R hR := by
    refine minimumOpens_isOpen (cont := cont) func ?_
    simp only [Set.mem_setOf_eq]
    use i, R

end Module.InverseLimit

namespace Ring.InverseLimit

variable [∀ i : ι, Ring (obj i)]
  [∀ i : ι, TopologicalSpace (obj i)]
  (func : ∀ {i j}, i ≤ j → obj j →+* obj i)
  {cont : {i j : ι} → (h : i ≤ j) → Continuous (func h)}

instance instTopologicalSpace : TopologicalSpace (InverseLimit obj func) :=
  induced (fun (x : InverseLimit obj func) ↦ x.val)
    (Pi.topologicalSpace (ι := ι) (Y := fun x ↦ obj x)
      (t₂ := fun _ ↦ generateFrom {U | IsOpen U}))

abbrev minimumOpens : Set (Set (InverseLimit obj func)) :=
    {V | ∃ (i : ι) (W : Set (obj i)), IsOpen W ∧ V = (toComponent func i) ⁻¹' W}

-- TODO: Why is cont not automatically added? Is this a Lean bug or am I unaware of something?
lemma minimumOpens_isSubbasis {cont : ∀ {i j}, (h : i ≤ j) → Continuous (func h)} :
    instTopologicalSpace func = generateFrom (minimumOpens func) := by
  unfold instTopologicalSpace minimumOpens toComponent
  rw [pi_generateFrom_eq, induced_generateFrom_eq]
  congr
  ext X
  simp only [Set.mem_setOf_eq, Set.mem_image, LinearMap.coe_mk, AddHom.coe_mk]
  apply Iff.intro
  . intro ⟨Y, ⟨⟨side, index, ⟨hY₁, hY₂⟩⟩, hY₃⟩⟩
    let index_sup := (index.sup (fun x ↦ x))
    use index_sup
    have h_le {j : ι} (h : j ∈ index) : j ≤ index_sup := Finset.le_sup (f := fun x ↦ x) h
    let side_sup {j : ι} (h : j ∈ index) : Set (obj index_sup) := (func (h_le h)) ⁻¹' (side j)
    let W := ⋂ (j : index), side_sup j.2
    use W
    split_ands
    . apply isOpen_iInter_of_finite
      intro ⟨j, j_in⟩
      exact IsOpen.preimage (cont (h_le j_in)) (hY₁ j j_in)
    . simp_rw [← hY₃, W, side_sup, hY₂, Set.pi_def, Set.preimage_iInter, ← Set.preimage_comp,
          Finset.mem_coe, Set.iInter_subtype]
      have comp_eq_comp (j : ι) (h : j ∈ index) : (Function.eval j) ∘ (fun (x : InverseLimit obj func) ↦ x.1)
          = (func (h_le h)) ∘ (toComponent func index_sup) := by
        ext x
        simp_rw [func_toComponent]
        aesop
      aesop
  . intro ⟨i, W, ⟨hW₁, hW₂⟩⟩
    let side := (fun (j : ι) ↦ by
      by_cases h : i = j
      . rw [h] at W; exact W
      . exact ⊥
    )
    use (Set.pi { i } side)
    split_ands
    . use side
      use { i }
      aesop
    . aesop

@[continuity]
lemma map_of_maps_continuous {cont : ∀ {i j}, (h : i ≤ j) → Continuous (func h)}
  {X : Type*} [TopologicalSpace X]
  (maps : (i : ι) → X → obj i) (comm : _) (maps_cont : (i : ι) → Continuous (maps i)) :
    Continuous (map_of_maps func maps comm) := by
  rw [minimumOpens_isSubbasis (cont := cont)]
  refine continuous_generateFrom_iff.mpr ?_
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

lemma minimumOpens_isOpen {cont : ∀ {i j}, (h : i ≤ j) → Continuous (func h)}
    {s : Set (InverseLimit obj func)} (h : s ∈ minimumOpens func) : IsOpen s := by
  rw [minimumOpens_isSubbasis (cont := cont)]
  exact isOpen_generateFrom_of_mem h

@[continuity]
lemma toComponent_continuous {cont : ∀ {i j}, (h : i ≤ j) → Continuous (func h)} (i : ι) :
    Continuous (toComponent func i) where
  isOpen_preimage R hR := by
    refine minimumOpens_isOpen (cont := cont) func ?_
    simp only [Set.mem_setOf_eq]
    use i, R

end Ring.InverseLimit

namespace Group.InverseLimit

variable [∀ i : ι, Group (obj i)]
  [∀ i : ι, TopologicalSpace (obj i)]
  (func : ∀ {i j}, i ≤ j → obj j →* obj i)
  (cont : {i j : ι} → (h : i ≤ j) → Continuous (func h))

instance instTopologicalSpace : TopologicalSpace (InverseLimit obj func) :=
  induced (fun (x : InverseLimit obj func) ↦ x.val)
    (Pi.topologicalSpace (ι := ι) (Y := fun x ↦ obj x)
      (t₂ := fun _ ↦ generateFrom {U | IsOpen U}))

abbrev minimumOpens : Set (Set (InverseLimit obj func)) :=
    {V | ∃ (i : ι) (W : Set (obj i)), IsOpen W ∧ V = (toComponent func i) ⁻¹' W}

-- TODO: Why is cont not automatically added? Is this a Lean bug or am I unaware of something?
lemma minimumOpens_isSubbasis {cont : ∀ {i j}, (h : i ≤ j) → Continuous (func h)} :
    instTopologicalSpace func = generateFrom (minimumOpens func) := by
  unfold instTopologicalSpace minimumOpens toComponent
  rw [pi_generateFrom_eq, induced_generateFrom_eq]
  congr
  ext X
  simp only [Set.mem_setOf_eq, Set.mem_image, LinearMap.coe_mk, AddHom.coe_mk]
  apply Iff.intro
  . intro ⟨Y, ⟨⟨side, index, ⟨hY₁, hY₂⟩⟩, hY₃⟩⟩
    let index_sup := (index.sup (fun x ↦ x))
    use index_sup
    have h_le {j : ι} (h : j ∈ index) : j ≤ index_sup := Finset.le_sup (f := fun x ↦ x) h
    let side_sup {j : ι} (h : j ∈ index) : Set (obj index_sup) := (func (h_le h)) ⁻¹' (side j)
    let W := ⋂ (j : index), side_sup j.2
    use W
    split_ands
    . apply isOpen_iInter_of_finite
      intro ⟨j, j_in⟩
      exact IsOpen.preimage (cont (h_le j_in)) (hY₁ j j_in)
    . simp_rw [← hY₃, W, side_sup, hY₂, Set.pi_def, Set.preimage_iInter, ← Set.preimage_comp,
          Finset.mem_coe, Set.iInter_subtype]
      have comp_eq_comp (j : ι) (h : j ∈ index) : (Function.eval j) ∘ (fun (x : InverseLimit obj func) ↦ x.1)
          = (func (h_le h)) ∘ (toComponent func index_sup) := by
        ext x
        simp_rw [func_toComponent]
        aesop
      aesop
  . intro ⟨i, W, ⟨hW₁, hW₂⟩⟩
    let side := (fun (j : ι) ↦ by
      by_cases h : i = j
      . rw [h] at W; exact W
      . exact ⊥
    )
    use (Set.pi { i } side)
    split_ands
    . use side
      use { i }
      aesop
    . aesop

@[continuity]
lemma map_of_maps_continuous {cont : ∀ {i j}, (h : i ≤ j) → Continuous (func h)}
  {X : Type*} [TopologicalSpace X]
  (maps : (i : ι) → X → obj i) (comm : _) (maps_cont : (i : ι) → Continuous (maps i)) :
    Continuous (map_of_maps func maps comm) := by
  rw [minimumOpens_isSubbasis (cont := cont)]
  refine continuous_generateFrom_iff.mpr ?_
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

lemma minimumOpens_isOpen {cont : ∀ {i j}, (h : i ≤ j) → Continuous (func h)}
    {s : Set (InverseLimit obj func)} (h : s ∈ minimumOpens func) : IsOpen s := by
  rw [minimumOpens_isSubbasis (cont := cont)]
  exact isOpen_generateFrom_of_mem h

@[continuity]
lemma toComponent_continuous {cont : ∀ {i j}, (h : i ≤ j) → Continuous (func h)} (i : ι) :
    Continuous (toComponent func i) where
  isOpen_preimage R hR := by
    refine minimumOpens_isOpen (cont := cont) func ?_
    simp only [Set.mem_setOf_eq]
    use i, R

namespace Group.InverseLimit
