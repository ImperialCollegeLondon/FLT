import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.Defs.Unbundled
import FLT.Deformation.ContinuousRepresentation.IsTopologicalModule
import FLT.Deformation.Algebra.InverseLimit.Basic

open TopologicalSpace

variable {ι : Type*} [instPreorder : Preorder ι]
  {obj : (i : ι) → Type*}

namespace Module.InverseLimit

variable {R : Type*} [Ring R] [∀ i : ι, AddCommGroup (obj i)] [∀ i : ι, Module R (obj i)]
  [∀ i : ι, TopologicalSpace (obj i)]
  (func : ∀ {i j}, i ≤ j → obj j →ₗ[R] obj i)
  (cont : {i j : ι} → (h : i ≤ j) → Continuous (func h))

abbrev minimumOpens : Set (Set (InverseLimit obj func)) :=
    {V | ∃ (i : ι) (W : Set (obj i)), IsOpen W ∧ V = (toComponent func i) ⁻¹' W}

instance : TopologicalSpace (InverseLimit obj func) := .generateFrom <| minimumOpens func

@[continuity]
lemma map_of_maps_continuous {X : Type*} [TopologicalSpace X]
  (maps : (i : ι) → X → obj i) (comm : _) (maps_cont : (i : ι) → Continuous (maps i))
    : Continuous (map_of_maps func maps comm) := by
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

lemma minimumOpens_isOpen {s : Set (InverseLimit obj func)} : s ∈ minimumOpens func → IsOpen s :=
  GenerateOpen.basic s

@[continuity]
lemma toComponent_continuous (i : ι) : Continuous (toComponent func i) where
  isOpen_preimage R hR := by
    refine minimumOpens_isOpen func ?_
    simp only [Set.mem_setOf_eq]
    use i, R

instance [TopologicalSpace R] [IsTopologicalRing R]
    [∀ i : ι, IsTopologicalModule R (obj i)] : IsTopologicalModule R (InverseLimit obj func) where
  continuous_smul := by
    refine continuous_generateFrom_iff.mpr ?_
    rintro V hV
    let i := hV.choose
    let X := hV.choose_spec.choose
    have hXo := hV.choose_spec.choose_spec.1
    have hX := hV.choose_spec.choose_spec.2
    rw [hX]
    rw [← Set.preimage_comp]
    let M := InverseLimit obj func
    let Xinvsmul := ((fun ⟨r, mi⟩ ↦ r • mi) : R × obj i → obj i) ⁻¹' X
    let hXinvaddo : IsOpen (Xinvsmul) := by
      exact (continuous_smul (M := R) (X := obj i)).isOpen_preimage X hXo
    have hcomm : ((toComponent func i) ∘ (fun ⟨r, m⟩ ↦ r • m) : R × M → obj i) =
      (fun ⟨r, mi⟩ ↦ r • mi) ∘ (fun ⟨r, m⟩ ↦ (⟨r, toComponent func i m⟩ : R × obj i))  := by
      ext x
      simp
    rw [hcomm, Set.preimage_comp]
    simp only
    have hcont : Continuous (fun (⟨r, m⟩ : R × M) ↦
      (⟨r, toComponent func i m⟩ : R × obj i)) := by
      continuity
    exact hcont.isOpen_preimage _ hXinvaddo
  continuous_add := by
    refine continuous_generateFrom_iff.mpr ?_
    rintro V hV
    let i := hV.choose
    let R := hV.choose_spec.choose
    have hRo := hV.choose_spec.choose_spec.1
    have hR := hV.choose_spec.choose_spec.2
    rw [hR]
    rw [← Set.preimage_comp]
    let G := InverseLimit obj func
    let Rinvadd := ((fun ⟨x, y⟩ ↦ x + y) : obj i × obj i → obj i) ⁻¹' R
    let hRinvaddo : IsOpen (Rinvadd) := by
      exact (continuous_add (M := obj i)).isOpen_preimage R hRo
    have hcomm : ((toComponent func i) ∘ (fun ⟨x, y⟩ ↦ x + y) : G × G → obj i) =
      (fun ⟨x, y⟩ ↦ x + y) ∘ (fun ⟨x, y⟩ ↦ (⟨toComponent func i x, toComponent func i y⟩ : obj i × obj i))  := by
      ext x
      simp
    rw [hcomm, Set.preimage_comp]
    simp only
    have hcont : Continuous (fun (⟨x, y⟩ : G × G) ↦
      (⟨toComponent func i x, toComponent func i y⟩ : obj i × obj i)) := by
      continuity
    exact hcont.isOpen_preimage _ hRinvaddo

end Module.InverseLimit

namespace Ring.InverseLimit

variable [∀ i : ι, Ring (obj i)]
  [∀ i : ι, TopologicalSpace (obj i)]
  (func : ∀ {i j}, i ≤ j → obj j →+* obj i)
  (cont : {i j : ι} → (h : i ≤ j) → Continuous (func h))

abbrev minimumOpens : Set (Set (InverseLimit obj func)) :=
    {V | ∃ (i : ι) (W : Set (obj i)), IsOpen W ∧ V = (toComponent func i) ⁻¹' W}

instance : TopologicalSpace (InverseLimit obj func) := .generateFrom <| minimumOpens func

@[continuity]
lemma map_of_maps_continuous {X : Type*} [TopologicalSpace X]
  (maps : (i : ι) → X → obj i) (comm : _) (maps_cont : (i : ι) → Continuous (maps i))
    : Continuous (map_of_maps func maps comm) := by
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

lemma minimumOpens_isOpen {s : Set (InverseLimit obj func)} : s ∈ minimumOpens func → IsOpen s :=
  GenerateOpen.basic s

@[continuity]
lemma toComponent_continuous (i : ι) : Continuous (toComponent func i) where
  isOpen_preimage R hR := by
    refine minimumOpens_isOpen func ?_
    simp only [Set.mem_setOf_eq]
    use i, R

instance [∀ i : ι, IsTopologicalRing (obj i)] : IsTopologicalRing (InverseLimit obj func) where
  continuous_add := by
    refine continuous_generateFrom_iff.mpr ?_
    rintro V hV
    let i := hV.choose
    let R := hV.choose_spec.choose
    have hRo := hV.choose_spec.choose_spec.1
    have hR := hV.choose_spec.choose_spec.2
    rw [hR]
    rw [← Set.preimage_comp]
    let G := InverseLimit obj func
    let Rinvadd := ((fun ⟨x, y⟩ ↦ x + y) : obj i × obj i → obj i) ⁻¹' R
    let hRinvaddo : IsOpen (Rinvadd) := by
      exact (continuous_add (M := obj i)).isOpen_preimage R hRo
    have hcomm : ((toComponent func i) ∘ (fun ⟨x, y⟩ ↦ x + y) : G × G → obj i) =
      (fun ⟨x, y⟩ ↦ x + y) ∘ (fun ⟨x, y⟩ ↦ (⟨toComponent func i x, toComponent func i y⟩ : obj i × obj i))  := by
      ext x
      simp
    rw [hcomm, Set.preimage_comp]
    simp only
    have hcont : Continuous (fun (⟨x, y⟩ : G × G) ↦
      (⟨toComponent func i x, toComponent func i y⟩ : obj i × obj i)) := by
      continuity
    exact hcont.isOpen_preimage _ hRinvaddo
  continuous_mul := by
    refine continuous_generateFrom_iff.mpr ?_
    rintro V hV
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
    exact hcont.isOpen_preimage _ hRinvaddo
  continuous_neg := by
    refine continuous_generateFrom_iff.mpr ?_
    rintro V hV
    let i := hV.choose
    let R := hV.choose_spec.choose
    have hRo := hV.choose_spec.choose_spec.1
    have hR := hV.choose_spec.choose_spec.2
    rw [hR]
    rw [← Set.preimage_comp]
    have hRnego : IsOpen (-R) := by exact IsOpen.neg hRo
    have hcomm : (toComponent func i) ∘ (fun x ↦ -x) = (fun x ↦ -x) ∘ (toComponent func i) := by
      ext x
      simp
    rw [hcomm]
    simp only [Set.inv_preimage]
    exact (toComponent_continuous func i).isOpen_preimage _ hRnego

end Ring.InverseLimit

namespace Group.InverseLimit

variable [∀ i : ι, Group (obj i)]
  [∀ i : ι, TopologicalSpace (obj i)]
  (func : ∀ {i j}, i ≤ j → obj j →* obj i)
  (cont : {i j : ι} → (h : i ≤ j) → Continuous (func h))

abbrev minimumOpens : Set (Set (InverseLimit obj func)) :=
    {V | ∃ (i : ι) (W : Set (obj i)), IsOpen W ∧ V = (toComponent func i) ⁻¹' W}

instance : TopologicalSpace (InverseLimit obj func) := .generateFrom <| minimumOpens func

@[continuity]
lemma map_of_maps_continuous {X : Type*} [TopologicalSpace X]
  (maps : (i : ι) → X → obj i) (comm : _) (maps_cont : (i : ι) → Continuous (maps i))
    : Continuous (map_of_maps func maps comm) := by
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

lemma minimumOpens_isOpen {s : Set (InverseLimit obj func)} : s ∈ minimumOpens func → IsOpen s :=
  GenerateOpen.basic s

@[continuity]
lemma toComponent_continuous (i : ι) : Continuous (toComponent func i) where
  isOpen_preimage R hR := by
    refine minimumOpens_isOpen func ?_
    simp only [Set.mem_setOf_eq]
    use i, R

instance [∀ i : ι, IsTopologicalGroup (obj i)] : IsTopologicalGroup (InverseLimit obj func) where
  continuous_mul := by
    refine continuous_generateFrom_iff.mpr ?_
    rintro V hV
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
    exact hcont.isOpen_preimage _ hRinvaddo
  continuous_inv := by
    refine continuous_generateFrom_iff.mpr ?_
    rintro V hV
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
    exact (toComponent_continuous func i).isOpen_preimage _ hRinvo

namespace Group.InverseLimit
