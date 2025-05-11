import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.Defs.Unbundled
import FLT.Deformation.ContinuousRepresentation.IsTopologicalModule
import FLT.Deformation.Algebra.InverseLimit.InverseLimit.Basic
import FLT.Deformation.Algebra.InverseLimit.Topology

open TopologicalSpace

variable {ι : Type*}
  [instSemilatticeSup : SemilatticeSup ι]
  [instOrderBot : OrderBot ι]
  [instDecidableEq : DecidableEq ι]
  {obj : (i : ι) → Type*}

namespace Module.InverseLimit

variable {R : Type*} [Ring R] [∀ i : ι, AddCommGroup (obj i)] [∀ i : ι, Module R (obj i)]
  [∀ i : ι, TopologicalSpace (obj i)]
  (func : ∀ {i j}, i ≤ j → obj j →ₗ[R] obj i)
  {cont : {i j : ι} → (h : i ≤ j) → Continuous (func h)}

instance [TopologicalSpace R] [IsTopologicalRing R]
    [∀ i : ι, IsTopologicalModule R (obj i)] : IsTopologicalModule R (InverseLimit obj func) where
  continuous_smul := by
    rw [minimumOpens_isSubbasis (cont := cont)]
    refine continuous_generateFrom_iff.mpr ?_
    rintro V ⟨i, X, hXo, hX⟩
    let M := InverseLimit obj func
    let Xinv := ((fun ⟨r, mi⟩ ↦ r • mi) : R × obj i → obj i) ⁻¹' X
    let hXinv : IsOpen (Xinv) := (continuous_smul (M := R) (X := obj i)).isOpen_preimage X hXo
    have hcomm : ((toComponent func i) ∘ (fun ⟨r, m⟩ ↦ r • m) : R × M → obj i) =
      (fun ⟨r, mi⟩ ↦ r • mi) ∘ (fun ⟨r, m⟩ ↦ (⟨r, toComponent func i m⟩ : R × obj i))  := by
      aesop
    have hcont : Continuous (fun (⟨r, m⟩ : R × M) ↦ (⟨r, toComponent func i m⟩ : R × obj i)) := by
      continuity
    rw [hX, ← Set.preimage_comp, hcomm, Set.preimage_comp, ← minimumOpens_isSubbasis (cont := cont)]
    exact hcont.isOpen_preimage _ hXinv
  continuous_add := by
    rw [minimumOpens_isSubbasis (cont := cont)]
    refine continuous_generateFrom_iff.mpr ?_
    rintro V ⟨i, R, hRo, hR⟩
    let G := InverseLimit obj func
    let Rinv := ((fun ⟨x, y⟩ ↦ x + y) : obj i × obj i → obj i) ⁻¹' R
    let hRinv : IsOpen (Rinv) := (continuous_add (M := obj i)).isOpen_preimage R hRo
    have hcomm : ((toComponent func i) ∘ (fun ⟨x, y⟩ ↦ x + y) : G × G → obj i) =
      (fun ⟨x, y⟩ ↦ x + y) ∘ (fun ⟨x, y⟩ ↦ (⟨toComponent func i x, toComponent func i y⟩ : obj i × obj i))  := by
      aesop
    have hcont : Continuous (fun (⟨x, y⟩ : G × G) ↦
      (⟨toComponent func i x, toComponent func i y⟩ : obj i × obj i)) := by
      continuity
    rw [hR, ← Set.preimage_comp, hcomm, Set.preimage_comp, ← minimumOpens_isSubbasis (cont := cont)]
    exact hcont.isOpen_preimage _ hRinv

end Module.InverseLimit

namespace Ring.InverseLimit

variable [∀ i : ι, Ring (obj i)]
  [∀ i : ι, TopologicalSpace (obj i)]
  (func : ∀ {i j}, i ≤ j → obj j →+* obj i)
  {cont : {i j : ι} → (h : i ≤ j) → Continuous (func h)}

instance [∀ i : ι, IsTopologicalRing (obj i)] : IsTopologicalRing (InverseLimit obj func) where
  continuous_add := by
    rw [minimumOpens_isSubbasis (cont := cont)]
    refine continuous_generateFrom_iff.mpr ?_
    rintro V ⟨i, R, hRo, hR⟩
    let G := InverseLimit obj func
    let Rinv := ((fun ⟨x, y⟩ ↦ x + y) : obj i × obj i → obj i) ⁻¹' R
    let hRinv : IsOpen (Rinv) := (continuous_add (M := obj i)).isOpen_preimage R hRo
    have hcomm : ((toComponent func i) ∘ (fun ⟨x, y⟩ ↦ x + y) : G × G → obj i) =
      (fun ⟨x, y⟩ ↦ x + y) ∘ (fun ⟨x, y⟩ ↦ (⟨toComponent func i x, toComponent func i y⟩ : obj i × obj i))  := by
      aesop
    have hcont : Continuous (fun (⟨x, y⟩ : G × G) ↦
      (⟨toComponent func i x, toComponent func i y⟩ : obj i × obj i)) := by
      continuity
    rw [hR, ← Set.preimage_comp, hcomm, Set.preimage_comp, ← minimumOpens_isSubbasis (cont := cont)]
    exact hcont.isOpen_preimage _ hRinv
  continuous_mul := by
    rw [minimumOpens_isSubbasis (cont := cont)]
    refine continuous_generateFrom_iff.mpr ?_
    rintro V ⟨i, R, hRo, hR⟩
    let G := InverseLimit obj func
    let Rinv := ((fun ⟨x, y⟩ ↦ x * y) : obj i × obj i → obj i) ⁻¹' R
    let hRinv : IsOpen (Rinv) := (continuous_mul (M := obj i)).isOpen_preimage R hRo
    have hcomm : ((toComponent func i) ∘ (fun ⟨x, y⟩ ↦ x * y) : G × G → obj i) =
      (fun ⟨x, y⟩ ↦ x * y) ∘ (fun ⟨x, y⟩ ↦ (⟨toComponent func i x, toComponent func i y⟩ : obj i × obj i))  := by
      aesop
    have hcont : Continuous (fun (⟨x, y⟩ : G × G) ↦
      (⟨toComponent func i x, toComponent func i y⟩ : obj i × obj i)) := by
      continuity
    rw [hR, ← Set.preimage_comp, hcomm, Set.preimage_comp, ← minimumOpens_isSubbasis (cont := cont)]
    exact hcont.isOpen_preimage _ hRinv
  continuous_neg := by
    rw [minimumOpens_isSubbasis (cont := cont)]
    refine continuous_generateFrom_iff.mpr ?_
    rintro V ⟨i, R, hRo, hR⟩
    have hRnego : IsOpen (-R) := by exact IsOpen.neg hRo
    have hcomm : (toComponent func i) ∘ (fun x ↦ -x) = (fun x ↦ -x) ∘ (toComponent func i) := by
      ext x
      simp
    rw [hR, ← Set.preimage_comp, hcomm, Set.preimage_comp, ← minimumOpens_isSubbasis (cont := cont)]
    exact (toComponent_continuous (cont := cont) func i).isOpen_preimage _ hRnego

end Ring.InverseLimit

namespace Group.InverseLimit

variable [∀ i : ι, Group (obj i)]
  [∀ i : ι, TopologicalSpace (obj i)]
  (func : ∀ {i j}, i ≤ j → obj j →* obj i)
  {cont : {i j : ι} → (h : i ≤ j) → Continuous (func h)}

instance [∀ i : ι, IsTopologicalGroup (obj i)] : IsTopologicalGroup (InverseLimit obj func) where
  continuous_mul := by
    rw [minimumOpens_isSubbasis (cont := cont)]
    refine continuous_generateFrom_iff.mpr ?_
    rintro V ⟨i, R, hRo, hR⟩
    let G := InverseLimit obj func
    let Rinv := ((fun ⟨x, y⟩ ↦ x * y) : obj i × obj i → obj i) ⁻¹' R
    let hRinv : IsOpen (Rinv) := (continuous_mul (M := obj i)).isOpen_preimage R hRo
    have hcomm : ((toComponent func i) ∘ (fun ⟨x, y⟩ ↦ x * y) : G × G → obj i) =
      (fun ⟨x, y⟩ ↦ x * y) ∘ (fun ⟨x, y⟩ ↦ (⟨toComponent func i x, toComponent func i y⟩ : obj i × obj i))  := by
      aesop
    have hcont : Continuous (fun (⟨x, y⟩ : G × G) ↦
      (⟨toComponent func i x, toComponent func i y⟩ : obj i × obj i)) := by
      continuity
    rw [hR, ← Set.preimage_comp, hcomm, Set.preimage_comp, ← minimumOpens_isSubbasis (cont := cont)]
    exact hcont.isOpen_preimage _ hRinv
  continuous_inv := by
    rw [minimumOpens_isSubbasis (cont := cont)]
    refine continuous_generateFrom_iff.mpr ?_
    rintro V ⟨i, R, hRo, hR⟩
    have hRo := IsOpen.inv hRo
    have hcomm : (toComponent func i) ∘ (fun x ↦ x⁻¹) = (fun x ↦ x⁻¹) ∘ (toComponent func i) := by
      ext x
      simp
    rw [hR, ← Set.preimage_comp, hcomm, Set.preimage_comp, ← minimumOpens_isSubbasis (cont := cont)]
    exact (toComponent_continuous (cont := cont) func i).isOpen_preimage _ hRo

namespace Group.InverseLimit
