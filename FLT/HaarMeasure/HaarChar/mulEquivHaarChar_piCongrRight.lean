import Mathlib
import FLT

set_option maxHeartbeats 20000000

section pi

variable {ι : Type*} {H : ι → Type*} [Π i, Group (H i)] [Π i, TopologicalSpace (H i)]
    [∀ i, IsTopologicalGroup (H i)] [∀ i, LocallyCompactSpace (H i)]
    [∀ i, MeasurableSpace (H i)] [∀ i, BorelSpace (H i)]

@[to_additive]
lemma mulEquivHaarChar_piCongrRight [Fintype ι] (ψ : Π i, (H i) ≃ₜ* (H i)) :
  letI : MeasurableSpace (Π i, H i) := borel _
  haveI : BorelSpace (Π i, H i) := ⟨rfl⟩
  mulEquivHaarChar (ContinuousMulEquiv.piCongrRight ψ) = ∏ i, mulEquivHaarChar (ψ i) := by
  sorry

end pi
