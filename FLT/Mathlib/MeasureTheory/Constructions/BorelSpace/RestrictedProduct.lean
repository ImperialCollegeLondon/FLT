module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.Topology.Algebra.RestrictedProduct.TopologicalSpace

@[expose] public section

/-

If a restricted product of measurable spaces is made into a measurable space in e.g. mathlib
then the measurable space instance below should be removed, and the Borel space instance
should be replaced by the appropriate theorem (which will presumably need second countability
assumptions everywhere) saying that a restricted product of Borel spaces is a Borel space.

-/

variable {ι : Type*} (R : ι → Type*) (A : (i : ι) → Set (R i)) (𝓕 : Filter ι)
  [(i : ι) → TopologicalSpace (R i)]

open scoped RestrictedProduct

instance : MeasurableSpace Πʳ (i : ι), [R i, A i]_[𝓕] := borel _

instance : BorelSpace Πʳ (i : ι), [R i, A i]_[𝓕] := ⟨rfl⟩
