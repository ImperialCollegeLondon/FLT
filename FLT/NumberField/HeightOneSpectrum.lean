import FLT.DedekindDomain.IntegralClosure
import FLT.NumberField.Padics.RestrictedProduct

variable (K : Type*) [Field K] [NumberField K]

open IsDedekindDomain NumberField HeightOneSpectrum

-- should be in /Mathlib/Data/Countable/Basic.lean
lemma Countable.of_countable_fibres {X Y : Type*} {f : X → Y} [Countable Y]
    (h : ∀ (y : Y), (f ⁻¹' {y}).Countable) : Countable X := by
  simp_rw [← Set.countable_univ_iff, ← Set.preimage_univ (f := f), ← Set.iUnion_of_singleton,
    Set.preimage_iUnion, Set.countable_iUnion ‹_›]

instance : Countable (HeightOneSpectrum (𝓞 ℚ)) := Countable.of_equiv _
  IsDedekindDomain.HeightOneSpectrum.ratEquiv.symm

instance : Countable (HeightOneSpectrum (𝓞 K)) :=
  Countable.of_countable_fibres <| fun y ↦
  ((preimage_comap_finite (𝓞 ℚ) ℚ K (𝓞 K)) {y} (by simp)).countable
