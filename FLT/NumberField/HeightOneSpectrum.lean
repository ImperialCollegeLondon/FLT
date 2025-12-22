import FLT.DedekindDomain.IntegralClosure
import FLT.Mathlib.Data.Set.Countable
import FLT.NumberField.Padics.RestrictedProduct
import Mathlib.NumberTheory.Padics.HeightOneSpectrum

-- should be upstreamed but I'll need to extract
variable (K : Type*) [Field K] [NumberField K]

open IsDedekindDomain NumberField HeightOneSpectrum

instance : Countable (HeightOneSpectrum (𝓞 ℚ)) := Countable.of_equiv _
  Rat.HeightOneSpectrum.primesEquiv.symm

instance : Countable (HeightOneSpectrum (𝓞 K)) :=
  Countable.of_countable_fibres <| fun y ↦
  ((preimage_comap_finite (𝓞 ℚ) ℚ K (𝓞 K)) {y} (by simp)).countable
