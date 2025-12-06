import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.RingTheory.DedekindDomain.AdicValuation

open NumberField in
variable (K : Type*) [Field K] [NumberField K] (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) in
instance : MeasurableSpace (v.adicCompletion K) := borel _

open NumberField in
variable (K : Type*) [Field K] [NumberField K] (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) in
instance : BorelSpace (v.adicCompletion K) := ⟨rfl⟩
