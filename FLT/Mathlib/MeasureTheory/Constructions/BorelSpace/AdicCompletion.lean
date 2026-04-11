import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.RingTheory.DedekindDomain.AdicValuation

open NumberField

variable (K : Type*) [Field K] [NumberField K] (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))

noncomputable instance : MeasurableSpace (v.adicCompletion K) := borel _

instance : BorelSpace (v.adicCompletion K) := ⟨rfl⟩
