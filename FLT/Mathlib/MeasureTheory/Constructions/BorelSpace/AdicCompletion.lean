module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.RingTheory.DedekindDomain.AdicValuation

@[expose] public section

open NumberField

variable (K : Type*) [Field K] [NumberField K] (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))

noncomputable instance : MeasurableSpace (v.adicCompletion K) := borel _

instance : BorelSpace (v.adicCompletion K) := ⟨rfl⟩
