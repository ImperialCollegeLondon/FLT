module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing

@[expose] public section

variable (K : Type*) [Field K] [NumberField K]

open NumberField

open IsDedekindDomain

noncomputable instance : MeasurableSpace (FiniteAdeleRing (𝓞 K) K) := borel _

instance : BorelSpace (FiniteAdeleRing (𝓞 K) K) := ⟨rfl⟩
