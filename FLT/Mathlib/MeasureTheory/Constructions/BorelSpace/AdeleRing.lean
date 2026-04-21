module

public import FLT.Mathlib.MeasureTheory.Constructions.BorelSpace.InfinitePlace
public import FLT.Mathlib.MeasureTheory.Constructions.BorelSpace.FiniteAdeleRing

@[expose] public section

variable (K : Type*) [Field K] [NumberField K]

open NumberField

instance : MeasurableSpace (AdeleRing (𝓞 K) K) := inferInstanceAs (MeasurableSpace (_ × _))

instance : BorelSpace (AdeleRing (𝓞 K) K) := inferInstanceAs (BorelSpace (_ × _))
