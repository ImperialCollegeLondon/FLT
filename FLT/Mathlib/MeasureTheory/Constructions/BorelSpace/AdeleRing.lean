import FLT.Mathlib.MeasureTheory.Constructions.BorelSpace.InfinitePlace
import FLT.Mathlib.MeasureTheory.Constructions.BorelSpace.FiniteAdeleRing

variable (K : Type*) [Field K] [NumberField K]

open NumberField

instance : MeasurableSpace (AdeleRing (𝓞 K) K) := inferInstanceAs (MeasurableSpace (_ × _))

instance : BorelSpace (AdeleRing (𝓞 K) K) := inferInstanceAs (BorelSpace (_ × _))
