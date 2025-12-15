import Mathlib.NumberTheory.NumberField.AdeleRing -- should be .InfiniteAdeleRing
import FLT.Mathlib.NumberTheory.NumberField.InfinitePlace.Completion

variable (K : Type*) [Field K] [NumberField K]

open NumberField InfinitePlace

instance : T2Space (InfiniteAdeleRing K) :=
  inferInstanceAs <| T2Space (Π _, _)

instance : SecondCountableTopology (InfiniteAdeleRing K) :=
  inferInstanceAs <| SecondCountableTopology (Π _, _)
