import FLT.Mathlib.Topology.MetricSpace.ProperSpace.InfinitePlace

open NumberField

open InfinitePlace.Completion

variable (K : Type*) [Field K] [NumberField K] (v : InfinitePlace K)

instance : MeasurableSpace (v.Completion) := borel _

instance : BorelSpace (v.Completion) := ⟨rfl⟩

instance : MeasurableSpace (InfiniteAdeleRing K) := inferInstanceAs (MeasurableSpace (∀ _, _))

instance : BorelSpace (InfiniteAdeleRing K) := inferInstanceAs (BorelSpace (∀ _, _))
