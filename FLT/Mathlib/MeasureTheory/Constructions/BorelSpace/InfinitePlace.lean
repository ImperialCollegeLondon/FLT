import Mathlib.NumberTheory.NumberField.InfinitePlace.Completion

variable (K : Type*) [Field K] [NumberField K] (v : NumberField.InfinitePlace K) in
instance : MeasurableSpace (v.Completion) := borel _

variable (K : Type*) [Field K] [NumberField K] (v : NumberField.InfinitePlace K) in
instance : BorelSpace (v.Completion) := ⟨rfl⟩
