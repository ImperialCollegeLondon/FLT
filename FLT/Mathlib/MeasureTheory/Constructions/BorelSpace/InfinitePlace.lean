import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.NumberTheory.NumberField.AdeleRing

open NumberField

variable (K : Type*) [Field K] [NumberField K] (v : InfinitePlace K)

instance : MeasurableSpace (v.Completion) := borel _

instance : BorelSpace (v.Completion) := ⟨rfl⟩

open InfinitePlace.Completion

instance : SecondCountableTopology (v.Completion) :=
  (isometry_extensionEmbedding v).isEmbedding.isInducing.secondCountableTopology

instance : MeasurableSpace (InfiniteAdeleRing K) := inferInstanceAs (MeasurableSpace (∀ _, _))

instance : BorelSpace (InfiniteAdeleRing K) := inferInstanceAs (BorelSpace (∀ _, _))

instance : SecondCountableTopology (InfiniteAdeleRing K) :=
    inferInstanceAs (SecondCountableTopology (∀ _, _))
