module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.NumberTheory.NumberField.AdeleRing

@[expose] public section

open NumberField

open InfinitePlace.Completion

variable (K : Type*) [Field K] [NumberField K] (v : InfinitePlace K)

-- TODO these should really be a proof of ProperSpace v.Completion etc

instance : SecondCountableTopology (v.Completion) :=
  (isometry_extensionEmbedding v).isEmbedding.isInducing.secondCountableTopology

instance : SecondCountableTopology (InfiniteAdeleRing K) :=
    inferInstanceAs (SecondCountableTopology (∀ _, _))
