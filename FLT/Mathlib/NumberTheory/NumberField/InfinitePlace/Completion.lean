import Mathlib.NumberTheory.NumberField.InfinitePlace.Completion

-- no better place to put it really, could go in .Basic but it's about completions
theorem AbsoluteValue.Completion.secondCountableTopology
    {K : Type*} [Field K] {v : AbsoluteValue K ℝ} {L : Type*}
    [NormedField L] [CompleteSpace L] {f : WithAbs v →+* L}
    [SecondCountableTopology L] (h : Isometry f) :
    SecondCountableTopology v.Completion :=
  h.completion_extension.isClosedEmbedding.isInducing.secondCountableTopology

instance NumberField.InfinitePlace.Completion.secondCountableTopology
    {K : Type*} [Field K] (v : InfinitePlace K) :
    SecondCountableTopology (v.Completion) :=
  AbsoluteValue.Completion.secondCountableTopology v.isometry_embedding
