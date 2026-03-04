/-
Copyright (c) 2025 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/

-- if I can get all imports as FLT.Mathlib then I can upstream
import FLT.Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
import FLT.Mathlib.Topology.Algebra.RestrictedProduct.TopologicalSpace
import FLT.NumberField.Completion.Finite
import FLT.NumberField.HeightOneSpectrum

/-

# The finite adele ring of a number field is locally compact.

-/
open scoped TensorProduct

universe u

open NumberField IsDedekindDomain RestrictedProduct

section Instances

variable (K : Type*) [Field K] [NumberField K]

open HeightOneSpectrum

open IsDedekindDomain HeightOneSpectrum RestrictedProduct in
instance : LocallyCompactSpace (FiniteAdeleRing (𝓞 K) K) :=
  haveI : Fact (∀ (i : HeightOneSpectrum (𝓞 K)),
      IsOpen (adicCompletionIntegers K i : Set (adicCompletion K i))) :=
    ⟨isOpenAdicCompletionIntegers K⟩
  inferInstanceAs <| LocallyCompactSpace (Πʳ _, [_, _])

instance : CompactSpace (IsDedekindDomain.FiniteAdeleRing.integralAdeles (𝓞 K) K) :=
  isCompact_iff_compactSpace.1 <|
  isCompact_range RestrictedProduct.isEmbedding_structureMap.continuous

instance : T2Space (FiniteAdeleRing (𝓞 K) K) :=
  inferInstanceAs <| T2Space (Πʳ _, [_, _])

instance : SecondCountableTopology (FiniteAdeleRing (𝓞 K) K) :=
  RestrictedProduct.secondCountableTopology (isOpenAdicCompletionIntegers K)

end Instances
