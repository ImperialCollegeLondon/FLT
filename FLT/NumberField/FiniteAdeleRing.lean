/-
Copyright (c) 2025 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/
import FLT.NumberField.Completion.Finite
import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
/-

# The finite adele ring of a number field is locally compact.

-/
open scoped TensorProduct

universe u

open NumberField IsDedekindDomain

section LocallyCompact

variable (K : Type*) [Field K] [NumberField K]

open HeightOneSpectrum

open IsDedekindDomain HeightOneSpectrum in
instance : LocallyCompactSpace (FiniteAdeleRing (𝓞 K) K) := by
  haveI : Fact (∀ (i : HeightOneSpectrum (𝓞 K)),
      IsOpen (adicCompletionIntegers K i : Set (adicCompletion K i))) :=
    .mk fun v ↦ isOpenAdicCompletionIntegers K v
  infer_instance

end LocallyCompact
