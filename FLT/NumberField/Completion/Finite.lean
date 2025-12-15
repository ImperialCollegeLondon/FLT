/-
Copyright (c) 2025 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/
import FLT.DedekindDomain.AdicValuation
import FLT.Mathlib.LinearAlgebra.Countable
import FLT.Mathlib.Topology.Algebra.Valued.WithZeroMulInt
import FLT.NumberField.Padics.RestrictedProduct
import Mathlib.NumberTheory.NumberField.FinitePlaces
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.Topology.MetricSpace.Polish

/-!

# Completion of a number field at a finite place

-/

variable (K : Type*) [Field K] [NumberField K]

open NumberField

example (I : Ideal (𝓞 K)) (hI : I ≠ 0) : Finite ((𝓞 K) ⧸ I) :=
  Ideal.finiteQuotientOfFreeOfNeBot I hI

open IsDedekindDomain

variable (v : HeightOneSpectrum (𝓞 K))

open IsLocalRing

instance NumberField.instFiniteResidueFieldAdicCompletionIntegers :
    Finite (ResidueField (v.adicCompletionIntegers K)) := by
  apply (HeightOneSpectrum.ResidueFieldEquivCompletionResidueField K v).toEquiv.finite_iff.mp
  exact Ideal.finiteQuotientOfFreeOfNeBot v.asIdeal v.ne_bot

open scoped Valued in
instance : Finite (𝓀[v.adicCompletion K]) :=
  inferInstanceAs (Finite (ResidueField (v.adicCompletionIntegers K)))

instance NumberField.instCompactSpaceAdicCompletionIntegers :
    CompactSpace (v.adicCompletionIntegers K) :=
  Valued.WithZeroMulInt.integer_compactSpace (v.adicCompletion K) inferInstance

lemma NumberField.isOpenAdicCompletionIntegers :
    IsOpen (v.adicCompletionIntegers K : Set (v.adicCompletion K)) :=
  Valued.isOpen_valuationSubring _

instance Rat.adicCompletion.locallyCompactSpace (v : HeightOneSpectrum (𝓞 ℚ)) :
    LocallyCompactSpace (v.adicCompletion ℚ) :=
  v.padicUniformEquiv.toHomeomorph.isClosedEmbedding.locallyCompactSpace

instance : TopologicalSpace.SeparableSpace (v.adicCompletion K) where
    exists_countable_dense := ⟨Set.range ((↑) : K → v.adicCompletion K),
  by
    have : Countable (WithVal (HeightOneSpectrum.valuation K v)) :=
      inferInstanceAs <| Countable K
    exact Set.countable_range _,
  UniformSpace.Completion.denseRange_coe⟩

example (v : HeightOneSpectrum (𝓞 K)) : SecondCountableTopology (v.adicCompletion K) :=
  inferInstance
