/-
Copyright (c) 2025 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/
import FLT.DedekindDomain.AdicValuation
import FLT.Mathlib.LinearAlgebra.Countable
import FLT.Mathlib.Topology.Algebra.Valued.WithZeroMulInt
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.NumberTheory.Padics.ProperSpace
import FLT.Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.NumberTheory.Padics.HeightOneSpectrum

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

set_option backward.isDefEq.respectTransparency false in
instance NumberField.instCompactSpaceAdicCompletionIntegers :
    CompactSpace (v.adicCompletionIntegers K) :=
  Valued.WithZeroMulInt.integer_compactSpace (v.adicCompletion K) inferInstance
    (v.valuedAdicCompletion_surjective K)

lemma NumberField.isCompactAdicCompletionIntegers :
    IsCompact (v.adicCompletionIntegers K : Set (v.adicCompletion K)) := by
  rw [isCompact_iff_compactSpace]
  exact instCompactSpaceAdicCompletionIntegers K v

lemma NumberField.isOpenAdicCompletionIntegers :
    IsOpen (v.adicCompletionIntegers K : Set (v.adicCompletion K)) :=
  Valued.isOpen_valuationSubring _

instance Rat.adicCompletion.locallyCompactSpace (v : HeightOneSpectrum (𝓞 ℚ)) :
    LocallyCompactSpace (v.adicCompletion ℚ) :=
  (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).toHomeomorph.isClosedEmbedding
  |>.locallyCompactSpace

instance (v : HeightOneSpectrum (𝓞 K)) :
    WeaklyLocallyCompactSpace (v.adicCompletion K) where
  exists_compact_mem_nhds x :=
    open Pointwise in
    ⟨x +ᵥ ((v.adicCompletionIntegers K) : Set (v.adicCompletion K)),
      (isCompact_iff_compactSpace.mpr <| instCompactSpaceAdicCompletionIntegers K v).vadd x,
      ((isOpenAdicCompletionIntegers K v).vadd x).mem_nhds (Set.mem_vadd_set.mpr ⟨0, by simp⟩)⟩

instance (v : HeightOneSpectrum (𝓞 K)) :
    LocallyCompactSpace (v.adicCompletion K) := inferInstance

-- does this exist upstream? Should do.
example (v : HeightOneSpectrum (𝓞 K)) : SecondCountableTopology (v.adicCompletion K) :=
  inferInstance
