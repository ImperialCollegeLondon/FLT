/-
Copyright (c) 2025 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/
import Mathlib.NumberTheory.NumberField.AdeleRing
import FLT.DedekindDomain.AdicValuation
/-!

# Completion of a number field at a finite place

-/

variable (K : Type) [Field K] [NumberField K]

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

instance NumberField.instCompactSpaceAdicCompletionIntegers :
    CompactSpace (v.adicCompletionIntegers K) := sorry -- issue FLT#451
