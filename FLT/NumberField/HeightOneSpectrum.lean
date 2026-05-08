/-
Copyright (c) 2025 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/
module

public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import FLT.DedekindDomain.IntegralClosure
import Mathlib.NumberTheory.Padics.HeightOneSpectrum

/-!
# The height-one spectrum of a number field

Basic countability instances for the height-one spectrum of `𝓞_K`, the ring
of integers of a number field `K`.
-/

@[expose] public section

-- should be upstreamed but I'll need to extract
variable (K : Type*) [Field K] [NumberField K]

open IsDedekindDomain NumberField HeightOneSpectrum

instance : Countable (HeightOneSpectrum (𝓞 ℚ)) := Countable.of_equiv _
  Rat.HeightOneSpectrum.primesEquiv.symm

instance : Countable (HeightOneSpectrum (𝓞 K)) :=
  Set.Countable.of_preimage_singleton <| fun y ↦
  ((preimage_comap_finite (𝓞 ℚ) ℚ K (𝓞 K)) {y} (by simp)).countable
