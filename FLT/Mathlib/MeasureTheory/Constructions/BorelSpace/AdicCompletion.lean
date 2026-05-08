/-
Copyright (c) 2025 Bryan Wang Peng Jun. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Wang Peng Jun, Kevin Buzzard
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.RingTheory.DedekindDomain.AdicValuation

/-!
# Adic Completion

Material destined for Mathlib.
-/

@[expose] public section

open NumberField

variable (K : Type*) [Field K] [NumberField K] (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))

noncomputable instance : MeasurableSpace (v.adicCompletion K) := borel _

instance : BorelSpace (v.adicCompletion K) := ⟨rfl⟩
