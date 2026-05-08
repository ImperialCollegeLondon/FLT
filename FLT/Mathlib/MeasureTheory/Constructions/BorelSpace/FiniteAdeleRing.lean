/-
Copyright (c) 2025 Bryan Wang Peng Jun. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Wang Peng Jun, Kevin Buzzard
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing

/-!
# Finite Adele Ring

Material destined for Mathlib.
-/

@[expose] public section

variable (K : Type*) [Field K] [NumberField K]

open NumberField

open IsDedekindDomain

noncomputable instance : MeasurableSpace (FiniteAdeleRing (𝓞 K) K) := borel _

instance : BorelSpace (FiniteAdeleRing (𝓞 K) K) := ⟨rfl⟩
