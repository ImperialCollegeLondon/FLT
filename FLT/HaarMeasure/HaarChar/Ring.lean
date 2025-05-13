/-
Copyright (c) 2024 Andrew Yang, Yaël Dillies, Javier López-Contreras. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang, Yaël Dillies, Javier López-Contreras
-/
import Mathlib.MeasureTheory.Measure.Haar.DistribChar

open scoped NNReal Pointwise ENNReal

namespace MeasureTheory

variable (R : Type*) [Ring R] [MeasurableSpace R] [TopologicalSpace R] [BorelSpace R]
  [IsTopologicalAddGroup R] [LocallyCompactSpace R]

/-- The σ-algebra on Rˣ coming from pulling back the σ-algebra on R × R along the usual
embedding g ↦ (g,g⁻¹). -/
local instance : MeasurableSpace Rˣ := MeasurableSpace.comap (Units.embedProduct R) inferInstance

local instance : MeasurableSMul Rˣ R := sorry -- TODO need advice from measure theorists

local instance : ContinuousConstSMul Rˣ R := sorry -- TODO need advice from measure theorists

noncomputable example : Rˣ → ℝ≥0 := distribHaarChar R

/-- The subgroup R^(1) of the units Rˣ of a locally compact topological ring R
consisting of the elements such that multiplication by them doesn't scale Haar measure.
-/
noncomputable def distribHaarChar.ker := MonoidHom.ker (distribHaarChar R : Rˣ →* ℝ≥0)

end MeasureTheory
