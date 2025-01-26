import Mathlib.Algebra.Group.Defs
import Mathlib.Analysis.SpecificLimits.Basic

open scoped Topology

theorem tendsto_one_add_pow {𝕜 : Type*} [LinearOrderedField 𝕜] [Archimedean 𝕜] [TopologicalSpace 𝕜]
    [OrderTopology 𝕜] {r : 𝕜} (h₁ : 0 ≤ r) (h₂ : r < 1) :
    Filter.Tendsto (fun n => 1 + r ^ n) Filter.atTop (𝓝 1) := by
  nth_rw 2 [← add_zero 1]
  exact Filter.Tendsto.const_add _ <| tendsto_pow_atTop_nhds_zero_of_lt_one h₁ h₂

theorem tendsto_one_sub_pow {𝕜 : Type*} [LinearOrderedField 𝕜] [Archimedean 𝕜] [TopologicalSpace 𝕜]
    [OrderTopology 𝕜] {r : 𝕜} (h₁ : 0 ≤ r) (h₂ : r < 1) :
    Filter.Tendsto (fun n => 1 - r ^ n) Filter.atTop (𝓝 1) := by
  nth_rw 2 [← sub_zero 1]
  exact Filter.Tendsto.const_sub _ <| tendsto_pow_atTop_nhds_zero_of_lt_one h₁ h₂
