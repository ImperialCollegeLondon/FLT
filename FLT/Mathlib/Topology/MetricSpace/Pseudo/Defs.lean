import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.Algebra.Ring.Basic

theorem DenseRange.exists_dist_lt_pi {α : Type*} [PseudoMetricSpace α] {β : Type*} {ι : Type*}
    {f : β → α} (hf : DenseRange f) (x : ι → α) {ε : ℝ} (hε : 0 < ε) :
    ∃ y : ι → β, ∀ i, dist (x i) (f (y i)) < ε :=
  ⟨fun i => (hf.exists_dist_lt (x i) hε).choose, fun i => (hf.exists_dist_lt (x i) hε).choose_spec⟩
