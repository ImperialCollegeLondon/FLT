import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Topology.Instances.Matrix
import FLT.Mathlib.Topology.Constructions

/-- Let `A : X → Matrix n n R` be a parameterisation of a matrix ring with entries in a
seminormed commutative ring `R` by a metric space `X` and let `f : Y → X` be dense.
If the identity matrix is in the parameterisation `A`, then there exists a
`y : Y` such that `A (f y)` has non-zero determinant. -/
theorem DenseRange.exists_matrix_det_ne_zero {X Y n R : Type*} [PseudoMetricSpace X]
    [Fintype n] [DecidableEq n] [SeminormedCommRing R] [NormOneClass R]
    [IsTopologicalRing R] {A : X → Matrix n n R} {f : Y → X} (hA : Continuous A) (hf : DenseRange f)
    {b : X} (hb : A b = 1) :
    ∃ y, (A (f y)).det ≠ 0 := by
  replace hf := hf.codRestrict_comp (Continuous.matrix_det hA)
  simp [Metric.denseRange_iff] at hf
  let ⟨y, h⟩ := hf (A b).det b rfl (1 / 2) (by linarith)
  exact ⟨y, fun hc => by simp [Subtype.dist_eq, hc, hb] at h; linarith⟩
