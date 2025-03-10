import Mathlib.Analysis.Normed.Ring.Seminorm
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.MetricSpace.Pseudo.Pi
import FLT.Mathlib.Topology.MetricSpace.Pseudo.Defs

/-- Given a parameterisation `A` of a matrix ring `Matrix n n R` with entries in a metric space `R`
by a metric space `n → X` and a dense map `Y → X`, to any `A b` there exists some `y : n → Y` such
that the determinant `A (f y)` is arbitrarily close to the determinany of `A b`. -/
theorem DenseRange.exists_dist_lt_matrix_det_pi {X Y n R : Type*} [PseudoMetricSpace X]
    [PseudoMetricSpace R] [Fintype n] [DecidableEq n] [CommRing R] [IsTopologicalRing R]
    {A : (n → X) → Matrix n n R} {f : Y → X} (hA : Continuous A) (hf : DenseRange f) (ε : ℝ)
    (hε : 0 < ε) (b : n → X) :
    ∃ (y : n → Y), dist (A b).det (A fun i => f (y i)).det < ε  := by
  have := Metric.continuous_iff.1 (Continuous.matrix_det hA)
  simp_rw [dist_comm] at this
  choose δ hδ using this b ε hε
  choose α hα using hf.exists_dist_lt_pi b hδ.1
  refine ⟨α, hδ.2 _ ?_⟩
  erw [dist_pi_def, show δ = ↑(⟨δ, by linarith⟩ : NNReal) by rfl, NNReal.coe_lt_coe]
  exact (Finset.sup_lt_iff hδ.1).2 fun i _ => hα i

/-- Let `A` be a parameterisation of a matrix ring `Matrix n n R` with entries in a
seminormed commutative ring `R` by a metric space `n → X` and let `f : Y → X` be dense.
Suppose that the identity matrix is in the parameterisation `A`. Then there exists a
`y : n → Y` such that `A (f y)` has non-zero determinant. -/
theorem DenseRange.exists_matrix_det_ne_zero {X Y n R : Type*} [PseudoMetricSpace X]
    [Fintype n] [DecidableEq n] [SeminormedCommRing R] [NormOneClass R] [IsTopologicalRing R]
    {A : (n → X) → Matrix n n R} {f : Y → X} (hA : Continuous A) (hf : DenseRange f)
    {b : n → X} (hb : A b = 1) : ∃ (y : n → Y), (A fun i => f (y i)).det ≠ 0 := by
  let ⟨y, h⟩ := hf.exists_dist_lt_matrix_det_pi hA (1 / 2) (by linarith) b
  refine ⟨y, fun hc => ?_⟩
  simp [hb, hc, dist_zero_right, norm_one] at h
  linarith
