import Mathlib.RingTheory.Norm.Defs

namespace LinearMap
variable {M A B : Type*} [CommRing A] [CommRing B] [AddCommGroup M] [Algebra A B] [Module A M]
  [Module B M] [IsScalarTower A B M] [Module.Finite A B] [Module.Finite B M]
  [Module.Free A B] [Module.Free B M] -- remark: needed because stuff like det only works
  -- for free modules of finite rank

lemma det_restrictScalars (f : M →ₗ[B] M) : (f.restrictScalars A).det = Algebra.norm A f.det := by
  sorry
