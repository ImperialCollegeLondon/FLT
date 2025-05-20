import Mathlib.Algebra.Module.Submodule.Basic
import Mathlib.Algebra.Ring.Subring.Basic

variable {R S : Type*} [CommRing R]

/-- If `S` is a subring of `R`, then `S` can be viewed as an `S`-submodule of `R`. -/
def Subring.toSubmodule {R : Type*} [CommRing R] (S : Subring R) : Submodule S R where
  __ := S
  smul_mem' x y h := by
    rw [smul_def, smul_eq_mul]
    apply S.mul_mem (SetLike.coe_mem x) h
