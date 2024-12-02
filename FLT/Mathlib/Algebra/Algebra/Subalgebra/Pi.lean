import Mathlib.Algebra.Algebra.Pi
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.LinearAlgebra.Pi

def Subalgebra.pi {ι R : Type*} {S : ι → Type*} [CommSemiring R] [∀ i, Semiring (S i)]
    [∀ i, Algebra R (S i)] (t : Set ι) (s : ∀ i, Subalgebra R (S i)) : Subalgebra R (Π i, S i) where
  __ := Submodule.pi t (fun i ↦ (s i).toSubmodule)
  mul_mem' hx hy i hi := (s i).mul_mem (hx i hi) (hy i hi)
  algebraMap_mem' _ i _ := (s i).algebraMap_mem _
