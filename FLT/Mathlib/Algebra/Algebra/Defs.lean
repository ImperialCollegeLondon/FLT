import Mathlib.Algebra.Algebra.Defs
import Mathlib.RingTheory.Ideal.Quotient.Defs

variable {R : Type*} [CommRing R]

instance idealQuotient_instAlgebra {X : Type*} [CommRing X] [Algebra R X] (a : Ideal X) : Algebra R (X ⧸ a) :=
  (RingHom.comp (Ideal.Quotient.mk a) (algebraMap R X)).toAlgebra
