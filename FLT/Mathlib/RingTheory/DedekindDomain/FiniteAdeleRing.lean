import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
import FLT.Mathlib.Topology.Algebra.RestrictedProduct.Basic

namespace IsDedekindDomain.HeightOneSpectrum.FiniteAdeleRing

variable (R K : Type*) [CommRing R] [Field K] [IsDedekindDomain R] [Algebra R K]
  [IsFractionRing R K]

/-- The integral adele subring inside the finite adele ring. -/
abbrev integralAdeles : Subring (FiniteAdeleRing R K) :=
  RestrictedProduct.structureSubring _ _ _

end IsDedekindDomain.HeightOneSpectrum.FiniteAdeleRing
