import Mathlib.RingTheory.DedekindDomain.AdicValuation

theorem IsDedekindDomain.HeightOneSpectrum.adicValued_apply'
  {R : Type*} [CommRing R] [IsDedekindDomain R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K] (v : HeightOneSpectrum R)
  {x : WithVal (v.valuation K)} :
  Valued.v x = v.valuation K x := rfl
