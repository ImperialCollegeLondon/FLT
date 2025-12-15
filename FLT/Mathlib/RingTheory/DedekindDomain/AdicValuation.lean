import Mathlib.RingTheory.DedekindDomain.AdicValuation
-- TODO upstream
open IsDedekindDomain in
instance {R : Type*} [CommRing R] [IsDedekindDomain R] (K : Type*) [Field K] [Countable K]
    [Algebra R K] [IsFractionRing R K] (v : HeightOneSpectrum R) :
    TopologicalSpace.SeparableSpace (v.adicCompletion K) where
    exists_countable_dense := ⟨Set.range ((↑) : K → v.adicCompletion K),
  by
    have : Countable (WithVal (HeightOneSpectrum.valuation K v)) :=
      inferInstanceAs <| Countable K
    exact Set.countable_range _,
  UniformSpace.Completion.denseRange_coe⟩
