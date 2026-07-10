/-
Copyright (c) 2025 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Salvatore Mercuri
-/
module

public import Mathlib.RingTheory.DedekindDomain.AdicValuation

/-!
# Adic Valuation

Material destined for Mathlib.
-/

@[expose] public section

namespace IsDedekindDomain.HeightOneSpectrum

-- TODO upstream
open IsDedekindDomain

instance {R : Type*} [CommRing R] [IsDedekindDomain R] (K : Type*) [Field K] [Countable K]
    [Algebra R K] [IsFractionRing R K] (v : HeightOneSpectrum R) :
    TopologicalSpace.SeparableSpace (v.adicCompletion K) where
  exists_countable_dense :=
    -- `adicCompletion` is now a one-field structure (not defeq to `Completion`), so use the
    -- mathlib-provided dense range of `algebraMap K → adicCompletion` and `K`'s countability.
    ⟨Set.range (algebraMap K (v.adicCompletion K)),
      Set.countable_range _, denseRange_algebraMap K v⟩

lemma intValuation_eq_coe_neg_multiplicity {A : Type*} [CommRing A] [IsDedekindDomain A]
    (v : HeightOneSpectrum A) {a : A} (hnz : a ≠ 0) :
    v.intValuation a = WithZero.exp (-(multiplicity v.asIdeal (Ideal.span {a}) : ℤ)) := by
  classical
  have hnb : Ideal.span {a} ≠ ⊥ := by
    rwa [ne_eq, Ideal.span_singleton_eq_bot]
  rw [intValuation_if_neg _ hnz, Ideal.count_associates_factors_eq hnb v.isPrime v.ne_bot]
  nth_rw 1 [← normalize_eq v.asIdeal]
  congr
  symm
  apply multiplicity_eq_of_emultiplicity_eq_some
  rw [← UniqueFactorizationMonoid.emultiplicity_eq_count_normalizedFactors v.irreducible hnb]

/-- `adicCompletion.equiv` as a `K`-algebra isomorphism onto the underlying completion. -/
noncomputable def adicCompletion.algEquiv
    {A : Type*} [CommRing A] [IsDedekindDomain A] (K : Type*) [Field K] [Algebra A K]
    [IsFractionRing A K] (v : HeightOneSpectrum A) :
    v.adicCompletion K ≃ₐ[K] (v.valuation K).Completion :=
  AlgEquiv.ofRingEquiv (f := adicCompletion.equiv K v)
    fun x => algebraMap_adicCompletion_toCompletion A K v x

end IsDedekindDomain.HeightOneSpectrum
