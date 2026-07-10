/-
Copyright (c) 2026 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll, Claude
-/
module

public import Mathlib.RingTheory.Polynomial.GaussLemma

/-!
# Monic divisors descend along the fraction field

Material for `Mathlib.RingTheory.Polynomial.GaussLemma`.
-/

@[expose] public section

open Polynomial

/-- Over an integrally closed domain `R` with fraction field `K`, a monic divisor `q ∈ K[X]` of
the image of a monic polynomial `P ∈ R[X]` is itself the image of a monic polynomial over `R`
(a form of Gauss's lemma, packaging `IsIntegrallyClosed.eq_map_mul_C_of_dvd`). -/
theorem Polynomial.Monic.exists_monic_map_eq_of_monic_dvd_map {R : Type*} [CommRing R]
    [IsIntegrallyClosed R] {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    {P : R[X]} (hP : P.Monic) {q : K[X]} (hq : q.Monic) (hdvd : q ∣ P.map (algebraMap R K)) :
    ∃ Q : R[X], Q.Monic ∧ Q.map (algebraMap R K) = q := by
  obtain ⟨Q, hQ⟩ := IsIntegrallyClosed.eq_map_mul_C_of_dvd K hP hdvd
  rw [hq.leadingCoeff, C_1, mul_one] at hQ
  exact ⟨Q, (IsFractionRing.injective R K).monic_map_iff.mpr (hQ ▸ hq), hQ⟩

end
