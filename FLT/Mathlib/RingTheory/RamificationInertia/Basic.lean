/-
Copyright (c) 2026 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/
module

public import Mathlib.NumberTheory.RamificationInertia.Inertia
public import Mathlib.NumberTheory.RamificationInertia.Ramification
public import Mathlib.RingTheory.RamificationInertia.Basic

/-!
# The fundamental identity, stated via `ramificationIdx'` and `inertiaDeg'`

`Mathlib.NumberTheory.RamificationInertia.Basic` has been deprecated in favour of
`Mathlib.RingTheory.RamificationInertia.Basic`, which states the fundamental identity
`∑ e * f = [L : K]` in terms of the unprimed `Ideal.ramificationIdx` and `Ideal.inertiaDeg`,
summing over the subtype `p.primesOver S`.

This file re-derives the two shapes of the identity that FLT uses, phrased with the primed
spellings `Ideal.ramificationIdx'` and `Ideal.inertiaDeg'` and summing over
`IsDedekindDomain.primesOverFinset p S`; they replace the deprecated
`Ideal.sum_ramification_inertia` and `Ideal.ramificationIdx_mul_inertiaDeg_of_isLocalRing`.
-/

@[expose] public section

namespace Ideal

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
  (S : Type*) [CommRing S] [IsDedekindDomain S] [Algebra R S] [Module.Finite R S]
  (K L : Type*) [Field K] [Field L] [Algebra R K] [IsFractionRing R K]
  [Algebra S L] [IsFractionRing S L] [Algebra K L] [Algebra R L]
  [IsScalarTower R S L] [IsScalarTower R K L]

/-- The **fundamental identity** of ramification index `e` and inertia degree `f`: for `P` ranging
over the primes lying over a maximal ideal `p`, `∑ P, e P * f P = [Frac(S) : Frac(R)]`.

This is `Ideal.sum_ramification_inertia_eq_finrank` restated in terms of `Ideal.ramificationIdx'`
and `Ideal.inertiaDeg'`. -/
theorem sum_ramificationIdx'_mul_inertiaDeg' {p : Ideal R} [p.IsMaximal] (hp0 : p ≠ ⊥) :
    ∑ P ∈ IsDedekindDomain.primesOverFinset p S,
      p.ramificationIdx' P * p.inertiaDeg' P = Module.finrank K L := by
  have : FaithfulSMul R S := FaithfulSMul.of_field_isFractionRing R S K L
  rw [IsFractionRing.finrank_eq R K S L, ← sum_ramification_inertia_eq_finrank p S,
    Finset.sum_subtype _ (fun _ ↦ IsDedekindDomain.mem_primesOverFinset_iff hp0 S)]
  refine Finset.sum_congr rfl fun P _ ↦ ?_
  have hP : P.1.IsPrime := P.2.1
  have : P.1.LiesOver p := P.2.2
  have : P.1.IsMaximal := hP.isMaximal (Ideal.ne_bot_of_mem_primesOver hp0 P.2)
  rw [ramificationIdx'_eq_ramificationIdx p P.1 hp0, inertiaDeg'_eq_inertiaDeg p P.1]

/-- `Ideal.sum_ramificationIdx'_mul_inertiaDeg'`, in the local (DVR) case. -/
theorem ramificationIdx'_mul_inertiaDeg'_of_isLocalRing [IsLocalRing S] {p : Ideal R}
    [p.IsMaximal] (hp0 : p ≠ ⊥) :
    p.ramificationIdx' (IsLocalRing.maximalIdeal S) *
      p.inertiaDeg' (IsLocalRing.maximalIdeal S) = Module.finrank K L := by
  have : FaithfulSMul R S := FaithfulSMul.of_field_isFractionRing R S K L
  simp_rw [← sum_ramificationIdx'_mul_inertiaDeg' S K L hp0,
    IsLocalRing.primesOverFinset_eq S hp0, Finset.sum_singleton]

end Ideal

end
