/-
Copyright (c) 2026 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/
module

public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.RamificationInertia.Basic

/-!
# The fundamental identity in the local case

`Ideal.sum_ramification_inertia_eq_finrank` says that if `S` is a finite flat algebra over a
domain `R` and `p` is a prime of `R`, then `∑ q, e q * f q = finrank R S`, the sum being over
the primes `q` of `S` above `p`. If `S` is local then there is exactly one such `q`, namely the
maximal ideal of `S`, and the identity becomes `e * f = finrank R S`.
-/

@[expose] public section

namespace Ideal

-- `ramificationIdx_mul_inertiaDeg_of_isLocalRing` is deprecated
-- in Aug 2026 so we use a longer name
/-- The **fundamental identity** `e * f = [S : R]` for a local ring `S`, finite over a Dedekind
domain `R`, and `p` a nonzero maximal ideal of `R`. -/
theorem ramificationIdx_mul_inertiaDeg_eq_finrank_of_isLocalRing
    {R : Type*} [CommRing R] [IsDedekindDomain R]
    (S : Type*) [CommRing S] [IsDedekindDomain S] [IsLocalRing S] [Algebra R S] [FaithfulSMul R S]
    [Module.Finite R S] {p : Ideal R} [p.IsMaximal] (hp0 : p ≠ ⊥) :
    (IsLocalRing.maximalIdeal S).ramificationIdx R *
      (IsLocalRing.maximalIdeal S).inertiaDeg R = Module.finrank R S := by
  have : IsDomain R := .of_faithfulSMul R S
  have hmax : IsLocalRing.maximalIdeal S ∈ p.primesOver S := by
    rw [IsLocalRing.primesOver_eq S hp0]; rfl
  have : (IsLocalRing.maximalIdeal S).LiesOver p := hmax.2
  have heq (q : p.primesOver S) : q.1 = IsLocalRing.maximalIdeal S :=
    IsLocalRing.eq_maximalIdeal (q.2.1.isMaximal (ne_bot_of_mem_primesOver hp0 q.2))
  have : Subsingleton (p.primesOver S) := ⟨fun q q' ↦ Subtype.ext ((heq q).trans (heq q').symm)⟩
  rw [← sum_ramification_inertia_eq_finrank p S,
    Fintype.sum_subsingleton _ (⟨IsLocalRing.maximalIdeal S, hmax⟩ : p.primesOver S)]

end Ideal

end
