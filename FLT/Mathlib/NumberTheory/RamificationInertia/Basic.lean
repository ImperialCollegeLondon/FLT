import Mathlib.NumberTheory.RamificationInertia.Basic

namespace Ideal

open IsDedekindDomain

/-- `Ideal.sum_ramification_inertia`, in the local (DVR) case. -/
lemma sum_ramification_inertia_of_isLocalRing {R : Type*} [CommRing R]
  (S : Type*) [CommRing S] (p : Ideal R) [IsDedekindDomain S] [Algebra R S]
  (K : Type u_1) (L : Type u_2) [Field K] [Field L] [IsLocalRing S]
  [IsDedekindDomain R] [Algebra R K] [IsFractionRing R K] [Algebra S L]
  [IsFractionRing S L] [Algebra K L] [Algebra R L] [IsScalarTower R S L]
  [IsScalarTower R K L] [Module.Finite R S] [p.IsMaximal] (hp0 : p ≠ ⊥)
    : ramificationIdx (algebraMap R S) p (IsLocalRing.maximalIdeal S) *
      p.inertiaDeg (IsLocalRing.maximalIdeal S) = Module.finrank K L := by
  have : NoZeroSMulDivisors R S := by
    have := FaithfulSMul.of_field_isFractionRing R S K L
    infer_instance
  rw [← sum_ramification_inertia S p K L hp0]
  symm
  apply Finset.sum_eq_single_of_mem
  · rw [← Finset.mem_coe, coe_primesOverFinset hp0]
    obtain ⟨w', hmax, hover⟩ := Ideal.exists_ideal_liesOver_maximal_of_isIntegral p S
    rw [← IsLocalRing.eq_maximalIdeal hmax]
    exact ⟨hmax.isPrime, hover⟩
  · intro b hb hnw
    absurd hnw
    rw [← Finset.mem_coe, coe_primesOverFinset hp0] at hb
    exact IsLocalRing.eq_maximalIdeal <| Ideal.primesOver.isMaximal ⟨b, hb⟩

end Ideal
