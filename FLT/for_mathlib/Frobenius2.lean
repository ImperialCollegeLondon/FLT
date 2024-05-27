/-
Copyright (c) 2024 Jou Glasheen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jou Glasheen, Amelia Livingston, Jujian Zhang, Kevin Buzzard
-/
import Mathlib.RingTheory.DedekindDomain.Ideal
import Mathlib.RingTheory.IntegralRestrict
import Mathlib.RingTheory.Ideal.QuotientOperations
import Mathlib.FieldTheory.Cardinality

variable (A : Type*) [CommRing A] (B : Type*) [CommRing B] [Algebra A B]

instance : MulDistribMulAction (B ≃ₐ[A] B) (Ideal B) where
  smul σ I := Ideal.comap σ.symm I
  one_smul I := I.comap_id
  smul_one σ := by simp only [Ideal.one_eq_top]; rfl
  mul_smul _ _ _ := rfl
  smul_mul σ I J := by
    refine le_antisymm (fun x ↦ ?_ : Ideal.comap _ _ ≤ _) (Ideal.le_comap_mul _)
    obtain ⟨y, rfl⟩ : ∃ y, σ y = x := ⟨σ.symm x, σ.apply_symm_apply x⟩
    rw [Ideal.mem_comap, AlgEquiv.symm_apply_apply, ← Ideal.mem_comap]
    revert y
    refine Ideal.mul_le.mpr (fun r hr s hs ↦ ?_)
    simp only [Ideal.mem_comap, map_mul]
    exact Ideal.mul_mem_mul (Ideal.mem_comap.2 (by simp [hr])) (Ideal.mem_comap.2 <| by simp [hs])

/-
Auxiliary lemma: if `Q` is a maximal ideal of a non-field Dedekind Domain `B` with a Galois action
and if `b ∈ B` then there's an element of `B` which is `b` mod `Q` and `0` modulo all the other
Galois conjugates of `Q`.
-/
lemma DedekindDomain.exists_generator [IsDedekindDomain B] (hB : ¬IsField B) [Fintype (B ≃ₐ[A] B)]
    [DecidableEq (Ideal B)] (Q : Ideal B) [Q.IsMaximal] (b : B) : ∃ y : B,
    y - b ∈ Q ∧ ∀ Q' : Ideal B, Q' ∈ MulAction.orbit (B ≃ₐ[A] B) Q → Q' ≠ Q → y ∈ Q' := by
  let O : Set (Ideal B) := MulAction.orbit (B ≃ₐ[A] B) Q
  have hO : O.Finite := Set.finite_range _
  have hPrime : ∀ Q' ∈ hO.toFinset, Prime Q' := by
    intro Q' hQ'
    rw [Set.Finite.mem_toFinset] at hQ'
    obtain ⟨σ, rfl⟩ := hQ'
    apply (MulEquiv.prime_iff <| MulDistribMulAction.toMulEquiv (Ideal B) σ).mp
    refine Q.prime_of_isPrime (Q.bot_lt_of_maximal hB).ne' ?_
    apply Ideal.IsMaximal.isPrime inferInstance
  obtain ⟨y, hy⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := hO.toFinset) id (fun _ ↦ 1)
    hPrime (fun _ _ _ _ ↦ id) (fun Q' ↦ if Q' = Q then b else 0)
  simp only [Set.Finite.mem_toFinset, id_eq, pow_one] at hy
  refine ⟨y, ?_, ?_⟩
  · specialize hy Q ⟨1, by simp⟩
    simpa only using hy
  · rintro Q' ⟨σ, rfl⟩ hQ'
    specialize hy (σ • Q) ⟨σ, by simp⟩
    simp_all
