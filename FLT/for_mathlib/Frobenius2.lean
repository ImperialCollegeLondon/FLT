/-
Copyright (c) 2024 Jou Glasheen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jou Glasheen, Amelia Livingston, Jujian Zhang, Kevin Buzzard
-/
import Mathlib.RingTheory.DedekindDomain.Ideal
import Mathlib.RingTheory.IntegralRestrict
import Mathlib.RingTheory.Ideal.QuotientOperations
import Mathlib.FieldTheory.Cardinality

/-

# Frobenius elements

Definition of Frob_Q ∈ Gal(L/K) where L/K is a finite Galois extension of number fields
and Q is a maximal ideal of the integers of L. In fact we work in sufficient generality
that the definition will also work in the function field over a finite field setting.

## The proof

We follow a proof by Milne. Let B be the integers of L. The Galois orbit of Q consists of Q and
possibly various other maximal ideals Q'. We know (B/Q)ˣ is finite hence cyclic; choose a
generator g. By the Chinese Remainder Theorem we may choose y ∈ B which reduces to g mod Q and
to 0 modulo all other primes Q' in the Galois orbit of Q. The polynomial F = ∏ (X - σ y), the
product running over σ in the Galois group, is in B[X] and is Galois-stable so is in fact in A[X]
where A is the integers of K. If q denotes the size of A / (A ∩ Q) and if Fbar is F mod Q
then Fbar has coefficients in 𝔽_q and thus Fbar(y^q)=Fbar(y)^q=0, meaning that y^q is a root
of Fbar and thus congruent to σ y mod Q for some σ. This σ can be checked to have the following
properties:

1) σ Q = Q
2) σ g = g^q mod Q

and because g is a generator this means that σ is in fact the q'th power map mod Q, which
is what we want.

## Note

This was Jou Glasheen's final project for Kevin Buzzard's Formalising Mathematics course.

-/
variable (A : Type*) [CommRing A] {B : Type*} [CommRing B] [Algebra A B]

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
lemma DedekindDomain.exists_y [IsDedekindDomain B] (hB : ¬IsField B) [Fintype (B ≃ₐ[A] B)]
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

lemma exists_y [Fintype (B ≃ₐ[A] B)] [DecidableEq (Ideal B)] (Q : Ideal B) [Q.IsMaximal] (b : B) :
    ∃ y : B, y - b ∈ Q ∧ ∀ Q' : Ideal B, Q' ∈ MulAction.orbit (B ≃ₐ[A] B) Q → Q' ≠ Q → y ∈ Q' := by
  let O : Set (Ideal B) := MulAction.orbit (B ≃ₐ[A] B) Q
  have hO' : Finite (O : Type _) := Set.finite_range _
  have hmax (I : O) : Ideal.IsMaximal (I : Ideal B) := by
    rcases I with ⟨_, σ, rfl⟩
    exact Ideal.comap_isMaximal_of_surjective _ (AlgEquiv.surjective σ.symm)
  have hPairwise : Pairwise fun (I : O) (J : O) ↦ IsCoprime (I : Ideal B) J := fun x y h ↦ ⟨1, 1, by
    simp only [Ideal.one_eq_top, Ideal.top_mul]
    exact Ideal.IsMaximal.coprime_of_ne (hmax x) (hmax y) <| mt Subtype.ext h⟩
  obtain ⟨y, hy⟩ := Ideal.exists_forall_sub_mem_ideal (ι := O) hPairwise
    (fun J ↦ if J = ⟨Q, 1, rfl⟩ then b else 0)
  refine ⟨y, ?_, ?_⟩
  · specialize hy ⟨Q, 1, Q.comap_id⟩
    simpa only using hy
  · rintro Q' ⟨σ, rfl⟩ hQ'
    specialize hy ⟨σ • Q, σ, rfl⟩
    simp_all

variable (Q : Ideal B) [Q.IsMaximal] [Fintype (B ⧸ Q)]

noncomputable abbrev g : (B ⧸ Q)ˣ := (IsCyclic.exists_monoid_generator (α := (B ⧸ Q)ˣ)).choose

lemma g_spec : ∀ (z : (B ⧸ Q)ˣ), z ∈ Submonoid.powers (g Q) :=
  (IsCyclic.exists_monoid_generator (α := (B ⧸ Q)ˣ)).choose_spec

noncomputable abbrev b : B := (Ideal.Quotient.mk_surjective (g Q : B ⧸ Q)).choose

lemma b_spec : ((b Q : B) : B ⧸ Q) = g Q := (Ideal.Quotient.mk_surjective (g Q : B ⧸ Q)).choose_spec

variable [Fintype (B ≃ₐ[A] B)] [DecidableEq (Ideal B)]

noncomputable abbrev y : B :=
  (exists_y A Q (b Q)).choose

lemma y_spec : (y A Q) - (b Q) ∈ Q ∧
    ∀ Q' : Ideal B, Q' ∈ MulAction.orbit (B ≃ₐ[A] B) Q → Q' ≠ Q → (y A Q) ∈ Q' :=
  (exists_y A Q (b Q)).choose_spec

open Polynomial BigOperators

/-- `F : B[X]` defined to be a product of linear factors `(X - τ • α)`; where
`τ` runs over `L ≃ₐ[K] L`, and `α : B` is an element which generates `(B ⧸ Q)ˣ`
and lies in `τ • Q` for all `τ ∉ (decomposition_subgroup_Ideal'  A K L B Q)`.-/
noncomputable abbrev F : B[X] := ∏ τ : B ≃ₐ[A] B, (X - C (τ • (y A Q)))
