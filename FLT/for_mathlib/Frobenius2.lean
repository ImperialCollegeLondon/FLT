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

Frobenius elements in Galois groups.

## Statement of the theorem

Say `L/K` is a finite Galois extension of number fields, with integer rings `B/A`,
and say `Q` is a maximal ideal of `B` dividing `P` of `A`. This file contains the
construction of an element `Frob Q` in `Gal(L/K)`, and a proof that
modulo `Q` it raises elements to the power `q := |A/P|`.

More generally, our theory works in the "ABKL" setting, with `B/A` a finite extension of
Dedekind domains, and the corresponding extension `L/K` of fields of fractions is
assumed finite and Galois. Given `Q/P` a compatible pair of maximal ideals, under the
assumption that `A/P` is a finite field of size `q`, we construct an element `Frob_Q`
in `Gal(L/K)` and prove:

1) `Frob_Q • Q = Q`;
2) `x ^ q ≡ Frob_Q x (mod Q)`.

Examples where these hypotheses hold are:

1) Finite Galois extensions of number fields and their integers or `S`-integers;
2) Finite Galois extensions of function fields over finite fields, and their `S`-integers for
   `S` a nonempty set of places;
3) Finite Galois extensions of finite fields L/K where B/A=L/K and Q/P=0/0 (recovering the
classical theory of Frobenius elements)

Note that if `Q` is ramified, there is more than one choice of `Frob_Q` which works;
for example if `L=ℚ(i)` and `K=ℚ` then both the identity and complex conjugation
work for `Frob Q` if `Q=(1+i)`, and `Frob` returns a random one (i.e. it's opaque; all we know
is that it satisfies the two properties).

## The construction

We follow a proof in a footnote of a book by Milne. **TODO** which book

The Galois orbit of `Q` consists of `Q` and possibly some other primes `Q'`. The unit group
`(B/Q)ˣ` is finite and hence cyclic; so by the Chinese Remainder Theorem we may choose y ∈ B
which reduces to a generator mod Q and to 0 modulo all other Q' in the Galois orbit of Q.

The polynomial `F = ∏ (X - σ y)`, the product running over `σ` in the Galois group, is in `B[X]`
and is Galois-stable so is in fact in `A[X]`. Hence if `Fbar` is `F mod Q`
then `Fbar` has coefficients in `A/P=𝔽_q` and thus `Fbar(y^q)=Fbar(y)^q=0`, meaning that `y^q`
is a root of `F` mod `Q` and thus congruent to `σ y mod Q` for some `σ`. We define `Frob Q` to
be this `σ`.

## The proof

We know `σ y ≡ y ^ q ≠ 0 mod Q`. Hence `σ y ∉ Q`, and thus `y ∉ σ⁻¹ Q`. But `y ∈ Q'` for all nontrivial
conjugates `Q'` of `Q`, hence `σ⁻¹ Q = Q` and thus `Q` is `σ`-stable.

Hence `σ` induces a field automorphism of `B/Q` and we know it's `x ↦ x^q` on a generator,
so it's `x ↦ x^q` on everything.

## Note

This was Jou Glasheen's final project for Kevin Buzzard's Formalising Mathematics course.

-/
variable (A : Type*) [CommRing A] {B : Type*} [CommRing B] [Algebra A B]

-- was Eric going to put this somewhere?
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
-- Auxiliary lemma: if `Q` is a maximal ideal of a non-field Dedekind Domain `B` with a Galois action
-- and if `b ∈ B` then there's an element of `B` which is `b` mod `Q` and `0` modulo all the other
-- Galois conjugates of `Q`.
-- -/
-- lemma DedekindDomain.exists_y [IsDedekindDomain B] [Fintype (B ≃ₐ[A] B)]
--     [DecidableEq (Ideal B)] (Q : Ideal B) [Q.IsMaximal] (b : B) : ∃ y : B,
--     y - b ∈ Q ∧ ∀ Q' : Ideal B, Q' ∈ MulAction.orbit (B ≃ₐ[A] B) Q → Q' ≠ Q → y ∈ Q' := by
--   let O : Set (Ideal B) := MulAction.orbit (B ≃ₐ[A] B) Q
--   have hO : O.Finite := Set.finite_range _
--   have hPrime : ∀ Q' ∈ hO.toFinset, Prime Q' := by
--     intro Q' hQ'
--     rw [Set.Finite.mem_toFinset] at hQ'
--     obtain ⟨σ, rfl⟩ := hQ'
--     apply (MulEquiv.prime_iff <| MulDistribMulAction.toMulEquiv (Ideal B) σ).mp
--     refine Q.prime_of_isPrime (Q.bot_lt_of_maximal hB).ne' ?_
--     apply Ideal.IsMaximal.isPrime inferInstance
--   obtain ⟨y, hy⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := hO.toFinset) id (fun _ ↦ 1)
--     hPrime (fun _ _ _ _ ↦ id) (fun Q' ↦ if Q' = Q then b else 0)
--   simp only [Set.Finite.mem_toFinset, id_eq, pow_one] at hy
--   refine ⟨y, ?_, ?_⟩
--   · specialize hy Q ⟨1, by simp⟩
--     simpa only using hy
--   · rintro Q' ⟨σ, rfl⟩ hQ'
--     specialize hy (σ • Q) ⟨σ, by simp⟩
--     simp_all

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

lemma F_spec : F A Q = ∏ τ : B ≃ₐ[A] B, (X - C (τ • (y A Q))) := rfl

variable {A Q} in
open Finset in
lemma F.smul_eq_self (σ :  B ≃ₐ[A] B)  : σ • (F A Q) = F A Q := calc
  σ • F A Q = σ • ∏ τ : B ≃ₐ[A] B, (X - C (τ • (y A Q))) := by rw [F_spec]
  _         = ∏ τ : B ≃ₐ[A] B, σ • (X - C (τ • (y A Q))) := smul_prod
  _         = ∏ τ : B ≃ₐ[A] B, (X - C ((σ * τ) • (y A Q))) := by simp [smul_sub]
  _         = ∏ τ' : B ≃ₐ[A] B, (X - C (τ' • (y A Q))) := Fintype.prod_bijective (fun τ ↦ σ * τ)
                                                      (Group.mulLeft_bijective σ) _ _ (fun _ ↦ rfl)
  _         = F A Q := by rw [F_spec]

open scoped algebraMap

noncomputable local instance : Algebra A[X] B[X] :=
  RingHom.toAlgebra (Polynomial.mapRingHom (Algebra.toRingHom))

@[simp, norm_cast]
lemma coe_monomial (n : ℕ) (a : A) : ((monomial n a : A[X]) : B[X]) = monomial n (a : B) := by
  change ((Polynomial.mapRingHom (Algebra.toRingHom : A →+* B))) (monomial n a : A[X]) = monomial n (a : B)
  simp
  rfl

lemma F.descent (h : ∀ b : B, (∀ σ : B ≃ₐ[A] B, σ • b = b) → ∃ a : A, b = a) :
    ∃ m : A[X], (m : B[X]) = F A Q := by
  choose f hf using h
  classical
  let f' : B → A := fun b ↦ if h : ∀ σ : B ≃ₐ[A] B, σ b = b then f b h else 37
  let m := (F A Q).sum (fun n r ↦ Polynomial.monomial n (f' r))
  use m
  ext N
  simp only [m, sum]
  push_cast
  simp_rw [finset_sum_coeff, ← lcoeff_apply, lcoeff_apply, coeff_monomial]
  simp only [Finset.sum_ite_eq', mem_support_iff, ne_eq, ite_not, f']
  symm
  split
  · next h1 => exact h1
  · next h1 =>
    rw [dif_pos <| fun σ ↦ ?_]
    · refine hf ?_ ?_
    · nth_rw 2 [← F.smul_eq_self σ]
      rfl

variable (isGalois : ∀ b : B, (∀ σ : B ≃ₐ[A] B, σ • b = b) → ∃ a : A, b = a)

noncomputable abbrev m := (F.descent A Q isGalois).choose

lemma m_spec : ((m A Q isGalois) : B[X]) = F A Q := (F.descent A Q isGalois).choose_spec

lemma m_spec' : (m A Q isGalois).map (algebraMap A B) = F A Q := by
  rw [← m_spec A Q isGalois]
  rfl

lemma F.y_eq_zero : (F A Q).eval (y A Q) = 0 := by
  simp [F_spec, eval_prod, Finset.prod_eq_zero (Finset.mem_univ (1 : B ≃ₐ[A] B))]

example : B →+* B ⧸ Q := algebraMap _ _

-- lemma F.mod_Q_y_eq_zero : ((F A Q).map (algebraMap B (B⧸Q))).eval (algebraMap B (B⧸Q) (y A Q)) = 0 := by
--   rw [Polynomial.eval_map]
--   simp
--   simp only [Polynomial.eval_map, Ideal.Quotient.algebraMap_eq, eval₂_at_apply, map_zero, F.y_eq_zero A Q]

variable (P : Ideal A) [P.IsMaximal] [Algebra (A ⧸ P) (B ⧸ Q)] [IsScalarTower A (A⧸P) (B⧸Q)]

lemma m.mod_P_y_eq_zero : (m A Q isGalois).eval₂ (algebraMap A (B⧸Q)) (algebraMap B (B⧸Q) (y A Q)) = 0 := by
  rw [show algebraMap A (B⧸Q) = (algebraMap B (B⧸Q)).comp (algebraMap A B) from IsScalarTower.algebraMap_eq A B (B ⧸ Q)]
  rw [←eval₂_map]
  change eval₂ _ _ (m A Q isGalois : B[X]) = _
  simp [m_spec A Q isGalois, eval_map, F.y_eq_zero]

noncomputable abbrev mmodP := (m A Q isGalois).map (algebraMap A (A⧸P))

open scoped Polynomial

-- example (K : Type*) [Field K] [Fintype K] : ∃ p n : ℕ, p.Prime ∧ Fintype.card K = p ^ n ∧ CharP K p := by
--   obtain ⟨p, n, h₁, h₂⟩ := FiniteField.card' K
--   refine ⟨p, n.val, h₁, h₂, ?_⟩
--   have : (p ^ n.val : K) = 0 := mod_cast h₂ ▸ Nat.cast_card_eq_zero K
--   rw [CharP.charP_iff_prime_eq_zero h₁]
--   simpa only [ne_eq, PNat.ne_zero, not_false_eq_true, pow_eq_zero_iff] using this

-- mathlib
lemma bar (k : Type*) [Field k] [Fintype k] : ∃ n : ℕ, ringExpChar k ^ n = Fintype.card k := by
  sorry

-- mathlib
lemma foo (k : Type*) [Field k] [Fintype k] (f : k[X]) (L : Type*) [CommRing L] [Algebra k L]
    (t : L) : f.eval₂ (algebraMap k L) (t^(Fintype.card k)) =
              (f.eval₂ (algebraMap k L) t)^(Fintype.card k) := by
  obtain ⟨n, hn⟩ := bar k
  induction f using Polynomial.induction_on
  · simp [← map_pow, FiniteField.pow_card]
  · next g h h1 h2 =>
    simp only [Polynomial.eval₂_add, h1, h2]
    rw [← hn]
    by_cases hL : Nontrivial L
    · haveI := expChar_of_injective_algebraMap (NoZeroSMulDivisors.algebraMap_injective k L) (ringExpChar k)
      rw [add_pow_expChar_pow]
    · apply (not_nontrivial_iff_subsingleton.mp hL).elim
  · simp only [Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X_pow, mul_pow,
                 ← map_pow, pow_right_comm, FiniteField.pow_card]

variable [Fintype (A⧸P)]
-- (m-bar)(y^q)=0 in B/Q
lemma m.mod_P_y_pow_q_eq_zero :
    (m A Q isGalois).eval₂ (algebraMap A (B⧸Q)) ((algebraMap B (B⧸Q) (y A Q)) ^ (Fintype.card (A⧸P)))
    = 0 := by
  suffices ((m A Q isGalois).map (algebraMap A (A⧸P))).eval₂ (algebraMap (A⧸P) (B⧸Q))
    ((algebraMap B (B⧸Q) (y A Q)) ^ (Fintype.card (A⧸P))) = 0 by
    rwa [eval₂_map, ← IsScalarTower.algebraMap_eq A (A ⧸ P) (B ⧸ Q)] at this
  let foobar : Field (A⧸P) := ((Ideal.Quotient.maximal_ideal_iff_isField_quotient P).mp ‹_›).toField
  rw [foo, eval₂_map, ← IsScalarTower.algebraMap_eq A (A ⧸ P) (B ⧸ Q), m.mod_P_y_eq_zero, zero_pow]
  exact Fintype.card_ne_zero

lemma F.mod_Q_y_pow_q_eq_zero : (F A Q).eval₂ (algebraMap B (B⧸Q)) ((algebraMap B (B⧸Q) (y A Q)) ^ (Fintype.card (A⧸P))) = 0 := by
  rw [← m_spec' A Q isGalois, eval₂_map]--, m.mod_P_y_pow_q_eq_zero]
  rw [← IsScalarTower.algebraMap_eq A B (B ⧸ Q), m.mod_P_y_pow_q_eq_zero]

lemma exists_thing : ∃ σ : B ≃ₐ[A] B, σ (y A Q) - (y A Q) ^ (Fintype.card (A⧸P)) ∈ Q := by
  have := F.mod_Q_y_pow_q_eq_zero A Q isGalois P
  rw [F_spec] at this
  rw [eval₂_finset_prod] at this
  rw [Finset.prod_eq_zero_iff] at this
  obtain ⟨σ, -, hσ⟩ := this
  use σ
  simp only [Ideal.Quotient.algebraMap_eq, AlgEquiv.smul_def, eval₂_sub, eval₂_X, eval₂_C,
    sub_eq_zero] at hσ
  exact (Submodule.Quotient.eq Q).mp (hσ.symm)

noncomputable abbrev Frob := (exists_thing A Q isGalois P).choose

lemma Frob_spec : (Frob A Q isGalois P) (y A Q) - (y A Q) ^ (Fintype.card (A⧸P)) ∈ Q :=
  (exists_thing A Q isGalois P).choose_spec

/- maths proof:

1) σ Q = Q. Because if not then Q ≠ σ⁻¹ Q so y ∈ σ⁻¹ Q so σ y ∈ Q so y^p ∈ Q so y ∈ Q so #
2) σ is x ^ #A/P mod Q
3) Application to number fields
-/
