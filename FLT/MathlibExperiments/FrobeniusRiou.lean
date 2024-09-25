/-
Copyright (c) 2024 Jou Glasheen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jou Glasheen, Amelia Livingston, Jujian Zhang, Kevin Buzzard
-/
import Mathlib.FieldTheory.Cardinality
import Mathlib.RingTheory.DedekindDomain.Ideal
import Mathlib.RingTheory.Ideal.Pointwise
import Mathlib.RingTheory.Ideal.QuotientOperations
import Mathlib.RingTheory.IntegralClosure.IntegralRestrict
import Mathlib.RingTheory.Ideal.Pointwise
import Mathlib.RingTheory.Ideal.Over
import Mathlib.FieldTheory.Normal
import Mathlib
import Mathlib.RingTheory.OreLocalization.Ring

/-!

# Frobenius elements.

This file proves a general result in commutative algebra which can be used to define Frobenius
elements of Galois groups of local or fields (for example number fields).

KB was alerted to this very general result (which needs no Noetherian or finiteness assumptions
on the rings, just on the Galois group) by Joel Riou
here https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/Uses.20of.20Frobenius.20elements.20in.20mathematics/near/448934112

## Mathematical details

### The general commutative algebra result

This is Theorem 2 in Chapter V, Section 2, number 2 of Bourbaki Alg Comm. It says the following.
Let `A → B` be commutative rings and let `G` be a finite group acting on `B` by ring automorphisms,
such that the `G`-invariants of `B` are exactly the image of `A`.

The two claims of the theorem are:
(i) If `P` is a prime ideal of `A` then `G` acts transitively on the primes of `B` above `P`.
(ii) If `Q` is a prime ideal of `B` lying over `P` then the canonica map from the stabilizer of `Q`
in `G` to the automorphism group of the residue field extension `Frac(B/Q) / Frac(A/P)` is
surjective.

We say "automorphism group" rather than "Galois group" because the extension might not be
separable (it is algebraic and normal however, but it can be infinite; however its maximal
separable subextension is finite).

This result means that if the inertia group I_Q is trivial and the residue fields are finite,
there's a Frobenius element Frob_Q in the stabiliser of Q, and a Frobenius conjugacy class
Frob_P in G.

-/


variable {A : Type*} [CommRing A]
  {B : Type*} [CommRing B] [Algebra A B] --[Algebra.IsIntegral A B]
  {G : Type*} [Group G] [Finite G] [MulSemiringAction G B]



open scoped algebraMap

--variable (hFull : ∀ (b : B), (∀ (g : G), g • b = b) ↔ ∃ a : A, b = a)
--variable (hFull' : ∀ (b : B), (∀ (g : G), g • b = b) → ∃ a : A, b = a)

section misc

variable {A : Type*} [CommRing A]
  {B : Type*} [CommRing B] [Algebra A B]
  {G : Type*} [Group G] [MulSemiringAction G B]
  [SMulCommClass G A B]

open scoped Pointwise

/-
If you're happy to stick to finite G, it's just this:

private theorem norm_fixed' (b : B) (g : G) [Finite G] : g • (∏ᶠ σ : G, σ • b) = ∏ᶠ σ : G, σ • b := calc
  g • (∏ᶠ σ : G, σ • b) = ∏ᶠ σ : G, g • (σ • b) := smul_finprod' _
  _                     = ∏ᶠ σ : G, σ • b := finprod_eq_of_bijective (g • ·) (MulAction.bijective g)
                                               fun x ↦ smul_smul g x b

But the below proof works in general.
-/

private theorem norm_fixed (b : B) (g : G) : g • (∏ᶠ σ : G, σ • b) = ∏ᶠ σ : G, σ • b := by
  obtain (hfin | hinf) := em <| Finite G
  · calc
    g • (∏ᶠ σ : G, σ • b) = ∏ᶠ σ : G, g • (σ • b) := smul_finprod' _
    _                     = ∏ᶠ σ : G, σ • b := finprod_eq_of_bijective (g • ·) (MulAction.bijective g)
                                                 fun x ↦ smul_smul g x b
  · obtain (rfl | hb) := eq_or_ne b 1
    · simp
    · suffices (Function.mulSupport ((· • b) : G → B)).Infinite by
        classical
        simp [finprod_def, dif_neg this]
      have htop : (⊤ : Set G).Infinite := by simpa using Set.infinite_univ_iff.mpr ({ not_finite := hinf })
      convert htop
      rw [eq_top_iff]
      intro g _
      simp only [Function.mem_mulSupport]
      contrapose! hb
      apply_fun (fun x ↦ g⁻¹ • x) at hb
      simpa using hb

theorem _root_.Ideal.IsPrime.finprod_mem_iff_exists_mem {R S : Type*} [Finite R] [CommSemiring S]
    (I : Ideal S) [hI : I.IsPrime] (f : R → S)  :
    ∏ᶠ x, f x ∈ I ↔ ∃ p, f p ∈ I := by
  have := Fintype.ofFinite R
  rw [finprod_eq_prod_of_fintype, Finset.prod_eq_multiset_prod, hI.multiset_prod_mem_iff_exists_mem]
  simp

end misc

section charpoly

open Polynomial BigOperators

variable {A : Type*} [CommRing A]
  {B : Type*} [CommRing B] [Algebra A B]
  {G : Type*} [Group G] [MulSemiringAction G B] --[SMulCommClass G A B]


variable (G) in
/-- `F : B[X]` defined to be a product of linear factors `(X - τ • α)`; where
`τ` runs over `L ≃ₐ[K] L`, and `α : B` is an element which generates `(B ⧸ Q)ˣ`
and lies in `τ • Q` for all `τ ∉ (decomposition_subgroup_Ideal'  A K L B Q)`.-/
private noncomputable abbrev F (b : B) : B[X] := ∏ᶠ τ : G, (X - C (τ • b))

private theorem F_spec (b : B) : F G b = ∏ᶠ τ : G, (X - C (τ • b)) := rfl

private theorem F_smul_eq_self [Finite G] (σ : G) (b : B) : σ • (F G b) = F G b := calc
  σ • F G b = σ • ∏ᶠ τ : G, (X - C (τ • b)) := by rw [F_spec]
  _         = ∏ᶠ τ : G, σ • (X - C (τ • b)) := smul_finprod' _
  _         = ∏ᶠ τ : G, (X - C ((σ * τ) • b)) := by simp [smul_sub, smul_smul]
  _         = ∏ᶠ τ' : G, (X - C (τ' • b)) := finprod_eq_of_bijective (fun τ ↦ σ * τ)
                                               (Group.mulLeft_bijective σ) (fun _ ↦ rfl)
  _         = F G b := by rw [F_spec]

private theorem F_eval_eq_zero [Finite G] (b : B) : (F G b).eval b = 0 := by
  let foo := Fintype.ofFinite G
  simp [F_spec,finprod_eq_prod_of_fintype,eval_prod]
  apply @Finset.prod_eq_zero _ _ _ _ _ (1 : G) (Finset.mem_univ 1)
  simp

open scoped algebraMap

noncomputable local instance : Algebra A[X] B[X] :=
  RingHom.toAlgebra (Polynomial.mapRingHom (Algebra.toRingHom))

@[simp, norm_cast]
theorem coe_monomial (n : ℕ) (a : A) : ((monomial n a : A[X]) : B[X]) = monomial n (a : B) :=
  map_monomial _

private theorem F_descent [Finite G]
    (hFull : ∀ (b : B), (∀ (g : G), g • b = b) → ∃ a : A, b = a) (b : B) :
    ∃ M : A[X], (M : B[X]) = F G b := by
  choose f hf using fun b ↦ (hFull b)
  classical
  let f' : B → A := fun b ↦ if h : ∀ σ : G, σ • b = b then f b h else 37
  use (∑ x ∈ (F G b).support, (monomial x) (f' ((F G b).coeff x)))
  ext N
  push_cast
  simp_rw [finset_sum_coeff, ← lcoeff_apply, lcoeff_apply, coeff_monomial]
  simp only [Finset.sum_ite_eq', mem_support_iff, ne_eq, ite_not, f']
  symm
  split
  · next h => exact h
  · next h1 =>
    rw [dif_pos <| fun σ ↦ ?_]
    · refine hf ?_ ?_
    · nth_rw 2 [← F_smul_eq_self σ]
      rfl

variable (hFull : ∀ (b : B), (∀ (g : G), g • b = b) → ∃ a : A, b = a) [Finite G]

variable [Nontrivial B]

theorem F_monic (b : B) : Monic (F G b) := by
  have := Fintype.ofFinite G
  rw [Monic, F_spec, finprod_eq_prod_of_fintype, leadingCoeff_prod'] <;> simp

private theorem F_descent_monic
  (hFull : ∀ (b : B), (∀ (g : G), g • b = b) → ∃ a : A, b = a) (b : B) :
    ∃ M : A[X], (M : B[X]) = F G b ∧ Monic M := by
  have : F G b ∈ Polynomial.lifts (algebraMap A B) := by
    choose M hM using F_descent hFull b
    use M; exact hM
  choose M hM using lifts_and_degree_eq_and_monic this (F_monic b)
  use M
  exact ⟨hM.1, hM.2.2⟩

variable (G) in
noncomputable def M [Finite G] (b : B) : A[X] := (F_descent_monic hFull b).choose

theorem M_spec (b : B) : ((M G hFull b : A[X]) : B[X]) = F G b :=
  (F_descent_monic hFull b).choose_spec.1

theorem M_spec' (b : B) : (map (algebraMap A B) (M G hFull b)) = F G b :=
  (F_descent_monic hFull b).choose_spec.1

theorem M_monic (b : B) : (M G hFull b).Monic := (F_descent_monic hFull b).choose_spec.2

theorem M_eval_eq_zero (b : B) : (M G hFull b).eval₂ (algebraMap A B) b = 0 := by
  rw [eval₂_eq_eval_map, M_spec', F_eval_eq_zero]

end charpoly

section part_a

variable {A : Type*} [CommRing A]
  {B : Type*} [CommRing B] [Algebra A B] [Nontrivial B]
  {G : Type*} [Group G] [Finite G] [MulSemiringAction G B]

theorem isIntegral_of_Full (hFull : ∀ (b : B), (∀ (g : G), g • b = b) → ∃ a : A, b = a) :
    Algebra.IsIntegral A B where
  isIntegral b := ⟨M G hFull b, M_monic hFull b, M_eval_eq_zero hFull b⟩

variable (P Q : Ideal B) [P.IsPrime] [Q.IsPrime]
  --
  (hPQ : Ideal.comap (algebraMap A B) P = Ideal.comap (algebraMap A B) Q)

-- Algebra.IsIntegral A B
open scoped Pointwise

-- (Part a of Théorème 2 in section 2 of chapter 5 of Bourbaki Alg Comm)
theorem part_a [SMulCommClass G A B]
    (hPQ : Ideal.comap (algebraMap A B) P = Ideal.comap (algebraMap A B) Q)
    (hFull' : ∀ (b : B), (∀ (g : G), g • b = b) → ∃ a : A, b = a) :
    ∃ g : G, Q = g • P := by
  haveI : Algebra.IsIntegral A B := isIntegral_of_Full hFull'
  cases nonempty_fintype G
  suffices ∃ g : G, Q ≤ g • P by
    obtain ⟨g, hg⟩ := this
    use g
    by_contra! hQ
    have : Q < g • P := lt_of_le_of_ne hg hQ
    obtain ⟨x, hxP, hxQ⟩ := Set.exists_of_ssubset <| this
    apply (Ideal.comap_lt_comap_of_integral_mem_sdiff (R := A) hg ⟨hxP, hxQ⟩ <|
      Algebra.isIntegral_def.1 inferInstance x).ne
    rw [← hPQ]
    ext x
    specialize hFull' (algebraMap A B x)
    have : ∀ (g : G), g • (algebraMap A B x) = (algebraMap A B x) := fun g ↦ by
      rw [Algebra.algebraMap_eq_smul_one, smul_comm, smul_one]
    simp only [Ideal.mem_comap]
    nth_rw 2 [← this]
    exact Ideal.smul_mem_pointwise_smul_iff.symm
  suffices ∃ g ∈ (⊤ : Finset G), Q ≤ g • P by
    convert this; simp
  rw [← Ideal.subset_union_prime 1 1 <| fun g _ _ _ ↦ ?_]; swap
  · exact Ideal.map_isPrime_of_equiv (MulSemiringAction.toRingEquiv _ _ g)
  intro x hx
  specialize hFull' (∏ᶠ σ : G, σ • x)
  obtain ⟨a, ha⟩ := hFull' (norm_fixed _)
  have : (a : B) ∈ Q := by
    rw [← ha, Ideal.IsPrime.finprod_mem_iff_exists_mem]
    use 1
    simpa using hx
  have : (a : B) ∈ P := by
    unfold Algebra.cast
    rwa [← Ideal.mem_comap, hPQ, Ideal.mem_comap]
  rw [← ha, Ideal.IsPrime.finprod_mem_iff_exists_mem] at this
  obtain ⟨σ, hσ⟩ : ∃ σ : G, σ • x ∈ P := this
  simp only [Finset.top_eq_univ, Finset.coe_univ, Set.mem_univ, Set.iUnion_true, Set.mem_iUnion,
    SetLike.mem_coe]
  use σ⁻¹
  rwa [Ideal.mem_inv_pointwise_smul_iff]

end part_a

-- section normal_elements

-- variable (K : Type*) [Field K] {L : Type*} [Field L] [Algebra K L]

-- open Polynomial

-- I've commented out the next section because ACL suggested
-- reading up-to-date Bourbaki here https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/poly.20whose.20roots.20are.20the.20products.20of.20the.20roots.20of.20polys/near/468585267
-- and apparently this will avoid the def below.

-- def IsNormalElement (x : L) : Prop := Splits (algebraMap K L) (minpoly K x)

-- namespace IsNormalElement

-- theorem iff_exists_monic_splits {x : L} (hx : IsIntegral K x) :
--     IsNormalElement K x ↔
--     ∃ P : K[X], P.Monic ∧ P.eval₂ (algebraMap K L) x = 0 ∧ Splits (algebraMap K L) P := by
--   constructor
--   · intro h
--     exact ⟨minpoly K x, minpoly.monic hx, minpoly.aeval K x, h⟩
--   · rintro ⟨P, hPmonic, hPeval, hPsplits⟩
--     -- need min poly divides P and then it should all be over
--     sorry -- presumably some form of this is in the library

-- theorem prod {x y : L} (hxint : IsIntegral K x) (hyint : IsIntegral K y)
--     (hx : IsNormalElement K x) (hy : IsNormalElement K y) :
--     IsNormalElement K (x * y) := by
--   rw [iff_exists_monic_splits K hxint] at hx
--   obtain ⟨Px, hx1, hx2, hx3⟩ := hx
--   rw [iff_exists_monic_splits K hyint] at hy
--   obtain ⟨Py, hy1, hy2, hy3⟩ := hy
--   rw [iff_exists_monic_splits K <| IsIntegral.mul hxint hyint]
--   -- If roots of Px are xᵢ and roots of Py are yⱼ, then use the poly whose roots are xᵢyⱼ.
--   -- Do we have this?
--   -- Is this even the best way to go about this?
--   -- Note: Chambert-Loir says there's a proof in Bourbaki
--   sorry

-- -- API

-- end IsNormalElement

-- end normal_elements

section part_b



variable {A : Type*} [CommRing A]
  {B : Type*} [CommRing B] [Algebra A B]
  {G : Type*} [Group G] [Finite G] [MulSemiringAction G B] [SMulCommClass G A B]

-- set-up for part (b) of the lemma. G acts on B with invariants A (or more precisely the
-- image of A). Warning: `P` was a prime ideal of `B` in part (a) but it's a prime ideal
-- of `A` here, in fact it's Q ∩ A, the preimage of Q in A.

/-
All I want to say is:

B ---> B / Q -----> L = Frac(B/Q)
/\       /\        /\
|        |         |
|        |         |
A ---> A / P ----> K = Frac(A/P)

-/
variable (Q : Ideal B) [Q.IsPrime] (P : Ideal A) [P.IsPrime]
--#synth Algebra A (B ⧸ Q) #exit -- works
--#synth IsScalarTower A B (B ⧸ Q) #exit-- works
-- (hPQ : Ideal.comap (algebraMap A B) P = p) -- we will *prove* this from the
-- commutativity of the diagram! This is a trick I learnt from Jou who apparently
-- learnt it from Amelia
  [Algebra (A ⧸ P) (B ⧸ Q)] [IsScalarTower A (A ⧸ P) (B ⧸ Q)]
-- So now we know the left square commutes.
-- Amelia's trick: commutativity of this diagram implies P ⊇ Q ∩ A
-- And the fact that K and L are fields implies A / P -> B / Q is injective
-- and thus P = Q ∩ A
-- Let's now make the right square. First `L`
  (L : Type*) [Field L] [Algebra (B ⧸ Q) L] [IsFractionRing (B ⧸ Q) L]
  -- Now top left triangle: A / P → B / Q → L commutes
  [Algebra (A ⧸ P) L] [IsScalarTower (A ⧸ P) (B ⧸ Q) L]
  -- now introduce K
  (K : Type*) [Field K] [Algebra (A ⧸ P) K] [IsFractionRing (A ⧸ P) K]
  -- now make bottom triangle commute
  [Algebra K L] [IsScalarTower (A ⧸ P) K L]
  -- So now both squares commute.

-- do I need this?
--  [Algebra A K] [IsScalarTower A (A ⧸ P) K]

-- Do I need this:
--  [Algebra B L] [IsScalarTower B (B ⧸ Q) L]

variable [Nontrivial B]

-- version of Ideal.Quotient.eq_zero_iff_mem with algebraMap
omit [P.IsPrime] in
theorem Ideal.Quotient.eq_zero_iff_mem' (x : A) :
    algebraMap A (A ⧸ P) x = 0 ↔ x ∈ P :=
  Ideal.Quotient.eq_zero_iff_mem

-- not sure if we need this but let's prove it just to check our setup is OK
open IsScalarTower in
example : --[Algebra A k] [IsScalarTower A (A ⧸ p) k] [Algebra k K] [IsScalarTower (A ⧸ p) k K]
    --[Algebra A K] [IsScalarTower A k K] :
    Ideal.comap (algebraMap A B) Q = P := by
  ext x
  simp only [Ideal.mem_comap]
  rw [← Ideal.Quotient.eq_zero_iff_mem', ← Ideal.Quotient.eq_zero_iff_mem']
  rw [← map_eq_zero_iff _ <| IsFractionRing.injective (A ⧸ P) K]
  rw [← map_eq_zero_iff _ <| IsFractionRing.injective (B ⧸ Q) L]
  rw [← map_eq_zero_iff _ <| RingHom.injective ((algebraMap K L) : K →+* L)]
  rw [← algebraMap_apply A B (B ⧸ Q)]
  rw [← algebraMap_apply (A ⧸ P) K L]
  rw [algebraMap_apply A (A ⧸ P) (B ⧸ Q)]
  rw [algebraMap_apply (A ⧸ P) (B ⧸ Q) L]

open Polynomial BigOperators

open scoped algebraMap

noncomputable local instance : Algebra A[X] B[X] :=
  RingHom.toAlgebra (Polynomial.mapRingHom (Algebra.toRingHom))

theorem IsAlgebraic.mul {R K : Type*} [CommRing R] [CommRing K] [Algebra R K] {x y : K}
  (hx : IsAlgebraic R x) (hy : IsAlgebraic R y) : IsAlgebraic R (x * y) := sorry

theorem IsAlgebraic.invLoc {R S K : Type*} [CommRing R] {M : Submonoid R} [CommRing S] [Algebra R S]
    [IsLocalization M S] {x : M} [CommRing K] [Algebra K S] (h : IsAlgebraic K ((x : R) : S)):
    IsAlgebraic K (IsLocalization.mk' S 1 x) := by
  rw [← IsAlgebraic.invOf_iff, IsLocalization.invertible_mk'_one_invOf]
  exact h

theorem Algebra.isAlgebraic_of_subring_isAlgebraic {R k K : Type*} [CommRing R] [CommRing k]
    [CommRing K] [Algebra R K] [IsFractionRing R K] [Algebra k K]
    (h : ∀ x : R, IsAlgebraic k (x : K)) : Algebra.IsAlgebraic k K := by
  -- ratio of two algebraic numbers is algebraic (follows from product of alg numbers is
  -- alg, which we surely have, and reciprocal of algebraic number
  -- is algebraic; proof of the latter is "reverse the min poly", don't know if we have it)
  rw [isAlgebraic_def]
  let M := nonZeroDivisors R
  intro x
  have ⟨r, s, h'⟩ := IsLocalization.mk'_surjective M x
  have : x = r * IsLocalization.mk' K 1 s := by
    rw [← h', IsLocalization.mul_mk'_eq_mk'_of_mul]
    simp
  rw [this]
  apply IsAlgebraic.mul (h r)
  exact IsAlgebraic.invLoc (h s)

theorem algebraMap_cast {R S: Type*} [CommRing R] [CommRing S] [Algebra R S] (r : R) :
  (r : S) = (algebraMap R S) r := by
  rfl

theorem algebraMap_algebraMap {R S T : Type*} [CommRing R] [CommRing S] [CommRing T] [Algebra R S]
  [Algebra S T] [Algebra R T] [IsScalarTower R S T] (r : R) :
  (algebraMap S T) ((algebraMap R S) r) = (algebraMap R T) r := by
  exact Eq.symm (IsScalarTower.algebraMap_apply R S T r)

-- (Théorème 2 in section 2 of chapter 5 of Bourbaki Alg Comm)
theorem Pointwise.residueFieldExtension_algebraic {A : Type*} [CommRing A] {B : Type*} [Nontrivial B] [CommRing B] [Algebra A B]
  [Algebra.IsIntegral A B] {G : Type*} [Group G] [Finite G] [MulSemiringAction G B] (Q : Ideal B)
  [Q.IsPrime] (P : Ideal A) [P.IsPrime] [Algebra (A ⧸ P) (B ⧸ Q)]
  [IsScalarTower A (A ⧸ P) (B ⧸ Q)] (L : Type*) [Field L] [Algebra (B ⧸ Q) L]
  [IsFractionRing (B ⧸ Q) L] [Algebra (A ⧸ P) L] [IsScalarTower (A ⧸ P) (B ⧸ Q) L]
  (K : Type*) [Field K] [Algebra (A ⧸ P) K] [IsFractionRing (A ⧸ P) K]
  [Algebra K L] [IsScalarTower (A ⧸ P) K L] [Algebra A K] [IsScalarTower A (A ⧸ P) K]
  [Algebra B L] [IsScalarTower B (B ⧸ Q) L] [Algebra A L] [IsScalarTower A K L]
  [IsScalarTower A B L]
  (hFull : ∀ (b : B), (∀ (g : G), g • b = b) → ∃ a : A, b = a): Algebra.IsAlgebraic K L := by
  /-
  Because of `IsFractionRing (B ⧸ Q) K` and the previous lemma it suffices to show that every
  element of B/Q is algebraic over k, and this is because you can lift to b ∈ B and then
  use `M` above (which needs to be coerced to A/P and then to K)
  -/
  apply @Algebra.isAlgebraic_of_subring_isAlgebraic (B ⧸ Q)
  intro b_bar
  have ⟨b, hb⟩ := Ideal.Quotient.mk_surjective b_bar
  have hb : (algebraMap B (B ⧸ Q)) b = b_bar := hb
  use ((M G hFull b).map (algebraMap A (A ⧸ P))).map (algebraMap (A ⧸ P) K)
  constructor
  . apply ne_zero_of_ne_zero_of_monic X_ne_zero
    apply Monic.map
    apply Monic.map
    exact M_monic hFull b
  . rw [← hb, algebraMap_cast, map_map, ← IsScalarTower.algebraMap_eq]
    rw [algebraMap_algebraMap, aeval_def, eval₂_eq_eval_map, map_map, ← IsScalarTower.algebraMap_eq]
    rw [IsScalarTower.algebraMap_eq A B L, ← map_map, M_spec']
    rw [eval_map, eval₂_hom, F_eval_eq_zero]
    exact algebraMap.coe_zero

theorem Pointwise.residueFieldExtension_normal : Normal K L := by
  /-

  See discussion at
  https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/poly.20whose.20roots.20are.20the.20products.20of.20the.20roots.20of.20polys/near/468585267

  Maybe I won't formalise the below proof then (which I made up):
  Let's temporarily say that an *element* of `K` is _normal_ if it is the root of a monic poly
  in `k[X]` all of whose roots are in `K`. Then `K/k` is normal iff all elements are normal
  (if `t` is a root of `P ∈ k[X]` then the min poly of `t` must divide `P`).
  I claim that the product of two normal elements is normal. Indeed if `P` and `Q` are monic polys
  in `k[X]` with roots `xᵢ` and `yⱼ` then there's another monic poly in `k[X]` whose roots are
  the products `xᵢyⱼ`. Also the reciprocal of a nonzero normal element is normal (reverse the
  polynomial and take the reciprocals of all the roots). This is enough.
  -/
  sorry

open scoped Pointwise

-- Basic API for what we're doing here. Writing down a map from the stabiliser of Q to
-- the residual Galois group `L ≃ₐ[K] L`, where L=Frac(B/Q) and K=Frac(A/P).
-- Hopefully sorrys aren't too hard

/-
All I want to say is:

B ---> B / Q -----> L = Frac(B/Q)
/\       /\        /\
|        |         |
|        |         |
A ---> A / P ----> K = Frac(A/P)
-/

def Pointwise.quotientRingAction (Q' : Ideal B) (g : G) (hg : g • Q = Q') :
    B ⧸ Q ≃+* B ⧸ Q' :=
  Ideal.quotientEquiv Q Q' (MulSemiringAction.toRingEquiv G B g) hg.symm

def Pointwise.quotientAlgebraAction (g : G) (hg : g • Q = Q) : (B ⧸ Q) ≃ₐ[A ⧸ P] B ⧸ Q where
  __ := quotientRingAction Q Q g hg
  commutes' := by
    intro a_bar; dsimp
    have ⟨a, ha⟩ := Ideal.Quotient.mk_surjective a_bar
    rw [Pointwise.quotientRingAction]; dsimp
    rw [← ha, ← Ideal.Quotient.algebraMap_eq, algebraMap_algebraMap]
    rw [@Ideal.quotientMap_algebraMap A B _ _ _ B _ Q Q _ ]
    simp

def Pointwise.quotientAlgebraActionMonoidHom :
    MulAction.stabilizer G Q →* ((B ⧸ Q) ≃ₐ[A ⧸ P] (B ⧸ Q)) where
  toFun gh := quotientAlgebraAction Q P gh.1 gh.2
  map_one' := by
    apply AlgEquiv.ext
    intro b_bar; dsimp
    unfold quotientAlgebraAction
    unfold quotientRingAction
    have ⟨b, hb⟩ := Ideal.Quotient.mk_surjective b_bar
    rw [← hb, ← Ideal.Quotient.algebraMap_eq]
    simp
  map_mul' := by
    intro ⟨x, hx⟩ ⟨y, hy⟩
    apply AlgEquiv.ext
    intro b_bar; dsimp
    unfold quotientAlgebraAction
    unfold quotientRingAction
    have ⟨b, hb⟩ := Ideal.Quotient.mk_surjective b_bar
    rw [← hb, ← Ideal.Quotient.algebraMap_eq]
    simp
    rw [smul_smul]

noncomputable def IsFractionRing.algEquiv_lift (e : (B ⧸ Q) ≃ₐ[A ⧸ P] B ⧸ Q) : L ≃ₐ[K] L where
  __ := IsFractionRing.fieldEquivOfRingEquiv e.toRingEquiv
  commutes' := sorry

noncomputable def Pointwise.stabilizer.toGaloisGroup : MulAction.stabilizer G Q →* (L ≃ₐ[K] L) where
  toFun gh := IsFractionRing.algEquiv_lift Q P L K (Pointwise.quotientAlgebraActionMonoidHom Q P gh)
  map_one' := sorry
  map_mul' := sorry

variable (hFull : ∀ (b : B), (∀ (g : G), g • b = b) ↔ ∃ a : A, b = a) in
theorem MulAction.stabilizer_surjective_of_action : Function.Surjective
    (Pointwise.stabilizer.toGaloisGroup Q P L K : MulAction.stabilizer G Q → (L ≃ₐ[K] L)) := by
  sorry

section localization

/-

In this section we reduce to the case where P and Q are maximal.
More precisely, we set `S := A - P` and localize everything in sight by `S`
We then construct a group isomophism
`MulAction.stabilizer G Q ≃ MulAction.stabilizer G SQ` where `SQ` is the prime ideal of `S⁻¹B`
obtained by localizing `Q` at `S`, and show that it commutes with the maps currently called
`baz2 Q P L K` and `baz2 SQ SP L K`.

-/

abbrev S := P.primeCompl
abbrev SA := A[(S P)⁻¹]

abbrev SB := B[(S P)⁻¹]

-- Currently stuck here
--instance : Algebra (A[(S P)⁻¹]) (B[(S P)⁻¹]) where
--  sorry--__ := OreLocalization.instModule (R := A) (X := B) (S := P.primeCompl)

/-
failed to synthesize
  Semiring (OreLocalization (S P) B)
-/
end localization

-- In Frobenius2.lean in this dir (Jou's FM24 project) there's a proof of surjectivity
-- assuming B/Q is finite and P is maximal.
-- Bourbaki reduce to maximal case by localizing at P, and use finite + separable = simple
-- on the max separable subextension, but then the argument in Bourbaki closely
-- follows Jou's formalisation in Frobenius2.lean in this directory, so this work will
-- be useful later.
end part_b
