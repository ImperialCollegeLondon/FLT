/-
Copyright (c) 2024 Jou Glasheen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jou Glasheen, Amelia Livingston, Jujian Zhang, Kevin Buzzard
-/
import Mathlib.FieldTheory.Cardinality
import Mathlib.RingTheory.DedekindDomain.Ideal
import Mathlib.RingTheory.Ideal.Pointwise
import Mathlib.RingTheory.IntegralClosure.IntegralRestrict
import Mathlib.RingTheory.Ideal.Pointwise
import Mathlib.RingTheory.Ideal.Over
import Mathlib.FieldTheory.Normal
import Mathlib.FieldTheory.SeparableClosure
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
/-- The characteristic polynomial of an element `b` of a `G`-semiring `B`
is the polynomial `∏_{g ∈ G} (X - g • b)` (here `G` is finite; junk
returned in the infinite case) .-/
noncomputable def MulSemiringAction.CharacteristicPolynomial.F (b : B) : B[X] :=
  ∏ᶠ τ : G, (X - C (τ • b))

namespace MulSemiringAction.CharacteristicPolynomial

theorem F_spec (b : B) : F G b = ∏ᶠ τ : G, (X - C (τ • b)) := rfl

section F_API

variable [Finite G]

theorem F_monic [Nontrivial B] (b : B) : (F G b).Monic := by
  have := Fintype.ofFinite G
  rw [Monic, F_spec, finprod_eq_prod_of_fintype, leadingCoeff_prod'] <;> simp

theorem F_natdegree [Nontrivial B] (b : B) : (F G b).natDegree = Nat.card G := by
  have := Fintype.ofFinite G
  rw [F_spec, finprod_eq_prod_of_fintype, natDegree_prod_of_monic _ _ (fun _ _ => monic_X_sub_C _)]
  simp only [natDegree_X_sub_C, Finset.sum_const, Finset.card_univ, Fintype.card_eq_nat_card,
    nsmul_eq_mul, mul_one, Nat.cast_id]

variable (G) in
theorem F_degree [Nontrivial B] (b : B) : (F G b).degree = Nat.card G := by
  have := Fintype.ofFinite G
  rw [degree_eq_iff_natDegree_eq_of_pos Nat.card_pos, F_natdegree]

theorem F_smul_eq_self (σ : G) (b : B) : σ • (F G b) = F G b := calc
  σ • F G b = σ • ∏ᶠ τ : G, (X - C (τ • b)) := by rw [F_spec]
  _         = ∏ᶠ τ : G, σ • (X - C (τ • b)) := smul_finprod' _
  _         = ∏ᶠ τ : G, (X - C ((σ * τ) • b)) := by simp [smul_sub, smul_smul]
  _         = ∏ᶠ τ' : G, (X - C (τ' • b)) := finprod_eq_of_bijective (fun τ ↦ σ * τ)
                                               (Group.mulLeft_bijective σ) (fun _ ↦ rfl)
  _         = F G b := by rw [F_spec]

theorem F_eval_eq_zero (b : B) : (F G b).eval b = 0 := by
  let foo := Fintype.ofFinite G
  simp [F_spec,finprod_eq_prod_of_fintype,eval_prod]
  apply @Finset.prod_eq_zero _ _ _ _ _ (1 : G) (Finset.mem_univ 1)
  simp

private theorem F_coeff_fixed (b : B) (n : ℕ) (g : G) :
    g • (F G b).coeff n = (F G b).coeff n := by
  change (g • (F G b)).coeff n = _
  rw [F_smul_eq_self]

end F_API

open scoped algebraMap

noncomputable local instance : Algebra A[X] B[X] :=
  RingHom.toAlgebra (Polynomial.mapRingHom (Algebra.toRingHom))

@[simp, norm_cast]
theorem _root_.coe_monomial (n : ℕ) (a : A) : ((monomial n a : A[X]) : B[X]) = monomial n (a : B) :=
  map_monomial _

section full_descent

variable (hFull : ∀ (b : B), (∀ (g : G), g • b = b) → ∃ a : A, b = a)

-- Remark: the `splitting_of_full` approach is lousy and should be
-- replaced by the commented-out code below (lines 275-296 currently)

/-- This "splitting" function from B to A will only ever be evaluated on
G-invariant elements of B, and the two key facts about it are
that it lifts such an element to `A`, and for reasons of
convenience it lifts `1` to `1`. -/
noncomputable def splitting_of_full
    (b : B) : A := by classical
  exact
  if b = 1 then 1 else
    if h : ∀ σ : G, σ • b = b then (hFull b h).choose
    else 37

theorem splitting_of_full_spec {b : B} (hb : ∀ σ : G, σ • b = b) :
    splitting_of_full hFull b = b := by
  unfold splitting_of_full
  split_ifs with h1
  · rw_mod_cast [h1]
  · exact (hFull b hb).choose_spec.symm

theorem splitting_of_full_one : splitting_of_full hFull 1 = 1 := by
  unfold splitting_of_full
  rw [if_pos rfl]

noncomputable def M (b : B) : A[X] :=
  (∑ x ∈ (F G b).support, monomial x (splitting_of_full hFull ((F G b).coeff x)))

theorem M_deg_le (b : B) : (M hFull b).degree ≤ (F G b).degree := by
  unfold M
  have := Polynomial.degree_sum_le (F G b).support (fun x => monomial x (splitting_of_full hFull ((F G b).coeff x)))
  refine le_trans this ?_
  rw [Finset.sup_le_iff]
  intro n hn
  apply le_trans (degree_monomial_le n _) ?_
  exact le_degree_of_mem_supp n hn

variable [Nontrivial B] [Finite G]

theorem M_coeff_card (b : B) :
    (M hFull b).coeff (Nat.card G) = 1 := by
  unfold M
  simp only [finset_sum_coeff]
  have hdeg := F_degree G b
  rw [degree_eq_iff_natDegree_eq_of_pos Nat.card_pos] at hdeg
  rw [ ← hdeg]
  rw [Finset.sum_eq_single_of_mem ((F G b).natDegree)]
  · have : (F G b).Monic := F_monic b
    simp
    simp_all [splitting_of_full_one]
  · refine natDegree_mem_support_of_nonzero ?h.H
    intro h
    rw [h] at hdeg
    have : 0 < Nat.card G := Nat.card_pos
    simp_all
  · intro d _ hd
    exact coeff_monomial_of_ne (splitting_of_full hFull ((F G b).coeff d)) hd

theorem M_deg_eq_F_deg [Nontrivial A] (b : B) : (M hFull b).degree = (F G b).degree := by
  apply le_antisymm (M_deg_le hFull b)
  rw [F_degree]
  have := M_coeff_card hFull b
  refine le_degree_of_ne_zero ?h
  rw [this]
  exact one_ne_zero

theorem M_deg [Nontrivial A] (b : B) : (M hFull b).degree = Nat.card G := by
  rw [M_deg_eq_F_deg hFull b]
  exact F_degree G b

theorem M_monic (b : B) : (M hFull b).Monic := by
  have this1 := M_deg_le hFull b
  have this2 := M_coeff_card hFull b
  have this3 : 0 < Nat.card G := Nat.card_pos
  rw [← F_natdegree b] at this2 this3
  -- then the hypos say deg(M)<=n, coefficient of X^n is 1 in M
  have this4 : (M hFull b).natDegree ≤ (F G b).natDegree := natDegree_le_natDegree this1
  exact Polynomial.monic_of_natDegree_le_of_coeff_eq_one _ this4 this2

omit [Nontrivial B] in
theorem M_spec (b : B) : ((M hFull b : A[X]) : B[X]) = F G b := by
  unfold M
  ext N
  push_cast
  simp_rw [splitting_of_full_spec hFull <| F_coeff_fixed b _]
  simp_rw [finset_sum_coeff, ← lcoeff_apply, lcoeff_apply, coeff_monomial]
  aesop

omit [Nontrivial B] in
theorem M_spec_map (b : B) : (map (algebraMap A B) (M hFull b)) = F G b := by
  rw [← M_spec hFull b]; rfl

omit [Nontrivial B] in
theorem M_eval_eq_zero (b : B) : (M hFull b).eval₂ (algebraMap A B) b = 0 := by
  rw [eval₂_eq_eval_map, M_spec_map, F_eval_eq_zero]

include hFull in
theorem isIntegral : Algebra.IsIntegral A B where
  isIntegral b := ⟨M hFull b, M_monic hFull b, M_eval_eq_zero hFull b⟩

end full_descent

end MulSemiringAction.CharacteristicPolynomial

end charpoly

section part_a

open MulSemiringAction.CharacteristicPolynomial

variable {A : Type*} [CommRing A]
  {B : Type*} [CommRing B] [Algebra A B] [Nontrivial B]
  {G : Type*} [Group G] [Finite G] [MulSemiringAction G B]

theorem isIntegral_of_Full (hFull : ∀ (b : B), (∀ (g : G), g • b = b) → ∃ a : A, b = a) :
    Algebra.IsIntegral A B where
  isIntegral b := ⟨M hFull b, M_monic hFull b, M_eval_eq_zero hFull b⟩

variable (P Q : Ideal B) [P.IsPrime] [Q.IsPrime]
  (hPQ : Ideal.comap (algebraMap A B) P = Ideal.comap (algebraMap A B) Q)

open scoped Pointwise

theorem Nontrivial_of_exists_prime {R : Type*} [CommRing R]
    (h : ∃ P : Ideal R, P.IsPrime) : Nontrivial R := by
  contrapose! h
  intro P hP
  rw [@not_nontrivial_iff_subsingleton] at h
  obtain ⟨h, _⟩ := hP
  apply h
  apply Subsingleton.elim

-- (Part a of Théorème 2 in section 2 of chapter 5 of Bourbaki Alg Comm)
omit   [Nontrivial B] in
theorem part_a [SMulCommClass G A B]
    (hPQ : Ideal.comap (algebraMap A B) P = Ideal.comap (algebraMap A B) Q)
    (hFull' : ∀ (b : B), (∀ (g : G), g • b = b) → ∃ a : A, b = a) :
    ∃ g : G, Q = g • P := by
  haveI : Nontrivial B := Nontrivial_of_exists_prime ⟨Q, inferInstance⟩
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
-- I'm going to avoid this because I'm just going to use scaling.
-- I'll show that every nonzero element of B/Q divides an element of A/P.

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

/-
Set-up for part (b) of the lemma. G acts on B with invariants A (or more precisely the
image of A). Warning: `P` was a prime ideal of `B` in part (a) but it's a prime ideal
of `A` here, in fact it's `Q ∩ A`, the preimage of `Q` in `A`.

We want to consider the following commutative diagram.

B ---> B / Q -----> L = Frac(B/Q)
/\       /\         /\
|        |          |
|        |          |
A ---> A / P ----> K = Frac(A/P)

We will get to L, K, and the second square later.
First let's explain how to do P and Q.
-/
variable (Q : Ideal B) [Q.IsPrime] (P : Ideal A) [P.IsPrime]
-- #synth Algebra A (B ⧸ Q) #exit -- works
---synth IsScalarTower A B (B ⧸ Q) #exit-- works
-- (hPQ : Ideal.comap (algebraMap A B) P = p) -- we will *prove* this from the
-- commutativity of the diagram! This is a trick I learnt from Jou who apparently
-- learnt it from Amelia
  [Algebra (A ⧸ P) (B ⧸ Q)] [IsScalarTower A (A ⧸ P) (B ⧸ Q)]
-- So now we know the left square commutes.
-- Amelia's first trick: commutativity of th LH diagram implies `P ⊆ Q ∩ A`
-- For the map `A -> A/P -> B/Q` must equal the map `A -> B -> B/Q` so `P` must
-- be a subset of the kernel of `A → B/Q`, which is `A ∩ Q`

omit [P.IsPrime] in
theorem Ideal.Quotient.eq_zero_iff_mem' (x : A) :
    algebraMap A (A ⧸ P) x = 0 ↔ x ∈ P :=
  Ideal.Quotient.eq_zero_iff_mem

section B_mod_Q_over_A_mod_P_stuff

section Mathlib.RingTheory.Ideal.Quotient

namespace Ideal

variable {R : Type*} [CommRing R] {I : Ideal R}

protected noncomputable
def Quotient.out (x : R ⧸ I) := x.out

theorem Quotient.out_eq (x : R ⧸ I) : Ideal.Quotient.mk I (Ideal.Quotient.out x) = x := by
  simp only [Ideal.Quotient.out, Ideal.Quotient.mk, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
    Submodule.Quotient.mk, Quotient.out_eq']

@[elab_as_elim]
protected theorem Quotient.induction_on
    {p : R ⧸ I → Prop} (x : R ⧸ I) (h : ∀ a, p (Ideal.Quotient.mk I a)) : p x :=
  Quotient.inductionOn x h

end Ideal

end Mathlib.RingTheory.Ideal.Quotient

namespace MulSemiringAction.CharacteristicPolynomial


open Polynomial
/-
I didn't check that this definition was independent
of the lift `b` of `bbar` (and it might not even be true).
But this doesn't matter, because `G` no longer acts on `B/Q`.
All we need is that `Mbar` is monic of degree `|G|`, is defined over the bottom ring
and kills `bbar`.
-/
variable {Q} in
noncomputable def Mbar
    (hFull' : ∀ (b : B), (∀ (g : G), g • b = b) → ∃ a : A, b = a)
    (bbar : B ⧸ Q) : (A ⧸ P)[X] :=
  Polynomial.map (Ideal.Quotient.mk P) <| M hFull' <| Ideal.Quotient.out bbar

variable (hFull' : ∀ (b : B), (∀ (g : G), g • b = b) → ∃ a : A, b = a)

omit [SMulCommClass G A B] [Q.IsPrime] [P.IsPrime] [Algebra (A ⧸ P) (B ⧸ Q)]
  [IsScalarTower A (A ⧸ P) (B ⧸ Q)] in
theorem Mbar_monic [Nontrivial B] (bbar : B ⧸ Q) : (Mbar P hFull' bbar).Monic := by
  have := M_monic hFull'
  simp [Mbar, (M_monic hFull' _).map]

omit [SMulCommClass G A B] [Q.IsPrime] [Algebra (A ⧸ P) (B ⧸ Q)] [IsScalarTower A (A ⧸ P) (B ⧸ Q)] in
theorem Mbar_deg [Nontrivial A] [Nontrivial B] (bbar : B ⧸ Q) :
    degree (Mbar P hFull' bbar) = Nat.card G := by
  simp only [Mbar]
  rw [degree_map_eq_of_leadingCoeff_ne_zero]
  · exact M_deg hFull' _
  · rw [(M_monic hFull' _).leadingCoeff]
    simp only [map_one, ne_eq, one_ne_zero, not_false_eq_true]

omit [SMulCommClass G A B] [Q.IsPrime] [P.IsPrime] in
theorem Mbar_eval_eq_zero [Nontrivial A] [Nontrivial B] (bbar : B ⧸ Q) :
    eval₂ (algebraMap (A ⧸ P) (B ⧸ Q)) bbar (Mbar P hFull' bbar) = 0 := by
  have h := congr_arg (algebraMap B (B ⧸ Q)) (M_eval_eq_zero hFull' (Ideal.Quotient.out bbar))
  rw [map_zero, hom_eval₂, Ideal.Quotient.algebraMap_eq, Ideal.Quotient.out_eq] at h
  simpa [Mbar, eval₂_map, ← Ideal.Quotient.algebraMap_eq,
    ← IsScalarTower.algebraMap_eq A (A ⧸ P) (B ⧸ Q), IsScalarTower.algebraMap_eq A B (B ⧸ Q)]

end CharacteristicPolynomial

open CharacteristicPolynomial in
omit [SMulCommClass G A B] [Q.IsPrime] [P.IsPrime] in
theorem reduction_isIntegral
    [Nontrivial A] [Nontrivial B]
    (hFull' : ∀ (b : B), (∀ (g : G), g • b = b) → ∃ a : A, b = a) :
    Algebra.IsIntegral (A ⧸ P) (B ⧸ Q) where
  isIntegral x := ⟨Mbar P hFull' x, Mbar_monic Q P hFull' x, Mbar_eval_eq_zero Q P hFull' x⟩

end MulSemiringAction

theorem Polynomial.nonzero_const_if_isIntegral (R S : Type) [CommRing R] [Nontrivial R]
    [CommRing S] [Algebra R S] [Algebra.IsIntegral R S] [IsDomain S] (s : S) (hs : s ≠ 0) :
    ∃ (q : Polynomial R), q.coeff 0 ≠ 0 ∧ q.eval₂ (algebraMap R S) s = 0 := by
  obtain ⟨p, p_monic, p_eval⟩ := (@Algebra.isIntegral_def R S).mp inferInstance s
  have p_nzero := ne_zero_of_ne_zero_of_monic X_ne_zero p_monic
  obtain ⟨q, p_eq, q_ndvd⟩ := Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd p p_nzero 0
  rw [C_0, sub_zero] at p_eq
  rw [C_0, sub_zero] at q_ndvd
  use q
  constructor
  . intro q_coeff_0
    exact q_ndvd <| X_dvd_iff.mpr q_coeff_0
  . rw [p_eq, eval₂_mul] at p_eval
    rcases NoZeroDivisors.eq_zero_or_eq_zero_of_mul_eq_zero p_eval with Xpow_eval | q_eval
    . by_contra
      apply hs
      rw [eval₂_X_pow] at Xpow_eval
      exact pow_eq_zero Xpow_eval
    . exact q_eval

theorem Algebra.exists_dvd_nonzero_if_isIntegral (R S : Type) [CommRing R] [Nontrivial R]
    [CommRing S] [Algebra R S] [Algebra.IsIntegral R S] [IsDomain S] (s : S) (hs : s ≠ 0) :
    ∃ r : R, r ≠ 0 ∧ s ∣ (algebraMap R S) r := by
  obtain ⟨q, q_zero_coeff, q_eval_zero⟩ := Polynomial.nonzero_const_if_isIntegral R S s hs
  use q.coeff 0
  refine ⟨q_zero_coeff, ?_⟩
  rw [← Polynomial.eval₂_X (algebraMap R S) s, ← dvd_neg, ← Polynomial.eval₂_C (algebraMap R S) s]
  rw [← zero_add (-_), Mathlib.Tactic.RingNF.add_neg, ← q_eval_zero, ← Polynomial.eval₂_sub]
  apply Polynomial.eval₂_dvd
  exact Polynomial.X_dvd_sub_C

end B_mod_Q_over_A_mod_P_stuff

/-
\section{The extension $L/K$.}

\begin{theorem}
  \label{foo1}
If $\lambda\in L$ then there's a monic polynomial $P_\lambda\in K[X]$ of degree $|G|$
with $\lambda$ as a root, and which splits completely in $L[X]$.
\end{theorem}
\begin{proof}
  A general $\lambda\in L$ can be written as $\beta_1/\beta_2$ where $\beta_1,\beta_2\in B/Q$.
  The previous corollary showed that there's some nonzero $\alpha\in A/P$ such that $\beta_2$
  divides $\alpha$, and hence $\alpha\lambda\in B/Q$ (we just cleared denominators).
  Thus $\alpha\lambda$ is a root of some monic polynomial $f(x)\in (A/P)[X]$,
  by~\ref{MulSemiringAction.CharacteristicPolynomial.Mbar_eval_eq_zero}.
  The polynomial $f(\alpha x)\in (A/P)[X]$ thus
  has $\lambda$ as a root, but it is not monic; its leading term is $\alpha^n$.
  Dividing through in $K[X]$ gives us the polynomial we seek.
\end{proof}

\begin{corollary} The extension $L/K$ is algebraic and normal.
\end{corollary}
\begin{proof} \uses{foo1}
  Exercise using the previous theorem.
\end{proof}

Note that $L/K$ might not be separable and might have infinite degree. However

\begin{corollary} Any subextension of $L/K$ which is finite and separable over $K$
  has degree at most $|G|$.
\end{corollary}
\begin{proof}
  Finite and separable implies simple, and we've already seen that any
  element of $L$ has degree at most $|G|$ over $K$.
\end{proof}

\begin{corollary} The maximal separable subextension $M$ of $L/K$ has degree at most $|G|$.
\end{corollary}
\begin{proof} If it has dimension greater than $|G|$ over $K$, then it has a finitely-generated
  subfeld of $K$-dimension greater than $|G|$, and is finite and separable, contradicting
  the previous result.
\end{proof}

\begin{corollary} $\Aut_K(L)$ is finite.
\end{corollary}
\begin{proof} Any $K$-automorphism of $L$ is determined by where it sends $M$.
\end{proof}

\begin{corollary} $\Aut_{A/P}(B/Q)$ is finite.
\end{corollary}
\begin{proof}
  Two elements of $\Aut_{A/P}(B/Q)$ which agree once extended to automorphisms of $L$
  must have already been equal, as $B/Q\subseteq L$. Hence the canonical map
  from $\Aut_{A/P}(B/Q)$ to $\Aut_K(L)$ is injective.
\end{proof}

\section{Proof of surjectivity.}

\begin{definition} We fix once and for all some nonzero $y\in B/Q$ such that $M=K(y)$,
  with $M$ the maximal separable subextension of $L/K$.
\end{definition}

Note that the existence of some $\lambda\in L$ with this property just comes from finite
and separable implies simple; we can use the ``clear denominator'' technique introduced
earlier to scale this by some nonzero $\alpha\in A$ into $B/Q$, as
$K(\lambda)=K(\alpha\lambda)$.

Here is a slightly delicate result whose proof I haven't thought too hard about.
\begin{theorem} There exists some $x\in B$ and $\alpha\in A$ with the following
  properties.
  \begin{enumerate}
  \item $x=\alpha y$ mod $Q$ and $\alpha$ isn't zero mod $Q$.
  \item $x\in Q'$ for all $Q'\not=Q$ in the $G$-orbit of $Q$.
  \end{enumerate}
\end{theorem}
\begin{proof}
  Idea. Localise away from P, then all the $Q_i$ are maximal, use CRT and then clear denominators.
\end{proof}

We now choose some $x\in B[1/S]$ which is $y$ modulo $Q$ and $0$ modulo all the other
primes of $B$ above $P$, and consider the monic degree $|G|$ polynomial $f$ in $K[X]$
with $x$ and its conjugates as roots. If $\sigma\in\Aut_K(L)$ then $\sigma(\overline{x})$
is a root of $f$ as $\sigma$ fixes $K$ pointwise. Hence $\sigma(\overline{x})=\overline{g(x)}$
for some $g\in G$, and because $\sigma(\overline{x})\not=0$ we have $\overline{g(x)}\not=0$
and hence $g(x)\notin Q[1/S]$. Hence $x\notin g^{-1} Q[1/S]$ and thus $g^{-1}Q=Q$ and $g\in SD_Q$.
Finally we have $\phi_g=\sigma$ on $K$ and on $y$, so they are equal on $M$ and hence on $L$ as
$L/M$ is purely inseparable.

This part of the argument seems weak.
-/

section L_over_K_stuff

-- Let's now make the right square. First `L`
variable (L : Type*) [Field L] [Algebra (B ⧸ Q) L] [IsFractionRing (B ⧸ Q) L]
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


-- Do we need a version of Ideal.Quotient.eq_zero_iff_mem with algebraMap?


-- not sure if we need this but let's prove it just to check our setup is OK.
-- The claim is that the preimage of Q really is P (rather than just containing P)
-- and the proof is that A/P -> B/Q extends to a map of fields which is injective,
-- so A/P -> B/Q must also be injective.
open IsScalarTower in
example : Ideal.comap (algebraMap A B) Q = P := by
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

open MulSemiringAction.CharacteristicPolynomial

namespace Bourbaki52222

variable (hFull' : ∀ (b : B), (∀ (g : G), g • b = b) → ∃ a : A, b = a) in
variable (G) in
noncomputable def residueFieldExtensionPolynomial [DecidableEq L] (x : L) : K[X] :=
  if x = 0 then monomial (Nat.card G) 1
  else 37 -- this is not actually right. In the nonzero case you
  -- clear denominators with a nonzero element of A, using
  -- `Algebra.exists_dvd_nonzero_if_isIntegral` above, and then use Mbar
  -- scaled appropriately.

theorem f_exists [DecidableEq L] (l : L) :
    ∃ f : K[X], f.Monic ∧ f.degree = Nat.card G ∧
    eval₂ (algebraMap K L) l f = 0 ∧ f.Splits (algebraMap K L) := by
  use Bourbaki52222.residueFieldExtensionPolynomial G L K l
  sorry

theorem algebraMap_cast {R S: Type*} [CommRing R] [CommRing S] [Algebra R S] (r : R) :
  (r : S) = (algebraMap R S) r := by
  rfl

theorem algebraMap_algebraMap {R S T : Type*} [CommRing R] [CommRing S] [CommRing T] [Algebra R S]
  [Algebra S T] [Algebra R T] [IsScalarTower R S T] (r : R) :
  (algebraMap S T) ((algebraMap R S) r) = (algebraMap R T) r := by
  exact Eq.symm (IsScalarTower.algebraMap_apply R S T r)

theorem Algebra.isAlgebraic_of_subring_isAlgebraic {R k K : Type*} [CommRing R] [CommRing k]
    [CommRing K] [Algebra R K] [IsFractionRing R K] [Algebra k K]
    (h : ∀ x : R, IsAlgebraic k (x : K)) : Algebra.IsAlgebraic k K := by
  rw [Algebra.isAlgebraic_def]
  let M := nonZeroDivisors R
  intro x
  have ⟨r, s, h'⟩ := IsLocalization.mk'_surjective M x
  have : x = r * IsLocalization.mk' K 1 s := by
    rw [← h', IsLocalization.mul_mk'_eq_mk'_of_mul]
    simp
  rw [this]
  apply IsAlgebraic.mul (h r)
  exact IsAlgebraic.invLoc (h s)

-- this uses `Algebra.isAlgebraic_of_subring_isAlgebraic` but I think we're going to have
-- to introduce `f` anyway because we need not just that the extension is algebraic but
-- that every element satisfies a poly of degree <= |G|.
theorem algebraic {A : Type*} [CommRing A] {B : Type*} [Nontrivial B] [CommRing B] [Algebra A B]
  [Algebra.IsIntegral A B] {G : Type*} [Group G] [Finite G] [MulSemiringAction G B] (Q : Ideal B)
  [Q.IsPrime] (P : Ideal A) [P.IsPrime] [Algebra (A ⧸ P) (B ⧸ Q)]
  [IsScalarTower A (A ⧸ P) (B ⧸ Q)] (L : Type*) [Field L] [Algebra (B ⧸ Q) L]
  [IsFractionRing (B ⧸ Q) L] [Algebra (A ⧸ P) L] [IsScalarTower (A ⧸ P) (B ⧸ Q) L]
  (K : Type*) [Field K] [Algebra (A ⧸ P) K] [IsFractionRing (A ⧸ P) K]
  [Algebra K L] [IsScalarTower (A ⧸ P) K L] [Algebra A K] [IsScalarTower A (A ⧸ P) K]
  [Algebra B L] [IsScalarTower B (B ⧸ Q) L] [Algebra A L] [IsScalarTower A K L]
  [IsScalarTower A B L]
  (hFull : ∀ (b : B), (∀ (g : G), g • b = b) → ∃ a : A, b = a): Algebra.IsAlgebraic K L := by
  apply @Algebra.isAlgebraic_of_subring_isAlgebraic (B ⧸ Q)
  intro b_bar
  have ⟨b, hb⟩ := Ideal.Quotient.mk_surjective b_bar
  have hb : (algebraMap B (B ⧸ Q)) b = b_bar := hb
  use ((M hFull b).map (algebraMap A (A ⧸ P))).map (algebraMap (A ⧸ P) K)
  constructor
  . apply ne_zero_of_ne_zero_of_monic X_ne_zero
    apply Monic.map
    apply Monic.map
    exact M_monic hFull b
  . rw [← hb, algebraMap_cast, map_map, ← IsScalarTower.algebraMap_eq]
    rw [algebraMap_algebraMap, aeval_def, eval₂_eq_eval_map, map_map, ← IsScalarTower.algebraMap_eq]
    rw [IsScalarTower.algebraMap_eq A B L, ← map_map, M_spec_map]
    rw [eval_map, eval₂_hom, F_eval_eq_zero]
    exact algebraMap.coe_zero

include G in
theorem normal [DecidableEq L] : Normal K L := by
  rw [normal_iff]
  intro l
  obtain ⟨f, hfmonic, _, hf, hfsplits⟩ := @f_exists G _ _ L _ K _ _ _ l
  have hnz : f ≠ 0 := hfmonic.ne_zero
  constructor
  · rw [← isAlgebraic_iff_isIntegral]
    exact ⟨f, hfmonic.ne_zero, hf⟩
  refine Polynomial.splits_of_splits_of_dvd (algebraMap K L) hnz hfsplits ?_
  exact minpoly.dvd _ _ hf

open Module

theorem separableClosure_finiteDimensional : FiniteDimensional K (separableClosure K L) := sorry

-- degree of max sep subextension is ≤ |G|
theorem separableClosure_finrank_le : finrank K (separableClosure K L) ≤ Nat.card G := sorry

open scoped IntermediateField
theorem primitive_element : ∃ y : L, K⟮y⟯ = separableClosure K L := sorry

-- this definition might break when primitive_element is proved because there will be
-- more hypotheses.
noncomputable def y : L := (primitive_element L K).choose

--noncomputable def y_spec : K⟮y⟯ = separableClosure K L := (primitive_element L K).choose_spec

end Bourbaki52222

end L_over_K_stuff

section main_theorem_statement

namespace Bourbaki52222

open scoped Pointwise

-- Basic API for what we're doing here. Writing down a map from the stabiliser of Q to
-- the residual Galois group `L ≃ₐ[K] L`, where L=Frac(B/Q) and K=Frac(A/P).
-- Hopefully sorrys aren't too hard

def quotientRingAction (Q' : Ideal B) (g : G) (hg : g • Q = Q') :
    B ⧸ Q ≃+* B ⧸ Q' :=
  Ideal.quotientEquiv Q Q' (MulSemiringAction.toRingEquiv G B g) hg.symm

def quotientAlgebraAction (g : G) (hg : g • Q = Q) : (B ⧸ Q) ≃ₐ[A ⧸ P] B ⧸ Q where
  __ := quotientRingAction Q Q g hg
  commutes' := by
    intro a_bar; dsimp
    have ⟨a, ha⟩ := Ideal.Quotient.mk_surjective a_bar
    rw [quotientRingAction]; dsimp
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

variable (L : Type*) [Field L] [Algebra (B ⧸ Q) L] [IsFractionRing (B ⧸ Q) L]
  [Algebra (A ⧸ P) L] [IsScalarTower (A ⧸ P) (B ⧸ Q) L]
  (K : Type*) [Field K] [Algebra (A ⧸ P) K] [IsFractionRing (A ⧸ P) K]
  [Algebra K L] [IsScalarTower (A ⧸ P) K L]



noncomputable def IsFractionRing.algEquiv_lift (e : (B ⧸ Q) ≃ₐ[A ⧸ P] B ⧸ Q) : L ≃ₐ[K] L where
  __ := IsFractionRing.ringEquivOfRingEquiv e.toRingEquiv
  commutes' := by
    intro k
    dsimp
    obtain ⟨x, y, _, rfl⟩ := @IsFractionRing.div_surjective (A ⧸ P) _ K _ _ _ k
    simp [algebraMap_algebraMap]
    unfold IsFractionRing.ringEquivOfRingEquiv
    unfold IsLocalization.ringEquivOfRingEquiv
    simp [IsScalarTower.algebraMap_apply (A ⧸ P) (B ⧸ Q) L]

noncomputable def stabilizer.toGaloisGroup : MulAction.stabilizer G Q →* (L ≃ₐ[K] L) where
  toFun gh := IsFractionRing.algEquiv_lift Q P L K (Pointwise.quotientAlgebraActionMonoidHom Q P gh)
  map_one' := by
    apply AlgEquiv.ext
    intro l; simp
    obtain ⟨x, y, _, rfl⟩ := @IsFractionRing.div_surjective (B ⧸ Q) _ L _ _ _ l
    unfold IsFractionRing.algEquiv_lift
    unfold IsFractionRing.ringEquivOfRingEquiv
    simp
  map_mul' := by
    intro ⟨x, hx⟩ ⟨y, hy⟩
    apply AlgEquiv.ext
    intro l; dsimp
    obtain ⟨r, s, _, rfl⟩ := @IsFractionRing.div_surjective (B ⧸ Q) _ L _ _ _ l
    unfold IsFractionRing.algEquiv_lift
    unfold IsFractionRing.ringEquivOfRingEquiv
    simp
    sorry

variable (hFull : ∀ (b : B), (∀ (g : G), g • b = b) ↔ ∃ a : A, b = a) in
/-- From Bourbaki Comm Alg, Chapter V. -/
theorem MulAction.stabilizer_surjective_of_action : Function.Surjective
    (stabilizer.toGaloisGroup Q P L K : MulAction.stabilizer G Q → (L ≃ₐ[K] L)) := by
  sorry

end Bourbaki52222

end main_theorem_statement

section localization

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
