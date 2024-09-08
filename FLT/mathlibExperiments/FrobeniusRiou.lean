-- Frobenius elements following Joel Riou's idea to use a very general lemma
-- from Bourbaki comm alg
-- (Théorème 2 in section 2 of chapter 5 of Bourbaki Alg Comm)
-- (see https://leanprover.zulipchat.com/#narrow/stream/416277-FLT/topic/Outstanding.20Tasks.2C.20V4/near/449562398)


import Mathlib.RingTheory.Ideal.Pointwise
import Mathlib.RingTheory.Ideal.Over
import Mathlib.FieldTheory.Normal

variable {A : Type*} [CommRing A]
  {B : Type*} [CommRing B] [Algebra A B] [Algebra.IsIntegral A B]
  {G : Type*} [Group G] [Finite G] [MulSemiringAction G B]

open scoped algebraMap

variable (hGalois : ∀ (b : B), (∀ (g : G), g • b = b) ↔ ∃ a : A, b = a)

section part_a

variable (P Q : Ideal B) [P.IsPrime] [Q.IsPrime]
  (hPQ : Ideal.comap (algebraMap A B) P = Ideal.comap (algebraMap A B) Q)

open scoped Pointwise

private lemma norm_fixed (b : B) (g : G) : g • (∏ᶠ σ : G, σ • b) = ∏ᶠ σ : G, σ • b := calc
  g • (∏ᶠ σ : G, σ • b) = ∏ᶠ σ : G, g • (σ • b) := sorry -- this is `smul_finprod` after we bump mathlib
  _                     = ∏ᶠ σ : G, σ • b := finprod_eq_of_bijective (g • ·) (MulAction.bijective g)
                                               fun x ↦ smul_smul g x b

theorem _root_.Ideal.IsPrime.finprod_mem_iff_exists_mem {R S : Type*} [Finite R] [CommSemiring S]
    (I : Ideal S) [hI : I.IsPrime] (f : R → S)  :
    ∏ᶠ x, f x ∈ I ↔ ∃ p, f p ∈ I := by
  have := Fintype.ofFinite R
  rw [finprod_eq_prod_of_fintype, Finset.prod_eq_multiset_prod, hI.multiset_prod_mem_iff_exists_mem]
  simp

-- (Part a of Théorème 2 in section 2 of chapter 5 of Bourbaki Alg Comm)
theorem part_a
    (hPQ : Ideal.comap (algebraMap A B) P = Ideal.comap (algebraMap A B) Q)
    (hGalois : ∀ (b : B), (∀ (g : G), g • b = b) ↔ ∃ a : A, b = a) :
    ∃ g : G, Q = g • P := by
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
    specialize hGalois (algebraMap A B x)
    have := hGalois.2 ⟨x, rfl⟩
    simp only [Ideal.mem_comap]
    nth_rw 2 [← this]
    exact Ideal.smul_mem_pointwise_smul_iff.symm
  suffices ∃ g ∈ (⊤ : Finset G), Q ≤ g • P by
    convert this; simp
  rw [← Ideal.subset_union_prime 1 1 <| fun g _ _ _ ↦ ?_]; swap
  · exact Ideal.map_isPrime_of_equiv (MulSemiringAction.toRingEquiv _ _ g)
  intro x hx
  specialize hGalois (∏ᶠ σ : G, σ • x)
  obtain ⟨a, ha⟩ := hGalois.1 (norm_fixed _)
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

section normal_elements

variable (K : Type*) [Field K] {L : Type*} [Field L] [Algebra K L]

open Polynomial
-- Do we have this?
def IsNormalElement (x : L) : Prop := Splits (algebraMap K L) (minpoly K x)

namespace IsNormalElement

lemma iff_exists_monic_splits {x : L} (hx : IsIntegral K x) :
    IsNormalElement K x ↔
    ∃ P : K[X], P.Monic ∧ P.eval₂ (algebraMap K L) x = 0 ∧ Splits (algebraMap K L) P := by
  constructor
  · intro h
    exact ⟨minpoly K x, minpoly.monic hx, minpoly.aeval K x, h⟩
  · rintro ⟨P, hPmonic, hPeval, hPsplits⟩
    -- need min poly divides P and then it should all be over
    sorry

lemma prod {x y : L} (hxint : IsIntegral K x) (hyint : IsIntegral K y)
    (hx : IsNormalElement K x) (hy : IsNormalElement K y) :
    IsNormalElement K (x * y) := by
  rw [iff_exists_monic_splits K hxint] at hx
  obtain ⟨Px, hx1, hx2, hx3⟩ := hx
  rw [iff_exists_monic_splits K hyint] at hy
  obtain ⟨Py, hy1, hy2, hy3⟩ := hy
  rw [iff_exists_monic_splits K <| IsIntegral.mul hxint hyint]
  -- If roots of Px are xᵢ and roots of Py are yⱼ, then use the poly whose roots are xᵢyⱼ.
  -- Do we have this? Is it the resultant or something?
  sorry

-- API

end IsNormalElement

end normal_elements

section part_b

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

lemma Ideal.Quotient.eq_zero_iff_mem' (x : A) :
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
  rw [← algebraMap_apply A B (B ⧸ Q), algebraMap_apply A (A ⧸ P) (B ⧸ Q)]
  rw [← algebraMap_apply (A ⧸ P) K L, algebraMap_apply (A ⧸ P) (B ⧸ Q) L]

open Polynomial BigOperators

variable (G) in
/-- `F : B[X]` defined to be a product of linear factors `(X - τ • α)`; where
`τ` runs over `L ≃ₐ[K] L`, and `α : B` is an element which generates `(B ⧸ Q)ˣ`
and lies in `τ • Q` for all `τ ∉ (decomposition_subgroup_Ideal'  A K L B Q)`.-/
private noncomputable abbrev F (b : B) : B[X] := ∏ᶠ τ : G, (X - C (τ • b))

private lemma F_spec (b : B) : F G b = ∏ᶠ τ : G, (X - C (τ • b)) := rfl

private lemma F_smul_eq_self (σ : G) (b : B) : σ • (F G b) = F G b := calc
  σ • F G b = σ • ∏ᶠ τ : G, (X - C (τ • b)) := by rfl
  _         = ∏ᶠ τ : G, σ • (X - C (τ • b)) := sorry -- smul_prod for finprod
  _         = ∏ᶠ τ : G, (X - C ((σ * τ) • b)) := by simp [smul_sub, smul_smul]; congr; ext t; congr 2; sorry -- is this missing??
  _         = ∏ᶠ τ' : G, (X - C (τ' • b)) := sorry -- Finite.finprod_bijective (fun τ ↦ σ * τ)
                                                      -- (Group.mulLeft_bijective σ) _ _ (fun _ ↦ rfl)
  _         = F G b := by rw [F_spec]

private lemma F_eval_eq_zero (b : B) : (F G b).eval b = 0 := by
  simp [F_spec, eval_prod]; sorry -- missing lemma? Finprod.prod_eq_zero (Finset.mem_univ (1 : G))]

open scoped algebraMap

noncomputable local instance : Algebra A[X] B[X] :=
  RingHom.toAlgebra (Polynomial.mapRingHom (Algebra.toRingHom))

-- PR?
@[simp, norm_cast]
lemma coe_monomial (n : ℕ) (a : A) : ((monomial n a : A[X]) : B[X]) = monomial n (a : B) :=
  map_monomial _

private lemma F_descent (hGalois : ∀ (b : B), (∀ (g : G), g • b = b) ↔ ∃ a : A, b = a) (b : B) :
    ∃ M : A[X], (M : B[X]) = F G b := by
  choose f hf using fun b ↦ (hGalois b).mp
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

variable (G) in
noncomputable def M (b : B) : A[X] := (F_descent hGalois b).choose

lemma M_spec (b : B) : ((M G hGalois b : A[X]) : B[X]) = F G b := (F_descent hGalois b).choose_spec

lemma M_eval_eq_zero (b : B) : (M G hGalois b).eval₂ (algebraMap A[X] B[X]) b = 0 := by
  sorry -- follows from `F_eval_eq_zero`

lemma Algebra.isAlgebraic_of_subring_isAlgebraic {R k K : Type*} [CommRing R] [CommRing k]
    [CommRing K] [Algebra R K] [IsFractionRing R K] [Algebra k K]
    (h : ∀ x : R, IsAlgebraic k (x : K)) : Algebra.IsAlgebraic k K := by
  -- ratio of two algebraic numbers is algebraic (follows from reciprocal of algebraic number
  -- is algebraic; proof is "reverse the min poly")
  sorry

-- (Théorème 2 in section 2 of chapter 5 of Bourbaki Alg Comm)
theorem part_b1 : Algebra.IsAlgebraic K L := by
  /-
  Because of `IsFractionRing (B ⧸ P) K` and the previous lemma it suffices to show that every
  element of B/P is algebraic over k, and this is because you can lift to b ∈ B and then
  use `M` above.
  -/
  sorry



theorem part_b2 : Normal K L := by
  /-
  Let's temporarily say that an *element* of `K` is _normal_ if it is the root of a monic poly
  in `k[X]` all of whose roots are in `K`. Then `K/k` is normal iff all elements are normal
  (if `t` is a root of `P ∈ k[X]` then the min poly of `t` must divide `P`).
  I claim that the product of two normal elements is normal. Indeed if `P` and `Q` are monic polys
  in `k[X]` with roots `xᵢ` and `yⱼ` then there's another monic poly in `k[X]` whose roots are
  the products `xᵢyⱼ`. Also the reciprocal of a nonzero normal element is normal (reverse the
  polynomial and take the reciprocals of all the roots). This is enough.
  -/
  sorry

-- yikes! Don't have Ideal.Quotient.map or Ideal.Quotient.congr??
open scoped Pointwise
def foo : MulAction.stabilizer G Q →* ((B ⧸ Q) ≃ₐ[A ⧸ P] (B ⧸ Q)) where
  toFun gh := {
    toFun := sorry
    invFun := sorry
    left_inv := sorry
    right_inv := sorry
    map_mul' := sorry
    map_add' := sorry
    commutes' := sorry
  }
  map_one' := sorry
  map_mul' := sorry
-- definition of canonical map G_P →* (K ≃ₐ[k] K)

-- Main result: it's surjective.
-- Jou proved this (see Frobenius2.lean) assuming (a) K/k simple and (b) P maximal.
-- Bourbaki reduce to maximal case by localizing at P, and use finite + separable = simple
-- on the max separable subextension, but then the argument follows Jou's formalisation
-- in Frobenius2.lean in this directory.
end part_b
