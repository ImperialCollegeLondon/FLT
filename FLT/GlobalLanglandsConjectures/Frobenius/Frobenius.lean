import Mathlib.Tactic
import Mathlib.RingTheory.DedekindDomain.Ideal
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.Ideal.LocalRing
import Mathlib.FieldTheory.Separable
import Mathlib.RingTheory.IntegralDomain
import Mathlib.Algebra.CharP.Reduced
import Mathlib.Tactic.ApplyFun
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Data.ZMod.Algebra
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.Galois
import Mathlib.FieldTheory.SplittingField.IsSplittingField
import Mathlib.FieldTheory.Fixed
import Mathlib.FieldTheory.NormalClosure
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.GroupTheory.GroupAction.FixingSubgroup
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.FieldTheory.PolynomialGaloisGroup
import Mathlib.RingTheory.IntegralRestrict
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.Data.Quot
import Mathlib.Data.Polynomial.Eval
import Mathlib.Data.Polynomial.RingDivision
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.NumberTheory.RamificationInertia
import Mathlib.Order.WellFoundedSet



/-!

## References

See [Karatarakis2022, Mathlib/RingTheory/Valuation/RamificationGroup.lean]
  for definitions of 'decomposition subgroup', 'inertia sugroup'

-/

section References

end References

section FiniteFrobeniusDef

-- translating p. 140 of Milne ANT + Prof. Buzzard's diagram (Feb. 8)

/-
local notation "Frob["K "," L "]" => FrobeniusElt K L
-/



-- Jujian Zhang helped with notation and writing 'theorem ex_FrobElt'
-- JZ: example of how to access a hypothesis in 'variables' or Mathlib:
-- "let i : FiniteDimensional L K := inferInstance"


open NumberField BigOperators
open scoped Pointwise

/-!

For 'L | K' an extension of fields, with automorphism group
'(L ≃ₐ[K] L)' and 'Q.valuationSubring L' as above,
the decomposition group of 'Q.valuationSubring L'
over 'K' is defined as the stabilizer of the multiplicative action
of '(L ≃ₐ[K] L)' on 'Q.valuationSubring L' :
'MulAction.stabilizer (L ≃ₐ[K] L) 'Q.valuationSubring L'.
(See "Mathlib.RingTheory.Valuation.RamificationGroup".)


-/


-- the following 'abbrev' was written by Amelia
-- we redefine 'Ideal B' to be "'Ideal B', keeping in mind 'A' exists'
-- this is so that we can unify the 'A K L B setup' used in 'galRectrictHom'
-- with the MulAction of 'L ≃ₐ[K] L' on the ideals of 'B'
-- note : 'Algebra A B' is given by the above lemma (may be unnecessary)

@[nolint unusedArguments] abbrev Ideal' (A K L B : Type*) [CommRing A]
  [CommRing B] [Algebra A B] [Field K] [Field L]
  [Algebra A K] [IsFractionRing A K] [Algebra B L]
  [Algebra K L] [Algebra A L] [IsScalarTower A B L]
  [IsScalarTower A K L] [IsIntegralClosure B A L]
  [FiniteDimensional K L] := Ideal B

variable [Field K] [Field L]
  (A K L B : Type*)
  [CommRing A] [CommRing B] [Algebra A B]
  [IsDomain A] [IsDomain B]
  [Field K] [Field L] [Algebra A K]
  [IsFractionRing A K] [Algebra B L]
  [Algebra K L] [Algebra A L]
  [IsScalarTower A B L]
  [IsScalarTower A K L]
  [IsIntegralClosure B A L]
  [FiniteDimensional K L]
  [IsFractionRing B L]
  [IsDedekindDomain A] [IsDedekindDomain B]

-- we define the action of Gal(L/K) on the prime ideals of B ⊂ L
-- the prime 'Ideal B' has been re-written as
-- "'Ideal B' , remembering that 'A' exists'
-- in order to synthesize the instance of 'MulAction' on 'Ideal B' with
-- the 'A K L B' setup

example (e : B ≃ₐ[A] B) : B → B := by
  apply AlgEquiv.Simps.symm_apply at e
  exact e

lemma galBmap (σ : L ≃ₐ[K] L)  : B → B := by
  have i : B ≃ₐ[A] B := galRestrict A K L B σ
  apply AlgEquiv.Simps.symm_apply at i
  exact i

-- we define the action of the Galois group on the prime ideals of
-- the ring of integers 'R' of 'L'
-- Amelia helped to define smul, below
noncomputable instance galActionIdeal': MulAction (L ≃ₐ[K] L) (Ideal' A K L B) where
  smul σ I := Ideal.comap (AlgEquiv.symm (galRestrict A K L B σ)) I
  one_smul _ := by
    -- 'show' unfolds goal into something definitionally equal
    show Ideal.comap _ _ = _
    simp
    -- had to use 'convert' instead of 'rw', because 'AlgEquiv.symm (galRestrict A K L B σ) 1'
    -- is not syntactically equal to 'id'
    convert Ideal.comap_id _
  mul_smul _ _ := by
     intro h
     show Ideal.comap _ _ = _
     simp
     exact rfl
    -- 'exact rfl' worked, because the two sides of the goal were ?definitionally equal

-- we define the decomposition group of '(Ideal' A K L B)' over 'K'
-- to be the stabilizer of the MulAction 'galActionisPrime'

def decompositionSubgroupIdeal' (Q : Ideal' A K L B) :
  Subgroup (L ≃ₐ[K] L) := MulAction.stabilizer (L ≃ₐ[K] L) Q

variable {P : Ideal A} [P.IsMaximal] [Fintype (A ⧸ P)]
  (Q : Ideal B) [Q.IsMaximal] [Fintype (B ⧸ Q)]
  [Algebra (A ⧸ P) (B ⧸ Q)]

-- "By the Chinese remainder theorem, there exists an element
-- 'α' of 'B' such that 'α' generates the group '(B ⧸ Q)ˣ'
-- and lies in 'τQ' for all 'τ ¬∈ decompositionSubgroupIdeal'' "

local notation "k" => A ⧸ P
local notation "l" => B ⧸ Q
local notation "q" => Fintype.card (B ⧸ Q)


instance residuefieldUnitsIsCyclic (Q : Ideal B) [hB : Ideal.IsMaximal Q]
  [Fintype (B ⧸ Q)] : IsCyclic (B ⧸ Q)ˣ :=
  isCyclic_of_subgroup_isDomain (Units.coeHom _) <| by
    unfold Function.Injective
    simp_all
    intros a b
    apply Units.ext_iff.2

#check ite

#check IsDedekindDomain.exists_representative_mod_finset



lemma CRT_generator {R : Type*} [CommRing R] [IsDomain R]
  [IsDedekindDomain R]  {s : Finset ℕ} (I : ℕ  → Ideal R)
  [hn : Nonempty s]
  (hp: ∀ i ∈ s, Prime (I i)) (hc : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → I i ≠ I j) :
  ∃ y,
  if ∀ i ∈ s, j ≤ i  then (Ideal.Quotient.mk (I j)) y = 1
  else Ideal.Quotient.mk (I (j)) y = 0 := by
  sorry

theorem generator (Q : Ideal B) [hB : Ideal.IsMaximal Q]
  [Fintype (B ⧸ Q)] :
  ∃ (ρ : B) (h : IsUnit (Ideal.Quotient.mk Q ρ)) ,
  (∀ (x : (B ⧸ Q)ˣ), x ∈ Subgroup.zpowers h.unit)∧
  (∀  τ : L ≃ₐ[K] L, (τ ∉ (decompositionSubgroupIdeal' A K L B Q)) →  ρ ∈ (τ • Q)) := by
  constructor
  · constructor
    · constructor
      · have i : IsCyclic (B ⧸ Q)ˣ := by exact residuefieldUnitsIsCyclic B Q
        apply IsCyclic.exists_monoid_generator at i
        rcases i with ⟨g, hg⟩
        intro x
        sorry
      · sorry
    · sorry
  · sorry

-- for CRT, maybe use : theorem IsDedekindDomain.exists_representative_mod_finset

-- need to prove x ∈ Subgroup.zpowers h.unit
-- b/c we know B ⧸ Q is a field
-- prove ρ non-zero

-- Amelia: these two statements should be unified;
-- state ρ : B,
-- then, use ρ as an element of the quotient (map to quotient)
-- is not 0; or is a generator of (B ⧸ Q)ˣ


-- for 'α : B', we want to define a polynomial 'F(X) : ℤ[X]' which is
-- the product over elements 'τ : L ≃ₐ[K] L' of the
-- linear factors '(X - τα)'
-- and such that '(Ideal.Quotient.mk Q) F(α) = 0',
-- where '(Ideal.Quotient.mk Q) := (B ⧸ Q)'



noncomputable def F (α : B) : Polynomial B := ∏ τ : L ≃ₐ[K] L,
  (Polynomial.X - Polynomial.C ((AlgEquiv.symm (galRestrict A K L B τ)) α))


lemma F_root (α : B) : (F A K L B α).eval α = 0 := by
  rw [F, Polynomial.eval_prod, Finset.prod_eq_zero_iff]
  use 1
  constructor
  · exact Finset.mem_univ _
  · rw [map_one, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
    exact sub_self α
/-
for 'so (F(α ^ q) - F(α) ^ q) ∈ Q':
theorem FiniteField.expand_card {K : Type u_1} [Field K] [Fintype K]
(f : Polynomial K) : (Polynomial.expand K (Fintype.card K)) f = f ^ Fintype.card K

would need 'K' here to be (B ⧸ Q); then would need the reduction
(FModQ : Polynomial (B ⧸ Q)

-/

noncomputable def FModQ (α : B) : Polynomial (B ⧸ Q) :=
  (F A K L B α).map (Ideal.Quotient.mk Q)

lemma FModQ_def (α : B) : FModQ A K L B Q α = Polynomial.map (Ideal.Quotient.mk Q) (F A K L B α) := by rfl

-- quotientEquivQuotientMvPolynomial

lemma FModQ_root (α : B) : (FModQ A K L B Q α).eval ((Ideal.Quotient.mk Q) α) = 0 := by
  rw [FModQ_def, Polynomial.eval_map]
  sorry
-- ? Polynomial.EisensteinCriterionAux.eval_zero_mem_ideal_of_eq_mul_X_pow

lemma Ideal.finset_prod_mem {α R : Type*} [CommRing R] {P : Ideal R} [P.IsPrime] {ι : Finset α} {f : α → R} (h : ∏ x in ι, f x ∈ P): ∃ x : ι, f x ∈ P := by
  classical
  induction' ι using Finset.induction_on with a _ ha hi
  · exfalso
    rw [Finset.prod_empty, ← Ideal.eq_top_iff_one] at h
    exact IsPrime.ne_top' h
  · rw [Finset.prod_insert ha] at h
    apply IsPrime.mem_or_mem' at h
    cases' h with hl hr
    · exact ⟨⟨a, Finset.mem_insert_self _ _⟩, hl⟩
    · apply hi at hr
      rcases hr with ⟨⟨x, hx⟩, hfx⟩
      exact ⟨⟨x, Finset.mem_insert_of_mem hx⟩, hfx⟩

attribute [instance] Ideal.Quotient.field

lemma qth_power_is_conjugate (α : B) : ∃ σ : L ≃ₐ[K] L, α ^ q - ((AlgEquiv.symm (galRestrict A K L B σ)) α) ∈ Q := by
  have h : (F A K L B α).eval (α ^ q) ∈ Q := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, ← Polynomial.eval₂_hom, ← Polynomial.eval_map, ← FModQ_def, RingHom.map_pow, ← Polynomial.expand_eval, FiniteField.expand_card, Polynomial.eval_pow]
    simp only [ne_eq, Fintype.card_ne_zero, not_false_eq_true, pow_eq_zero_iff]
    exact FModQ_root A K L B Q α
  simp_rw [F, Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C] at h
  apply Ideal.finset_prod_mem at h
  simp_all only [Subtype.exists, Finset.mem_univ, exists_const]

example (a b x : ℕ) : (x ^ a) ^ b = (x ^ b) ^ a := by exact Nat.pow_right_comm x a b

theorem ex_FrobElt : ∃ σ : decompositionSubgroupIdeal' A K L B Q, ∀ α : B, α ^ q - (AlgEquiv.symm (galRestrict A K L B σ)) α ∈ Q  := by
  have h := generator A K L B Q
  rcases h with ⟨α ,  ⟨hu , hα⟩⟩
  have hq := qth_power_is_conjugate A K L B Q α
  rcases hq with ⟨σ , hσ⟩
  have hd : σ ∈ decompositionSubgroupIdeal' A K L B Q := by
    rw[decompositionSubgroupIdeal', ← Subgroup.inv_mem_iff]
    by_contra hc
    apply hα.2 at hc
    sorry
  refine ⟨⟨σ , hd⟩, ?_⟩
  intro γ
  have : ∃ i : ℕ,  γ - α ^ i ∈ Q := sorry
  rcases this with ⟨i, hγ⟩
  have h' : (AlgEquiv.symm (galRestrict A K L B σ)) (γ - α ^ i) ∈ Q := sorry
  rw[← Ideal.Quotient.eq_zero_iff_mem, map_sub] at h' hγ hσ ⊢
  rw [map_sub] at h'
  rw [sub_eq_zero] at h' hγ hσ ⊢
  simp only [map_pow]
  rw[h', hγ, AlgEquiv.map_pow, RingHom.map_pow, RingHom.map_pow, pow_right_comm, ← RingHom.map_pow , hσ]


end FiniteFrobeniusDef
