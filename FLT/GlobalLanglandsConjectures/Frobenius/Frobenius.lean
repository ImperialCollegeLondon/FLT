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



/-!

## References

See [Karatarakis2022, Mathlib/RingTheory/Valuation/RamificationGroup.lean]
  for definitions of 'decomposition subgroup', 'inertia sugroup'

-/

section References

#check FiniteField.pow_card
#check FiniteField.frobenius_pow
-- def GaloisField(p : ℕ) [Fact (Nat.Prime p)] (n : ℕ) : Type
-- "A finite field with p ^ n elements"
-- [Commelin et. al., "Mathlib.FieldTheory.Finite.GaloisField"]
#check isGalois_iff -- 'is Galois' iff 'normal'∧'separable'
#check IsAlgClosure.isGalois


end References

section FiniteFrobeniusDef

-- translating p. 140 of Milne ANT + Prof. Buzzard's diagram (Feb. 8)
-- set-up from "Mathlib.FieldTheory.Galois"

/- def FrobeniusElt  (K : Type*) [Field K] (L : Type*) [Field L]
  [Algebra K L] [hG: IsGalois K L]
  (B : ValuationSubring L) (A : ValuationSubring K): true := sorry
local notation "Frob["K "," L "]" => FrobeniusElt K L
-/



-- Jujian Zhang helped with notation and writing 'theorem ex_FrobElt'
-- cut: ' '
-- need integer rings 'A' of 'K', 'B' of 'L', resp.
-- need non-zero prime ideal 'Q' of 'B' over non-zero prime 'P' of 'A'
-- '[hQe: Ideal.ramificationIdx f P Q] = 1
-- i.e., 'Q' is unramified in 'L/K'; see "Mathlib.NumberTheory.RamificationInertia"
-- JZ: example of how to access a hypothesis in 'variables' or Mathlib:
-- "let i : FiniteDimensional L K := inferInstance"
-- from Sheet5 in 'galoisTheory' section of class notes:
-- " The Galois group Gal(F/E) doesn't have special notation, it's just the F-algebra isomorphisms
-- from E to itself
-- example : Type := F ≃ₐ[E] F"

open NumberField BigOperators
open scoped Pointwise

/-!
If 'L' is a number field, and 'B' is the ring of integers of 'L',
then 'B' is a Dedekind domain, and 'L' is the field of
fractions of 'L' (Milne, ANT, p. 28).

From "Mathlib.RingTheory.DedekindDomain.Ideal,"
if 'B' is a Dedekind domain, then,
'HeightOneSpectrum B' is the type of nonzero prime ideals
of 'B'. So, "let 'Q' be a nonzero prime ideal of 'B'"
translates as '(Q : HeightOneSpectrum B)'.

If 'B' is a Dedekind domain, 'L' its field of fractions,
and '(Q : HeightOneSpectrum B)', then
'Q.valuationSubring L' is the valuation subring
of 'L' associated with 'Q' (See "ValuationSubring.asSubalgebra").

For 'L | K' an extension of fields, with automorphism group
'(L ≃ₐ[K] L)' and 'Q.valuationSubring L' as above,
the decomposition group of 'Q.valuationSubring L'
over 'K' is defined as the stabilizer of the multiplicative action
of '(L ≃ₐ[K] L)' on 'Q.valuationSubring L' :
'MulAction.stabilizer (L ≃ₐ[K] L) 'Q.valuationSubring L'.
(See "Mathlib.RingTheory.Valuation.RamificationGroup".)




-/

-- variable (A K L B : Type*) [Field K] (L : Type*) [Field L]
--   [Algebra K L] [hG: IsGalois K L]
--   [nfK : NumberField K] [nfL : NumberField L]
--   [FiniteDimensional K L]
--   [CommRing A] [CommRing B]
--   [IsDomain A] [IsDomain B]
--   [Algebra A K] [Algebra B L] [Algebra A L]
--   [IsFractionRing A K]  [IsFractionRing B L]
--   [IsIntegralClosure A ℤ K] [IsIntegralClosure B ℤ L]
--   (A := 𝓞 K) (B := 𝓞 L)

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

#check decompositionSubgroupIdeal'

-- we will eventually show that the order 'q' of 'Frob [K , L]' is
-- the number of elements in the residue field 'A  ⧸ P',
-- where 'P ⊂ A' is a prime ideal lying under the prime ideal 'Q ⊂ B'

/-
noncomputable def residueFieldA (A : Type*) [CommRing A] (P : Ideal A) [P.IsMaximal] :
 Field (A ⧸ P) :=
 Ideal.Quotient.field P

noncomputable def residueFieldB (B : Type*) [CommRing B] (Q : Ideal B) [Q.IsMaximal] :
 Field (B ⧸ Q) :=
 Ideal.Quotient.field Q
-/

variable {P : Ideal A} [P.IsMaximal] [Fintype (A ⧸ P)]
  (Q : Ideal B) [Q.IsMaximal] [Fintype (B ⧸ Q)]
  [Algebra (A ⧸ P) (B ⧸ Q)]

-- "By the Chinese remainder theorem, there exists an element
-- 'α' of 'B' such that 'α' generates the group '(B ⧸ Q)ˣ'
-- and lies in 'τQ' for all 'τ ¬∈ decompositionSubgroupIdeal'' "



local notation "k" => A ⧸ P
local notation "l" => B ⧸ Q
local notation "q" => Fintype.card (B ⧸ Q)

#check q

#check decompositionSubgroupIdeal' A K L B Q

#check isCyclic_of_subgroup_isDomain
#check Ideal.Quotient.field
#check Subgroup.inclusion
#check isCyclic_of_subgroup_isDomain
#check Function.Injective

#check MonoidHom.toHomUnits
#check  Units.ext_iff

instance residuefieldUnitsIsCyclic (Q : Ideal B) [hB : Ideal.IsMaximal Q]
  [Fintype (B ⧸ Q)] : IsCyclic (B ⧸ Q)ˣ :=
  isCyclic_of_subgroup_isDomain (Units.coeHom _) <| by
    unfold Function.Injective
    simp_all
    intros a b
    apply Units.ext_iff.2

#check Ideal.Quotient.mk

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
/-
class IsCyclic (α : Type u) [Group α] : Prop where
  exists_generator : ∃ g : α, ∀ x, x ∈ zpowers g
-/


-- set_option autoImplicit false
-- the map `D(Q) → Gal(l/k)` via `σ ↦ (x + Q ↦ σ(x) + Q)`
--def residueGalMap : (σ : decompositionSubgroupisPrime A K B L Q) → l ≃ₐ[k] l := by
--intro σ
--sorry

--theorem residueGalMap_surj : Function.Surjective (residueGalMap A K B L P Q):= by
--sorry



-- for 'α : B', we want to define a polynomial 'F(X) : ℤ[X]' which is
-- the product over elements 'τ : L ≃ₐ[K] L' of the
-- linear factors '(X - τα)'
-- and such that '(Ideal.Quotient.mk Q) F(α) = 0',
-- where '(Ideal.Quotient.mk Q) := (B ⧸ Q)'

/-
open Polynomial BigOperators
variable (α R : Type*) [Semiring R] [Fintype α] (a : R) (f : α → R)
#check X - C a
#check ∏ i, (X - C (f i))
-/

noncomputable def F (α : B) : Polynomial B := ∏ τ : L ≃ₐ[K] L,
  (Polynomial.X - Polynomial.C ((AlgEquiv.symm (galRestrict A K L B τ)) α))



--  "⟦" a "⟧" => Quot.mk _ a
-- theorem Ideal.Quotient.eq_zero_iff_mem{R : Type u}
--  [CommRing R] {a : R} {I : Ideal R} :
-- (Ideal.Quotient.mk I) a = 0 ↔ a ∈ I

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

theorem ex_FrobElt : ∃ σ : decompositionSubgroupIdeal' A K L B Q, ∀ α : B, α ^ q - (galBmap A K L B σ) α ∈ Q  := by
  have h := generator A K L B Q
  rcases h with ⟨α , hα⟩
  have hq := qth_power_is_conjugate A K L B Q α
  rcases hq with ⟨σ , hσ⟩
  have hd : σ ∈ decompositionSubgroupIdeal' A K L B Q := by
    rw[decompositionSubgroupIdeal', MulAction.mem_stabilizer_iff, ← inv_smul_eq_iff.symm]

    by_contra hc


-- #check MulEquiv.toMulHom
-- #check Polynomial.Gal.galActionAux
-- #check Ideal.map_isPrime_of_equiv
-- #check Polynomial.rootSet_maps_to'
-- #check IsScalarTower.toAlgHom
-- #check Set.MapsTo.restrict
-- #check coe_galRestrict_apply
-- #check galRestrict
-- #check galRestrictHom
-- #check algebraMap_galRestrict_apply

-- #check AlgHom.toRingHom
-- #check Algebra.toRingHom
-- #check RingHom.toAlgebra
-- #check Algebra.id (𝓞 K)

-- I was instructed to define the action of the Galois group
-- in terms of an isomorphism from L to itself
-- #check Frob[K, L]



-- #lint


end FiniteFrobeniusDef
