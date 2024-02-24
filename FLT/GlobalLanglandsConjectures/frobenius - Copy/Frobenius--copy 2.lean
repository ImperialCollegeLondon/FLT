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
import Mathlib.Tactic.PushNeg



/-!

## References

See [Karatarakis2022, Mathlib/RingTheory/Valuation/RamificationGroup.lean]
  for definitions of 'decomposition subgroup', 'inertia sugroup'

-/

section References

end References

section FiniteFrobeniusDef

-- translating p. 140 of Milne ANT + Prof. Buzzard's diagram (Feb. 8)



-- Jujian Zhang helped with notation and writing 'theorem ex_FrobElt'
-- JZ: example of how to access a hypothesis in 'variables' or Mathlib:
-- "let i : FiniteDimensional L K := inferInstance"


open NumberField BigOperators
open scoped Pointwise


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

noncomputable def galBmap (σ : L ≃ₐ[K] L) : B ≃ₐ[A] B := AlgEquiv.symm (galRestrict A K L B σ)
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


def decompositionSubgroupIdeal' (P : Ideal' A K L B) :
  Subgroup (L ≃ₐ[K] L) := MulAction.stabilizer (L ≃ₐ[K] L) P

#check decompositionSubgroupIdeal'


noncomputable def residueField (A : Type*) [CommRing A] (P : Ideal A) [P.IsMaximal] : Field (A ⧸ P) :=
 Ideal.Quotient.field P

variable (P : Ideal A) [P.IsMaximal] [Fintype (A ⧸ P)]
  (Q : Ideal B) [Q.IsMaximal] [Fintype (B ⧸ Q)]
  [Algebra (A ⧸ P) (B ⧸ Q)]




-- "By the Chinese remainder theorem, there exists an element
-- 'α' of 'B' such that 'α' generates the group '(B ⧸ Q)ˣ'
-- and lies in 'τQ' for all 'τ ¬∈ decompositionSubgroupIdeal'' "

local notation "q" => Fintype.card (A ⧸ P)


instance residuefieldUnitsIsCyclic (Q : Ideal B) [hB : Ideal.IsMaximal Q]
  [Fintype (B ⧸ Q)] : IsCyclic (B ⧸ Q)ˣ :=
  isCyclic_of_subgroup_isDomain (Units.coeHom _) <| by
    unfold Function.Injective
    simp_all
    intros a b
    apply Units.ext_iff.2

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
  have i : IsCyclic (B ⧸ Q)ˣ := by exact residuefieldUnitsIsCyclic B Q
  apply IsCyclic.exists_monoid_generator at i
  rcases i with ⟨α, hα⟩
  refine ⟨?_, ?_, ?_⟩
  · let α' := (Units.coeHom (B ⧸ Q)) α
    have hαeq : α = α' := by exact rfl
    have hrep : ∃ y : B, (Ideal.Quotient.mk Q) y = α' := by sorry
    sorry
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


end FiniteFrobeniusDef
