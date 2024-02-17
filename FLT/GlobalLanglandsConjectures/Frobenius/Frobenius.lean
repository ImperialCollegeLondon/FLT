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
-- IsDedekindDomain.HeightOneSpectrum.valuation_def

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

open NumberField
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

variable (K : Type*) [Field K] (L : Type*) [Field L]
  [Algebra K L] [hG: IsGalois K L]
  [nfK : NumberField K] [nfL : NumberField L]
  [FiniteDimensional K L]
  (A : Type*) (B : Type*) [CommRing A] [CommRing B]
  [IsDomain A] [IsDomain B]
  [Algebra A K] [Algebra B L]
  [IsFractionRing A K]  [IsFractionRing B L]
  [IsIntegralClosure A ℤ K] [IsIntegralClosure B ℤ L]
  (A := 𝓞 K) (B := 𝓞 L)

#check ringOfIntegers

lemma ringOfIntegersAlgebra [Algebra K L] : Algebra (A) (B) := by
  have h : Algebra (𝓞 K) (𝓞 L) := by exact inst_ringOfIntegersAlgebra K L
  sorry

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

lemma galEquiv.togalHom (σ : L ≃ₐ[K] L) : L →ₐ[K] L := by
  apply AlgEquiv.toAlgHom
  exact σ

example (σ : (L →ₐ[K] L)) [h : (L →ₐ[K] L) ≃* (B →ₐ[A] B)] : (B →ₐ[A] B) := by
  apply?

lemma Ideal_algebraMap_galRestrictHom_apply (A K L B : Type*) [CommRing A]
  [CommRing B] [Algebra A B] [Field K] [Field L]
  [Algebra A K] [IsFractionRing A K] [Algebra B L]
  [Algebra K L] [Algebra A L] [IsScalarTower A B L]
  [IsScalarTower A K L] [IsIntegralClosure B A L]
  [FiniteDimensional K L] (σ : L ≃ₐ[K] L) :
  ((galRestrict A K L B σ : B →ₐ[A] B) : (B →ₐ[A] B)) := by apply?




#check coe_galRestrict_apply
#check galRestrict
#check galRestrictHom
#check algebraMap_galRestrict_apply

#check AlgHom.toRingHom
#check Algebra.toRingHom
#check RingHom.toAlgebra
#check Algebra.id (𝓞 K)


-- We define the sub-'B'-algebra of 'L' corresponding to the
--valuation subring of 'L' associated to 'Q'
-- See "Mathlib.RingTheory.DedekindDomain.Ideal"
/- The following doesn't work, because I changed the type of brackets
and the order of variables -- they have to be identical to what Kevin sent.
I also need to open the namespace in the code he sent.
noncomputable abbrev ValuationSubring.asSubalgebra : Subalgebra B L :=
  Localization.subalgebra.ofField L (Ideal.primeCompl Q.asIdeal) (by
    intro x hx
    apply mem_nonZeroDivisors_of_ne_zero
    rintro rfl
    apply hx
    simp only [SetLike.mem_coe, Submodule.zero_mem]
  )


noncomputable def valuationSubring : ValuationSubring L :=
  haveI := IsLocalization.AtPrime.discreteValuationRing_of_dedekind_domain
    B Q.ne_bot (ValuationSubring.asSubalgebra L B)
  Valuation.valuationSubring (ValuationRing.valuation (ValuationSubring.asSubalgebra L Q) L)

-/




-- the decomposition group of 'A' over 'K':
def decompositionSubgroup  (A : ValuationSubring L) :
  Subgroup (L ≃ₐ[K] L) := MulAction.stabilizer (L ≃ₐ[K] L) A
-- I was instructed to define the action of the Galois group
-- in terms of an isomorphism from L to itself
-- #check Frob[K, L]




-- modify 'def decompositionSubgroup', so that it does not use 'ValuationSubring L':
-- use 'MulAction.stabilizer', "The stabilizer of an element under an action,
--  i.e. what sends the element to itself".



variable {L} in
-- need '(L ≃ₐ[K] L)' "acts transitively on the set of all prime ideals 'Q' of '𝓞' lying above 'P'"




-- the following proof from p. 141 Milne ANT
theorem ex_FrobElt
  (Q : Ideal (𝓞 L)) (hQ: Ideal.IsPrime Q) : true := by
  sorry

#check Ideal.map



-- we define the action of the Galois group on the prime ideals of
-- the ring of integers 'R' of 'L'
-- def RestrictRingOfIntegers
-- topEquiv
-- equivMapofInjective -- "A subring is isomorphic to its image under an injective function"
-- rangeRestrict
-- RingHom.range, def ofLeftInverse
-- algebraMap : "Embedding R →+* A given by Algebra structure."
-- #lint

/-
instance GalAction : MulAction (L ≃ₐ[K] L) (Ideal B) where
  smul {g : L ≃ₐ[K] L} {P : Ideal B} := by
    refine Ideal.map (RingHom.restrict g.toAlgHom.toRingHom B B ?_) P
  one_smul := sorry
  mul_smul := sorry
-- ∃ function which turns algebra equiv (to alg hom) to ring hom,
-- and then one to restrict
-- ∃ g : L → L, g (P) = P' :=
-/

end FiniteFrobeniusDef
