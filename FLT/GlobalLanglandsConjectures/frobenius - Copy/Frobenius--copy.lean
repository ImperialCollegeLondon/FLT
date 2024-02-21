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

#check ringOfIntegers

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

variable (A K B L : Type*)
  [CommRing A] [CommRing B] [Algebra A B]
  [Field K] [Field L] [Algebra K L]
  [IsDomain A] [IsDomain B]
  [Algebra A K] [Algebra B L] [Algebra A L]
  [IsScalarTower A B L] [IsScalarTower A K L]
  [IsFractionRing A K] [IsFractionRing B L]
  [IsIntegralClosure B A L] [IsIntegralClosure A ℤ K] [IsIntegralClosure B ℤ L]
  [FiniteDimensional K L]

-- def galEquiv.toGalHom (σ : L ≃ₐ[K] L) : L →ₐ[K] L := AlgEquiv.toAlgHom σ

-- lemma ringOfIntegersAlgebra : Algebra A B := by
--   have h : Algebra (𝓞 K) (𝓞 L) := by exact inst_ringOfIntegersAlgebra K L
--   sorry

lemma galToMulHom (e: (L →ₐ[K] L) ≃* (B →ₐ[A] B)) : ((L →ₐ[K] L) →ₙ* (B →ₐ[A] B)) := by
  apply MulEquiv.toMulHom
  exact e



-- now, need '(B →ₐ[A] B)' from the RHS of 'galToMulHom'
-- need: theorem MulHom.restrict_apply{M : Type u_1} {σ : Type u_4}
-- [Mul M] {N : Type u_5} [Mul N] [SetLike σ M] [MulMemClass σ M] (f : M →ₙ* N) {S : σ}
-- (x : ↥S) : (MulHom.restrict f S) x = f ↑x
-- Check : IntegralRestrict, PolynomialGaloisGroup

variable {K L}
-- instance galtoRingHom (g : L ≃ₐ[K] L) (x : B) :  B →ₐ[A] B :=
-- (galRestrict A K L B g : B →ₐ[A] B)


-- B →+* B
#check B →+* B
instance galtoRingHom' : (B →ₐ[A] B) where
  toFun := sorry
  map_one' := sorry
  map_mul' := sorry
  map_zero' := sorry
  map_add' := sorry
  commutes' := sorry


-- we define the action of Gal(L/K) on the prime ideals of B ⊂ L
-- the prime 'Ideal B' has been re-written as
-- "'Ideal B' , remembering that 'A' exists'
-- in order to synthesize the instance of 'MulAction' on 'Ideal B' with
-- the 'A K L B' setup
instance galActionIdeal': MulAction (L ≃ₐ[K] L) (Ideal' A K L B) where
  smul := sorry
  one_smul :=sorry
  mul_smul := sorry

-- we define the decomposition group of '(Ideal' A K L B)' over 'K'
-- to be the stabilizer of the MulAction 'galActionisPrime'


-- Bendit: I think these are not needed
--[Group (L ≃ₐ[K] L)] {_ : Type*}
--[galActionisPrime : MulAction (L ≃ₐ[K] L) ((Ideal' A K L B))]

def decompositionSubgroupisPrime (P : Ideal' A K L B) :
  Subgroup (L ≃ₐ[K] L) := MulAction.stabilizer (L ≃ₐ[K] L) P

#check decompositionSubgroupisPrime

-- def MulAction.stabilizer(G : Type u_1) {α : Type u_2} [Group G]
-- [MulAction G α] (a : α) : Subgroup G

-- we will eventually show that the order 'q' of 'Frob [K , L]' is
-- the number of elements in the residue field 'A  ⧸ P',
-- where 'P ⊂ A' is a prime ideal lying under the prime ideal 'Q ⊂ B'

noncomputable def residueField (A : Type*) [CommRing A] (P : Ideal A) [P.IsMaximal] : Field (A ⧸ P) :=
 Ideal.Quotient.field P

variable (P : Ideal A) [P.IsMaximal] [Fintype (A ⧸ P)]
  (Q : Ideal B) [Q.IsMaximal] [Fintype (B ⧸ Q)]
  [Algebra (A ⧸ P) (B ⧸ Q)]

local notation "k" => A ⧸ P
local notation "l" => B ⧸ Q
-- def q := Fintype.card (A ⧸ P)

-- the map `D(Q) → Gal(l/k)` via `σ ↦ (x + Q ↦ σ(x) + Q)`
-- def residueGalMap : (σ : decompositionSubgroupisPrime A K B L Q) → l ≃ₐ[k] l := by
-- intro σ
-- sorry

-- theorem residueGalMap_surj : Function.Surjective (residueGalMap A K B L P Q):= by
-- sorry



-- for 'α : B', we want to define a polynomial 'F(X) : ℤ[X]' which is
-- the product over elements 'τ : L ≃ₐ[K] L' of the
-- linear factors '(X - τα)'
-- and such that '(Ideal.Quotient.mk Q) F(α) = 0',
-- where '(Ideal.Quotient.mk Q) := (B ⧸ Q)'
-- IsRoot p x implies x is a root of p. The evaluation of p at x is zero
-- see: "Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq":
-- "A monic polynomial `p` that has as many roots as its degree
-- can be written `p = ∏(X - a)`, for `a` in `p.roots`"
--

-- noncomputable def F (α : B) (τ : L ≃ₐ[K] L) :
--  Polynomial B := (F.roots.map fun α => X - C τα).prod
-- we need to specify 'α' to be a generator of (B ⧸ Q)^×, though

-- maybe define an instance of a polynomial F where
-- ∀ τ : L≃ₐ[K] L, τ(α) is a root of F
--AND, ∀ roots r of F, r = τ(α), for some τ : L≃ₐ[K] L

-- instance rootF (F: Polynomial L) : roots F := _

-- below, modelled on "Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq":
noncomputable def F.roots (F : Polynomial L) (hF : Polynomial.Monic F)
(hroots : Multiset.card (Polynomial.roots F) = Polynomial.natDegree F) : Multiset L :=
 sorry

def F (R : Type*) [Field R] : Polynomial R where
  toFinsupp := {
    support := {
      val := sorry
      nodup := sorry
    }
    toFun := fun
      | .zero => sorry
      | .succ n => sorry
    mem_support_toFun := fun
      | .zero => {
        mp := sorry
        mpr := sorry
      }
      | .succ n => {
        mp := sorry
        mpr := sorry
      }
  }

--  "⟦" a "⟧" => Quot.mk _ a
-- theorem Ideal.Quotient.eq_zero_iff_mem{R : Type u}
--  [CommRing R] {a : R} {I : Ideal R} :
-- (Ideal.Quotient.mk I) a = 0 ↔ a ∈ I

#check MulEquiv.toMulHom
#check Polynomial.Gal.galActionAux
#check Ideal.map_isPrime_of_equiv
#check Polynomial.rootSet_maps_to'
#check IsScalarTower.toAlgHom
#check Set.MapsTo.restrict
#check coe_galRestrict_apply
#check galRestrict
#check galRestrictHom
#check algebraMap_galRestrict_apply

#check AlgHom.toRingHom
#check Algebra.toRingHom
#check RingHom.toAlgebra
#check Algebra.id (𝓞 K)





-- I was instructed to define the action of the Galois group
-- in terms of an isomorphism from L to itself
-- #check Frob[K, L]






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


end FiniteFrobeniusDef
