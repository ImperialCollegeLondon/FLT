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

@[simp]
lemma galBmap_def (σ : L ≃ₐ[K] L) : galBmap A K L B σ = AlgEquiv.symm (galRestrict A K L B σ) := rfl

lemma galBmap_inv (σ : L ≃ₐ[K] L) : galBmap A K L B σ⁻¹ = (galBmap A K L B σ)⁻¹ := by rfl

-- we define the action of the Galois group on the prime ideals of
-- the ring of integers 'R' of 'L'
-- Amelia helped to define smul, below
noncomputable instance galActionIdeal': MulAction (L ≃ₐ[K] L) (Ideal' A K L B) where
  smul σ I := Ideal.comap (galBmap A K L B σ) I
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

lemma galActionIdeal'.mem_iff {α : B} {I : Ideal' A K L B} {σ : L ≃ₐ[K] L} : α ∈ σ • I ↔ ∃ x : I, α = (galBmap A K L B σ) x := by
  sorry

lemma galActionIdeal'.apply_fun {α : B} {I : Ideal' A K L B} (σ : L ≃ₐ[K] L) : α ∈ I → (galBmap A K L B σ) α ∈ σ • I := by
  intro hα
  rw [mem_iff]
  refine ⟨⟨α, hα⟩, rfl⟩

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



noncomputable def F (α : B) : Polynomial B := ∏ τ : L ≃ₐ[K] L,
  (Polynomial.X - Polynomial.C ((galBmap A K L B τ) α))


lemma F_root (α : B) : (F A K L B α).eval α = 0 := by
  rw [F, Polynomial.eval_prod, Finset.prod_eq_zero_iff]
  use 1
  constructor
  · exact Finset.mem_univ _
  · rw [galBmap_def, map_one, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
    exact sub_self α

noncomputable def FModQ (α : B) : Polynomial (B ⧸ Q) :=
  (F A K L B α).map (Ideal.Quotient.mk Q)

@[simp]
lemma FModQ_def (α : B) : FModQ A K L B Q α = Polynomial.map (Ideal.Quotient.mk Q) (F A K L B α) := rfl

lemma FModQ_root (α : B) : (FModQ A K L B Q α).eval ((Ideal.Quotient.mk Q) α) = 0 := by
  rw [FModQ_def, Polynomial.eval_map, Polynomial.eval₂_hom, F_root]
  exact rfl

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

lemma qth_power_is_conjugate (α : B) : ∃ σ : L ≃ₐ[K] L, α ^ q - (galBmap A K L B σ) α ∈ Q := by
  have h : (F A K L B α).eval (α ^ q) ∈ Q := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, ← Polynomial.eval₂_hom, ← Polynomial.eval_map, ← FModQ_def, RingHom.map_pow, ← Polynomial.expand_eval, FiniteField.expand_card, Polynomial.eval_pow]
    simp only [ne_eq, Fintype.card_ne_zero, not_false_eq_true, pow_eq_zero_iff]
    exact FModQ_root A K L B Q α
  simp_rw [F, Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C] at h
  apply Ideal.finset_prod_mem at h
  simp_all only [Subtype.exists, Finset.mem_univ, exists_const]

theorem ex_FrobElt : ∃ σ : decompositionSubgroupIdeal' A K L B Q, ∀ α : B, α ^ q - (galBmap A K L B σ) α ∈ Q  := by
  rcases (generator A K L B Q) with ⟨α, ⟨hu, hα⟩⟩
  rcases (qth_power_is_conjugate A K L B Q α) with ⟨σ, hσ⟩
  have hd : σ ∈ decompositionSubgroupIdeal' A K L B Q := by
    rw [decompositionSubgroupIdeal', ← Subgroup.inv_mem_iff]
    by_contra hc
    apply hα.2 at hc
    rcases ((galActionIdeal'.mem_iff A K L B).mp hc) with ⟨x, hx⟩
    apply_fun (galBmap A K L B σ) at hx
    rw [galBmap_inv] at hx
    change (galBmap A K L B σ) α = (galBmap A K L B σ).toFun ((galBmap A K L B σ).invFun x) at hx
    rw [(galBmap A K L B σ).right_inv] at hx
    rw [hx] at hσ
    apply Ideal.add_mem _ (Submodule.coe_mem x) at hσ
    rw [add_sub_cancel'_right, ← Ideal.Quotient.eq_zero_iff_mem, map_pow] at hσ
    apply (IsUnit.pow q) at hu
    rw [hσ] at hu
    exact not_isUnit_zero hu
  refine ⟨⟨σ , hd⟩, ?_⟩
  intro γ
  cases' eq_zero_or_neZero (Ideal.Quotient.mk Q γ) with h0 hn0
  · rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_pow, h0]
    apply Ideal.Quotient.eq_zero_iff_mem.mp at h0
    apply (galActionIdeal'.apply_fun A K L B σ) at h0
    rw [hd, ← Ideal.Quotient.eq_zero_iff_mem] at h0
    rw [h0, zero_pow Fintype.card_ne_zero, sub_zero]
  · have hpow : ∃ i : ℕ,  γ - α ^ i ∈ Q := by
      sorry
      -- specialize hα.1 (Ideal.Quotient.mk Q γ)
      -- doesn't work yet; need a "specialize with holes"
    rcases hpow with ⟨i, hγ⟩
    have h' : (galBmap A K L B σ) (γ - α ^ i) ∈ Q := by
      convert (galActionIdeal'.apply_fun A K L B σ) hγ using 1
      rw [hd]
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub] at h' hγ hσ ⊢
    rw [map_sub] at h'
    rw [sub_eq_zero] at h' hγ hσ ⊢
    rw [map_pow, h', hγ, map_pow, map_pow, map_pow, pow_right_comm, ← map_pow, hσ]


-- local notation "Frob["K "," L "]" => FrobeniusElt K L


example {R : Type*} [CommRing R] [IsDomain R] (I : Ideal R) [Ideal.IsMaximal I]
  (a b : R) : (a - b ∈ I) → (Ideal.Quotient.mk I (a - b)) = 0 := by
   intro h
   apply Ideal.Quotient.eq_zero_iff_mem.2 at h
   exact h

example {S : Type*} (a : S)   {s : Finset S} [hn : Nonempty s] :
  (a ∉ s) → ((a ∈ s) → False) := by exact fun a_1 a => a_1 a

theorem ex_FrobEltworking : ∃ σ : decompositionSubgroupIdeal' A K L B Q, ∀ α : B, α ^ q - (galBmap A K L B σ) α ∈ Q  := by
  rcases (generator A K L B Q) with ⟨α, ⟨hu, hα⟩⟩
  rcases (qth_power_is_conjugate A K L B Q α) with ⟨σ, hσ⟩
  have hd : σ ∈ decompositionSubgroupIdeal' A K L B Q := by
    rw [decompositionSubgroupIdeal', ← Subgroup.inv_mem_iff]
    by_contra hc
    apply hα.2 at hc
    rcases ((galActionIdeal'.mem_iff A K L B).mp hc) with ⟨x, hx⟩
    apply_fun (galBmap A K L B σ) at hx
    rw [galBmap_inv] at hx
    change (galBmap A K L B σ) α = (galBmap A K L B σ).toFun ((galBmap A K L B σ).invFun x) at hx
    rw [(galBmap A K L B σ).right_inv] at hx
    rw [hx] at hσ
    apply Ideal.add_mem _ (Submodule.coe_mem x) at hσ
    rw [add_sub_cancel'_right, ← Ideal.Quotient.eq_zero_iff_mem, map_pow] at hσ
    apply (IsUnit.pow q) at hu
    rw [hσ] at hu
    exact not_isUnit_zero hu
  refine ⟨⟨σ , hd⟩, ?_⟩
  intro γ
  cases' eq_zero_or_neZero (Ideal.Quotient.mk Q γ) with h0 hn0
  · rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_pow, h0]
    apply Ideal.Quotient.eq_zero_iff_mem.mp at h0
    apply (galActionIdeal'.apply_fun A K L B σ) at h0
    rw [hd, ← Ideal.Quotient.eq_zero_iff_mem] at h0
    rw [h0, zero_pow Fintype.card_ne_zero, sub_zero]
  · have hpow : ∃ i : ℕ,  γ - α ^ i ∈ Q := by
      have huγ : IsUnit (Ideal.Quotient.mk Q γ) := by
        by_contra hcγ
        change IsUnit (Ideal.Quotient.mk Q γ) → False at hcγ
        apply neZero_iff.1 at hn0
        simp_all
        sorry
      have hγpow : huγ.unit ∈ Subgroup.zpowers (hu.unit) := by sorry
      constructor
      · rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub]
        · sorry
        · sorry
    sorry

/- by_contra hc
      rw[Membership.mem] at hc
      change (∃ i, ( γ - α ^ i ∈  Q)) → False at hc
      -/
-- theorem ENNReal.pow_ne_zero {a : ENNReal} : a ≠ 0 → ∀ (n : ℕ), a ^ n ≠ 0
-- application type mismatch hα.left ((Ideal.Quotient.mk Q) γ)
-- argument (Ideal.Quotient.mk Q) γ has type B ⧸ Q : Type u_4
-- but is expected to have type (B ⧸ Q)ˣ : Type u_4
 -- specialize hα.1 (Ideal.Quotient.mk Q γ)
      -- doesn't work yet; need a "specialize with holes"
#check Subgroup.zpowers

/-
#check neZero_iff
#check NeZero
-/
end FiniteFrobeniusDef
