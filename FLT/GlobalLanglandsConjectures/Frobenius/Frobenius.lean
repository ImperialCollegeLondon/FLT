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
import Mathlib.RingTheory.Ideal.Operations


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

lemma galRestrict_inv : galRestrict A K L B σ⁻¹ = (galRestrict A K L B σ)⁻¹ := rfl

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

lemma galActionIdeal'.smul_def {I : Ideal' A K L B} {σ : L ≃ₐ[K] L} : σ • I = Ideal.comap (AlgEquiv.symm (galRestrict A K L B σ)) I := rfl

lemma galActionIdeal'.mem_iff {α : B} {I : Ideal' A K L B} {σ : L ≃ₐ[K] L} : α ∈ σ • I ↔ ∃ x : I, α = (galRestrict A K L B σ) x := by
  rw [galActionIdeal'.smul_def, Ideal.mem_comap]
  constructor <;> intro h
  · refine ⟨⟨AlgEquiv.symm ((galRestrict A K L B) σ) α, h⟩, ?_⟩
    simp only [AlgEquiv.apply_symm_apply]
  · rcases h with ⟨x, hx⟩
    rw [hx, AlgEquiv.symm_apply_apply]
    exact SetLike.coe_mem x

lemma galActionIdeal'.apply_fun {α : B} {I : Ideal' A K L B} (σ : L ≃ₐ[K] L) : α ∈ I → (galRestrict A K L B σ) α ∈ σ • I := by
  intro hα
  rw [mem_iff]
  refine ⟨⟨α, hα⟩, rfl⟩

-- we define the decomposition group of '(Ideal' A K L B)' over 'K'
-- to be the stabilizer of the MulAction 'galActionisPrime'

def decompositionSubgroupIdeal' (Q : Ideal' A K L B) :
  Subgroup (L ≃ₐ[K] L) := MulAction.stabilizer (L ≃ₐ[K] L) Q



variable (P : Ideal A) [P.IsMaximal] [Fintype (A ⧸ P)]
  (Q : Ideal B) [Q.IsMaximal] [Fintype (B ⧸ Q)]
  [Algebra (A ⧸ P) (B ⧸ Q)] [IsScalarTower A (A ⧸ P) (B ⧸ Q)]

attribute [instance] Ideal.Quotient.field

-- "By the Chinese remainder theorem, there exists an element
-- 'α' of 'B' such that 'α' generates the group '(B ⧸ Q)ˣ'
-- and lies in 'τQ' for all 'τ ¬∈ decompositionSubgroupIdeal'' "

local notation "q" => Fintype.card (A ⧸ P)

lemma Q_over_P : Ideal.comap (algebraMap A B) Q = P := by
  exact Ideal.comap_eq_of_scalar_tower_quotient (algebraMap (A ⧸ P) (B ⧸ Q)).injective

instance residuefieldUnitsIsCyclic (Q : Ideal B) [hB : Ideal.IsMaximal Q]
  [Fintype (B ⧸ Q)] : IsCyclic (B ⧸ Q)ˣ :=
  isCyclic_of_subgroup_isDomain (Units.coeHom _) <| by
    unfold Function.Injective
    simp_all
    intros a b
    apply Units.ext_iff.2

-- this lemma, 'CRT_generator' may not be necessary
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
  (∀  τ : L ≃ₐ[K] L, (τ ∉ decompositionSubgroupIdeal' A K L B Q) →  ρ ∈ (τ • Q)) := by
 sorry

lemma generator_pow {γ ρ : B} [hn0 : NeZero ((Ideal.Quotient.mk Q) γ)] (h : IsUnit (Ideal.Quotient.mk Q ρ)) (hx : ∀ (x : (B ⧸ Q)ˣ), x ∈ Subgroup.zpowers h.unit) : ∃ i : ℕ, γ - ρ ^ i ∈ Q := by
  have huγ : IsUnit (Ideal.Quotient.mk Q γ) := isUnit_iff_ne_zero.mpr (neZero_iff.1 hn0)
  have hγpow : huγ.unit ∈ Subgroup.zpowers (h.unit) := hx _
  have h : ∃ i, (Ideal.Quotient.mk Q γ) = (Ideal.Quotient.mk Q ρ) ^ i := by
    rw [Subgroup.mem_zpowers_iff] at hγpow
    rcases hγpow with ⟨i, hi⟩
    sorry
  convert h
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, sub_eq_zero]
  rfl

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
  (Polynomial.X - Polynomial.C ((galRestrict A K L B τ) α))


lemma F_root (α : B) : (F A K L B α).eval α = 0 := by
  rw [F, Polynomial.eval_prod, Finset.prod_eq_zero_iff]
  use 1
  constructor
  · exact Finset.mem_univ _
  · rw [map_one, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
    exact sub_self α

lemma F_coeff_in_A (α : B) : ∀ n : ℕ, ∃ a : A, Polynomial.coeff (F A K L B α) n = algebraMap _ _ a := by
  sorry

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

theorem qth_power_is_conjugate (α : B) : ∃ σ : L ≃ₐ[K] L, α ^ q - (galRestrict A K L B σ) α ∈ Q := by
  rcases CharP.exists (A ⧸ P) with ⟨p, hpA⟩
  have hpB := (Algebra.charP_iff (A ⧸ P) (B ⧸ Q) p).mp hpA
  have hF : Polynomial.expand (B ⧸ Q) q (FModQ A K L B Q α) = (FModQ A K L B Q α) ^ q := by
    rcases FiniteField.card (A ⧸ P) p with ⟨⟨n, _⟩, ⟨hp, hq⟩⟩
    have : Fact p.Prime := ⟨hp⟩
    dsimp at hq
    have hres (a : A) : (frobenius (B ⧸ Q) p ^ n) (algebraMap _ _ a) = algebraMap _ _ a := by
      rw [RingHom.coe_pow, iterate_frobenius]
      change (Ideal.Quotient.mk Q) (algebraMap A B a ^ p ^ n) = (Ideal.Quotient.mk Q) (algebraMap A B a)
      rw [← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem, ← map_pow, ← map_sub, ← Ideal.mem_comap, Q_over_P A B P Q, ← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_pow, sub_eq_zero, ← hq, FiniteField.pow_card]
    rw [hq, ← Polynomial.map_expand_pow_char p, FModQ_def, ← Polynomial.map_expand]
    ext i
    rw [Polynomial.coeff_map, Polynomial.coeff_map, Polynomial.coeff_map, Polynomial.coeff_expand Fin.size_pos', apply_ite (Ideal.Quotient.mk Q), apply_ite (frobenius (B ⧸ Q) p ^ n)]
    congr 1
    · rcases F_coeff_in_A A K L B α (i / p ^ n) with ⟨a, ha⟩
      rw [ha]
      exact (hres a).symm
    · repeat rw [map_zero]
  have h : (F A K L B α).eval (α ^ q) ∈ Q := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, ← Polynomial.eval₂_hom, ← Polynomial.eval_map, ← FModQ_def, RingHom.map_pow, ← Polynomial.expand_eval, hF, Polynomial.eval_pow]
    simp only [ne_eq, Fintype.card_ne_zero, not_false_eq_true, pow_eq_zero_iff]
    exact FModQ_root A K L B Q α
  simp_rw [F, Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C] at h
  apply Ideal.finset_prod_mem at h
  simp_all only [Subtype.exists, Finset.mem_univ, exists_const]

theorem ex_FrobElt : ∃ σ : decompositionSubgroupIdeal' A K L B Q, ∀ α : B, α ^ q - (galRestrict A K L B σ) α ∈ Q  := by
  rcases (generator A K L B Q) with ⟨α, ⟨hu, hα⟩⟩
  rcases (qth_power_is_conjugate A K L B P Q α) with ⟨σ, hσ⟩
  have hd : σ ∈ decompositionSubgroupIdeal' A K L B Q := by
    rw [decompositionSubgroupIdeal', ← Subgroup.inv_mem_iff]
    by_contra hc
    apply hα.2 at hc
    rcases ((galActionIdeal'.mem_iff A K L B).mp hc) with ⟨x, hx⟩
    apply_fun (galRestrict A K L B σ) at hx
    rw [galRestrict_inv] at hx
    change (galRestrict A K L B σ) α = (galRestrict A K L B σ).toFun ((galRestrict A K L B σ).invFun x) at hx
    rw [(galRestrict A K L B σ).right_inv] at hx
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
  · have hpow : ∃ i : ℕ,  γ - α ^ i ∈ Q := generator_pow B Q hu hα.1
    rcases hpow with ⟨i, hγ⟩
    have h' : (galRestrict A K L B σ) (γ - α ^ i) ∈ Q := by
      convert (galActionIdeal'.apply_fun A K L B σ) hγ using 1
      rw [hd]
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub] at h' hγ hσ ⊢
    rw [map_sub] at h'
    rw [sub_eq_zero] at h' hγ hσ ⊢
    rw [map_pow, h', hγ, map_pow, map_pow, map_pow, pow_right_comm, ← map_pow, hσ]

-- local notation "Frob["K "," L "]" => FrobeniusElt K L

end FiniteFrobeniusDef
