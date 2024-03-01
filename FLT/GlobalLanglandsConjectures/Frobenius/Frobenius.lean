/-
Copyright (c) 2023 Tsz Hin Chan, Jou Glasheen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Tsz Hin Chan, Jou Glasheen.
-/
import Mathlib.Tactic
import Mathlib.RingTheory.IntegralRestrict

/-!
# Frobenius elements

This is the second project of the course (MATH60040) Formalising Mathematics.

This file defines the Galois action on the set of ideals of `B`
in an AKLB scenario, and proceeds to prove the existence of Frobenius elements.

## Main definitions

* `galActionIdeal A K L B'` : the action of `Gal L/K` on the set of ideals of `B`.
* `decompositionSubgroupIdeal' A K L B Q` : the decomposition subgroup of `Q`.
* `FrobElement A K L B P Q` : the Frobenius element of `Q : Ideal B` (over `P`).

## Main results

* `ex_FrobElement` : the existence of Frobenius elements.
-/

open NumberField BigOperators Pointwise

theorem Ideal.finset_prod_mem {α R : Type*} [CommRing R] {P : Ideal R} [P.IsPrime]
    {ι : Finset α} {f : α → R} (h : ∏ x in ι, f x ∈ P): ∃ x : ι, f x ∈ P := by
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

namespace Frobenius

/-- We use the abbreviation `Ideal' A K L B` instead of `Ideal B` to store the
information of `A` when we define an ideal in `B`. -/
-- This is defined with help from Amelia.
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

lemma galRestrict_inv : galRestrict A K L B σ⁻¹ = (galRestrict A K L B σ)⁻¹ := rfl

/-- *Galois action on Ideals*: the action of `Gal L/K` on the set of ideals of `B`,
defined by mapping the ideal along the restriction of `σ : L ≃ₐ[K] L` to `B`. -/
noncomputable instance galActionIdeal': MulAction (L ≃ₐ[K] L) (Ideal' A K L B) where
  -- `smul` is defined with help from Amelia.
  smul σ I := Ideal.comap (AlgEquiv.symm (galRestrict A K L B σ)) I
  one_smul _ := by
    -- 'show' unfolds goal into something definitionally equal
    show Ideal.comap _ _ = _
    simp
    -- had to use 'convert' instead of 'rw', because
    -- 'AlgEquiv.symm (galRestrict A K L B σ) 1' is not syntactically equal to 'id'
    convert Ideal.comap_id _
  mul_smul _ _ := by
     intro h
     show Ideal.comap _ _ = _
     simp
     exact rfl
    -- the two sides of the goal were definitionally equal

lemma galActionIdeal'.smul_def {I : Ideal' A K L B} {σ : L ≃ₐ[K] L} :
    σ • I = Ideal.comap (AlgEquiv.symm (galRestrict A K L B σ)) I := rfl

lemma galActionIdeal'.mem_iff {α : B} {I : Ideal' A K L B} {σ : L ≃ₐ[K] L} :
    α ∈ σ • I ↔ ∃ x : I, α = (galRestrict A K L B σ) x := by
  rw [galActionIdeal'.smul_def, Ideal.mem_comap]
  constructor <;> intro h
  · refine ⟨⟨AlgEquiv.symm ((galRestrict A K L B) σ) α, h⟩, ?_⟩
    simp only [AlgEquiv.apply_symm_apply]
  · rcases h with ⟨x, hx⟩
    rw [hx, AlgEquiv.symm_apply_apply]
    exact SetLike.coe_mem x

lemma galActionIdeal'.apply_fun {α : B} {I : Ideal' A K L B} (σ : L ≃ₐ[K] L) :
    α ∈ I → (galRestrict A K L B σ) α ∈ σ • I := by
  intro hα
  rw [mem_iff]
  refine ⟨⟨α, hα⟩, rfl⟩

/-- *Decomposition subgroup*: the decomposition subgroup of an ideal `Q` in `B`
is the stabiliser of `Q` under `galActionIdeal'`. -/
def decompositionSubgroupIdeal' (Q : Ideal' A K L B) :
    Subgroup (L ≃ₐ[K] L) := MulAction.stabilizer (L ≃ₐ[K] L) Q

variable (P : Ideal A) [P.IsMaximal] [Fintype (A ⧸ P)]
  (Q : Ideal B) [Q.IsMaximal] [Fintype (B ⧸ Q)]
  [Algebra (A ⧸ P) (B ⧸ Q)] [IsScalarTower A (A ⧸ P) (B ⧸ Q)]

local notation "q" => Fintype.card (A ⧸ P)

attribute [instance] Ideal.Quotient.field

lemma Q_over_P : Ideal.comap (algebraMap A B) Q = P := by
  exact Ideal.comap_eq_of_scalar_tower_quotient (algebraMap (A ⧸ P) (B ⧸ Q)).injective

/-- The units of the residue field is a cyclic group. -/
instance residueFieldUnitsIsCyclic : IsCyclic (B ⧸ Q)ˣ :=
  isCyclic_of_subgroup_isDomain (Units.coeHom _) <| by
    unfold Function.Injective
    simp_all
    intros a b
    apply Units.ext_iff.2

theorem generator (Q : Ideal B) [hB : Ideal.IsMaximal Q]
  [Fintype (B ⧸ Q)] :
  ∃ (ρ : B) (h : IsUnit (Ideal.Quotient.mk Q ρ)) ,
  (∀ (x : (B ⧸ Q)ˣ), x ∈ Subgroup.zpowers h.unit)∧
  (∀  τ : L ≃ₐ[K] L, (τ ∉ decompositionSubgroupIdeal' A K L B Q) →  ρ ∈ (τ • Q)) := by
  sorry

lemma generator_pow {γ ρ : B} [hn0 : NeZero ((Ideal.Quotient.mk Q) γ)]
    (h : IsUnit (Ideal.Quotient.mk Q ρ))
    (hx : ∀ (x : (B ⧸ Q)ˣ), x ∈ Subgroup.zpowers h.unit) :
    ∃ i : ℕ, γ - ρ ^ i ∈ Q := by
  have huγ : IsUnit (Ideal.Quotient.mk Q γ) := isUnit_iff_ne_zero.mpr (neZero_iff.1 hn0)
  have hγpow : huγ.unit ∈ Subgroup.zpowers (h.unit) := hx _
  have h : ∃ i, (Ideal.Quotient.mk Q γ) = (Ideal.Quotient.mk Q ρ) ^ i := by
    rw [Subgroup.mem_zpowers_iff] at hγpow
    rcases hγpow with ⟨i, hi⟩
    apply_fun (Units.coeHom _) at hi
    simp only [map_zpow, Units.coeHom_apply, IsUnit.unit_spec] at hi
    have hρn0 : (Ideal.Quotient.mk Q) ρ ≠ 0 := IsUnit.ne_zero h
    use (i % (Fintype.card (B ⧸ Q) - 1 : Nat)).toNat
    rw [← hi, ← zpow_ofNat, Int.toNat_of_nonneg]
    · rw [Int.emod_def, zpow_sub₀ hρn0 , eq_div_iff (zpow_ne_zero _ hρn0),
          mul_right_eq_self₀, zpow_mul]
      left
      rw [zpow_coe_nat, FiniteField.pow_card_sub_one_eq_one _ hρn0, one_zpow]
    · apply Int.emod_nonneg
      rw [ne_eq, Nat.cast_eq_zero, tsub_eq_zero_iff_le, not_le]
      exact Fintype.one_lt_card
  convert h
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, sub_eq_zero]
  rfl

/-- The characteristic polynomial of `α : B` over `K`,
defined as the product of `X - conjugates of α`. -/
noncomputable def charpoly (α : B) : Polynomial B := ∏ τ : L ≃ₐ[K] L,
  (Polynomial.X - Polynomial.C ((galRestrict A K L B τ) α))

lemma charpoly_root (α : B) : (charpoly A K L B α).eval α = 0 := by
  rw [charpoly, Polynomial.eval_prod, Finset.prod_eq_zero_iff]
  use 1
  constructor
  · exact Finset.mem_univ _
  · rw [map_one, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
    exact sub_self α

-- This might be proven by using `IsIntegralClosure`?
lemma charpoly_coeff_in_A (α : B) : ∀ n : ℕ, ∃ a : A,
    Polynomial.coeff (charpoly A K L B α) n = algebraMap _ _ a := by
  sorry

/-- The characteristic polynomial of `α` modulo `Q`. -/
noncomputable def charpolyModQ (α : B) : Polynomial (B ⧸ Q) :=
  (charpoly A K L B α).map (Ideal.Quotient.mk Q)

lemma charpolyModQ_def (α : B) : charpolyModQ A K L B Q α
    = Polynomial.map (Ideal.Quotient.mk Q) (charpoly A K L B α) := rfl

lemma charpolyModQ_root (α : B) :
    (charpolyModQ A K L B Q α).eval ((Ideal.Quotient.mk Q) α) = 0 := by
  rw [charpolyModQ_def, Polynomial.eval_map, Polynomial.eval₂_hom, charpoly_root]
  exact rfl

theorem charpolyModQ_expand (α : B) :
    Polynomial.expand (B ⧸ Q) q (charpolyModQ A K L B Q α) = (charpolyModQ A K L B Q α) ^ q := by
  -- Let `p` be the characteristic of `A/P`.
  rcases CharP.exists (A ⧸ P) with ⟨p, hpA⟩
  -- Then `p` is also the characteristic of `B/Q`.
  have hpB := (Algebra.charP_iff (A ⧸ P) (B ⧸ Q) p).mp hpA
  -- `q=|A/P|` is some power of `p`.
  rcases FiniteField.card (A ⧸ P) p with ⟨⟨n, _⟩, ⟨hp, hq⟩⟩
  have : Fact p.Prime := ⟨hp⟩
  dsimp at hq
  -- First we show that `(frobenius (B / Q) p)^n`, i.e. `x ↦ x^p^n`,
  -- fixes any element of `B/Q` of the form `algebraMap a` with `a : A`.
  have hres (a : A) : (frobenius (B ⧸ Q) p ^ n) (algebraMap _ _ a) = algebraMap _ _ a := by
    rw [RingHom.coe_pow, iterate_frobenius]
    change (Ideal.Quotient.mk Q) (algebraMap A B a ^ p ^ n)
      = (Ideal.Quotient.mk Q) (algebraMap A B a)
    rw [← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem, ← map_pow,
        ← map_sub, ← Ideal.mem_comap, Q_over_P A B P Q, ← Ideal.Quotient.eq_zero_iff_mem,
        map_sub, map_pow, sub_eq_zero, ← hq, FiniteField.pow_card]
  -- Transforming the goal to be about `charpoly` instead of `charpolyModQ`.
  rw [hq, ← Polynomial.map_expand_pow_char p, charpolyModQ_def, ← Polynomial.map_expand]
  -- Then we compare coefficients.
  ext i
  -- Eliminating `Polynomial.expand`.
  rw [Polynomial.coeff_map, Polynomial.coeff_map, Polynomial.coeff_map,
      Polynomial.coeff_expand Fin.size_pos', apply_ite (Ideal.Quotient.mk Q),
      apply_ite (frobenius (B ⧸ Q) p ^ n)]
  congr 1
  · -- Show that when `p^n ∣ i`, the two sides agree.
    -- This uses the fact that `charpoly` has coefficients in `A`.
    rcases charpoly_coeff_in_A A K L B α (i / p ^ n) with ⟨a, ha⟩
    rw [ha]
    exact (hres a).symm
  · -- Show that otherwise, the two sides agree (in this case they are just `0`).
    repeat rw [map_zero]

/-- For any `α : B`, its `q`-th power is its conjugate. -/
theorem qth_power_is_conjugate (α : B) :
    ∃ σ : L ≃ₐ[K] L, α ^ q - (galRestrict A K L B σ) α ∈ Q := by
  -- We claim that `charpoly(α^q) = 0 (mod Q)`.
  have h : (charpoly A K L B α).eval (α ^ q) ∈ Q := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, ← Polynomial.eval₂_hom,
        ← Polynomial.eval_map, ← charpolyModQ_def, RingHom.map_pow,
        ← Polynomial.expand_eval, charpolyModQ_expand, Polynomial.eval_pow]
    simp only [ne_eq, Fintype.card_ne_zero, not_false_eq_true, pow_eq_zero_iff]
    exact charpolyModQ_root A K L B Q α
  -- By definition this translates to `α^q - σ α = 0 (mod Q)` for some `σ`.
  simp_rw [charpoly, Polynomial.eval_prod, Polynomial.eval_sub,
           Polynomial.eval_X, Polynomial.eval_C] at h
  apply Ideal.finset_prod_mem at h
  simp_all only [Subtype.exists, Finset.mem_univ, exists_const]

/-- **Existence of Frobenius elements**: there exists a `σ` in the decomposition
subgroup such that `α ^ |A/P| = σ α (mod Q)` for all `α : B`, i.e. `σ` acts as the
Frobenius automorphism on the residue field. -/
theorem ex_FrobElement : ∃ σ : decompositionSubgroupIdeal' A K L B Q,
    ∀ α : B, α ^ q - (galRestrict A K L B σ) α ∈ Q  := by
  -- Specify the above theorem with `α` as the generator to obtain `σ : L ≃ₐ[K] L`.
  rcases (generator A K L B Q) with ⟨α, ⟨hu, hα⟩⟩
  rcases (qth_power_is_conjugate A K L B P Q α) with ⟨σ, hσ⟩
  -- Show that `σ` is in the decomposition subgroup.
  have hd : σ ∈ decompositionSubgroupIdeal' A K L B Q := by
    -- Suppose not.
    rw [decompositionSubgroupIdeal', ← Subgroup.inv_mem_iff]
    by_contra hc
    -- Then `α ∈ σ⁻¹ • Q` by construction of `α`.
    apply hα.2 at hc
    rcases ((galActionIdeal'.mem_iff A K L B).mp hc) with ⟨x, hx⟩
    apply_fun (galRestrict A K L B σ) at hx
    rw [galRestrict_inv] at hx
    change (galRestrict A K L B σ) α
      = (galRestrict A K L B σ).toFun ((galRestrict A K L B σ).invFun x) at hx
    -- After some simplifications, this means `σ α ∈ Q`.
    rw [(galRestrict A K L B σ).right_inv] at hx
    rw [hx] at hσ
    apply Ideal.add_mem _ (Submodule.coe_mem x) at hσ
    -- As `α^q - σα ∈ Q`, this gives `α^q ∈ Q`.
    rw [add_sub_cancel'_right, ← Ideal.Quotient.eq_zero_iff_mem, map_pow] at hσ
    apply (IsUnit.pow q) at hu
    rw [hσ] at hu
    -- This is a contradiction to `α + Q` being a unit in `(B/Q)ˣ`.
    exact not_isUnit_zero hu
  -- We claim that `σ` is the desired Frobenius element.
  refine ⟨⟨σ , hd⟩, ?_⟩
  -- Remains to show that `γ^q - σγ ∈ Q` for all `γ : B`.
  intro γ
  cases' eq_zero_or_neZero (Ideal.Quotient.mk Q γ) with h0 hn0
  · -- If `γ ∈ Q`, trivial (here we need to use `σ • Q = Q`).
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_pow, h0]
    apply Ideal.Quotient.eq_zero_iff_mem.mp at h0
    apply (galActionIdeal'.apply_fun A K L B σ) at h0
    rw [hd, ← Ideal.Quotient.eq_zero_iff_mem] at h0
    rw [h0, zero_pow Fintype.card_ne_zero, sub_zero]
  · -- If `γ ∉ Q`, then `γ + Q = α ^ i + Q` for some `i` by construction of `α`.
    have hpow : ∃ i : ℕ,  γ - α ^ i ∈ Q := generator_pow B Q hu hα.1
    rcases hpow with ⟨i, hγ⟩
    have h' : (galRestrict A K L B σ) (γ - α ^ i) ∈ Q := by
      convert (galActionIdeal'.apply_fun A K L B σ) hγ using 1
      rw [hd]
    -- Some simplifications together with `α^q - σα ∈ Q` proves the result.
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub] at h' hγ hσ ⊢
    rw [map_sub] at h'
    rw [sub_eq_zero] at h' hγ hσ ⊢
    rw [map_pow, h', hγ, map_pow, map_pow, map_pow, pow_right_comm, ← map_pow, hσ]

/-- *Frobenius element*: The Frobenius element of an ideal `Q` with respect to `L/K`. -/
noncomputable def FrobElement : decompositionSubgroupIdeal' A K L B Q :=
  (ex_FrobElement A K L B P Q).choose

theorem FrobElement_def : ∀ α : B,
    α ^ q - (galRestrict A K L B (FrobElement A K L B P Q)) α ∈ Q :=
  (ex_FrobElement A K L B P Q).choose_spec

end Frobenius
