/-
Copyright (c) 2025 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Andrew Yang, Matthew Jasper
-/
module

public import Mathlib.Algebra.BigOperators.GroupWithZero.Action
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Ring.Action.Submonoid
public import Mathlib.GroupTheory.GroupAction.Quotient

@[expose] public section
/-

# Abstract Hecke operators

We give an abstract exposition of the theory of Hecke operators.

The set-up: a group `G` acts on an additive group `A`, we have
an element `g : G`, and `U`, `V` are subgroups of `G`. We impose the
finiteness hypothesis that the double coset `UgV` is a *finite* union
of single left cosets `gᵢV`. Under this hypothesis we define a Hecke
operator [UgV] or `T_g`, which is an additive group homorphism
from `A^V` (the `V`-fixedpoints of `G` on `A`) to `A^U` defined
by `a ↦ ∑ᵢ(gᵢ•a)`.

## Main definition

Let `G` act on `A` via `R`-linear maps, where `R` is an underlying
ring of coefficient (which can be an arbitrary commutative ring here).

* `AbstractHeckeOperator.HeckeOperator` : the `R`-linear map from `A^V` to `A^U`
  coming from the double coset `UgV`.

## Mathematical details

The definition of the Hecke operator is as follows. Write `UgV` as a
finite disjoint union `gᵢV` (the finiteness is our running assumption).
If `a ∈ A^V` then we define `[UgV]a := ∑ᵢ(gᵢ•a)`. Note that replacing
the choice of `gᵢ` with another element `g'ᵢ := gᵢv` will not change `gᵢ•a`
as `a ∈ A^V`, so the sum is a well-defined element of `A`. Finally
we observe that it's in `A^U` because if `u ∈ U` then left multiplication
by `u` is a permutation of the cosets `gᵢV`.

Note that if `G` is a topological group and `U`, `V` are compact open
subgroups of `G`, then our finiteness hypothesis is automatically satisfied
for all `g ∈ G`, because `g⁻¹Ug ∩ V` is open in compact `g⁻¹Ug` and hence
has finite index, and so by the second isomorphism theorem `g⁻¹UgV` is
a finite union of left cosets of `V`, and thus so is `UgV`.

-/

namespace FixedPoints

open MulAction

variable {G : Type*} [Group G] {A : Type*} [AddCommMonoid A]
    [DistribMulAction G A] {g : G}

instance : AddCommMonoid (fixedPoints G A) :=
  AddSubmonoid.toAddCommMonoid (FixedPoints.addSubmonoid G A)

@[simp, norm_cast]
lemma coe_zero : ((0 : fixedPoints G A) : A) = 0 := rfl

@[simp, norm_cast]
lemma coe_add (a b : fixedPoints G A) :
    ((a + b : fixedPoints G A) : A) = a + b := rfl

-- note: `[SMulCommClass R G A]` is mathematically equivalent
-- to `[SMulCommClass G R A]` but we need a convention for an order here,
-- because `SMulCommClass X Y A → SMulCommClass Y X A` isn't
-- an instance because it would cause loops :-/
variable {R : Type*}

instance [SMul R A] [SMulCommClass G R A] :
    SMul R (fixedPoints G A) where
  smul r a := ⟨r • a.1, fun g ↦ by rw [smul_comm, a.2]⟩

@[simp, norm_cast]
lemma coe_smul [SMul R A] [SMulCommClass G R A] (r : R) (a : fixedPoints G A) :
    ((r • a : fixedPoints G A) : A) = r • a := rfl

instance [Monoid R] [MulAction R A] [SMulCommClass G R A] :
    MulAction R (fixedPoints G A) where
  one_smul a := by
    ext
    push_cast
    simp
  mul_smul r s a := by
    ext
    push_cast
    simp [mul_smul]

-- Probably this should be a submodule instance and then get module instance for free
instance module [Ring R] [Module R A] [SMulCommClass G R A] : Module R (fixedPoints G A) where
  one_smul a := one_smul _ _
  mul_smul r s a := mul_smul _ _ _
  smul_zero a := by
    ext
    exact smul_zero _
  smul_add r s a := by
    ext
    exact smul_add _ _ _
  add_smul r s a := by
    ext
    exact add_smul _ _ _
  zero_smul a := by
    ext
    exact zero_smul _ _

end FixedPoints

open scoped Pointwise

-- should maybe be in mathlib but not sure where to put it.
variable (G : Type*) [Group G] (U : Subgroup G) (X : Set G) {u : G} in
lemma Set.bijOn_smul (hu : u ∈ U) : Set.BijOn (fun x ↦ u • x) ((U : Set G) * X) (U * X) := by
  refine ⟨?_, Set.injOn_of_injective (MulAction.injective u), ?_⟩
  · rintro x ⟨u', hu', x, hx, rfl⟩
    exact ⟨u * u', mul_mem hu hu', x, hx, by simp [mul_assoc]⟩
  · rintro x ⟨u', hu', x, hx, rfl⟩
    exact ⟨(u⁻¹ * u') * x, ⟨u⁻¹ * u', mul_mem (inv_mem hu) hu', x, hx, rfl⟩, by simp [mul_assoc]⟩

variable {G : Type*} [Group G] {A : Type*} [AddCommMonoid A]
    [DistribMulAction G A] {g : G} {U V : Subgroup G}

open MulAction

-- finiteness hypothesis we need to make Hecke operators work: `UgV` is
-- a finite number of left `V`-cosets.
variable (h : (QuotientGroup.mk '' (U * {g}) : Set (G ⧸ V)).Finite)

open ConjAct

namespace AbstractHeckeOperator

/-- If `a` is fixed by `V` then `∑ᶠ g ∈ s, g • a` is independent of the choice `s` of
coset representatives in `G` for a subset of `G ⧸ V` -/
lemma eq_finsum_quotient_out_of_bijOn' (a : fixedPoints V A)
    {X : Set (G ⧸ V)}
    {s : Set G} (hs : s.BijOn (QuotientGroup.mk : G → G ⧸ V) X) :
    ∑ᶠ g ∈ s, g • (a : A) = ∑ᶠ g ∈ Quotient.out '' X, g • (a : A) := by
  let e (g : G) : G := Quotient.out (QuotientGroup.mk g : G ⧸ V)
  have he₀ : Set.BijOn e s (Quotient.out '' X) := by
    refine Set.BijOn.comp ?_ hs
    exact Set.InjOn.bijOn_image <| Set.injOn_of_injective Quotient.out_injective
  have he₁ : ∀ g ∈ s, g • (a : A) = (Quotient.out (QuotientGroup.mk g : G ⧸ V)) • a := by
    intro g hgs
    obtain ⟨v, hv⟩ := QuotientGroup.mk_out_eq_mul V g
    rw [hv, mul_smul, (show (v : G) • (a : A) = a from a.2 v)]
  exact finsum_mem_eq_of_bijOn e he₀ he₁

/-- The Hecke operator T_g = [UgV] : A^V → A^U associated to the double coset UgV. -/
noncomputable def HeckeOperator_toFun (a : fixedPoints V A) : fixedPoints U A :=
  ⟨∑ᶠ gᵢ ∈ Quotient.out '' (QuotientGroup.mk '' (U * {g}) : Set (G ⧸ V)), gᵢ • a.1, by
  rintro ⟨u, huU⟩
  rw [smul_finsum_mem (h.image Quotient.out), ← eq_finsum_quotient_out_of_bijOn' a]
  · rw [finsum_mem_eq_of_bijOn (fun g ↦ u • g)]
    · exact Set.InjOn.bijOn_image <| Set.injOn_of_injective (MulAction.injective u)
    · simp [mul_smul]
  · apply (Set.bijOn_comp_iff (Set.injOn_of_injective (MulAction.injective u))).1
    change Set.BijOn ((fun xbar ↦ u • xbar) ∘ (QuotientGroup.mk : G → G ⧸ V)) _ _
    rw [Set.bijOn_comp_iff]
    · rw [← Set.image_comp]
      simp only [Function.comp_apply, Quotient.out_eq, Set.image_id']
      refine Set.bijOn_image_image (f := fun (x : G) ↦ u • x) (p₁ := (QuotientGroup.mk : G → G ⧸ V))
        (fun a ↦ rfl) ?_ (Set.injOn_of_injective (MulAction.injective u))
      apply Set.bijOn_smul _ _ _ huU
    · refine Set.InjOn.image_of_comp ?_
      simp only [Function.comp_def, Quotient.out_eq]
      exact Function.Injective.injOn Function.injective_id
    ⟩

/-- The Hecke operator `T_g = [UgV] : A^V → A^U` packaged as an additive monoid homomorphism. -/
noncomputable def HeckeOperator_addMonoidHom : fixedPoints V A →+ fixedPoints U A where
  toFun := HeckeOperator_toFun h
  map_zero' := by
    ext
    simp [HeckeOperator_toFun]
  map_add' a b := by
    ext
    simp only [HeckeOperator_toFun, FixedPoints.coe_add, smul_add,
      finsum_mem_add_distrib (h.image Quotient.out)]


variable {R : Type*} [Ring R] [Module R A] [SMulCommClass G R A]

variable (g U V) in
/-- The Hecke operator `T_g = [UgV] : A^V → A^U` as an `R`-linear map, where `R` is any ring
acting on `A` and commuting with the `G`-action. -/
noncomputable def HeckeOperator : fixedPoints V A →ₗ[R] fixedPoints U A where
  toFun := HeckeOperator_toFun h
  map_add' a b := by
    ext
    simp only [HeckeOperator_toFun, FixedPoints.coe_add, smul_add,
      finsum_mem_add_distrib (h.image Quotient.out)]
  map_smul' r a := by
    ext
    simp only [HeckeOperator_toFun, FixedPoints.coe_smul, smul_comm,
      smul_finsum_mem (h.image Quotient.out), RingHom.id_apply]

lemma HeckeOperator_apply (a : fixedPoints V A) :
    (HeckeOperator (R := R) g U V h a : A) =
    ∑ᶠ (gᵢ ∈ Quotient.out '' (QuotientGroup.mk '' (U * {g}) : Set (G ⧸ V))), gᵢ • (a : A) :=
  rfl

theorem comm {g₁ g₂ : G} (h₁ : (QuotientGroup.mk '' (U * {g₁}) : Set (G ⧸ U)).Finite)
    (h₂ : (QuotientGroup.mk '' (U * {g₂}) : Set (G ⧸ U)).Finite)
    (hcomm : ∃ s₁ s₂ : Set G,
      Set.BijOn QuotientGroup.mk s₁ (QuotientGroup.mk '' (U * {g₁}) : Set (G ⧸ U)) ∧
      Set.BijOn QuotientGroup.mk s₂ (QuotientGroup.mk '' (U * {g₂}) : Set (G ⧸ U)) ∧
      ∀ a ∈ s₁, ∀ b ∈ s₂, a * b = b * a) :
    (HeckeOperator g₁ U U h₁ ∘ₗ HeckeOperator g₂ U U h₂ : fixedPoints U A →ₗ[R] fixedPoints U A) =
    HeckeOperator g₂ U U h₂ ∘ₗ HeckeOperator g₁ U U h₁ := by
  ext a
  rcases hcomm with ⟨s₁, s₂, hs₁, hs₂, hcomm⟩
  simp only [LinearMap.coe_comp, Function.comp_apply]
  nth_rw 1 [HeckeOperator_apply]
  rw [← eq_finsum_quotient_out_of_bijOn' _ hs₁]
  nth_rw 1 [HeckeOperator_apply]
  rw [← eq_finsum_quotient_out_of_bijOn' _ hs₂]
  nth_rw 1 [HeckeOperator_apply]
  rw [← eq_finsum_quotient_out_of_bijOn' _ hs₂]
  nth_rw 1 [HeckeOperator_apply]
  rw [← eq_finsum_quotient_out_of_bijOn' _ hs₁]
  have hfs₁ : s₁.Finite := by rwa [hs₁.finite_iff_finite]
  have hfs₂ : s₂.Finite := by rwa [hs₂.finite_iff_finite]
  simp_rw [smul_finsum_mem hfs₁, smul_finsum_mem hfs₂, finsum_mem_comm _ hfs₁ hfs₂]
  -- I'm sure there's a better way to do this!
  congr; ext g₂; congr; ext hg₂; congr; ext g₁; congr; ext hg₁;
  rw [smul_smul, smul_smul, hcomm _ hg₁ _ hg₂]

end AbstractHeckeOperator
