import Mathlib.Algebra.BigOperators.GroupWithZero.Action
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib
/-

# Abstract Hecke operators

We give an abstract exposition of the theory of Hecke operators

The set-up: a group `G` acts on additive group `A`, we have
an element `g : G`, and `U`, `V` are subgroups of `G`. We impose the
finiteness hypothesis that the double coset `UgV` is a *finite* union
of single left cosets `gᵢV`. Under this hypothesis we define a Hecke
operator [UgV] or `T_g`, which is an additive group homorphism
from `A^V` (the `V`-fixedpoints of `G` on `A`) to `A^U`.

## Main definition

## Mathematical details


Before we give the definition, let us observe that our finiteness
hypothesis is the same as asking that g⁻¹Ug ∩ V has finite index in
g⁻¹Ug, and by an appropriate version of the second isomorphism theorem,
that g⁻¹UgV is a finite union of left cosets hᵢV of V.
Hence the double coset UgV is also a finite union of left cosets
of `V` (namely `ghᵢV`).

The definition of the Hecke operator is as follows. Write UgV as a
finite disjoint union gᵢV.
If a ∈ A^V then we define `[UgV]a := ∑ᵢ gᵢ•a`. Note that replacing
the choice of gᵢ with another element g'ᵢ := gᵢv will not change gᵢ•a
as a ∈ A^v, so the sum is a well-defined element of A. Finally
we observe that it's in A^U because if u ∈ U then left multiplication
by u is a permutation of the cosets gᵢV.

Note that if G is a topological group and U, V are compact open
subgroups of G, then our hypothesis is automatically satisfied
for all g ∈ G, because g⁻¹Ug ∩ V is open in compact V and hence
has finite index.

-/

section move_these

-- This should be in Mathlib.Algebra.BigOperators.Finprod
lemma finsum_mem_eq_finset_sum {ι A : Type*} [AddCommMonoid A]
    {s : Set ι} (hs : s.Finite) (f : ι → A) :
    ∑ᶠ i ∈ s, f i = ∑ i ∈ hs.toFinset, f i := by
  rw [finsum_mem_eq_sum_of_inter_support_eq]
  simp

-- This should be in Mathlib.Data.Set.Function
/-- If `f : α → β` and `g : β → γ` and if `f` is injective on `s`, then `f ∘ g` is a bijection
on `s` iff  `g` is a bijection on `f '' s`. -/
theorem _root_.Set.bijOn_comp_iff_bijOn_image {α β γ : Type*} {f : α → β} {g : β → γ} {s : Set α}
    (hf : Set.InjOn f s) {t : Set γ} :
    Set.BijOn (g ∘ f) s t ↔ Set.BijOn g (f '' s) t := by
  constructor
  · rintro ⟨h₁, h₂, h₃⟩
    refine ⟨?_, ?_, ?_⟩
    · exact Set.mapsTo_image_iff.mpr h₁
    · exact Set.InjOn.image_of_comp h₂
    · intro x hx
      obtain ⟨y, hy, rfl⟩ := h₃ hx
      refine ⟨f y, ?_, rfl⟩
      refine ⟨y, hy, rfl⟩
  · rintro ⟨h₁, h₂, h₃⟩
    refine ⟨?_, ?_, ?_⟩
    · exact Set.mapsTo_image_iff.mp h₁
    · apply Set.InjOn.comp h₂ hf
      exact Set.mapsTo_image f s
    · exact Set.SurjOn.comp h₃ fun ⦃a⦄ a ↦ a

-- This should be in Mathlib.Data.Set.Function
/--
If we have a commutative square

α --f--> β
|        |
p₁       p₂
|        |
\/       \/
γ --g--> δ

and `f` induces a bijection from `s : Set α` to `t : Set β` then `g`
induces a bijection from the image of `s` to the image of `t`, as long as it
is injective on the image of `s`.
-/
theorem _root_.Set.bijOn_image_image {α β γ δ : Type*} {f : α → β} {p₁ : α → γ} {p₂ : β → δ}
    {g : γ → δ} (comm : ∀ a, p₂ (f a) = g (p₁ a)) {s : Set α} {t : Set β}
    (hbij : Set.BijOn f s t) (hinj: Set.InjOn g (p₁ '' s)) : Set.BijOn g (p₁ '' s) (p₂ '' t) := by
  obtain ⟨h1, h2, h3⟩ := hbij
  refine ⟨?_, hinj, ?_⟩
  . rintro _ ⟨a, ha, rfl⟩
    exact ⟨f a, h1 ha, by rw [comm a]⟩
  . rintro _ ⟨b, hb, rfl⟩
    obtain ⟨a, ha, rfl⟩ := h3 hb
    rw [← Set.image_comp, comm]
    exact ⟨a, ha, rfl⟩

end move_these

--section delaborator

--variable (α β : Type) [AddCommMonoid β] (s : Set α) (f : α → β) in
--#check ∑ᶠ a ∈ s, f a -- ∑ᶠ (a : α) (_ : a ∈ s), f a : β

--end delaborator

variable {G : Type*} [Group G] {A : Type*} [AddCommMonoid A]
    [DistribMulAction G A] {g : G} {U V : Subgroup G}

open scoped Pointwise

-- finiteness hypothesis we need
variable (h : (QuotientGroup.mk '' (U * g • V) : Set (G ⧸ V)).Finite)

open ConjAct

namespace AbstractHeckeOperator

/-- If a is fixed by V then `∑ᶠ g ∈ s, g • a` is independent of the choice `s` of
coset representatives in `G` for a subset of `G ⧸ V` -/
lemma eq_finsum_quotient_out_of_bijOn
    {a : A} (hVa : ∀ γ ∈ V, γ • a = a) {X : Set (G ⧸ V)}
    {s : Set G} (hs : s.BijOn (QuotientGroup.mk : G → G ⧸ V) X) :
    ∑ᶠ g ∈ s, g • a = ∑ᶠ g ∈ Quotient.out '' X, g • a := by
  let e (g : G) : G := Quotient.out (QuotientGroup.mk g : G ⧸ V)
  have he₀ : Set.BijOn e s (Quotient.out '' X) := by
    refine Set.BijOn.comp ?_ hs
    exact Set.InjOn.bijOn_image <| Set.injOn_of_injective Quotient.out_injective
  have he₁ : ∀ g ∈ s, g • a = (Quotient.out (QuotientGroup.mk g : G ⧸ V)) • a := by
    intro g hgs
    obtain ⟨v, hv⟩ := QuotientGroup.mk_out_eq_mul V g
    rw [hv, mul_smul, hVa v v.2]
  exact finsum_mem_eq_of_bijOn e he₀ he₁

/-- The Hecke operator T_g = [UgV] : A^V → A^U associated to the double coset UgV. -/
noncomputable def HeckeOperator_toFun : {a : A // ∀ γ ∈ V, γ • a = a} → {a : A // ∀ γ ∈ U, γ • a = a} :=
  fun a ↦ ⟨∑ᶠ gᵢ ∈ Quotient.out '' (QuotientGroup.mk '' (U * g • V) : Set (G ⧸ V)), gᵢ • a.1, by
  intro u huU
  classical
  have := h.image Quotient.out
  -- missing lemma from finsum means we need to convert to finset and back
  rw [finsum_mem_eq_finset_sum this, Finset.smul_sum,
    ← finsum_mem_eq_finset_sum this, ← finsum_mem_eq_finset_sum this]
  rw [← eq_finsum_quotient_out_of_bijOn (X := (QuotientGroup.mk '' (↑U * g • ↑V)))
        (s := u • (Quotient.out '' (QuotientGroup.mk '' (U * g • V) : Set (G ⧸ V)))) a.2]
  · rw [finsum_mem_eq_of_bijOn (fun g ↦ u • g)]
    · exact Set.InjOn.bijOn_image <| Set.injOn_of_injective (MulAction.injective u)
    · simp [mul_smul]
  · -- fun
    apply (Set.bijOn_comp_iff_bijOn_image (Set.injOn_of_injective (MulAction.injective u))).1
    change Set.BijOn ((fun xbar ↦ u • xbar) ∘ (QuotientGroup.mk : G → G ⧸ V)) _ _
    rw [Set.bijOn_comp_iff_bijOn_image]
    · rw [← Set.image_comp]
      simp only [Function.comp_apply, Quotient.out_eq, Set.image_id']
      refine Set.bijOn_image_image (f := fun (x : G) ↦ u • x) (p₁ := (QuotientGroup.mk : G → G ⧸ V))
        (fun a ↦ rfl) ?_ (Set.injOn_of_injective (MulAction.injective u))
      refine ⟨?_, ?_, ?_⟩
      . rintro x ⟨u', hu', gv, hgv, rfl⟩
        refine ⟨u * u', mul_mem huU hu', gv, hgv, ?_⟩
        simp [mul_assoc]
      . exact Set.injOn_of_injective (MulAction.injective u)
      · rintro x ⟨u', hu', gv, hgv, rfl⟩
        refine ⟨(u⁻¹ * u') * gv, ⟨u⁻¹ * u', mul_mem (inv_mem huU) hu', gv, hgv, rfl⟩, ?_⟩
        simp [mul_assoc]
    · refine Set.InjOn.image_of_comp ?_
      change Set.InjOn (fun x ↦ QuotientGroup.mk (Quotient.out x)) _
      simp only [Quotient.out_eq]
      exact Function.Injective.injOn Function.injective_id
    ⟩

namespace HeckeOperator_toFun

-- define `FixedPoints`?

--lemma map_add (a b : {a : A | ∀ v ∈ V, v • a = a}) :
--  HeckeOperator_toFun h a + HeckeOperator_toFun h b = 0 := sorry

#check {a : A // ∀ γ ∈ V, γ • a = a}
