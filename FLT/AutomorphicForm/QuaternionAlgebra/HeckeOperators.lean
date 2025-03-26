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

-- PRed to mathlib in #23284
lemma finsum_mem_eq_sum' {ι A : Type*} [AddCommMonoid A]
    {s : Set ι} (hs : s.Finite) (f : ι → A) :
    ∑ᶠ i ∈ s, f i = ∑ i ∈ hs.toFinset, f i := by
  rw [finsum_mem_eq_sum_of_inter_support_eq]
  simp

-- PRed to mathlib in #23284
lemma smul_finsum_mem {ι A : Type*} [AddCommMonoid A]
    {s : Set ι} (hs : s.Finite) (f : ι → A) {M : Type*} [Monoid M]
    [DistribMulAction M A] (m : M) :
    m • ∑ᶠ i ∈ s, f i = ∑ᶠ i ∈ s, m • f i := by
  rw [finsum_mem_eq_sum' hs, Finset.smul_sum,
    ← finsum_mem_eq_sum']

-- PRed to mathlib #23286
/-- If `f : α → β` and `g : β → γ` and if `f` is injective on `s`, then `f ∘ g` is a bijection
on `s` iff  `g` is a bijection on `f '' s`. -/
theorem Set.bijOn_comp_iff_bijOn_image {α β γ : Type*} {f : α → β} {g : β → γ} {s : Set α}
    (hf : InjOn f s) {t : Set γ} :
    Set.BijOn (g ∘ f) s t ↔ BijOn g (f '' s) t := by
  constructor
  · rintro ⟨h₁, h₂, h₃⟩
    refine ⟨mapsTo_image_iff.mpr h₁, InjOn.image_of_comp h₂, fun x hx ↦ ?_⟩
    obtain ⟨y, hy, rfl⟩ := h₃ hx
    exact ⟨f y, ⟨y, hy, rfl⟩, rfl⟩
  · rintro ⟨h₁, h₂, h₃⟩
    exact ⟨mapsTo_image_iff.mp h₁, InjOn.comp h₂ hf <| mapsTo_image f s,
      SurjOn.comp h₃ <| surjOn_image _ _⟩

-- PRed to mathlib #23286
/--
If we have a commutative square

α --f--> β
|        |
p₁       p₂
|        |
\/       \/
γ --g--> δ

and `f` induces a bijection from `s : Set α` to `t : Set β` then `g`
induces a bijection from the image of `s` to the image of `t`, as long as `g` is
is injective on the image of `s`.
-/
theorem Set.bijOn_image_image {α β γ δ : Type*} {f : α → β} {p₁ : α → γ} {p₂ : β → δ}
    {g : γ → δ} (comm : ∀ a, p₂ (f a) = g (p₁ a)) {s : Set α} {t : Set β}
    (hbij : BijOn f s t) (hinj: InjOn g (p₁ '' s)) : BijOn g (p₁ '' s) (p₂ '' t) := by
  obtain ⟨h1, h2, h3⟩ := hbij
  refine ⟨?_, hinj, ?_⟩
  . rintro _ ⟨a, ha, rfl⟩
    exact ⟨f a, h1 ha, by rw [comm a]⟩
  . rintro _ ⟨b, hb, rfl⟩
    obtain ⟨a, ha, rfl⟩ := h3 hb
    rw [← image_comp, comm]
    exact ⟨a, ha, rfl⟩

-- not yet PRed
lemma Set.Finite.of_injOn {α β : Type*} {f : α → β} {s : Set α} {t : Set β}
    (hm : MapsTo f s t) (hi : InjOn f s) (ht : t.Finite) : s.Finite :=
  Set.Finite.of_finite_image (ht.subset (image_subset_iff.mpr hm)) hi

-- not yet PRed
lemma Set.BijOn.finite_iff_finite {α β : Type*} {f : α → β} {s : Set α}
    {t : Set β} (h : BijOn f s t) : s.Finite ↔ t.Finite :=
  ⟨fun h1 ↦ h1.of_surjOn _ h.2.2, fun h1 ↦ h1.of_injOn h.1 h.2.1⟩

end move_these

--section delaborator

--variable (α β : Type) [AddCommMonoid β] (s : Set α) (f : α → β) in
--#check ∑ᶠ a ∈ s, f a -- ∑ᶠ (a : α) (_ : a ∈ s), f a : β

--end delaborator

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

-- should I be making a submodule?? Is that the point??
instance module [Ring R] [Module R A] [SMulCommClass G R A] : Module R (fixedPoints G A) where
  one_smul a := by
    ext
    push_cast
    simp
  mul_smul r s a := by
    ext
    push_cast
    simp [mul_smul]
  smul_zero a := by
    ext
    push_cast
    simp
  smul_add r s a := by
    ext
    push_cast
    simp
  add_smul r s a := by
    ext
    push_cast
    simp [add_smul]
  zero_smul a := by
    ext
    push_cast
    simp

end FixedPoints

open scoped Pointwise

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
  ⟨∑ᶠ gᵢ ∈ Quotient.out '' (QuotientGroup.mk '' (U * g • V) : Set (G ⧸ V)), gᵢ • a.1, by
  rintro ⟨u, huU⟩
  obtain ⟨a, ha⟩ := a
  have aprop : ∀ v ∈ V, v • a = a := fun v hv ↦ ha ⟨v, hv⟩
  have := h.image Quotient.out
  rw [smul_finsum_mem (h.image Quotient.out), ← eq_finsum_quotient_out_of_bijOn aprop]
  · rw [finsum_mem_eq_of_bijOn (fun g ↦ u • g)]
    · exact Set.InjOn.bijOn_image <| Set.injOn_of_injective (MulAction.injective u)
    · simp [mul_smul]
  · apply (Set.bijOn_comp_iff_bijOn_image (Set.injOn_of_injective (MulAction.injective u))).1
    change Set.BijOn ((fun xbar ↦ u • xbar) ∘ (QuotientGroup.mk : G → G ⧸ V)) _ _
    rw [Set.bijOn_comp_iff_bijOn_image]
    · rw [← Set.image_comp]
      simp only [Function.comp_apply, Quotient.out_eq, Set.image_id']
      refine Set.bijOn_image_image (f := fun (x : G) ↦ u • x) (p₁ := (QuotientGroup.mk : G → G ⧸ V))
        (fun a ↦ rfl) ?_ (Set.injOn_of_injective (MulAction.injective u))
      apply Set.bijOn_smul _ _ _ huU
    · refine Set.InjOn.image_of_comp ?_
      simp only [Function.comp_def, Quotient.out_eq]
      exact Function.Injective.injOn Function.injective_id
    ⟩

  noncomputable def HeckeOperator_addMonoidHom : fixedPoints V A →+ fixedPoints U A where
    toFun := HeckeOperator_toFun h
    map_zero' := by
      ext
      simp [HeckeOperator_toFun]
    map_add' a b := by
      ext
      simp [HeckeOperator_toFun, -Set.mem_image, finsum_mem_add_distrib (h.image Quotient.out)]

variable {R : Type*} [Ring R] [Module R A] [SMulCommClass G R A]

noncomputable def HeckeOperator : fixedPoints V A →ₗ[R] fixedPoints U A where
  toFun := HeckeOperator_toFun h
  map_add' a b := by
    ext
    simp [HeckeOperator_toFun, -Set.mem_image, finsum_mem_add_distrib (h.image Quotient.out)]
  map_smul' r a := by
    ext
    simp [-Set.mem_image, HeckeOperator_toFun, smul_comm, smul_finsum_mem (h.image Quotient.out)]

lemma HeckeOperator_apply (a : fixedPoints V A) :
    (HeckeOperator (R := R) h a : A) =
    ∑ᶠ (gᵢ ∈ Quotient.out '' (QuotientGroup.mk '' (U * g • ↑V) : Set (G ⧸ V))), gᵢ • (a : A) :=
  rfl

theorem comm {g₁ g₂ : G} (h₁ : (QuotientGroup.mk '' (U * g₁ • U) : Set (G ⧸ U)).Finite)
    (h₂ : (QuotientGroup.mk '' (U * g₂ • U) : Set (G ⧸ U)).Finite)
    (hcomm : ∃ s₁ s₂ : Set G,
      Set.BijOn QuotientGroup.mk s₁ (QuotientGroup.mk '' (U * g₁ • U) : Set (G ⧸ U)) ∧
      Set.BijOn QuotientGroup.mk s₂ (QuotientGroup.mk '' (U * g₂ • U) : Set (G ⧸ U)) ∧
      ∀ a ∈ s₁, ∀ b ∈ s₂, a * b = b * a) :
    (HeckeOperator h₁ ∘ₗ HeckeOperator h₂ : fixedPoints U A →ₗ[R] fixedPoints U A) =
    HeckeOperator h₂ ∘ₗ HeckeOperator h₁ := by
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
  congr; ext g₂; congr; ext hg₂; congr; ext g₁; congr; ext hg₁;
  rw [smul_smul, smul_smul, hcomm _ hg₁ _ hg₂]
