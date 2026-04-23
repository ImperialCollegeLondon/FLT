module

public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Ring.Subring.Basic
public import Mathlib.Topology.Algebra.RestrictedProduct.Basic
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Group.Pointwise.Set.Basic

@[expose] public section

namespace RestrictedProduct

variable {ι : Type*}
variable {R : ι → Type*} {A : (i : ι) → Set (R i)}
variable {ℱ : Filter ι}
variable {S : ι → Type*} -- subobject type
variable [Π i, SetLike (S i) (R i)]
variable {B : Π i, S i}

variable
    {G H : ι → Type*}
    {C : (i : ι) → Set (G i)}
    {D : (i : ι) → Set (H i)}

end RestrictedProduct

open RestrictedProduct

section modules

variable {ι₁ ι₂ : Type*}
variable (R₁ : ι₁ → Type*) (R₂ : ι₂ → Type*)
variable {𝓕₁ : Filter ι₁} {𝓕₂ : Filter ι₂}
variable {A₁ : (i : ι₁) → Set (R₁ i)} {A₂ : (i : ι₂) → Set (R₂ i)}
variable {S₁ : ι₁ → Type*} {S₂ : ι₂ → Type*}
variable [Π i, SetLike (S₁ i) (R₁ i)] [Π j, SetLike (S₂ j) (R₂ j)]
variable {B₁ : Π i, S₁ i} {B₂ : Π j, S₂ j}
variable (f : ι₂ → ι₁) (hf : Filter.Tendsto f 𝓕₂ 𝓕₁)
variable {A : Type*} [Semiring A]
variable [Π i, AddCommMonoid (R₁ i)] [Π i, AddCommMonoid (R₂ i)] [Π i, Module A (R₁ i)]
    [Π i, Module A (R₂ i)] [∀ i, AddSubmonoidClass (S₁ i) (R₁ i)]
    [∀ i, AddSubmonoidClass (S₂ i) (R₂ i)] [∀ i, SMulMemClass (S₁ i) A (R₁ i)]
    [∀ i, SMulMemClass (S₂ i) A (R₂ i)]
    (φ : ∀ j, R₁ (f j) →ₗ[A] R₂ j)
    (hφ : ∀ᶠ j in 𝓕₂, Set.MapsTo (φ j) (B₁ (f j)) (B₂ j))

/--
Given two restricted products `Πʳ (i : ι₁), [R₁ i, B₁ i]_[𝓕₁]` and `Πʳ (j : ι₂), [R₂ j, B₂ j]_[𝓕₂]`
of `A`-modules, `RestrictedProduct.mapAlongLinearMap` gives an `A`-linear map between them.
The data needed is a function `f : ι₂ → ι₁` such that `𝓕₂` tends to `𝓕₁` along `f`, and `A`-linear
maps `φ j : R₁ (f j) → R₂ j` sending `B₁ (f j)` into `B₂ j` for an `𝓕₂`-large set of `j`'s.
-/
def RestrictedProduct.mapAlongLinearMap :
    Πʳ i, [R₁ i, B₁ i]_[𝓕₁] →ₗ[A] Πʳ j, [R₂ j, B₂ j]_[𝓕₂] where
  __ := mapAlongAddMonoidHom R₁ R₂ f hf (fun j ↦ φ j) hφ
  map_smul' a f := by
    ext i
    apply map_smul (φ i)

@[simp]
lemma RestrictedProduct.mapAlongLinearMap_apply (x : Πʳ i, [R₁ i, B₁ i]_[𝓕₁]) (j : ι₂) :
    x.mapAlongLinearMap R₁ R₂ f hf φ hφ j = φ j (x (f j)) :=
  rfl

variable (A : Type*) [CommRing A] {ι : Type*} (R : ι → Type*)
  [Π i, AddCommGroup (R i)] [∀ i, Module A (R i)] (C : ∀ i, Submodule A (R i))

/-- A linear map version of `RestrictedProduct.inclusion` :
if `𝓕 ≤ 𝓖` then there's a linear map
`Πʳ i, [R i, C i]_[𝓖] →ₗ[A] Πʳ i, [R i, C i]_[𝓕]` where the `R i`
are `A`-modules and the `C i` are submodules.
-/
def RestrictedProduct.inclusionLinearMap
     {𝓕 𝓖 : Filter ι} (h : 𝓕 ≤ 𝓖) :
    Πʳ i, [R i, C i]_[𝓖] →ₗ[A] Πʳ i, [R i, C i]_[𝓕] :=
  mapAlongLinearMap R R id h (fun _ ↦ .id)
  (Filter.Eventually.of_forall <| fun _ _ ↦ id)

lemma inclusionLinearMap_apply {𝓕 𝓖 : Filter ι} (h : 𝓕 ≤ 𝓖) (x : Πʳ i, [R i, C i]_[𝓖]) :
  inclusionLinearMap A R C h x = ⟨x.1, x.2.filter_mono h⟩ := rfl

end modules

variable {ι : Type*}
variable {ℱ : Filter ι}
    {G H : ι → Type*}
    {C : (i : ι) → Set (G i)}
    {D : (i : ι) → Set (H i)}

namespace RestrictedProduct

section supports

variable {S T : ι → Type*} -- subobject types
variable [Π i, SetLike (S i) (G i)] [Π i, SetLike (T i) (H i)]
variable {A : Π i, S i} {B : Π i, T i}

-- this should all be for dependent functions

variable [(i : ι) → One (G i)] in
/-- The support of an element of a restricted product of monoids (or more generally,
objects with a 1. The support is the components which aren't 1.)
-/
@[to_additive
/-- The support of an element of a restricted product of additive monoids (or more generally,
objects with a 0. The support is the components which aren't 0. -/]
def mulSupport (u : Πʳ i, [G i, A i]) : Set ι :=
  {i : ι | u i ≠ 1}

variable [(i : ι) → One (G i)] in
@[to_additive (attr := simp)]
lemma not_mem_mulSupport {u : Πʳ i, [G i, A i]} (i : ι) :
  i ∉ mulSupport u ↔ u i = 1 := by simp [mulSupport]

variable [(i : ι) → Monoid (G i)] [∀ i, SubmonoidClass (S i) (G i)] in
@[to_additive]
lemma mul_comm_of_disjoint_mulSupport {u v : Πʳ i, [G i, A i]}
    (h : mulSupport u ∩ mulSupport v = ∅) : u * v = v * u := by
  ext i
  obtain hi | hi : i ∉ u.mulSupport ∨ i ∉ v.mulSupport := by
    rw [Set.ext_iff] at h
    specialize h i
    tauto
  · rw [not_mem_mulSupport] at hi
    simp [hi]
  · rw [not_mem_mulSupport] at hi
    simp [hi]

variable [(i : ι) → Monoid (G i)] [∀ i, SubmonoidClass (S i) (G i)] in
@[to_additive]
lemma mulSupport_mul_subset {u v : Πʳ i, [G i, A i]} {J : Set ι} (hu : mulSupport u ⊆ J)
    (hv : mulSupport v ⊆ J) : mulSupport (u * v) ⊆ J := by
  intro i hi
  contrapose! hi
  simp [not_mem_mulSupport, (not_mem_mulSupport i).1 (fun a ↦ hi (hu a)),
    (not_mem_mulSupport i).1 (fun a ↦ hi (hv a))]

variable [(i : ι) → Group (G i)] [∀ i, SubgroupClass (S i) (G i)] in
@[to_additive (attr := simp)]
lemma mulSupport_inv {u : Πʳ i, [G i, A i]} : mulSupport u⁻¹ = mulSupport u := by
  ext i
  simp only [mulSupport]
  exact inv_ne_one

variable [(i : ι) → Monoid (G i)] [∀ i, SubmonoidClass (S i) (G i)]
    {T : Type*} [SetLike T (Πʳ i, [G i, A i])]
    [SubmonoidClass T (Πʳ i, [G i, A i])] in
/-- A submonoid `U` of a resticted product of monoids is a product at `i` if
`U` can be written as Uᵢ × Uⁱ with Uᵢ supported at the i'th component and Uⁱ supported
away from `i`.
-/
def SubmonoidClass.isProductAt (U : T) (i : ι) : Prop :=
  ∀ u ∈ U, ∃ uᵢ, uᵢ ∈ U ∧ ∃ uᵢ', uᵢ' ∈ U ∧ u = uᵢ * uᵢ' ∧ mulSupport uᵢ ⊆ {i} ∧ i ∉ mulSupport uᵢ'

variable [(i : ι) → Group (G i)] [∀ i, SubgroupClass (S i) (G i)]
    {T : Type*} [SetLike T (Πʳ i, [G i, A i])]
    [SubgroupClass T (Πʳ i, [G i, A i])] in
open scoped Pointwise in
/--
If `U` is a product at `i` and `g` is supported at `i` then `UgU` can be written as
a disjoint union of cosets `gᵢU` with the `gᵢ` supported at `i`.
-/
lemma mem_coset_and_mulSupport_subset_of_isProductAt
    {U : T} (i : ι) (g : Πʳ i, [G i, A i])
    (hU : SubmonoidClass.isProductAt U i) (hg : mulSupport g ⊆ {i}) (γ : Πʳ i, [G i, A i])
    (hγ : γ ∈ U * g • (U : Set (Πʳ i, [G i, A i]))) :
    ∃ δ, δ ∈ γ • (U : Set (Πʳ i, [G i, A i])) ∧ mulSupport δ ⊆ {i} := by
  obtain ⟨u, hu, _, ⟨v, hv, rfl⟩, rfl⟩ := hγ
  obtain ⟨uᵢ, huᵢU, uᵢ', huᵢ'U, rfl, huᵢ, huᵢ'⟩ := hU u hu
  refine ⟨uᵢ * g, ⟨v⁻¹ * uᵢ'⁻¹, mul_mem (inv_mem hv) (inv_mem huᵢ'U), by
    have hcomm : g * uᵢ'⁻¹ = uᵢ'⁻¹ * g := mul_comm_of_disjoint_mulSupport <| by
      rw [mulSupport_inv]
      -- X ⊆ {i}, i ∉ Y => X ∩ Y = ∅
      rw [Set.eq_empty_iff_forall_notMem]
      intro j ⟨hj1, hj2⟩
      apply huᵢ'
      apply hg at hj1
      simp_all
    simp only [smul_eq_mul, mul_assoc, mul_inv_cancel_left, hcomm]⟩,
    mulSupport_mul_subset huᵢ hg⟩

/-- For a cofinite restricted product `Πʳ i, [G i, A i]`, `indexSupport` is the finite set of
indices for which `u ∉ A i`. -/
noncomputable
def indexSupport (u : Πʳ i, [G i, A i]) : Finset ι :=
  Set.Finite.toFinset (s := {x | u x ∉ A x}) (by simpa using u.2)

@[simp]
theorem mem_indexSupport_iff {u : Πʳ i, [G i, A i]} {i : ι} :
    i ∈ indexSupport u ↔ u i ∉ A i := by
  simp [indexSupport]

end supports

section components

variable {ι₂ : Type*} {f : ι₂ → ι} {𝒢 : Filter ι₂}
variable {G₂ : ι₂ → Type*} {C₂ : (i : ι₂) → Set (G₂ i)}
variable (hf : 𝒢 = Filter.comap f ℱ)
variable (φ : Πʳ i, [G i, C i]_[ℱ] → Πʳ i, [G₂ i, C₂ i]_[𝒢])
variable (g : (j : ι₂) → G (f j) → G₂ j) (hcomponent : ∀ x j, φ x j = g j (x (f j)))

include hcomponent in
variable {φ} {g} in
lemma components_comp_coe_eq_coe_apply : (fun a j ↦ g j (a (f j))) ∘ (⇑) = (⇑) ∘ φ := by
  ext x i
  simp [hcomponent]

lemma exists_update (x : Πʳ i, [G i, C i]_[ℱ]) (i : ι) (a : G i)
    (h : {i}ᶜ ∈ ℱ) : ∃ y : Πʳ i, [G i, C i]_[ℱ], y i = a ∧ ∀ j ≠ i, y j = x j := by
  classical
  exact ⟨⟨fun j ↦ if hj : j = i then hj ▸ a else x j, by
    filter_upwards [h, x.2] with j (hj : j ≠ i)
    aesop⟩, by
    aesop⟩

variable (C) in
lemma exists_apply_eq [∀ i, Nonempty (C i)] (i : ι) (a : G i) (h : {i}ᶜ ∈ ℱ) :
    ∃ x : Πʳ i, [G i, C i]_[ℱ], x i = a := by
  let y : Πʳ i, [G i, C i]_[ℱ] := ⟨fun i ↦ (Classical.ofNonempty : C i),
    Filter.Eventually.of_forall (fun x ↦ Subtype.coe_prop _)⟩
  obtain ⟨x, hx, -⟩ := exists_update y i a h
  exact ⟨x, hx⟩

variable [∀ j, Nonempty (C₂ j)]

include hcomponent in
lemma surjective_components_of_surjective (hφ : Function.Surjective φ) (j : ι₂) (hj : {j}ᶜ ∈ 𝒢) :
    Function.Surjective (g j) := by
  intro y
  obtain ⟨y', hy'⟩ := exists_apply_eq C₂ j y hj
  obtain ⟨x, hx⟩ := hφ y'
  use (x (f j))
  rw [← hcomponent, hx, hy']

include hf hcomponent in
lemma eventually_surjOn_of_surjective (hφ : Function.Surjective φ) :
    ∀ᶠ (j : ι₂) in 𝒢, Set.SurjOn (g j) (C (f j)) (C₂ j) := by
  classical
  have p (j : ι₂) : ∃ (y : C₂ j), (∃ (x : C (f j)), g j x = y)
       → Set.SurjOn (g j) (C (f j)) (C₂ j) := by
    by_cases hsurj : Set.SurjOn (g j) (C (f j)) (C₂ j)
    · exact ⟨Classical.choice inferInstance, fun _ ↦ hsurj⟩
    · rw [Set.SurjOn, Set.not_subset_iff_exists_mem_notMem] at hsurj
      obtain ⟨y, hy, hne⟩ := hsurj
      exact ⟨⟨y, hy⟩, fun ⟨⟨x, hx⟩, hxy⟩ ↦ absurd ⟨x, hx, hxy⟩ hne⟩
  choose y' hy' using p
  set y : Πʳ i, [G₂ i, C₂ i]_[𝒢] :=
    ⟨fun i ↦ y' i, Filter.Eventually.of_forall (fun i ↦ (y' i).prop)⟩ with hy
  obtain ⟨x, hx⟩ := hφ y
  rw [hf, Filter.eventually_comap]
  filter_upwards [x.eventually]
  rintro - hx' j rfl
  apply hy'
  use ⟨x (f j), hx'⟩
  rw [← hcomponent, hx, hy, mk_apply]

end components

section structure_map

/-- The structure map for a restricted product of monoids is a `MonoidHom`. -/
@[to_additive
/-- The structure map for a restricted product of AddMonoids is an `AddMonoidHom`. -/]
def structureMapMonoidHom {ι : Type*} (M : ι → Type*) [(i : ι) → Monoid (M i)]
    {S : ι → Type*} [∀ i, SetLike (S i) (M i)] [∀ i, SubmonoidClass (S i) (M i)] (A : Π i, S i)
    (𝓕 : Filter ι) : ((i : ι) → (A i)) →* Πʳ (i : ι), [M i, Submonoid.ofClass (A i)]_[𝓕] where
  toFun := structureMap M (A ·) 𝓕
  map_one' := rfl
  map_mul' := by intros; rfl

/-- The structure map for a restricted product of ring. -/
def structureMapRingHom {ι : Type*} (M : ι → Type*) [(i : ι) → Ring (M i)]
    {S : ι → Type*} [∀ i, SetLike (S i) (M i)] [∀ i, SubringClass (S i) (M i)] (A : Π i, S i)
    (𝓕 : Filter ι) : ((i : ι) → (A i)) →+* Πʳ (i : ι), [M i, Subring.ofClass (A i)]_[𝓕] where
  toFun := structureMap M (A ·) 𝓕
  map_zero' := rfl
  map_one' := rfl
  map_mul' := by intros; rfl
  map_add' := by intros; rfl

/-- The subring `∏ i, A i` inside `Πʳ i, [R i, A i]_[𝓕]`. -/
def structureSubring {ι : Type*} (R : ι → Type*) {S : ι → Type*}
    (A : (i : ι) → (S i)) (𝓕 : Filter ι) [(i : ι) → SetLike (S i) (R i)] [(i : ι) → Ring (R i)]
    [(i : ι) → SubringClass (S i) (R i)] :
    Subring (Πʳ i, [R i, A i]_[𝓕]) :=
  (RestrictedProduct.structureMapRingHom R A 𝓕).range

@[simp]
theorem mem_structureSubring_iff {ι : Type*} {R : ι → Type*} {S : ι → Type*}
    {A : (i : ι) → (S i)} {𝓕 : Filter ι} [(i : ι) → SetLike (S i) (R i)] [(i : ι) → Ring (R i)]
    [(i : ι) → SubringClass (S i) (R i)] {x : Πʳ i, [R i, A i]_[𝓕]} :
    x ∈ RestrictedProduct.structureSubring R A 𝓕 ↔
      ∀ i, x i ∈ A i := by
  rw [RestrictedProduct.structureSubring]
  change x ∈ Set.range (RestrictedProduct.structureMap _ _ _) ↔ _
  rw [RestrictedProduct.range_structureMap]
  aesop

end structure_map

section single

/-

## Maps from a factor into a restricted product

-/

variable {ι : Type*} [DecidableEq ι] (A : ι → Type*) {𝓕 : Filter ι}
    {S : ι → Type*}
    [(i : ι) → SetLike (S i) (A i)] {B : (i : ι) → S i} (j : ι) [(i : ι) → AddMonoid (A i)]
    [∀ (i : ι), AddSubmonoidClass (S i) (A i)]

/-- The inclusion from a factor into a restricted product of additive groups. -/
noncomputable def singleAddMonoidHom (j : ι) : A j →+ Πʳ i, [A i, B i] where
  toFun x := ⟨Pi.single j x, by
    simpa using (Set.finite_singleton j).subset fun i _ ↦ by by_cases h : i = j <;> simp_all⟩
  map_zero' := by ext; simp
  map_add' _ _ := by ext; simp [Pi.single_add]

end single

end RestrictedProduct
