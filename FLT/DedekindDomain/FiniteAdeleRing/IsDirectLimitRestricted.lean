/-
Copyright (c) 2025 Madison Crim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Madison Crim
-/

import FLT.Mathlib.Topology.Algebra.RestrictedProduct.Basic
import FLT.DedekindDomain.FiniteAdeleRing.TensorPi
import FLT.DedekindDomain.FiniteAdeleRing.IsDirectLimit

section RestrictedProduct

open Set Filter

variable {ι : Type*} {𝓕 : Filter ι}

variable (𝓕) in
/-- The complements of sets in a `Filter`.
E.g. for the cofinite filter, these are just the finite subsets. -/
def Filter.complement : Set (Set ι) := (fun S => Sᶜ) '' 𝓕.sets

theorem principal_filter_order {S₁ S₂ : 𝓕.complement} (h : S₁ ≤ S₂) :
    (𝓟 S₂ᶜ : Filter ι) ≤ 𝓟 S₁ᶜ := by
  simp only [le_principal_iff, mem_principal, compl_subset_compl]; exact h

theorem filter_bot :
    ∀ S : 𝓕.complement, 𝓕 ≤ (𝓟 Sᶜ : Filter ι) := by
  intro S
  simp only [le_principal_iff]
  refine Filter.mem_sets.mp ?_
  have h : 𝓕.sets = (fun S => Sᶜ) '' (𝓕.complement) := by
    rw[complement]
    exact Eq.symm (compl_compl_image 𝓕.sets)
  rw[h]
  simp

open scoped RestrictedProduct

variable {R : ι → Type*} {A : ι → Type*} [Π i, SetLike (A i) (R i)] {C : Π i, A i}

variable (C) in
/-- This is (isomorphic to) `(Π i ∈ S, R i) × (Π i ∉ S, A i)` -/
def mem_A_away_from_S (S : 𝓕.complement) : Type _ :=
  Πʳ i, [R i, C i]_[𝓟 Sᶜ]

/-- The inclusions between `mem_A_away_from_S` which will form the directed system. -/
def inclusion (S₁ S₂ : 𝓕.complement) (h : S₁ ≤ S₂) :
    mem_A_away_from_S C S₁ → mem_A_away_from_S C S₂ :=
  RestrictedProduct.inclusion _ _ (principal_filter_order h)

instance directed_system :
    @DirectedSystem (𝓕.complement) _ (mem_A_away_from_S C) (inclusion) where
  map_self _ _ := rfl
  map_map _ _ _ _ _ _ := rfl

/-- The maps from the directed system to the actual restricted product. -/
def inclusion_to_restrictedProduct (S : 𝓕.complement) :
    mem_A_away_from_S C S → Πʳ i, [R i, C i]_[𝓕] :=
  RestrictedProduct.inclusion _ _ (filter_bot S)

end RestrictedProduct

open scoped RestrictedProduct TensorProduct Module.IsDirectLimit

variable {A : Type*} [CommRing A] {ι : Type*} {R : ι → Type*} {ℱ : Filter ι}
  [Π i, AddCommGroup (R i)] [∀ i, Module A (R i)] {C : ∀ i, Submodule A (R i)} {M : Type*}
  [AddCommGroup M] [Module A M] [Module.FinitePresentation A M] (S : Filter.complement ℱ)

open Set Filter RestrictedProduct

instance add (S : ℱ.complement) :
  AddCommMonoid (mem_A_away_from_S C S) := by
  dsimp [mem_A_away_from_S]
  exact AddCommGroup.toDivisionAddCommMonoid.toAddCommMonoid

instance module' (S : ℱ.complement) :
  Module A (mem_A_away_from_S C S) := by
  dsimp [mem_A_away_from_S]
  exact instModuleCoeOfSMulMemClass R

/-- Linear map version of `inclusion`. -/
def inclusion_module (S₁ S₂ : ℱ.complement) (h : S₁ ≤ S₂) :
    mem_A_away_from_S C S₁ →ₗ[A]
      mem_A_away_from_S C S₂ where
  toFun := inclusion S₁ S₂ h
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma inclusion_module_apply (S₁ S₂ : ℱ.complement) (h : S₁ ≤ S₂) (x : mem_A_away_from_S C S₁) :
  inclusion_module S₁ S₂ h x = ⟨x.1, x.2.filter_mono (principal_filter_order h)⟩ := rfl

/-- Linear map version of `inclusion_to_restrictedProduct` -/
def inclusion_to_restricted_product_module (S : ℱ.complement) :
  mem_A_away_from_S C S →ₗ[A] Πʳ i, [R i, C i]_[ℱ] where
  toFun := inclusion_to_restrictedProduct S
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

instance directed : IsDirected (ℱ.complement) (· ≤ ·) := by
  refine { directed := ?_ }
  intro Si Sj
  obtain ⟨Si, hi⟩ := Si
  obtain ⟨Sj, hj⟩ := Sj
  let c := Si ∪ Sj
  have : c ∈ ℱ.complement := by
    unfold Filter.complement at hi hj ⊢
    simp only [mem_image, Filter.mem_sets] at hi hj ⊢
    obtain ⟨si, hsi⟩ := hi
    obtain ⟨sj, hsj⟩ := hj
    use si ∩ sj
    constructor
    · exact ℱ.inter_sets hsi.1 hsj.1
    · unfold c
      rw [compl_inter, hsi.2, hsj.2]
  use ⟨c, this⟩
  constructor <;>
  simp [c]

instance RestrictedProductIsDirectLimit :
  Module.IsDirectLimit (mem_A_away_from_S C)
  Πʳ i, [R i, C i]_[ℱ] (inclusion_module (ℱ := ℱ))
  (inclusion_to_restricted_product_module ) where
  inj Sᵢ Sⱼ mi mj hmij := by
    obtain ⟨Sₖ, hik, hjk⟩ := @directed_of _ (· ≤ ·) directed Sᵢ Sⱼ
    refine ⟨Sₖ, hik, hjk, ?_⟩
    dsimp [inclusion_module,_root_.inclusion, RestrictedProduct.inclusion]
    dsimp [inclusion_to_restricted_product_module, inclusion_to_restrictedProduct,
      RestrictedProduct.inclusion] at hmij
    apply Subtype.ext
    simp only
    injection hmij
  surj r := by
    dsimp [inclusion_to_restricted_product_module, inclusion_to_restrictedProduct]
    let b:= r.property
    let c:= r.1
    have : { i : ι | r.1 i ∈ (C i : Set (R i)) }ᶜ ∈ ℱ.complement := by
      rw [complement]
      simp only [mem_image, Filter.mem_sets]
      refine ⟨{ i : ι | r.1 i ∈ (C i : Set (R i)) }, r.property, ?_⟩
      rfl
    use ⟨{ i : ι | r.1 i ∈ (C i : Set (R i)) }ᶜ, this⟩
    apply RestrictedProduct.exists_inclusion_eq_of_eventually
    simp only [SetLike.mem_coe, compl_compl, eventually_principal, mem_setOf_eq]
    exact fun x a ↦ a
  compatibility i j hij x := by
    dsimp [inclusion_to_restricted_product_module, inclusion_to_restrictedProduct,
    inclusion_module,_root_.inclusion, inclusion_module,RestrictedProduct.inclusion]
    exact Subtype.ext rfl

variable {ι : Type*} (R : ι → Type*) (S : Set ι) [∀ i, Decidable (i ∈ S)] (A : (i : ι) → Set (R i))

open scoped Filter

namespace RestrictedProduct

section type

/-- This canonical isomorphism between `Πʳ i, [R i, A i]_[𝓟 S]` and
`(Π i ∈ S, R i) × (Π i ∉ S, A i)`
-/
def principalEquivProd : Πʳ i, [R i, A i]_[𝓟 S] ≃
    (Π i : {i // i ∈ S}, A i) × (Π i : {i // i ∉ S}, R i) where
  toFun x := (fun i ↦ ⟨x i, x.property i.property⟩, fun i ↦ x i)
  invFun y := ⟨fun i ↦ if hi : i ∈ S then y.1 ⟨i, hi⟩ else y.2 ⟨i, hi⟩,
  Filter.eventually_principal.mpr (fun i hi ↦ by simp only [hi]; exact (y.1 ⟨i, hi⟩).2)⟩
  left_inv x := by
    simp only [dite_eq_ite, ite_self]
    rfl
  right_inv x := by
    simp only [mk_apply, Subtype.coe_prop, ↓reduceDIte, Subtype.coe_eta]
    ext i
    · rfl
    · simp only [dif_neg i.property]

end type


variable {T : ι → Type*} [Π i, SetLike (T i) (R i)] {A : Π i, T i}

section monoid

/-- Monoid equivalence version of `principalEquivProd`. -/
@[to_additive /-- Additive monoid equivalence of principalEquivProd. -/]
def principalMulEquivProd [Π i, Monoid (R i)] [∀ i, SubmonoidClass (T i) (R i)] :
    Πʳ i, [R i, A i]_[𝓟 S] ≃* (Π i : {i // i ∈ S}, A i) × (Π i : {i // i ∉ S}, R i) where
  __ := principalEquivProd R S _
  map_mul' _ _ := rfl

end monoid

end RestrictedProduct

variable {ι : Type*} (R : ι → Type*) {ℱ : Filter ι} (A : Type*) [CommRing A]

open scoped RestrictedProduct TensorProduct

open Filter

/-- Module equivalence version of `principalEquivProd`. -/
noncomputable def RestrictedProduct.principal [Π i, AddCommGroup (R i)]
    [∀ i, Module A (R i)] {C : ∀ i, Submodule A (R i)}
    (S : Set ι) [∀ i, Decidable (i ∈ S)] :
   (Πʳ i, [R i, C i]_[𝓟 S]) ≃ₗ[A] ((Π i : {i // i ∈ S}, C i) ×
  (Π i : {i // i ∉ S}, R i)) where
    __ := principalAddEquivSum R S (A := C)
    map_smul' m x := by
      simp only [AddEquiv.toEquiv_eq_coe, Equiv.toFun_as_coe, EquivLike.coe_coe, RingHom.id_apply]
      dsimp [principalAddEquivSum, principalEquivProd]
      ext i
      · simp only [Pi.smul_apply, SetLike.coe_sort_coe, SetLike.val_smul]
      · simp only [Pi.smul_apply]

variable [Π i, AddCommGroup (R i)] [∀ i, Module A (R i)] (C : ∀ i, Submodule A (R i))

noncomputable instance : DecidableEq ℱ.complement := Classical.typeDecidableEq ↑ℱ.complement

instance : Nonempty ℱ.complement := by
  use ∅
  dsimp [complement]
  use Set.univ
  split_ands
  · exact Filter.univ_mem (f := ℱ)
  · simp only [compl_univ]

instance : DirectedSystem (mem_A_away_from_S C) fun x1 x2 x3 ↦
  ⇑(inclusion_module (ℱ := ℱ) (C:= C) x1 x2 x3) := directed_system
