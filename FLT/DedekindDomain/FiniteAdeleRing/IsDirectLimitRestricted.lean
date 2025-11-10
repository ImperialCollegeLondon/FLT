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

instance : Nonempty 𝓕.setsᵒᵈ := by
  use ⊤
  simp

theorem principal_filter_order {S₁ S₂ : 𝓕.setsᵒᵈ} (h : S₁ ≤ S₂) :
    (𝓟 S₂.1 : Filter ι) ≤ 𝓟 S₁.1 := by
  simp only [le_principal_iff, mem_principal]; exact h

theorem filter_bot :
    ∀ S : 𝓕.setsᵒᵈ, 𝓕 ≤ (𝓟 S.1 : Filter ι) := by
  intro S
  simp only [le_principal_iff]
  exact S.2

open scoped RestrictedProduct

variable {R : ι → Type*} {A : ι → Type*} [Π i, SetLike (A i) (R i)] {C : Π i, A i}

variable (C) in
/-- This is (isomorphic to) `(Π i ∈ S, R i) × (Π i ∉ S, A i)` -/
def mem_A_away_from_S (S : 𝓕.setsᵒᵈ) : Type _ :=
  Πʳ i, [R i, C i]_[𝓟 S.1]

/-- The inclusions between `mem_A_away_from_S` which will form the directed system. -/
def inclusion (S₁ S₂ : 𝓕.setsᵒᵈ) (h : S₁ ≤ S₂) :
    mem_A_away_from_S C S₁ → mem_A_away_from_S C S₂ :=
  RestrictedProduct.inclusion _ _ (principal_filter_order h)

instance directed_system :
    @DirectedSystem (𝓕.setsᵒᵈ) _ (mem_A_away_from_S C) (inclusion) where
  map_self _ _ := rfl
  map_map _ _ _ _ _ _ := rfl

/-- The maps from the directed system to the actual restricted product. -/
def inclusion_to_restrictedProduct (S : 𝓕.setsᵒᵈ) :
    mem_A_away_from_S C S → Πʳ i, [R i, C i]_[𝓕] :=
  RestrictedProduct.inclusion _ _ (filter_bot S)

end RestrictedProduct

open scoped RestrictedProduct TensorProduct IsDirectLimit

variable {A : Type*} [CommRing A] {ι : Type*} {R : ι → Type*} {ℱ : Filter ι}
  [Π i, AddCommGroup (R i)] [∀ i, Module A (R i)] {C : ∀ i, Submodule A (R i)} {M : Type*}
  [AddCommGroup M] [Module A M] [Module.FinitePresentation A M] (S : ℱ.setsᵒᵈ)

open Set Filter RestrictedProduct

instance add (S : ℱ.setsᵒᵈ) :
  AddCommMonoid (mem_A_away_from_S C S) := by
  dsimp [mem_A_away_from_S]
  exact AddCommGroup.toDivisionAddCommMonoid.toAddCommMonoid

instance module' (S : ℱ.setsᵒᵈ) :
  Module A (mem_A_away_from_S C S) := by
  dsimp [mem_A_away_from_S]
  exact instModuleCoeOfSMulMemClass R

/-- Linear map version of `inclusion`. -/
def inclusion_module (S₁ S₂ : ℱ.setsᵒᵈ) (h : S₁ ≤ S₂) :
    mem_A_away_from_S C S₁ →ₗ[A]
      mem_A_away_from_S C S₂ where
  toFun := inclusion S₁ S₂ h
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

instance : DirectedSystem (mem_A_away_from_S C) fun x1 x2 x3 ↦
  (inclusion_module (ℱ := ℱ) (C:= C) x1 x2 x3) := directed_system

lemma inclusion_module_apply (S₁ S₂ : ℱ.setsᵒᵈ) (h : S₁ ≤ S₂) (x : mem_A_away_from_S C S₁) :
  inclusion_module S₁ S₂ h x = ⟨x.1, x.2.filter_mono (principal_filter_order h)⟩ := rfl

/-- Linear map version of `inclusion_to_restrictedProduct` -/
def inclusion_to_restricted_product_module (S : ℱ.setsᵒᵈ) :
  mem_A_away_from_S C S →ₗ[A] Πʳ i, [R i, C i]_[ℱ] where
  toFun := inclusion_to_restrictedProduct S
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

instance directed : IsDirected (ℱ.setsᵒᵈ) (· ≤ ·) := by
  refine { directed := ?_ }
  intro Si Sj
  obtain ⟨Si, hi⟩ := Si
  obtain ⟨Sj, hj⟩ := Sj
  use ⟨Si ∩ Sj, ℱ.inter_sets hi hj⟩, inter_subset_left, inter_subset_right

instance RestrictedProductIsDirectLimit :
  IsDirectLimit (mem_A_away_from_S C)
  Πʳ i, [R i, C i]_[ℱ] (inclusion_module · · ·)
  (inclusion_to_restricted_product_module · ·) where
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
    have : { i : ι | r.1 i ∈ (C i : Set (R i)) } ∈ ℱ.sets := by
      simp only [Filter.mem_sets]
      exact b
    use ⟨{ i : ι | r.1 i ∈ (C i : Set (R i)) }, this⟩
    apply RestrictedProduct.exists_inclusion_eq_of_eventually
    simp only [SetLike.mem_coe, eventually_principal, mem_setOf_eq]
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

variable {ι : Type*} (R : ι → Type*) {ℱ : Filter ι} (A : Type*) [CommRing A]

open scoped RestrictedProduct TensorProduct

open Filter

section module

/-- Module equivalence version of `principalEquivProd`. -/
noncomputable def principal [Π i, AddCommGroup (R i)]
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

end module

end RestrictedProduct
