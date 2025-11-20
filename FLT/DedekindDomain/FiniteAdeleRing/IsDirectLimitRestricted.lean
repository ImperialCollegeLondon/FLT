/-
Copyright (c) 2025 Madison Crim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Madison Crim
-/

import FLT.Mathlib.Topology.Algebra.RestrictedProduct.Basic
import FLT.DedekindDomain.FiniteAdeleRing.TensorPi
import FLT.Mathlib.Algebra.IsDirectLimit

namespace RestrictedProduct

open Set Filter

section directedSystem

variable {ι : Type*} {𝓕 : Filter ι}

instance : Nonempty 𝓕.setsᵒᵈ := ⟨⊤, by simp⟩

variable {R : ι → Type*} {A : ι → Type*} [Π i, SetLike (A i) (R i)] {C : Π i, A i}

instance instDirectedSystem :
    DirectedSystem (fun (S : 𝓕.setsᵒᵈ) ↦ Πʳ i, [R i, C i]_[𝓟 S.1])
      (fun _ _ h ↦ RestrictedProduct.inclusion _ _ <| monotone_principal h) where
  map_self _ _ := rfl
  map_map _ _ _ _ _ _ := rfl

end directedSystem

section inclusion

open scoped RestrictedProduct TensorProduct IsDirectLimit

variable {A : Type*} [CommRing A] {ι : Type*} {R : ι → Type*} {ℱ : Filter ι}
  [Π i, AddCommGroup (R i)] [∀ i, Module A (R i)] {C : ∀ i, Submodule A (R i)} {M : Type*}
  [AddCommGroup M] [Module A M] [Module.FinitePresentation A M] (S : ℱ.setsᵒᵈ)

open Set Filter RestrictedProduct

/-- Linear map version of `inclusion`. -/
def inclusionLinearMap {S₁ S₂ : ℱ.setsᵒᵈ} (h : S₁ ≤ S₂) :
    Πʳ i, [R i, C i]_[𝓟 S₁.1] →ₗ[A] Πʳ i, [R i, C i]_[𝓟 S₂.1] :=
  mapAlongLinearMap R R id (tendsto_principal_principal.2 h) (fun _ ↦ .id)
  (Filter.Eventually.of_forall <| fun _ _ ↦ id)

lemma inclusionLinearMap_apply {S₁ S₂ : ℱ.setsᵒᵈ} (h : S₁ ≤ S₂) (x : Πʳ i, [R i, C i]_[𝓟 S₁.1]) :
  inclusionLinearMap h x = ⟨x.1, x.2.filter_mono (monotone_principal h)⟩ := rfl

instance : DirectedSystem (fun (S : ℱ.setsᵒᵈ) ↦ Πʳ i, [R i, C i]_[𝓟 S.1]) fun _ _ x3 ↦
  (inclusionLinearMap (ℱ := ℱ) (C := C) x3) := RestrictedProduct.instDirectedSystem

/-- Linear map version of `inclusion_to_restrictedProduct` -/
def coeLinearMap (S : ℱ.setsᵒᵈ) :
   Πʳ i, [R i, C i]_[𝓟 S.1] →ₗ[A] Πʳ i, [R i, C i]_[ℱ] where
  toFun := RestrictedProduct.inclusion _ _ (Filter.le_principal_iff.2 S.2)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

instance directed : IsDirected (ℱ.setsᵒᵈ) (· ≤ ·) := by
  refine { directed := ?_ }
  intro Si Sj
  obtain ⟨Si, hi⟩ := Si
  obtain ⟨Sj, hj⟩ := Sj
  use ⟨Si ∩ Sj, ℱ.inter_sets hi hj⟩, inter_subset_left, inter_subset_right

end inclusion

variable {ι : Type*} (R : ι → Type*) (S : Set ι) [∀ i, Decidable (i ∈ S)] (A : (i : ι) → Set (R i))

open scoped Filter

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
    ext
    simp
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
    map_smul' _ _ := rfl

variable [Π i, AddCommGroup (R i)] [∀ i, Module A (R i)] {C : ∀ i, Submodule A (R i)}

/-- If `𝓕 ≤ 𝓖`, the restricted product `Πʳ i, [R i, A i]_[𝓖]` is naturally included in
`Πʳ i, [R i, A i]_[𝓕]`. This is the corresponding map. -/
def linclusion
    {ι : Type*} {R₀ : Type*} (R : ι → Type*) [Semiring R₀] [∀ i, AddCommMonoid (R i)]
    [∀ i, Module R₀ (R i)] (A : (i : ι) → Submodule R₀ (R i)) {ℱ 𝓖 : Filter ι}
    (h : ℱ ≤ 𝓖) : Πʳ i, [R i, A i]_[𝓖] →ₗ[R₀] Πʳ i, [R i, A i]_[ℱ] where
  toFun := inclusion R (A ·) h
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

instance {I : Type*} [Preorder I] (𝓖 : I → Filter ι) (h𝓖 : Antitone 𝓖) :
    DirectedSystem (fun x ↦ Πʳ (i : ι), [R i, ↑(C i)]_[𝓖 x]) (linclusion _ _ <| @h𝓖 · · ·) where
  map_self _ _ := rfl
  map_map _ _ _ _ _ _ := rfl

instance instIsDirectLimit {I : Type*} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (𝓖 : I → Filter ι) (h𝓖 : Antitone 𝓖) (hℱ : ℱ = iInf 𝓖) :
    IsDirectLimit (linclusion R C <| @h𝓖 · · ·)
    (linclusion R C <| hℱ.trans_le <| iInf_le 𝓖 ·) where
  inj Sᵢ Sⱼ mi mj hmij := by
    obtain ⟨Sₖ, hik, hjk⟩ := @directed_of _ (· ≤ ·) _ Sᵢ Sⱼ
    refine ⟨Sₖ, hik, hjk, ?_⟩
    apply Subtype.ext
    injection hmij
  surj r := by
    dsimp [coeLinearMap]
    have : { i : ι | r.1 i ∈ (C i : Set (R i)) } ∈ (iInf 𝓖) := hℱ ▸ r.property
    obtain ⟨j, hj⟩ := (Filter.mem_iInf_of_directed h𝓖.directed_ge _).mp this
    use j
    apply RestrictedProduct.exists_inclusion_eq_of_eventually _ _ _ hj
    rw [hℱ]
    exact iInf_le_iff.mpr fun b a ↦ a j
  compatibility i j hij x := by
    dsimp [coeLinearMap, RestrictedProduct.inclusion, RestrictedProduct.inclusion]
    exact Subtype.ext rfl

instance instIsDirectLimit' : IsDirectLimit (M := fun (S : ℱ.setsᵒᵈ) ↦ Πʳ i, [R i, C i]_[𝓟 S.1])
    ((fun _ _ x3 ↦ inclusionLinearMap (ℱ := ℱ) (C := C) x3)) (coeLinearMap ·) := by
  apply instIsDirectLimit
  · intro i j hij
    simpa only [le_principal_iff, mem_principal]
  · exact eq_iInf_of_mem_iff_exists_mem (fun {s} ↦ ⟨fun h ↦ ⟨⟨s, h⟩, subset_refl s⟩,
      fun ⟨i, hi⟩ ↦ Filter.mem_of_superset i.2 hi⟩)

end module

end RestrictedProduct
