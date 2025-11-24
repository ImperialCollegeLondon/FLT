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

/-- A linear map version of `RestrictedProduct.inclusion` :
if `𝓕 ≤ 𝓖` then there's a linear map
`Πʳ i, [R i, C i]_[𝓖] →ₗ[A] Πʳ i, [R i, C i]_[𝓕]` where the `R i`
are `A`-modules and the `C i` are submodules.
-/
def inclusionLinearMap {𝓕 𝓖 : Filter ι} (h : 𝓕 ≤ 𝓖) :
    Πʳ i, [R i, C i]_[𝓖] →ₗ[A] Πʳ i, [R i, C i]_[𝓕] :=
  mapAlongLinearMap R R id h (fun _ ↦ .id)
  (Filter.Eventually.of_forall <| fun _ _ ↦ id)

lemma inclusionLinearMap_apply {𝓕 𝓖 : Filter ι} (h : 𝓕 ≤ 𝓖) (x : Πʳ i, [R i, C i]_[𝓖]) :
  inclusionLinearMap h x = ⟨x.1, x.2.filter_mono h⟩ := rfl

instance : DirectedSystem (fun (S : ℱ.setsᵒᵈ) ↦ Πʳ i, [R i, C i]_[𝓟 S.1])
    fun _ _ h ↦ (inclusionLinearMap <| monotone_principal h) :=
  RestrictedProduct.instDirectedSystem

instance directed : IsDirected (ℱ.setsᵒᵈ) (· ≤ ·) where
    directed Si Sj := by
      obtain ⟨Si, hi⟩ := Si
      obtain ⟨Sj, hj⟩ := Sj
      use ⟨Si ∩ Sj, ℱ.inter_sets hi hj⟩, inter_subset_left, inter_subset_right

end inclusion

variable {ι : Type*} (R : ι → Type*) (S : Set ι) [∀ i, Decidable (i ∈ S)] (A : (i : ι) → Set (R i))

open scoped Filter

section type

/-- The canonical isomorphism between `Πʳ i, [R i, A i]_[𝓟 S]` and
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
  right_inv x := by aesop

end type

variable {T : ι → Type*} [Π i, SetLike (T i) (R i)] {A : Π i, T i}

section monoid

-- TODO move to FLT/Mathlib
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

-- TODO move to FLT/Mathlib
/-- Module equivalence version of `principalEquivProd`. -/
noncomputable def principalLinearEquivProd [Π i, AddCommGroup (R i)]
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
    dsimp [inclusionLinearMap]
    have : { i : ι | r.1 i ∈ (C i : Set (R i)) } ∈ (iInf 𝓖) := hℱ ▸ r.property
    obtain ⟨j, hj⟩ := (Filter.mem_iInf_of_directed h𝓖.directed_ge _).mp this
    use j
    apply RestrictedProduct.exists_inclusion_eq_of_eventually _ _ _ hj
    rw [hℱ]
    exact iInf_le_iff.mpr fun b a ↦ a j
  compatibility i j hij x := by
    dsimp [inclusionLinearMap, RestrictedProduct.inclusion, RestrictedProduct.inclusion]
    exact Subtype.ext rfl

instance instIsDirectLimit' : IsDirectLimit (M := fun (S : ℱ.setsᵒᵈ) ↦ Πʳ i, [R i, C i]_[𝓟 S.1])
    ((fun _ _ h ↦ inclusionLinearMap <| monotone_principal h))
    (fun S ↦ inclusionLinearMap <| Filter.le_principal_iff.2 S.2) := by
  apply instIsDirectLimit
  · intro i j hij
    simpa only [le_principal_iff, mem_principal]
  · exact eq_iInf_of_mem_iff_exists_mem (fun {s} ↦ ⟨fun h ↦ ⟨⟨s, h⟩, subset_refl s⟩,
      fun ⟨i, hi⟩ ↦ Filter.mem_of_superset i.2 hi⟩)

end module

end RestrictedProduct
#lint
