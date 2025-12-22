/-
Copyright (c) 2025 Madison Crim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Madison Crim
-/

import FLT.Mathlib.Topology.Algebra.RestrictedProduct.Equiv
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

instance : DirectedSystem (fun (S : ℱ.setsᵒᵈ) ↦ Πʳ i, [R i, C i]_[𝓟 S.1])
    fun _ _ h ↦ (inclusionLinearMap A R C <| monotone_principal h) :=
  RestrictedProduct.instDirectedSystem

instance directed : IsDirected (ℱ.setsᵒᵈ) (· ≤ ·) where
    directed Si Sj := by
      obtain ⟨Si, hi⟩ := Si
      obtain ⟨Sj, hj⟩ := Sj
      use ⟨Si ∩ Sj, ℱ.inter_sets hi hj⟩, inter_subset_left, inter_subset_right

end inclusion

variable {ι : Type*} (R : ι → Type*) {ℱ : Filter ι} (A : Type*) [CommRing A]
variable [Π i, AddCommGroup (R i)] [∀ i, Module A (R i)] {C : ∀ i, Submodule A (R i)}

instance {I : Type*} [Preorder I] (𝓖 : I → Filter ι) (h𝓖 : Antitone 𝓖) :
    DirectedSystem (fun x ↦ Πʳ (i : ι), [R i, ↑(C i)]_[𝓖 x])
      (inclusionLinearMap A R C <| @h𝓖 · · ·) where
  map_self _ _ := rfl
  map_map _ _ _ _ _ _ := rfl

instance instIsDirectLimit {I : Type*} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (𝓖 : I → Filter ι) (h𝓖 : Antitone 𝓖) (hℱ : ℱ = iInf 𝓖) :
    IsDirectLimit (inclusionLinearMap A R C <| @h𝓖 · · ·)
    (inclusionLinearMap A R C <| hℱ.trans_le <| iInf_le 𝓖 ·) where
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
    ((fun _ _ h ↦ inclusionLinearMap A R C <| monotone_principal h))
    (fun S ↦ inclusionLinearMap A R C <| Filter.le_principal_iff.2 S.2) := by
  apply instIsDirectLimit
  exact eq_iInf_of_mem_iff_exists_mem (fun {s} ↦ ⟨fun h ↦ ⟨⟨s, h⟩, subset_refl s⟩,
    fun ⟨i, hi⟩ ↦ Filter.mem_of_superset i.2 hi⟩)

end RestrictedProduct
