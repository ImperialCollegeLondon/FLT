/-
Copyright (c) 2025 Matthew Jasper. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Jasper
-/

import FLT.Mathlib.Topology.Algebra.RestrictedProduct
import FLT.Mathlib.Topology.Algebra.Module.ModuleTopology
import FLT.Mathlib.Topology.Algebra.MulAction
import FLT.Mathlib.Algebra.Module.Submodule.Basic

namespace RestrictedProduct

-- mathlib#25715
variable {ι : Type*} {𝓕 : Filter ι} {A : ι → Type*} [∀ i, AddCommMonoid (A i)]
    {S : ι → Type*} [∀ i, SetLike (S i) (A i)] [∀ i, AddSubmonoidClass (S i) (A i)]
    {B : Π i, S i} in
/-- restricted product of additive commutative monoids is an additive commutative monoid -/
instance instAddCommMonoid: AddCommMonoid (Πʳ i, [A i, B i]_[𝓕]) :=
  DFunLike.coe_injective.addCommMonoid _ rfl (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)

-- mathlib#25715
variable {ι : Type*} {𝓕 : Filter ι} {A : ι → Type*} [∀ i, AddCommGroup (A i)]
    {S : ι → Type*} [∀ i, SetLike (S i) (A i)] [∀ i, AddSubgroupClass (S i) (A i)]
    {B : Π i, S i} in
/-- restricted product of additive commutative groups is an additive commutative group -/
instance instAddCommGroup: AddCommGroup (Πʳ i, [A i, B i]_[𝓕]) :=
  DFunLike.coe_injective.addCommGroup _ rfl (fun _ _ ↦ rfl) (fun _ ↦ rfl)
    (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)

variable {ι : Type*}
variable {R : ι → Type*} [Π i, Ring (R i)]
variable {S : ι → Type*} -- subring type
variable [Π i, SetLike (S i) (R i)] [∀ i, SubringClass (S i) (R i)]
variable {B : Π i, S i}
variable {ℱ : Filter ι}

variable {M : ι → Type*} [Π i, AddCommGroup (M i)] [Π i, Module (R i) (M i)]
variable {N : ι → Type*} -- submodule type
variable [Π i, SetLike (N i) (M i)] [∀ i, AddSubgroupClass (N i) (M i)]
variable [∀ i, SMulMemClass (N i) (B i) (M i)]
variable {C : Π i, N i}

instance : SMul (Πʳ i, [R i, B i]_[ℱ]) (Πʳ i, [M i, C i]_[ℱ]) where
  smul r m := ⟨fun i ↦ (r i) • (m i), by
    filter_upwards [r.prop, m.prop] with i hr hm using SMulMemClass.smul_mem ⟨r i, hr⟩ hm⟩

omit [Π i, AddSubgroupClass (N i) (M i)] in
@[simp]
lemma smul_apply' (r : Πʳ i, [R i, B i]_[ℱ]) (m : Πʳ i, [M i, C i]_[ℱ]) (i : ι) :
    (r • m) i = r i • m i :=
  rfl

instance module' : Module (Πʳ i, [R i, B i]_[ℱ]) (Πʳ i, [M i, C i]_[ℱ]) where
  zero_smul m := by ext; simp
  smul_zero r := by ext; simp
  one_smul m := by ext; simp
  add_smul r s m:= by ext; simp [add_smul]
  smul_add r m n := by ext; simp
  mul_smul r s m := by ext; simp [mul_smul]

@[simp]
lemma single_smul [DecidableEq ι] (i : ι) (r : R i) (m : Πʳ i, [M i, C i]) :
    single B i r • m = single C i (r • m i) := by
  ext j
  obtain (rfl | hi) := em (i = j)
  · simp
  · simp [single_eq_of_ne' _ _ hi]

@[simp]
lemma smul_single [DecidableEq ι] (i : ι) (r : Πʳ i, [R i, B i]) (m : M i) :
    r • single C i m = single C i (r i • m) := by
  ext j
  obtain (rfl | hi) := em (i = j)
  · simp
  · simp [single_eq_of_ne' _ _ hi]

lemma single_eq_smul [DecidableEq ι] (i : ι) (m : Πʳ i, [M i, C i]) :
    single B i 1 • m = single C i (m i) := by
  simp

variable {M₂ : ι → Type*} [Π i, AddCommGroup (M₂ i)] [Π i, Module (R i) (M₂ i)]
variable {N₂ : ι → Type*} -- submodule type
variable [Π i, SetLike (N₂ i) (M₂ i)] [∀ i, AddSubgroupClass (N₂ i) (M₂ i)]
variable [∀ i, SMulMemClass (N₂ i) (B i) (M₂ i)]
variable {C₂ : Π i, N₂ i}

section components

/-- Components of a linear map. -/
noncomputable def linearMap_component
    (f : Πʳ i, [M i, C i] →ₗ[Πʳ i, [R i, B i]] Πʳ i, [M₂ i, C₂ i]) (i : ι) :
    M i →ₗ[R i] M₂ i where
  toFun x :=
    letI := Classical.typeDecidableEq ι
    let x' := single C i x
    f x' i
  map_add' x y := by
    simp [←add_apply, ← map_add f]
  map_smul' r m := by
    classical
    let r' := single B i r
    dsimp
    have hr : r = r' i := by simp [r']
    rw [hr, ← smul_single, map_smul, smul_apply']

lemma linearMap_component_apply (f : Πʳ i, [M i, C i] →ₗ[Πʳ i, [R i, B i]]  Πʳ i, [M₂ i, C₂ i])
    (x : Πʳ i, [M i, C i]) (i : ι) : f x i = (linearMap_component f i) (x i):= by
  classical
  dsimp [linearMap_component]
  rw [← single_eq_smul, map_smul]
  simp

lemma linearMap_components_surjective
    (f : Πʳ i, [M i, C i] →ₗ[Πʳ i, [R i, B i]] Πʳ i, [M₂ i, C₂ i]) (hf : Function.Surjective f)
    (i : ι) : Function.Surjective (linearMap_component f i) := by
  classical
  intro y
  let y' := single C₂ i y
  obtain ⟨x, hx⟩ := hf y'
  use (x i)
  rw [← linearMap_component_apply, hx]
  unfold y'
  simp

lemma linearMap_surjOn_components
    (f : Πʳ i, [M i, C i] →ₗ[Πʳ i, [R i, B i]] Πʳ i, [M₂ i, C₂ i]) (hf : Function.Surjective f) :
    ∀ᶠ (i : ι) in Filter.cofinite, Set.SurjOn (linearMap_component f i) (C i) (C₂ i) := by
  classical
  have p (i : ι) : ¬Set.SurjOn (linearMap_component f i) (C i) (C₂ i) →
      ∃ (y : C₂ i), ∀ (x : C i), linearMap_component f i x ≠ y := by
    intro hmap
    unfold Set.SurjOn at hmap
    rw [Set.not_subset_iff_exists_mem_notMem] at hmap
    obtain ⟨y, hy, hne⟩ := hmap
    rw [Set.mem_image] at hne
    push_neg at hne
    use ⟨y, hy⟩
    intro x
    apply hne _ x.prop
  choose g hg using p
  let y' (i : ι) : C₂ i :=
    if h : Set.SurjOn (linearMap_component f i) (C i) (C₂ i) then 0 else g i h
  let y : Πʳ i, [M₂ i, C₂ i] := ⟨fun i ↦ y' i, by filter_upwards with i using (y' i).prop⟩
  obtain ⟨x, hx⟩ := hf y
  filter_upwards [x.eventually] with i hi
  replace hx : f x i = y i := by rw [hx]
  by_contra hnsurj
  simp only [linearMap_component_apply, mk_apply, hnsurj, ↓reduceDIte, y, y'] at hx
  exact hg i hnsurj ⟨x i, hi⟩ hx

end components

variable [Π i, TopologicalSpace (R i)] [Π i, TopologicalSpace (M i)]

section continuous_smul

variable [∀ i, ContinuousSMul (R i) (M i)] (T : Set ι)

open scoped Filter in
instance : ContinuousSMul (Πʳ i, [R i, B i]_[𝓟 T]) (Πʳ i, [M i, C i]_[𝓟 T]) :=
  isEmbedding_coe_of_principal.continuousSMul isEmbedding_coe_of_principal.continuous
    (fun {c x} ↦ by ext; rfl)

variable [hBopen : Fact (∀ i, IsOpen (B i : Set (R i)))]
variable [hCopen : Fact (∀ i, IsOpen (C i : Set (M i)))]

instance [∀ i, ContinuousSMul (R i) (M i)] :
    ContinuousSMul (Πʳ i, [R i, B i]) (Πʳ i, [M i, C i]) where
  continuous_smul := by
    rw [continuous_dom_prod hBopen.out hCopen.out]
    exact fun S hS ↦ (continuous_inclusion hS).comp continuous_smul

end continuous_smul

section components

variable [Π i, TopologicalSpace (M₂ i)]

omit [(i : ι) → TopologicalSpace (R i)] in
lemma isOpenMap_linearMap_of_surjective
    (hCopen : ∀ i, IsOpen (C i : Set (M i)))
    (hCopen₂ : ∀ i, IsOpen (C₂ i : Set (M₂ i)))
    (f : Πʳ i, [M i, C i] →ₗ[Πʳ i, [R i, B i]] Πʳ i, [M₂ i, C₂ i])
    (hf : ∀ i, IsOpenMap (linearMap_component f i))
    (hsurj : ∀ᶠ i in Filter.cofinite, Set.SurjOn (linearMap_component f i) (C i) (C₂ i)) :
    IsOpenMap f := by
  apply RestrictedProduct.isOpenMap_of_open_components hCopen hCopen₂ f
    (fun i ↦ linearMap_component f i) (linearMap_component_apply f) hf hsurj

end components

section free_topology

variable (n : Type*) [Fintype n]

variable (B) in
/-- If `B i` is subring of `R i` then `(B i)^n` is a `B i`-submodule of `(R i)^n`. -/
def piSubringSubmodule (i : ι) : Submodule (B i) (n → R i) :=
  Submodule.pi Set.univ fun (_ : n) ↦ Subring.toSubmodule (Subring.ofClass (B i))

/-- Canonical linear equivalence between `Π' R^n` and `(Π' R)^n` -/
def _root_.LinearEquiv.restrictedProductPi
    : Πʳ i, [n → R i, piSubringSubmodule B n i]_[ℱ] ≃ₗ[Πʳ i, [R i, B i]_[ℱ]]
      n → Πʳ i, [R i, B i]_[ℱ] where
  toFun x j := congrRight (fun i y ↦ y j)
    (by
      filter_upwards with i r hr
      rw [piSubringSubmodule, Submodule.coe_pi, Set.mem_univ_pi] at hr
      exact hr j)
    x
  invFun x := ⟨fun i j ↦ x j i, by simpa [piSubringSubmodule] using fun j ↦ (x j).eventually⟩
  left_inv x := by ext; rfl
  right_inv x := by ext; rfl
  map_add' x y := by ext; rfl
  map_smul' x y := by ext; rfl

lemma isOpen_piSubringSubmodule (hOpen : ∀ i, IsOpen (B i : Set (R i))) (i : ι) :
    IsOpen (SetLike.coe <| piSubringSubmodule B n i) := by
  rw [piSubringSubmodule, Submodule.coe_pi]
  apply isOpen_set_pi Set.finite_univ
  intro j _
  show IsOpen (B i : Set (R i))
  exact hOpen i

variable [∀ i, IsTopologicalRing (R i)]

/-- Canonical continuous linear equivalence between `Π' R^n` and `(Π' R)^n` -/
def _root_.ContinuousLinearEquiv.restrictedProductPi (hOpen : ∀ i, IsOpen (B i : Set (R i)))
    : Πʳ i, [n → R i, piSubringSubmodule B n i] ≃L[Πʳ i, [R i, B i]] n → Πʳ i, [R i, B i] where
  __ := LinearEquiv.restrictedProductPi n
  continuous_toFun := by
    apply continuous_pi
    intro i
    dsimp [LinearEquiv.restrictedProductPi]
    apply Continuous.restrictedProduct_congrRight _ (fun _ ↦ _root_.continuous_apply i)
  continuous_invFun := by
    have := Fact.mk hOpen
    have := Fact.mk (isOpen_piSubringSubmodule n hOpen)
    apply IsModuleTopology.continuous_of_linearMap
      (LinearEquiv.restrictedProductPi n).symm.toLinearMap

lemma moduleToplogy_of_prod (hOpen : ∀ i, IsOpen (B i : Set (R i))) :
    IsModuleTopology (Πʳ i, [R i, B i])
    (Πʳ i, [n → R i, piSubringSubmodule B n i]) :=
  have := Fact.mk hOpen
  IsModuleTopology.iso (ContinuousLinearEquiv.restrictedProductPi n hOpen).symm

end free_topology

variable [∀ i, IsTopologicalRing (R i)]
variable [∀ i, IsModuleTopology (R i) (M i)]
variable [Module.Finite (Πʳ i, [R i, B i]) (Πʳ i, [M i, C i])]

theorem isModuleTopology (hBOpen : ∀ i, IsOpen (B i : Set (R i)))
    (hCOpen : ∀ i, IsOpen (C i : Set (M i)))
    : IsModuleTopology (Πʳ i, [R i, B i]) (Πʳ i, [M i, C i]) := by
  have := Fact.mk hBOpen
  have := Fact.mk hCOpen
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' (Πʳ i, [R i, B i]) (Πʳ i, [M i, C i])
  let g' := ContinuousLinearEquiv.restrictedProductPi (Fin n) hBOpen
  let g := f ∘ₗ g'.toLinearMap
  have (i : ι) : ContinuousAdd (M i) := IsModuleTopology.toContinuousAdd (R i) (M i)
  have (i : ι) : ContinuousSMul (R i) (M i) := IsModuleTopology.toContinuousSMul (R i) (M i)
  have := moduleToplogy_of_prod (Fin n) hBOpen
  have hsurj : Function.Surjective g := by
    apply Function.Surjective.comp hf g'.surjective
  have hopen : IsOpenMap g := by
    apply isOpenMap_linearMap_of_surjective (isOpen_piSubringSubmodule (Fin n) hBOpen) hCOpen
    · intro i
      apply IsModuleTopology.isOpenMap_of_surjective
      exact linearMap_components_surjective g hsurj i
    · exact linearMap_surjOn_components g hsurj
  apply IsModuleTopology.of_isOpenMap_surjective _ g hopen hsurj

end RestrictedProduct
