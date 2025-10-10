import FLT.Mathlib.Algebra.Algebra.Bilinear
import FLT.Mathlib.Algebra.Algebra.Pi
import FLT.Mathlib.Algebra.Module.Submodule.Basic
import FLT.Mathlib.NumberTheory.RamificationInertia.Basic
import FLT.Mathlib.Topology.Algebra.Module.Equiv
import FLT.Mathlib.Topology.Algebra.Module.ModuleTopology
import FLT.Mathlib.Topology.Algebra.UniformRing
import FLT.Mathlib.Topology.Algebra.Valued.ValuationTopology
import FLT.Mathlib.Topology.Algebra.Valued.WithVal
import FLT.Mathlib.RingTheory.TensorProduct.Basis
import Mathlib.Algebra.Algebra.Subalgebra.Pi
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.Int.TypeTags
import Mathlib.Data.Int.WithZero
import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
import Mathlib.Topology.Algebra.Algebra.Equiv
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.Algebra.Valued.NormedValued
import Mathlib.RingTheory.Valuation.RankOne
import Mathlib.Topology.Algebra.Module.FiniteDimension
import FLT.DedekindDomain.AdicValuation
import FLT.DedekindDomain.Completion.BaseChange
import FLT.Mathlib.Topology.Algebra.RestrictedProduct.Basic
import Mathlib.LinearAlgebra.TensorProduct.Prod
import Mathlib.RingTheory.Flat.Basic
import FLT.DedekindDomain.FiniteAdeleRing.TensorPi
import Mathlib.Order.DirectedInverseSystem
import FLT.DedekindDomain.FiniteAdeleRing.IsDirectLimit
import FLT.DedekindDomain.FiniteAdeleRing.TensorRestrictedProduct



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

theorem principal_filter_order' {S₁ S₂ : 𝓕.sets} (h : S₁ ≤ S₂) :
    (𝓟 S₁ : Filter ι) ≤ 𝓟 S₂:= by
  simp only [le_principal_iff, mem_principal]; exact h


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

variable {R : ι → Type*}
variable {A : ι → Type*}
variable [Π i, SetLike (A i) (R i)]
variable {C : Π i, A i}

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

-- ....


def inclusion' (S₁ S₂ : 𝓕.complement) (h : S₁ ≤ S₂) :
    Πʳ i, [R i, C i]_[𝓟 S₁ᶜ] → Πʳ i, [R i, C i]_[𝓟 S₂ᶜ] :=
  RestrictedProduct.inclusion _ _ (principal_filter_order h)


/-- The maps from the directed system to the actual restricted product. -/
def inclusion_to_restrictedProduct' (S : 𝓕.complement) :
    Πʳ i, [R i, C i]_[𝓟 Sᶜ] → Πʳ i, [R i, C i]_[𝓕] :=
  RestrictedProduct.inclusion _ _ (filter_bot S)


end RestrictedProduct



variable {ι : Type*} {R : ι → Type*} {ℱ : Filter ι}

variable {T : ι → Type*} -- subobject type
variable [Π i, SetLike (T i) (R i)]
variable {B : Π i, T i}

open scoped RestrictedProduct TensorProduct Module.IsDirectLimit

variable {A : Type*} [CommRing A]

-- In open PR #25715
-- restricted product of addcommgroups is an addcommgroup
instance [Π i, AddCommGroup (R i)] [∀ i, AddSubgroupClass (T i) (R i)] :
    AddCommGroup (Πʳ i, [R i, B i]_[ℱ]) where
  __ := inferInstanceAs (AddGroup (Πʳ i, [R i, B i]_[ℱ]))
  add_comm a b := by ext i; simp [add_comm]

-- when #25715 lands we'll be able to change these to AddCommMonoid
-- restricted product of A-modules is an A-module
instance module [Π i, AddCommGroup (R i)] [∀ i, Module A (R i)]
    -- next line is how we do "SubmoduleClass"
    [∀ i, AddSubgroupClass (T i) (R i)] [∀ i, SMulMemClass (T i) A (R i)] :
    Module A (Πʳ i, [R i, B i]_[ℱ]) where
      smul a x := ⟨fun i ↦ a • x i, Filter.Eventually.mono x.property (fun _ hi ↦
     SMulMemClass.smul_mem a hi)⟩
      one_smul b := by ext; simp
      mul_smul x y b := by ext; simp [mul_smul]
      smul_zero b := by ext; simp
      smul_add x a b := by ext; simp
      add_smul a b x := by
        ext
        simp only [RestrictedProduct.smul_apply, RestrictedProduct.add_apply, add_smul]
      zero_smul b := by ext; simp



variable {ι : Type*} {R : ι → Type*} {ℱ : Filter ι}



variable [Π i, AddCommGroup (R i)] [∀ i, Module A (R i)] {C : ∀ i, Submodule A (R i)}
{M : Type*} [AddCommGroup M] [Module A M] [Module.FinitePresentation A M] (S : Filter.complement ℱ)

open Set Filter RestrictedProduct

instance add (S : ℱ.complement) :
  AddCommMonoid (mem_A_away_from_S C S) := by
  dsimp [mem_A_away_from_S]
  exact AddCommGroup.toDivisionAddCommMonoid.toAddCommMonoid

instance module' (S : ℱ.complement) :
  Module A (mem_A_away_from_S C S) := by
  dsimp [mem_A_away_from_S]
  exact module


def inclusion_module (S₁ S₂ : ℱ.complement) (h : S₁ ≤ S₂) :
    mem_A_away_from_S C S₁ →ₗ[A]
      mem_A_away_from_S C S₂ where
  toFun := inclusion S₁ S₂ h
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma inclusion_module_apply (S₁ S₂ : ℱ.complement) (h : S₁ ≤ S₂) (x : mem_A_away_from_S C S₁) :
  inclusion_module S₁ S₂ h x = ⟨x.1, x.2.filter_mono (principal_filter_order h)⟩ := rfl

def inclusion_module' (S₁ S₂ : ℱ.complement) (h : S₁ ≤ S₂) :
    Πʳ i, [R i, C i]_[𝓟 S₁ᶜ]  →ₗ[A]
      Πʳ i, [R i, C i]_[𝓟 S₂ᶜ]  where
  toFun := inclusion' S₁ S₂ h
  map_add' _ _ := rfl
  map_smul' _ _ := rfl



def inclusion_to_restricted_product_module (S : ℱ.complement) :
  mem_A_away_from_S C S →ₗ[A] Πʳ i, [R i, C i]_[ℱ] where
  toFun := inclusion_to_restrictedProduct S
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def inclusion_to_restricted_product_module' (S : ℱ.complement) :
  Πʳ i, [R i, C i]_[𝓟 Sᶜ] →ₗ[A] Πʳ i, [R i, C i]_[ℱ] where
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

open Set
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
    have : ∅ ∈ ℱ.complement := by
      rw [complement]
      simp only [mem_image, Filter.mem_sets, compl_empty_iff, exists_eq_right, univ_mem]
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


#check TensorProduct.directLimitRight


variable {ι : Type*} (R : ι → Type*) (S : Set ι) [∀ i, Decidable (i ∈ S)]

open scoped Filter

namespace RestrictedProduct

section type

variable (A : (i : ι) → Set (R i))

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

def principalEquivProd' : Πʳ i, [R i, A i]_[𝓟 Sᶜ] ≃
    (Π i : {i // i ∉ S}, A i) × (Π i : {i // i ∈ S}, R i) where
  toFun x := (fun i ↦ ⟨x i, x.property i.property⟩, fun i ↦ x i)
  invFun y := ⟨fun i ↦ if hi : i ∉ S then y.1 ⟨i, hi⟩ else y.2 ⟨i, by simpa using hi⟩,
  Filter.eventually_principal.mpr (fun i hi ↦ by
    simp only [mem_compl_iff] at hi
    simp only [hi]
    exact (y.1 ⟨i, hi⟩).2)⟩
  left_inv x := by
    simp only [dite_eq_ite, ite_self]
    rfl
  right_inv x := by
    simp only [dite_not, mk_apply, Subtype.coe_prop, ↓reduceDIte]
    ext i <;> simp only [i.property, ↓reduceDIte]



end type


variable {T : ι → Type*} -- subobject type
variable [Π i, SetLike (T i) (R i)]
variable {A : Π i, T i}

section monoid

@[to_additive]
def principalMulEquivProd [Π i, Monoid (R i)] [∀ i, SubmonoidClass (T i) (R i)] :
    Πʳ i, [R i, A i]_[𝓟 S] ≃* (Π i : {i // i ∈ S}, A i) × (Π i : {i // i ∉ S}, R i) where
  __ := principalEquivProd R S _
  map_mul' _ _ := rfl

@[to_additive]
def principalMulEquivProd' [Π i, Monoid (R i)] [∀ i, SubmonoidClass (T i) (R i)] :
    Πʳ i, [R i, A i]_[𝓟 Sᶜ] ≃* (Π i : {i // i ∉ S}, A i) × (Π i : {i // i ∈ S}, R i) where
  __ := principalEquivProd' R S _
  map_mul' _ _ := rfl

end monoid


end RestrictedProduct

section
variable {ι : Type*}
variable (R : ι → Type*)
variable {ℱ : Filter ι}



open scoped RestrictedProduct TensorProduct

variable (A : Type*) [CommRing A]



open Filter


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

noncomputable def RestrictedProduct.principal' [Π i, AddCommGroup (R i)]
    [∀ i, Module A (R i)] {C : ∀ i, Submodule A (R i)}
    (S : Set ι) [∀ i, Decidable (i ∈ S)] :
   (Πʳ i, [R i, C i]_[𝓟 Sᶜ]) ≃ₗ[A] ((Π i : {i // i ∉ S}, C i) ×
  (Π i : {i // i ∈ S}, R i)) where
    __ := principalAddEquivSum' R S (A := C)
    map_smul' m x := by
      simp only [AddEquiv.toEquiv_eq_coe, Equiv.toFun_as_coe, EquivLike.coe_coe, RingHom.id_apply]
      dsimp [principalAddEquivSum', principalEquivProd']
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
instance : DirectedSystem (mem_A_away_from_S C)
      fun x1 x2 x3 ↦ ⇑(inclusion_module (ℱ := ℱ) (C:= C) x1 x2 x3) := directed_system



noncomputable def RestrictedProduct.tensor_comm'
    (M : Type*) [AddCommGroup M] [Module A M] [Module.FinitePresentation A M] [Module.Flat A M] :
    M ⊗[A] (Πʳ i, [R i, C i]_[ℱ]) ≃ₗ[A] Πʳ i, [M ⊗[A] R i, rangeLTensor A M R C i]_[ℱ] :=
    let comp1 := TensorProduct.directLimitRight (inclusion_module (C:=C) (ℱ := ℱ)) M (R:=A)
    let comp := Module.iso_of_isDirectLimit (mem_A_away_from_S C)
       (inclusion_module (ℱ := ℱ)) (Πʳ i, [R i, C i]_[ℱ])
       (Module.DirectLimit (mem_A_away_from_S C) (inclusion_module (C:=C) (ℱ := ℱ)))
      (inclusion_to_restricted_product_module) (Module.DirectLimit.of A _
      (mem_A_away_from_S C) (inclusion_module (ℱ := ℱ)))
    let comp2 : Πʳ (i : ι), [M ⊗[A] R i, (rangeLTensor A M R C i)]_[ℱ] ≃ₗ[A]
      Module.DirectLimit (mem_A_away_from_S (fun i ↦ rangeLTensor A M R C i)) inclusion_module :=
      Module.iso_of_isDirectLimit (mem_A_away_from_S
      (fun i ↦ rangeLTensor A M R C i))
       (inclusion_module (ℱ := ℱ)) Πʳ i, [M ⊗[A] R i, rangeLTensor A M R C i]_[ℱ]
       (Module.DirectLimit (mem_A_away_from_S
      (fun i ↦ rangeLTensor A M R C i)) (inclusion_module (ℱ := ℱ)))
      (inclusion_to_restricted_product_module) (Module.DirectLimit.of A _
    (mem_A_away_from_S
      (fun i ↦ rangeLTensor A M R C i)) (inclusion_module (ℱ := ℱ)))
    let comp4 :=  (LinearEquiv.lTensor M comp) ≪≫ₗ comp1
    let comp5 : Module.DirectLimit (fun (S: ℱ.complement) ↦
      M ⊗[A] Πʳ (i : ι), [R i, ↑(C i)]_[𝓟 Sᶜ]) (fun i j h ↦
      LinearMap.lTensor M (inclusion_module i j h)) ≃ₗ[A] Module.DirectLimit (fun (S: ℱ.complement)
      ↦ Πʳ (i : ι), [M ⊗[A] R i, (rangeLTensor A M R C i)]_[𝓟 (S)ᶜ]) inclusion_module :=
      Module.DirectLimit.congr (fun (S : ℱ.complement) ↦
        (RestrictedProduct.lTensorPrincipalEquiv A M R C (Sᶜ : Set ι))) (by
      intro i j hij
      refine TensorProduct.ext' (fun x y ↦ ?_)
      ext k
      simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
        LinearMap.lTensor_tmul, lTensorPrincipalEquiv_tmul]
      change x ⊗ₜ[A] y k = ((lTensorPrincipalEquiv A M R C (↑i)ᶜ) (x ⊗ₜ[A] y)) k
      rw [lTensorPrincipalEquiv_tmul])
    comp4 ≪≫ₗ comp5 ≪≫ₗ comp2.symm



theorem equality [Π i, AddCommGroup (R i)]
    [∀ i, Module A (R i)] {C : ∀ i, Submodule A (R i)}
    {M : Type*} [AddCommGroup M] [Module A M] [Module.FinitePresentation A M] [Module.Flat A M] :
    RestrictedProduct.lTensor A M R ℱ C  = RestrictedProduct.tensor_comm' R A C M (ℱ := ℱ) := by
    refine TensorProduct.ext' (fun x y ↦ ?_)
    simp only [TensorProduct.AlgebraTensorModule.curry_apply, TensorProduct.curry_apply,
      LinearMap.coe_restrictScalars, lTensor_tmul, LinearEquiv.coe_coe, tensor_comm']
    simp only [LinearEquiv.trans_apply, LinearEquiv.lTensor_tmul]
    set iso1 := (Module.iso_of_isDirectLimit (mem_A_away_from_S fun i ↦ rangeLTensor A M R C i)
      inclusion_module
          Πʳ (i : ι), [M ⊗[A] R i, ↑(rangeLTensor A M R C i)]_[ℱ]
          (Module.DirectLimit (mem_A_away_from_S fun i ↦ rangeLTensor A M R C i) inclusion_module)
          inclusion_to_restricted_product_module
          (Module.DirectLimit.of A (↑ℱ.complement) (mem_A_away_from_S fun i ↦ rangeLTensor A M R C i)
            inclusion_module))



    sorry
