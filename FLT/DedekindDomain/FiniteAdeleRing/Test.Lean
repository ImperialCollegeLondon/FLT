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
import FLT.Mathlib.RingTheory.Finiteness.Pi
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
import Mathlib.Algebra.Colimit.Module
import Mathlib.RingTheory.Flat.Basic
import FLT.DedekindDomain.FiniteAdeleRing.TensorPi
import Mathlib.Order.DirectedInverseSystem




section IsDirectLimit

namespace Module

variable {R : Type*} [Semiring R] {ι : Type*} [Preorder ι] (M : ι → Type*) (P : Type*)
variable [AddCommMonoid P] [Module R P]
variable [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)] (f : ∀ i j, i ≤ j → M i →ₗ[R] M j)
variable (g : ∀ i, M i →ₗ[R] P) (Hg : ∀ i j hij x, g j (f i j hij x) = g i x)
variable [DecidableEq ι] [IsDirected ι (· ≤ ·)] [Nonempty ι] [DirectedSystem M (f · · ·)]

@[mk_iff] class IsDirectLimit : Prop where
  surj : ∀ m : P, ∃ i, ∃ mi : M i, g i mi = m
  inj :  ∀ i j, ∀ mi : M i, ∀ mj : M j, g i mi = g j mj → ∃ (k : ι) (hik : i ≤ k) (hjk : j ≤ k),
      f i k hik mi = f j k hjk mj

instance isDirectLimit : IsDirectLimit M (Module.DirectLimit M f) f
  (Module.DirectLimit.of R ι M f) where
  surj := Module.DirectLimit.exists_of
  inj i j mi mj h := by
    apply_fun Module.DirectLimit.linearEquiv _ _ at h
    simp_rw [Module.DirectLimit.linearEquiv_of] at h
    have ⟨k, hi, hj, hij⟩ := Quotient.exact h
    exact ⟨k, hi, hj, hij⟩

end Module

end IsDirectLimit


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

variable {R : ι → Type*} {A : (i : ι) → Set (R i)}

variable (A) in
/-- This is (isomorphic to) `(Π i ∈ S, R i) × (Π i ∉ S, A i)` -/
def mem_A_away_from_S (S : 𝓕.complement) : Type _ :=
  Πʳ i, [R i, A i]_[𝓟 Sᶜ]

/-- The inclusions between `mem_A_away_from_S` which will form the directed system. -/
def inclusion (S₁ S₂ : 𝓕.complement) (h : S₁ ≤ S₂) :
    mem_A_away_from_S A S₁ → mem_A_away_from_S A S₂ :=
  RestrictedProduct.inclusion _ _ (principal_filter_order h)

instance directed_system :
    @DirectedSystem (𝓕.complement) _ (mem_A_away_from_S A) (inclusion) where
  map_self _ _ := rfl
  map_map _ _ _ _ _ _ := rfl

/-- The maps from the directed system to the actual restricted product. -/
def inclusion_to_restrictedProduct (S : 𝓕.complement) :
    mem_A_away_from_S A S → Πʳ i, [R i, A i]_[𝓕] :=
  RestrictedProduct.inclusion _ _ (filter_bot S)

-- ....


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
instance [Π i, AddCommGroup (R i)] [∀ i, Module A (R i)]
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

noncomputable def Submodule.lTensor (M : Type*) {N : Type*} [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N] (P : Submodule A N) : Submodule A (M ⊗[A] N) :=
  LinearMap.range (P.subtype.lTensor M)


variable {ι : Type*} {R : ι → Type*} {ℱ : Filter ι} [Preorder ι]

variable {T : ι → Type*} -- subobject type
variable [Π i, SetLike (T i) (R i)]
variable {B : Π i, T i}
variable {A : Type*} [CommRing A]

variable [Π i, AddCommGroup (R i)] [∀ i, Module A (R i)] {C : ∀ i, Submodule A (R i)}
{M : Type*} [AddCommGroup M] [Module A M] [Module.FinitePresentation A M] (S : Filter.complement ℱ)

open Set Filter RestrictedProduct

instance add (S : ℱ.complement) :
  AddCommMonoid (mem_A_away_from_S (R:=R) (fun i ↦ (C i : Set (R i))) S) := by
  dsimp [mem_A_away_from_S]
  exact AddCommGroup.toDivisionAddCommMonoid.toAddCommMonoid

instance module (S : ℱ.complement) :
  Module A (mem_A_away_from_S (R:=R) (fun i ↦ (C i : Set (R i))) S) := by
  dsimp [mem_A_away_from_S]
  exact
    «instModuleRestrictedProductCoeOfSMulMemClass_external:file:///c%3A/Users/Maddy/Documents/Github/FLT/FLT/DedekindDomain/FiniteAdeleRing/Test.Lean»



def inclusion_module (S₁ S₂ : ℱ.complement) (h : S₁ ≤ S₂) :
    mem_A_away_from_S (fun i ↦ (C i : Set (R i))) S₁ →ₗ[A]
      mem_A_away_from_S ((fun i ↦ (C i : Set (R i)))) S₂ where
  __ := RestrictedProduct.inclusion R _ (principal_filter_order h)
  map_mul' _ _ := rfl





#check _root_.inclusion (𝓕 := ℱ) (A:= (fun i ↦ (C i : Set (R i))))

#check Module.IsDirectLimit (mem_A_away_from_S (𝓕 := ℱ) (fun i ↦ (C i : Set (R i))))
  Πʳ i, [R i, C i]_[ℱ] --(_root_.inclusion (𝓕 := ℱ) (A:= (fun i ↦ (C i : Set (R i)))))

instance RestrictedProductIsDirectLimit :
  Module.IsDirectLimit R Πʳ i, [R i, C i]_[ℱ] (inclusion_to_restrictedProduct C S) := sorry





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

end monoid


end RestrictedProduct

section
variable {ι : Type*}
variable {R : ι → Type*}
variable {ℱ : Filter ι}

variable {T : ι → Type*} -- subobject type
variable [Π i, SetLike (T i) (R i)]
--variable {B : Π i, T i}

open scoped RestrictedProduct TensorProduct

variable {A : Type*} [CommRing A]



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


noncomputable def RestrictedProduct.principal_tensor_comm' [Π i, AddCommGroup (R i)]
    [∀ i, Module A (R i)] {C : Π i, Submodule A (R i)} {M : Type*} [AddCommGroup M] [Module A M]
    [Module.FinitePresentation A M] {S : Set ι} :
   M ⊗[A] (Πʳ i, [R i, C i]_[𝓟 S]) ≃ₗ[A] (Πʳ i, [M ⊗[A] R i, (C i).lTensor M]_[𝓟 S]) := sorry




-- this now compiles
noncomputable def RestrictedProduct.tensor_comm' [Π i, AddCommGroup (R i)]
    [∀ i, Module A (R i)] {C : Π i, Submodule A (R i)}
    {M : Type*} [AddCommGroup M] [Module A M] [Module.FinitePresentation A M] [Module.Flat A M] :
    M ⊗[A] (Πʳ i, [R i, C i]_[ℱ]) ≃ₗ[A] Πʳ i, [M ⊗[A] R i, (C i).lTensor M]_[ℱ] :=
  LinearEquiv.ofBijective (TensorProduct.lift {
    toFun m := {
      toFun x := ⟨fun i ↦ m ⊗ₜ (x i), Filter.Eventually.mono x.property (fun i hi ↦
     LinearMap.mem_range.mpr ⟨m ⊗ₜ[A] ⟨x i, hi⟩, rfl⟩)⟩
      map_add' x y := by
        ext i
        simp only [add_apply, mk_apply, TensorProduct.tmul_add]
      map_smul' a x := by
        ext i
        simp only [smul_apply, TensorProduct.tmul_smul, mk_apply, RingHom.id_apply]
    }
    map_add' x y := by
      refine LinearMap.ext (fun x₁ ↦ ?_)
      ext i
      simp only [LinearMap.coe_mk, AddHom.coe_mk, mk_apply, LinearMap.add_apply, add_apply,
        TensorProduct.add_tmul]
    map_smul' a x := by
      refine LinearMap.ext (fun x₁ ↦ ?_)
      ext i
      simp only [LinearMap.coe_mk, AddHom.coe_mk, mk_apply, RingHom.id_apply, LinearMap.smul_apply,
        smul_apply, TensorProduct.smul_tmul']
  }) ⟨
  fun a b h ↦ by
    -- injectivity proof: if `a`, `b` in `M ⊗[A] Πʳ (i : ι), [R i, ↑(C i)]_[ℱ]`
    -- and their images in `Πʳ (i : ι), [M ⊗[A] R i, ↑(Submodule.lTensor M (C i))]_[ℱ]`
    -- are the same, then choose some `S ∈ ℱ` such that `a`, `b` are both in
    -- `M ⊗ ((∏ i ∈ S, C i) × (∏ i ∉ S, R i))`, and then by your earlier work we know
    -- that the map from this to `(∏ i ∈ S, M ⊗ C i) × (∏ i ∉ S, M ⊗ R i)` is injective,
    -- and then by flatness the map from that to
    -- `Πʳ (i : ι), [M ⊗[A] R i, ↑(Submodule.lTensor M (C i))]_[ℱ]` is injective,
    -- and `a` and `b` have become equal after the composite of those two injections,
    -- so they are equal.
    -- have h_finite : ∃ (S : Finset ι), S.toSet ∈ ℱ ∧
    -- (∀ x ∈ {a, b}, ∃ (f : ι → A), Set.finite {i | f i ≠ 0} ∧
    --  ∀ i ∉ S, (TensorProduct.lift _ x : _) i ∈ Submodule.lTensor M (C i)) := by
    --   sorry


    -- haveI {S: Set ι} {h: S ∈ ℱ} : AddCommMonoid ((Π i ∈ S, C i) × (Π i ∉ S, R i)) := sorry
    -- have : ∃S ∈ ℱ, a.val ∈ (M ⊗[A] ((Π i ∈ S, C i) × (Π i ∉ S, R i))) ∧
    --   b.val ∈ (M ⊗[A] ((Π i ∈ S, C i) × (Π i ∉ S, R i))) := sorry
    sorry,
  by
    intro y
    -- by definition `y ∈ (∏ i ∈ S, ↑(Submodule.lTensor M (C i))) × (∏ i ∉ S, M ⊗ R i)`
    -- for some `S ∈ ℱ`, and there's a surjection (in fact a bijection) from
    -- `(∏ i ∈ S, M ⊗ (C i)) × (∏ i ∉ S, M ⊗ R i)` onto this, and then by your earlier
    -- work there's something in `M ⊗ ((∏ i ∈ S, C i) × (∏ i ∉ S, R i))` which hits
    -- this, and the image of that thing in `M ⊗[A] Πʳ (i : ι), [R i, ↑(C i)]_[ℱ]`
    -- will do
    sorry⟩




end

section
variable (A K L B : Type*) [CommRing A] [CommRing B] [Algebra A B] [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K] [Algebra B L] [IsDedekindDomain A]
    [Algebra K L] [Algebra A L] [IsScalarTower A B L] [IsScalarTower A K L]
    [IsIntegralClosure B A L] [FiniteDimensional K L] [Module.Finite A B]
    [IsDedekindDomain B] [IsFractionRing B L]

variable (M : Type*) [AddCommGroup M] [Module A M] [Module.FinitePresentation A M]
namespace IsDedekindDomain

open IsDedekindDomain HeightOneSpectrum
#check Module.DirectLimit

noncomputable instance : DecidableEq (HeightOneSpectrum A) :=
  Classical.typeDecidableEq (HeightOneSpectrum A)


noncomputable def f (S T : Finset (HeightOneSpectrum A)) (h : S ≤ T) :
  ((Π v : S, v.1.adicCompletion K) ×
  (Π v : {v // v ∉ S}, (adicCompletionIntegers K v.1))) →ₗ[A]
  ((Π v : T, v.1.adicCompletion K) ×
  (Π v : {v // v ∉ T}, (adicCompletionIntegers K v.1))) where
    toFun x := (fun v ↦
      if h' : (v : HeightOneSpectrum A) ∈ S then
        x.1 ⟨v, h'⟩
      else
        algebraMap _ _ (x.2 ⟨v, h'⟩),
     fun v ↦ x.2 ⟨v, Set.notMem_subset h v.2⟩)
    map_add' x y := by
      simp only [Prod.fst_add, Pi.add_apply, Prod.snd_add, ValuationSubring.algebraMap_apply,
        AddMemClass.coe_add, Prod.mk_add_mk, Prod.mk.injEq]
      constructor
      · ext v
        by_cases hv : (v : HeightOneSpectrum A) ∈ S
        · simp [hv]
        · simp [hv]
      · ext v
        simp only [AddMemClass.coe_add, Pi.add_apply]
    map_smul' r x := by
      simp only [Prod.smul_fst, Pi.smul_apply, Prod.smul_snd, ValuationSubring.algebraMap_apply,
        coe_smul_adicCompletionIntegers, RingHom.id_apply, Prod.smul_mk, Prod.mk.injEq]
      constructor
      · ext v
        by_cases hv : (v : HeightOneSpectrum A) ∈ S
        · simp [hv]
        · simp [hv]
      · ext v
        simp only [coe_smul_adicCompletionIntegers, Pi.smul_apply]


noncomputable def direct_limit : (@Module.DirectLimit A _ (Finset (HeightOneSpectrum A)) _
  (fun S ↦ ((Π v : S, v.1.adicCompletion K) × (Π v : (Set.compl (Finset.toSet S)),
  (adicCompletionIntegers K v.1)))) _ _ (f A K) _) ≃ₗ[A] FiniteAdeleRing A K := by
  refine LinearEquiv.ofBijective (Module.DirectLimit.lift A (Finset (HeightOneSpectrum A))
    (fun S ↦ ((Π v : S, v.1.adicCompletion K) × (Π v : (Set.compl (Finset.toSet S)),
   (adicCompletionIntegers K v.1)))) (f A K) ?_ ?_) ⟨?_, ?_⟩
  · intro v
    simp only
    -- can rw as restricted product on princpal filter and go from there?
    sorry
  · intro v w
    sorry
  · apply Module.DirectLimit.lift_injective
    intro v

    sorry
  ·
    sorry

end IsDedekindDomain


#exit



-- def G (S : Finset (HeightOneSpectrum A)):=
-- ((Π v : S, v.1.adicCompletion K) × (Π v : (Set.compl (Finset.toSet S)), (adicCompletionIntegers K v.1)))

-- #check G A K

-- noncomputable instance (S : Finset (HeightOneSpectrum A)) : AddCommGroup (G A K S) :=
--   Prod.instAddCommGroup

-- instance (S : Finset (HeightOneSpectrum A)) : Module A (G A K S) := by
--   sorry

def DirectLimit' :=
  @Module.DirectLimit A _ (Finset (HeightOneSpectrum A)) _
  (fun S ↦ ((Π v : S, v.1.adicCompletion K) × (Π v : (Set.compl (Finset.toSet S)),
  (adicCompletionIntegers K v.1)))) _ _ (f A K) _

-- noncomputable def LHS (S : FiniteSubsets A) :=
--   M ⊗[A] ((Π v : S.val, adicCompletion K v.1) ×
--           (Π v : (Set.compl S.val), adicCompletionIntegers K v.1))

-- noncomputable def RHS (S : FiniteSubsets A) :=
--   (Π v : S.val, M ⊗[A] adicCompletion K v.1) ×
--   (Π v : (Set.compl S.val), M ⊗[A] adicCompletionIntegers K v.1)

-- instance (S: FiniteSubsets A): AddCommMonoid (LHS A K M S) := by
--   dsimp [LHS]
--   exact TensorProduct.addCommMonoid

variable (iso : ∀ S : FiniteSubsets A, (M ⊗[A] ((Π v : S.val, adicCompletion K v.1) ×
          (Π v : (Set.compl S.val), adicCompletionIntegers K v.1))) ≃ₗ[A]
          ((Π v : S.val, M ⊗[A] adicCompletion K v.1) ×
  (Π v : (Set.compl S.val), M ⊗[A] adicCompletionIntegers K v.1)))

let q : ℤ := 1
def LHS_limit : Type* :=
  lim (fun S : FiniteSubsets => (M ⊗[A] ((Π v : S.val, adicCompletion K v.1) ×
          (Π v : (Set.compl S.val), adicCompletionIntegers K v.1))))



end IsDedekindDomain
