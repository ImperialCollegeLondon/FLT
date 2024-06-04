/-
Copyright (c) 2024 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/

import Mathlib.Algebra.Quaternion -- probably get away with less
import FLT.for_mathlib.Con
import FLT.for_mathlib.CrazySimple
import Mathlib.RingTheory.Flat.Basic
import Mathlib.LinearAlgebra.TensorProduct.RightExactness

/-!
# Characteristic predicate for central simple algebras

In this file we define the predicate `IsCentralSimple K D` where `K` is a field
and `D` is a (noncommutative) `K`-algebra.

Note that the predicate makes sense just for `K` a `CommRing` but it doesn't give the
right definition; for a commutative ring base one should use the theory of Azumaya algebras.
This adds an extra layer of complication which we don't need. In fact ideals of `K`
immediately give rise to nontrivial quotients of `D` so there are no central simple
algebras in this case according to our definition.

-/

universe u v w

open Classical
open scoped BigOperators

/--
For a field `K` and a `K`-algebra `D`, we say that `D` is a central algebra over `K` if the center
of `D` is exactly `K` and that `D` is a simple ring.
-/
class IsCentralSimple
    (K : Type u) [Field K] (D : Type v) [Ring D] [Algebra K D] : Prop where
  is_central : Subalgebra.center K D ≤ ⊥
  [is_simple : IsSimpleOrder (RingCon D)]

lemma IsCentralSimple.center_eq
    (K D : Type*) [Field K] [Ring D] [Algebra K D] [IsCentralSimple K D] :
    Subalgebra.center K D = ⊥ :=
  le_antisymm IsCentralSimple.is_central $ by
    rintro _ ⟨x, rfl⟩
    rw [Subalgebra.mem_center_iff]
    exact (Algebra.commutes' x · |>.symm)


variable (K : Type u) [Field K]

open Matrix in
instance MatrixRing.isCentralSimple (ι : Type v) [Fintype ι] [Nonempty ι] [DecidableEq ι] :
    IsCentralSimple K (Matrix ι ι K) where
  is_central _ h := mem_range_scalar_of_commute_stdBasisMatrix fun _ _ _ =>
    Subalgebra.mem_center_iff.mp h _

namespace IsCentralSimple

variable (D : Type v) [Ring D] [Algebra K D]

/-
\begin{lemma}
    \label{IsCentralSimple.baseChange}
    If DD is a central simple algebra over~KK and L/KL/K is a field extension, then L⊗KDL\otimes_KD
    is a central simple algebra over~LL.
\end{lemma}
\begin{proof}
    This is not too hard: it's lemma b of section 12.4 in Peirce's "Associative algebras".
    Will maybe write more on Saturday.
\end{proof}
-/
open scoped TensorProduct

section should_be_elsewhere

instance (B : Type*) [Ring B] [Algebra K B]: Algebra K (Subring.center B) :=
  RingHom.toAlgebra <| (algebraMap K B).codRestrict _ <| fun x => by
    rw [Subring.mem_center_iff]
    exact fun y => Algebra.commutes x y |>.symm

lemma TensorProduct.eq_repr_basis_right
    (B : Type*) [Ring B] [Algebra K B]
    (C : Type*) [Ring C] [Algebra K C]
    {ιC : Type*} (𝒞 : Basis ιC K C)
    (x : B ⊗[K] C) :
    ∃ (s : Finset ιC) (b : ιC → B), ∑ i ∈ s, b i ⊗ₜ[K] 𝒞 i = x := by
  let ℬ := Basis.ofVectorSpace K B
  let 𝒯 := Basis.tensorProduct ℬ 𝒞
  have eq1 := calc x
      _ = ∑ ij ∈ (𝒯.repr x).support, (𝒯.repr x) ij • 𝒯 ij := 𝒯.total_repr x |>.symm
      _ = ∑ ij ∈ (𝒯.repr x).support, (𝒯.repr x) (ij.1, ij.2) • 𝒯 (ij.1, ij.2) :=
          Finset.sum_congr rfl <| by simp
      _ = ∑ i ∈ (𝒯.repr x).support.image Prod.fst, ∑ j ∈ (𝒯.repr x).support.image Prod.snd,
            𝒯.repr x (i, j) • 𝒯 (i, j) := by
          rw [← Finset.sum_product']
          apply Finset.sum_subset
          · rintro ⟨i, j⟩ hij
            simp only [Finsupp.mem_support_iff, ne_eq, Finset.mem_product, Finset.mem_image,
              Prod.exists, exists_and_right, exists_eq_right, Subtype.exists, 𝒯] at hij ⊢
            exact ⟨⟨j, hij⟩, ⟨i.1, ⟨i.2, hij⟩⟩⟩
          · rintro ⟨i, j⟩ hij1 hij2
            simp only [Finset.mem_product, Finset.mem_image, Finsupp.mem_support_iff, ne_eq,
              Prod.exists, exists_and_right, exists_eq_right, Subtype.exists, Decidable.not_not,
              Basis.tensorProduct_apply, smul_eq_zero, 𝒯] at hij1 hij2 ⊢
            rw [hij2]
            tauto
      _ = ∑ j ∈ (𝒯.repr x).support.image Prod.snd, ∑ i ∈ (𝒯.repr x).support.image Prod.fst,
            𝒯.repr x (i, j) • 𝒯 (i, j) := Finset.sum_comm
      _ = ∑ j ∈ (𝒯.repr x).support.image Prod.snd, ∑ i ∈ (𝒯.repr x).support.image Prod.fst,
            𝒯.repr x (i, j) • (ℬ i ⊗ₜ[K] 𝒞 j) := by
          refine Finset.sum_congr rfl fun _ _ => ?_
          simp only [𝒯, Basis.tensorProduct_apply]
      _ =  ∑ j ∈ (𝒯.repr x).support.image Prod.snd, ∑ i ∈ (𝒯.repr x).support.image Prod.fst,
            (𝒯.repr x (i, j) • ℬ i) ⊗ₜ[K] 𝒞 j := by
          refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
          rw [TensorProduct.smul_tmul']
      _ =  ∑ j ∈ (𝒯.repr x).support.image Prod.snd, (∑ i ∈ (𝒯.repr x).support.image Prod.fst,
            (𝒯.repr x (i, j) • ℬ i)) ⊗ₜ[K] 𝒞 j := by
          refine Finset.sum_congr rfl fun _ _ => ?_
          rw [TensorProduct.sum_tmul]
  exact ⟨_, _, eq1.symm⟩

lemma TensorProduct.eq_repr_basis_left
    (B : Type*) [Ring B] [Algebra K B]
    (C : Type*) [Ring C] [Algebra K C]
    {ιB : Type*} (ℬ : Basis ιB K B)
    (x : B ⊗[K] C) :
    ∃ (s : Finset ιB) (c : ιB → C), ∑ i ∈ s, ℬ i ⊗ₜ[K] c i = x := by
  let 𝒞 := Basis.ofVectorSpace K C
  let 𝒯 := Basis.tensorProduct ℬ 𝒞
  have eq1 := calc x
      _ = ∑ ij ∈ (𝒯.repr x).support, (𝒯.repr x) ij • 𝒯 ij := 𝒯.total_repr x |>.symm
      _ = ∑ ij ∈ (𝒯.repr x).support, (𝒯.repr x) (ij.1, ij.2) • 𝒯 (ij.1, ij.2) :=
          Finset.sum_congr rfl <| by simp
      _ = ∑ i ∈ (𝒯.repr x).support.image Prod.fst, ∑ j ∈ (𝒯.repr x).support.image Prod.snd,
            𝒯.repr x (i, j) • 𝒯 (i, j) := by
          rw [← Finset.sum_product']
          apply Finset.sum_subset
          · rintro ⟨i, j⟩ hij
            simp only [Finsupp.mem_support_iff, ne_eq, Finset.mem_product, Finset.mem_image,
              Prod.exists, exists_and_right, exists_eq_right, Subtype.exists, 𝒯] at hij ⊢
            exact ⟨⟨j.1, ⟨j.2, hij⟩⟩, ⟨i, hij⟩⟩
          · rintro ⟨i, j⟩ hij1 hij2
            simp only [Finset.mem_product, Finset.mem_image, Finsupp.mem_support_iff, ne_eq,
              Prod.exists, exists_and_right, exists_eq_right, Subtype.exists, Decidable.not_not,
              Basis.tensorProduct_apply, smul_eq_zero, 𝒯] at hij1 hij2 ⊢
            rw [hij2]
            tauto
      _ = ∑ i ∈ (𝒯.repr x).support.image Prod.fst, ∑ j ∈ (𝒯.repr x).support.image Prod.snd,
            𝒯.repr x (i, j) • (ℬ i ⊗ₜ[K] 𝒞 j) := by
          refine Finset.sum_congr rfl fun _ _ => ?_
          simp only [𝒯, Basis.tensorProduct_apply]
      _ =  ∑ i ∈ (𝒯.repr x).support.image Prod.fst, ∑ j ∈ (𝒯.repr x).support.image Prod.snd,
            ℬ i ⊗ₜ[K] (𝒯.repr x (i, j) • 𝒞 j : C) := by
          refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
          rw [TensorProduct.smul_tmul', TensorProduct.smul_tmul]
      _ =  ∑ i ∈ (𝒯.repr x).support.image Prod.fst,
            ℬ i ⊗ₜ[K] (∑ j ∈ (𝒯.repr x).support.image Prod.snd, (𝒯.repr x (i, j) • 𝒞 j)) := by
          refine Finset.sum_congr rfl fun _ _ => ?_
          rw [TensorProduct.tmul_sum]
  exact ⟨_, _, eq1.symm⟩

lemma TensorProduct.sum_tmul_basis_right_eq_zero
    (B : Type*) [Ring B] [Algebra K B]
    (C : Type*) [Ring C] [Algebra K C]
    {ιC : Type*} (𝒞 : Basis ιC K C)
    (s : Finset ιC) (b : ιC → B)
    (h : ∑ i ∈ s, b i ⊗ₜ[K] 𝒞 i = 0) :
    ∀ i ∈ s, b i = 0 := by
  let ℬ := Basis.ofVectorSpace K B
  let 𝒯 := Basis.tensorProduct ℬ 𝒞
  let I := s.biUnion fun i => (ℬ.repr (b i)).support
  have eq1 := calc (0 : B ⊗[K] C)
      _ = ∑ i ∈ s, b i ⊗ₜ[K] 𝒞 i := h.symm
      _ = ∑ i ∈ s, (∑ k ∈ (ℬ.repr (b i)).support, (ℬ.repr (b i)) k • ℬ k) ⊗ₜ[K] 𝒞 i := by
          refine Finset.sum_congr rfl fun z _ => ?_
          congr
          exact ℬ.total_repr (b z) |>.symm
      _ = ∑ i ∈ s, ∑ k ∈ (ℬ.repr (b i)).support, (ℬ.repr (b i)) k • (ℬ k ⊗ₜ[K] 𝒞 i) := by
          refine Finset.sum_congr rfl fun z _ => ?_
          rw [TensorProduct.sum_tmul]
          refine Finset.sum_congr rfl fun _ _ => ?_
          rw [TensorProduct.smul_tmul']
      _ = ∑ i ∈ s, ∑ k ∈ I, (ℬ.repr (b i)) k • (ℬ k ⊗ₜ[K] 𝒞 i) := by
          refine Finset.sum_congr rfl fun j h => ?_
          apply Finset.sum_subset
          · intro i hi
            simp only [Finsupp.mem_support_iff, ne_eq, Finset.mem_biUnion, I] at hi ⊢
            exact ⟨_, h, hi⟩
          · intro i hi1 hi2
            simp only [Finsupp.mem_support_iff, ne_eq, Decidable.not_not, smul_eq_zero]
              at hi1 hi2 ⊢
            tauto
      _ = ∑ k ∈ I, ∑ i ∈ s, (ℬ.repr (b i)) k • (ℬ k ⊗ₜ[K] 𝒞 i) := Finset.sum_comm
      _ = ∑ ij ∈ I ×ˢ s, (ℬ.repr (b ij.2)) ij.1 • (ℬ ij.1 ⊗ₜ[K] 𝒞 ij.2) := by
          rw [Finset.sum_product]
      _ = ∑ ij ∈ I ×ˢ s, (ℬ.repr (b ij.2)) ij.1 • 𝒯 ij := by
          refine Finset.sum_congr rfl fun ij _ => ?_
          rw [Basis.tensorProduct_apply]
  have LI := 𝒯.linearIndependent
  rw [linearIndependent_iff'] at LI
  specialize LI (I ×ˢ s) _ eq1.symm
  intro i hi
  rw [← ℬ.total_repr (b i)]
  change ∑ _ ∈ _, _ = 0
  simp only [LinearMap.coe_smulRight, LinearMap.id_coe, id_eq]
  refine Finset.sum_eq_zero fun j hj => ?_
  specialize LI ⟨j, i⟩ (by
    simp only [Finset.mem_product, Finset.mem_biUnion, Finsupp.mem_support_iff, ne_eq, I] at hj ⊢
    refine ⟨⟨_, hi, hj⟩, hi⟩)
  simp [LI]

lemma TensorProduct.sum_tmul_basis_left_eq_zero
    (B : Type*) [Ring B] [Algebra K B]
    (C : Type*) [Ring C] [Algebra K C]
    {ιB : Type*} (ℬ : Basis ιB K B)
    (s : Finset ιB) (c : ιB → C)
    (h : ∑ i ∈ s, ℬ i ⊗ₜ[K] c i = 0) :
    ∀ i ∈ s, c i = 0 := by
  let 𝒞 := Basis.ofVectorSpace K C
  let 𝒯 := Basis.tensorProduct ℬ 𝒞
  let I := s.biUnion fun i => (𝒞.repr (c i)).support
  have eq1 := calc (0 : B ⊗[K] C)
      _ = ∑ i ∈ s, ℬ i ⊗ₜ[K] c i := h.symm
      _ = ∑ i ∈ s, (ℬ i ⊗ₜ[K] (∑ k ∈ (𝒞.repr (c i)).support, (𝒞.repr (c i)) k • 𝒞 k)) := by
          refine Finset.sum_congr rfl fun z _ => ?_
          congr
          exact 𝒞.total_repr (c z) |>.symm
      _ = ∑ i ∈ s, ∑ k ∈ (𝒞.repr (c i)).support, (𝒞.repr (c i)) k • (ℬ i ⊗ₜ[K] 𝒞 k) := by
          refine Finset.sum_congr rfl fun z _ => ?_
          rw [TensorProduct.tmul_sum]
          simp_rw [TensorProduct.smul_tmul', TensorProduct.smul_tmul]
      _ = ∑ i ∈ s, ∑ k ∈ I, (𝒞.repr (c i)) k • (ℬ i ⊗ₜ[K] 𝒞 k) := by
          refine Finset.sum_congr rfl fun j h => ?_
          apply Finset.sum_subset
          · intro i hi
            simp only [Finsupp.mem_support_iff, ne_eq, Finset.mem_biUnion, I] at hi ⊢
            exact ⟨_, h, hi⟩
          · intro i hi1 hi2
            simp only [Finsupp.mem_support_iff, ne_eq, Decidable.not_not, smul_eq_zero]
              at hi1 hi2 ⊢
            tauto
      _ = ∑ ij ∈ s ×ˢ I, (𝒞.repr (c ij.1)) ij.2 • (ℬ ij.1 ⊗ₜ[K] 𝒞 ij.2) := by
          rw [Finset.sum_product]
      _ = ∑ ij ∈ s ×ˢ I, (𝒞.repr (c ij.1)) ij.2 • 𝒯 ij := by
          refine Finset.sum_congr rfl fun ij _ => ?_
          rw [Basis.tensorProduct_apply]
  have LI := 𝒯.linearIndependent
  rw [linearIndependent_iff'] at LI
  specialize LI (s ×ˢ I) _ eq1.symm
  intro i hi
  rw [← 𝒞.total_repr (c i)]
  change ∑ _ ∈ _, _ = 0
  simp only [LinearMap.coe_smulRight, LinearMap.id_coe, id_eq]
  refine Finset.sum_eq_zero fun j hj => ?_
  specialize LI ⟨i, j⟩ (by
    simp only [Finset.mem_product, Finset.mem_biUnion, Finsupp.mem_support_iff, ne_eq, I] at hj ⊢
    exact ⟨hi, ⟨_, hi, hj⟩⟩)
  simp [LI]

lemma Subalgebra.centralizer_sup (K B : Type*) [CommRing K] [Ring B] [Algebra K B]
    (S T : Subalgebra K B) :
    Subalgebra.centralizer K ((S ⊔ T : Subalgebra K B) : Set B) =
    Subalgebra.centralizer K S ⊓ Subalgebra.centralizer K T := by
  ext x
  simp only [Subalgebra.mem_centralizer_iff, SetLike.mem_coe, Algebra.mem_inf]
  constructor
  · intro h
    exact ⟨fun g hg => h g <| (le_sup_left : S ≤ S ⊔ T) hg,
      fun g hg => h g <| (le_sup_right : T ≤ S ⊔ T) hg⟩
  · rintro ⟨h1, h2⟩ g hg
    change g ∈ Algebra.adjoin _ _ at hg
    refine Algebra.adjoin_induction hg ?_ ?_ ?_ ?_
    · rintro y (hy | hy)
      · exact h1 y hy
      · exact h2 y hy
    · intro k
      exact Algebra.commutes k x
    · intro y1 y2 hy1 hy2
      simp [add_mul, hy1, hy2, mul_add]
    · intro y1 y2 hy1 hy2
      rw [mul_assoc, hy2, ← mul_assoc, hy1, mul_assoc]

lemma TensorProduct.left_tensor_base_sup_base_tensor_right
    (K B C : Type*) [CommRing K] [Ring B] [Algebra K B] [Ring C] [Algebra K C] :
    (Algebra.TensorProduct.map (AlgHom.id K B) (Algebra.ofId K C)).range ⊔
    (Algebra.TensorProduct.map (Algebra.ofId K B) (AlgHom.id K C)).range = ⊤ := by
  rw [eq_top_iff]
  rintro x -
  induction x using TensorProduct.induction_on with
  | zero => exact Subalgebra.zero_mem _
  | tmul b c =>
    rw [show b ⊗ₜ[K] c = b ⊗ₜ[K] 1 * 1 ⊗ₜ[K] c by simp]
    exact Algebra.mul_mem_sup ⟨b ⊗ₜ 1, by simp⟩ ⟨1 ⊗ₜ c, by simp⟩
  | add x y hx hy =>
    exact Subalgebra.add_mem _ hx hy

-- We need to restrict the universe, because we used properties of flatness.
lemma TensorProduct.submodule_tensor_inf_tensor_submodule [Small.{v, u} K]
    (B C : Type v) [AddCommGroup B] [Module K B] [AddCommGroup C] [Module K C]
    (b : Submodule K B) (c : Submodule K C) :
    LinearMap.range (TensorProduct.map b.subtype .id) ⊓
    LinearMap.range (TensorProduct.map .id c.subtype) =
    LinearMap.range (TensorProduct.map b.subtype c.subtype) := by

  refine le_antisymm ?_ ?_
  · letI : Module.Flat K (B ⧸ b) := Module.Flat.of_free _ _

    let u : b ⊗[K] c →ₗ[K] B ⊗[K] c := TensorProduct.map b.subtype LinearMap.id
    let v : B ⊗[K] c →ₗ[K] (B ⧸ b) ⊗[K] c :=
      TensorProduct.map (Submodule.mkQ _) LinearMap.id
    have exactuv : Function.Exact u v := by
      apply rTensor_exact
      rw [LinearMap.exact_iff]
      simp only [Submodule.ker_mkQ, Submodule.range_subtype]
      exact Submodule.mkQ_surjective _

    let u' : b ⊗[K] C →ₗ[K] B ⊗[K] C := TensorProduct.map b.subtype LinearMap.id
    let v' : B ⊗[K] C →ₗ[K] (B ⧸ b) ⊗[K] C := TensorProduct.map (Submodule.mkQ _) LinearMap.id
    have exactu'v' : Function.Exact u' v' := by
      apply rTensor_exact
      rw [LinearMap.exact_iff]
      simp only [Submodule.ker_mkQ, Submodule.range_subtype]
      exact Submodule.mkQ_surjective _

    let α : b ⊗[K] c →ₗ[K] b ⊗[K] C := TensorProduct.map LinearMap.id c.subtype
    let β : B ⊗[K] c →ₗ[K] B ⊗[K] C := TensorProduct.map LinearMap.id c.subtype
    let γ : (B ⧸ b) ⊗[K] c →ₗ[K] (B ⧸ b) ⊗[K] C := TensorProduct.map LinearMap.id c.subtype

    have γ_inj : Function.Injective γ :=
      Module.Flat.iff_lTensor_preserves_injective_linearMap K (B ⧸ b) |>.1 inferInstance
        c.subtype c.injective_subtype

    rintro z (hz : z ∈ LinearMap.range u' ⊓ LinearMap.range β)
    obtain ⟨z, rfl⟩ := hz.2
    have comm0 : v' ∘ₗ β = γ ∘ₗ v := by
      ext
      simp [v', β, γ, v]
    have hz1 : v' (β z) = γ (v z) := congr($comm0 z)
    have hz2 : v' (β z) = 0 := by
      rw [← LinearMap.mem_ker]
      rw [LinearMap.exact_iff] at exactu'v'
      rw [exactu'v']
      exact hz.1
    rw [hz2] at hz1
    have hz3 : v z ∈ LinearMap.ker γ := by rw [LinearMap.mem_ker]; exact hz1.symm
    replace hz3 : v z = 0 := by
      rw [← LinearMap.ker_eq_bot] at γ_inj; rw [γ_inj] at hz3; exact hz3
    replace hz3 : z ∈ LinearMap.ker v := hz3
    replace hz3 : z ∈ LinearMap.range u := by
      rw [LinearMap.exact_iff] at exactuv
      rwa [← exactuv]
    obtain ⟨z, rfl⟩ := hz3
    change (β ∘ₗ u) z ∈ _

    have comm1 : β ∘ₗ u = u' ∘ₗ α := by
      ext
      simp [β, u, u', α]

    rw [comm1, LinearMap.comp_apply]
    refine ⟨z, ?_⟩
    simp only [u', α]
    change _ = (TensorProduct.map b.subtype .id ∘ₗ TensorProduct.map .id c.subtype) z
    rw [← TensorProduct.map_comp, LinearMap.comp_id, LinearMap.id_comp]

  · rintro _ ⟨x, rfl⟩
    refine ⟨⟨TensorProduct.map LinearMap.id c.subtype x, ?_⟩,
      ⟨TensorProduct.map b.subtype LinearMap.id x, ?_⟩⟩
    · change (TensorProduct.map b.subtype LinearMap.id ∘ₗ
        TensorProduct.map LinearMap.id c.subtype) x = _
      rw [← TensorProduct.map_comp]
      rfl
    · change (TensorProduct.map LinearMap.id c.subtype ∘ₗ
        TensorProduct.map b.subtype LinearMap.id) x = _
      rw [← TensorProduct.map_comp]
      rfl

end should_be_elsewhere

lemma centralizer_tensorProduct_eq_center_tensorProduct_right
    (B : Type*) [Ring B] [Algebra K B]
    (C : Type*) [Ring C] [Algebra K C] :
    Subalgebra.centralizer K
      (Algebra.TensorProduct.map (AlgHom.id K B) (Algebra.ofId K C)).range =
      (Algebra.TensorProduct.map (Subalgebra.center K B).val (AlgHom.id K C)).range := by
  ext w; constructor
  · intro hw
    rw [Subalgebra.mem_centralizer_iff] at hw
    let 𝒞 := Basis.ofVectorSpace K C
    obtain ⟨S, b, rfl⟩ := TensorProduct.eq_repr_basis_right K B C 𝒞 w

    have aux (i) (hi : i ∈ S) : b i ∈ Subalgebra.center K B := by
      rw [Subalgebra.mem_center_iff]
      intro x
      specialize hw (x ⊗ₜ[K] 1) (by
        simp only [AlgHom.coe_range, Set.mem_range]
        exact ⟨x ⊗ₜ[K] 1, by simp⟩)
      simp only [Finset.mul_sum, Algebra.TensorProduct.tmul_mul_tmul, one_mul, Finset.sum_mul,
        mul_one] at hw
      rw [← sub_eq_zero, ← Finset.sum_sub_distrib] at hw
      simp_rw [← TensorProduct.sub_tmul] at hw
      simpa [sub_eq_zero] using TensorProduct.sum_tmul_basis_right_eq_zero K B C 𝒞 S _ hw i hi
    exact Subalgebra.sum_mem _ fun j hj => ⟨⟨b j, aux _ hj⟩ ⊗ₜ[K] 𝒞 j, by simp⟩
  · rintro ⟨w, rfl⟩
    rw [Subalgebra.mem_centralizer_iff]
    rintro _ ⟨x, rfl⟩
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul b c =>
      simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul,
        Subalgebra.coe_val, AlgHom.coe_id, id_eq]
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul x0 x1 =>
        simp only [Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq,
          Algebra.TensorProduct.tmul_mul_tmul]
        rcases b with ⟨b, hb⟩
        congr 1
        · rw [Subalgebra.mem_center_iff] at hb
          exact hb _
        · exact Algebra.commutes _ _
      | add x x' hx hx' =>
        rw [map_add, add_mul, hx, hx', mul_add]
    | add y z hy hz =>
      rw [map_add, mul_add, hy, hz, add_mul]

lemma centralizer_tensorProduct_eq_left_tensorProduct_center
    (B : Type*) [Ring B] [Algebra K B]
    (C : Type*) [Ring C] [Algebra K C] :
    Subalgebra.centralizer K
      (Algebra.TensorProduct.map (Algebra.ofId K B) (AlgHom.id K C)).range =
      (Algebra.TensorProduct.map (AlgHom.id K B) (Subalgebra.center K C).val).range := by
  have H1 := centralizer_tensorProduct_eq_center_tensorProduct_right K C B
  ext z
  have h1 :
      z ∈ Subalgebra.centralizer K
        (Algebra.TensorProduct.map (Algebra.ofId K B) (AlgHom.id K C)).range  ↔
      (Algebra.TensorProduct.comm K B C z) ∈ Subalgebra.centralizer K
        (Algebra.TensorProduct.map (AlgHom.id K C) (Algebra.ofId K B)).range := by
    rw [Subalgebra.mem_centralizer_iff, Subalgebra.mem_centralizer_iff]
    constructor
    · rintro h _ ⟨x, rfl⟩
      specialize h (Algebra.TensorProduct.comm K C B
        (Algebra.TensorProduct.map (AlgHom.id K C) (Algebra.ofId K B) x))
        (by
          simp only [AlgHom.coe_range, Set.mem_range]
          refine ⟨Algebra.TensorProduct.comm K C K x, ?_⟩
          change (AlgHom.comp (Algebra.TensorProduct.map (Algebra.ofId K B) (AlgHom.id K C))
            (Algebra.TensorProduct.comm K C K)) x =
            (AlgHom.comp (Algebra.TensorProduct.comm K C B)
              (Algebra.TensorProduct.map (AlgHom.id K C) (Algebra.ofId K B))) x
          refine DFunLike.congr_fun ?_ x
          ext
          simp)

      apply_fun Algebra.TensorProduct.comm K C B
      simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_mul]
      convert h  <;>
      rw [← Algebra.TensorProduct.comm_symm] <;>
      simp only [AlgEquiv.symm_apply_apply]
    · rintro h _ ⟨x, rfl⟩
      specialize h (Algebra.TensorProduct.comm K B C
        (Algebra.TensorProduct.map (Algebra.ofId K B) (AlgHom.id K C) x))
        (by
          simp only [AlgHom.coe_range, Set.mem_range]
          refine ⟨Algebra.TensorProduct.comm K K C x, ?_⟩
          change (AlgHom.comp (Algebra.TensorProduct.map (AlgHom.id K C) (Algebra.ofId K B))
            (Algebra.TensorProduct.comm K K C)) x =
            (AlgHom.comp (Algebra.TensorProduct.comm K B C)
              (Algebra.TensorProduct.map (Algebra.ofId K B) (AlgHom.id K C))) x
          refine DFunLike.congr_fun ?_ x
          ext
          simp)
      apply_fun Algebra.TensorProduct.comm K B C
      simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_mul]
      convert h
  rw [h1, H1]
  simp only [AlgHom.mem_range]
  constructor
  · rintro ⟨x, hx⟩
    apply_fun (Algebra.TensorProduct.comm K B C).symm at hx
    simp only [AlgEquiv.symm_apply_apply] at hx
    refine ⟨(Algebra.TensorProduct.comm K B _).symm x, Eq.trans ?_ hx⟩
    simp only [Algebra.TensorProduct.comm_symm]
    change (AlgHom.comp (Algebra.TensorProduct.map (AlgHom.id K B) (Subalgebra.center K C).val)
      (Algebra.TensorProduct.comm K (Subalgebra.center K C) B)) x =
      (AlgHom.comp (Algebra.TensorProduct.comm K C B)
      (Algebra.TensorProduct.map (Subalgebra.center K C).val (AlgHom.id K B))) x
    refine DFunLike.congr_fun ?_ x
    ext x
    simp only [AlgHom.coe_comp, AlgHom.coe_coe, Function.comp_apply,
      Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.comm_tmul,
      Algebra.TensorProduct.map_tmul, map_one, Subalgebra.coe_val]
    rfl
  · rintro ⟨x, hx⟩
    refine ⟨Algebra.TensorProduct.comm _ _ _ x, ?_⟩
    apply_fun (Algebra.TensorProduct.comm K B C).symm
    simp only [AlgEquiv.symm_apply_apply]
    rw [← hx]
    change AlgHom.comp (Algebra.TensorProduct.comm K B C).symm
      (AlgHom.comp (Algebra.TensorProduct.map (Subalgebra.center K C).val (AlgHom.id K B))
        (Algebra.TensorProduct.comm K B ↥(Subalgebra.center K C))) x =
      (Algebra.TensorProduct.map (AlgHom.id K B) (Subalgebra.center K C).val) x
    refine DFunLike.congr_fun ?_ x
    ext x
    simp only [AlgHom.coe_comp, AlgHom.coe_coe, Function.comp_apply,
      Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.comm_tmul,
      Algebra.TensorProduct.map_tmul, map_one, AlgHom.coe_id, id_eq,
      Algebra.TensorProduct.comm_symm_tmul, Algebra.TensorProduct.map_comp_includeLeft,
      AlgHom.comp_id]
    rfl

-- We need to restrict the universe, because we used properties of flatness.
lemma center_tensorProduct [Small.{v, u} K]
    (B C : Type v) [Ring B] [Algebra K B] [Ring C] [Algebra K C] :
    Subalgebra.center K (B ⊗[K] C) =
      (Algebra.TensorProduct.map (Subalgebra.center K B).val
        (Subalgebra.center K C).val).range := by
  rw [show Subalgebra.center K (B ⊗[K] C) = Subalgebra.centralizer K (⊤ : Subalgebra K (B ⊗[K] C))
    by simp, ← TensorProduct.left_tensor_base_sup_base_tensor_right K B C,
    Subalgebra.centralizer_sup, centralizer_tensorProduct_eq_center_tensorProduct_right,
    centralizer_tensorProduct_eq_left_tensorProduct_center]
  suffices eq :
    Subalgebra.toSubmodule (Algebra.TensorProduct.map (Subalgebra.center K B).val (AlgHom.id K C)).range ⊓
    Subalgebra.toSubmodule (Algebra.TensorProduct.map (AlgHom.id K B) (Subalgebra.center K C).val).range =
    Subalgebra.toSubmodule (Algebra.TensorProduct.map (Subalgebra.center K B).val (Subalgebra.center K C).val).range by
    apply_fun Subalgebra.toSubmodule using Subalgebra.toSubmodule_injective
    rw [← eq]
    ext x
    simp only [Algebra.inf_toSubmodule, Submodule.mem_inf, Subalgebra.mem_toSubmodule,
      AlgHom.mem_range]

  have eq1:
      Subalgebra.toSubmodule (Algebra.TensorProduct.map (Subalgebra.center K B).val (AlgHom.id K C)).range =
      LinearMap.range (TensorProduct.map (Subalgebra.center K B).val.toLinearMap (LinearMap.id)) := by
    rfl
  rw [eq1]

  have eq2 :
      Subalgebra.toSubmodule (Algebra.TensorProduct.map (AlgHom.id K B) (Subalgebra.center K C).val).range =
      LinearMap.range (TensorProduct.map (LinearMap.id) (Subalgebra.center K C).val.toLinearMap) := by
    rfl
  rw [eq2]

  have eq3 :
      Subalgebra.toSubmodule (Algebra.TensorProduct.map (Subalgebra.center K B).val (Subalgebra.center K C).val).range =
      LinearMap.range (TensorProduct.map (Subalgebra.center K B).val.toLinearMap
        (Subalgebra.center K C).val.toLinearMap) := by
    rfl
  rw [eq3]

  have := TensorProduct.submodule_tensor_inf_tensor_submodule K B C
    (Subalgebra.toSubmodule <| .center K B)
    (Subalgebra.toSubmodule <| .center K C)

  have eq4 : (Subalgebra.toSubmodule (Subalgebra.center K B)).subtype =
    (Subalgebra.center K B).val.toLinearMap := by rfl
  rw [eq4] at this

  have eq5 : (Subalgebra.toSubmodule (Subalgebra.center K C)).subtype =
    (Subalgebra.center K C).val.toLinearMap := by rfl
  rw [eq5] at this
  rw [this]

example : true := rfl

lemma TensorProduct.isCentral [Small.{v, u} K]
    (A B : Type v) [Ring A] [Algebra K A] [Ring B] [Algebra K B]
    (isCentral_A : Subalgebra.center K A ≤ ⊥)
    (isCentral_B : Subalgebra.center K B ≤ ⊥) :
    Subalgebra.center K (A ⊗[K] B) ≤ ⊥ := by
  intro _ H
  obtain ⟨x, rfl⟩ := le_of_eq (center_tensorProduct K A B) H; clear H
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | tmul a b =>
    obtain ⟨a', ha⟩ := isCentral_A a.2
    obtain ⟨b', hb⟩ := isCentral_B b.2
    refine ⟨b' * a', ?_⟩
    simp only [AlgHom.toRingHom_eq_coe, map_mul, RingHom.coe_coe, Algebra.TensorProduct.map_tmul,
      Subalgebra.coe_val, ← ha, ← hb]
    change _ ⊗ₜ _ = _
    simp only [LinearMap.mul_apply', mul_one]
    rw [← Algebra.smul_def, TensorProduct.smul_tmul, ← Algebra.algebraMap_eq_smul_one]
    rfl
  | add x y hx hy =>
    obtain ⟨kx, hx⟩ := hx
    obtain ⟨ky, hy⟩ := hy
    refine ⟨kx + ky, ?_⟩
    rw [map_add, hx, hy, map_add]

instance TensorProduct.nontrivial
    (A B : Type v) [Ring A] [Algebra K A] [Ring B] [Algebra K B]
    [Nontrivial A] [Nontrivial B] :
    Nontrivial (A ⊗[K] B) := by
  refine ⟨0, 1, fun r => ?_⟩
  let f : K ⊗[K] B →ₐ[K] A ⊗[K] B :=
    Algebra.TensorProduct.map (Algebra.ofId _ _) (.id _ _)
  have hf : Function.Injective f := Module.Flat.rTensor_preserves_injective_linearMap _
    (algebraMap K A).injective
  have r' : f 0 = f 1 := by convert r; simp [f]
  specialize hf r'
  apply_fun Algebra.TensorProduct.lid K B at hf
  simp only [map_zero, map_one] at hf
  exact zero_ne_one hf

variable {K} in
/--
a non-zero element in an ideal that can be represented as a sum of tensor products of `n`-terms.
-/
structure is_obtainable_by_sum_tmul
    {ιA A B : Type*} [Ring A] [Algebra K A] [Ring B] [Algebra K B]
    (x : A ⊗[K] B) (𝒜 : Basis ιA K A) (I : RingCon $ A ⊗[K] B) (n : ℕ) : Prop :=
  mem : x ∈ I
  ne_zero : x ≠ 0
  rep : ∃ (s : Finset ιA) (_ : s.card = n) (f : ιA → B),
    x = ∑ i in s, 𝒜 i ⊗ₜ[K] f i

variable {K} in
lemma is_obtainable_by_sum_tmul.exists_minimal_element
    {A B : Type v} [Ring A] [Algebra K A] [Ring B] [Algebra K B]
    (ιA : Type*) (𝒜 : Basis ιA K A)
    (I : RingCon (A ⊗[K] B)) (hI : I ≠ ⊥) :
    ∃ (n : ℕ) (x : A ⊗[K] B), is_obtainable_by_sum_tmul x 𝒜 I n ∧
      ∀ (m : ℕ) (y : A ⊗[K] B) , is_obtainable_by_sum_tmul y 𝒜 I m → n ≤ m := by
  classical
  have := SetLike.ext_iff.not.mp hI
  push_neg at this

  obtain ⟨x, ⟨hx0, hx1⟩|⟨hx0, hx1⟩⟩ := this
  pick_goal 2
  · change x = 0 at hx1
    subst hx1
    exact hx0 I.zero_mem |>.elim
  obtain ⟨s, c, rfl⟩ := TensorProduct.eq_repr_basis_left K A B 𝒜 x
  let n := @Nat.find (fun n => ∃ x : A ⊗[K] B, is_obtainable_by_sum_tmul x 𝒜 I n) _
    ⟨s.card, ∑ i ∈ s, 𝒜 i ⊗ₜ[K] c i, ⟨hx0, hx1, s, rfl, c, rfl⟩⟩
  obtain ⟨x, hx⟩ : ∃ x, is_obtainable_by_sum_tmul x 𝒜 I n :=
    @Nat.find_spec (fun n => ∃ x : A ⊗[K] B, is_obtainable_by_sum_tmul x 𝒜 I n) _
      ⟨s.card, ∑ i ∈ s, 𝒜 i ⊗ₜ[K] c i, ⟨hx0, hx1, s, rfl, c, rfl⟩⟩
  refine ⟨n, x, hx, fun m y hy => ?_⟩
  by_contra r
  simp only [not_le] at r
  have := @Nat.find_min (fun n => ∃ x : A ⊗[K] B, is_obtainable_by_sum_tmul x 𝒜 I n) _
      ⟨s.card, ∑ i ∈ s, 𝒜 i ⊗ₜ[K] c i, ⟨hx0, hx1, s, rfl, c, rfl⟩⟩ m r
  simp only [not_exists] at this
  exact this y hy

lemma TensorProduct.map_comap_eq_of_isSimple_isCentralSimple
    {A B : Type v} [Ring A] [Algebra K A] [Ring B] [Algebra K B]
    [isSimple_A : IsSimpleOrder $ RingCon A]
    [isCentralSimple_B : IsCentralSimple K B]
    (I : RingCon (A ⊗[K] B)) :
    I = RingCon.span
      (Set.image (Algebra.TensorProduct.includeLeft : A →ₐ[K] A ⊗[K] B) $
        I.comap (Algebra.TensorProduct.includeLeft : A →ₐ[K] A ⊗[K] B)) := by
  classical
  refine le_antisymm ?_ ?_
  · if I_ne_bot : I = ⊥
    then subst I_ne_bot; exact bot_le
    else

    let f : A →ₐ[K] A ⊗[K] B := Algebra.TensorProduct.includeLeft
    change I ≤ RingCon.span (Set.image f $ I.comap f)
    let 𝒜 := Basis.ofVectorSpace K A
    obtain ⟨n, x, ⟨x_mem, x_ne_zero, ⟨s, card_s, b, rfl⟩⟩, H⟩ :=
      is_obtainable_by_sum_tmul.exists_minimal_element _ 𝒜 I I_ne_bot

    have b_ne_zero : ∀ i ∈ s, b i ≠ 0 := by
      by_contra! h
      rcases h with ⟨i, h1, h2⟩

      specialize H (n - 1) (∑ i ∈ s, 𝒜 i ⊗ₜ[K] b i) ⟨x_mem, x_ne_zero, ⟨s.erase i,
        by rw [Finset.card_erase_of_mem, card_s]; exact h1, b, by
        symm
        fapply Finset.sum_subset
        · exact Finset.erase_subset i s
        · intro x hx1 hx2
          simp only [Finset.mem_erase, ne_eq, not_and] at hx2
          rw [show x = i by tauto, h2, TensorProduct.tmul_zero]⟩⟩
      have ineq1 : 0 < n := by
        rw [← card_s, Finset.card_pos]
        exact ⟨i, h1⟩
      omega

    if s_ne_empty : s = ∅
    then
      subst s_ne_empty
      simp only [Finset.card_empty, Finset.sum_empty, ne_eq, not_true_eq_false] at *
    else
      obtain ⟨i₀, hi₀⟩ := Finset.nonempty_iff_ne_empty.mpr s_ne_empty

      have ineq1 : 0 < n := by
        rw [← card_s, Finset.card_pos]
        exact ⟨i₀, hi₀⟩

      have x_eq' :
          ∑ i ∈ s, 𝒜 i ⊗ₜ[K] b i =
          𝒜 i₀ ⊗ₜ[K] b i₀ +
          ∑ i ∈ s.erase i₀, 𝒜 i ⊗ₜ[K] b i := by
        rw [show 𝒜 i₀ ⊗ₜ[K] b i₀ = ∑ i ∈ {i₀}, 𝒜 i ⊗ₜ[K] b i by rw [Finset.sum_singleton],
          ← Finset.sum_disjUnion]
        pick_goal 2
        · rw [← Finset.disjoint_erase_comm]
          simp only [Finset.erase_singleton, Finset.image_empty, Finset.disjoint_empty_left]
        refine Finset.sum_congr ?_ fun _ _ => rfl
        ext x
        simp only [Finset.disjUnion_eq_union, Finset.mem_union, Finset.mem_singleton,
          Finset.mem_erase, ne_eq]
        constructor
        · intro hx
          if hx' : x = i₀ then left; exact hx'
          else right; exact ⟨hx', hx⟩
        · rintro (rfl|⟨_, hx2⟩) <;> assumption


      have span_bi₀ : RingCon.span {b i₀} = ⊤ := isCentralSimple_B.2.2 _ |>.resolve_left fun r => by
        have mem : b i₀ ∈ ⊥ := by
          rw [← r]
          apply RingCon.subset_span
          simp only [Set.mem_singleton_iff]
        exact b_ne_zero i₀ hi₀ mem

      have one_mem : (1 : B) ∈ RingCon.span {b i₀} := by rw [span_bi₀]; trivial
      rw [RingCon.mem_span_iff_exists_fin] at one_mem
      obtain ⟨ℐ, inst1, xL, xR, y, one_eq⟩ := one_mem

      replace one_eq : 1 = ∑ i : ℐ, xL i * b i₀ * xR i := by
        rw [one_eq]
        refine Finset.sum_congr rfl fun i _ => ?_
        congr
        simpa only [Set.mem_singleton_iff] using (y i).2

      let ω := ∑ i ∈ s, 𝒜 i ⊗ₜ[K] b i
      let Ω := ∑ i : ℐ, (1 ⊗ₜ[K] xL i) * ω * (1 ⊗ₜ[K] xR i)
      have Ω_in_I : Ω ∈ I := RingCon.sum_mem _ _ fun i _ => I.mul_mem_right _ _ $
        I.mul_mem_left _ _ x_mem

      have Ω_eq :
          Ω =
          𝒜 i₀ ⊗ₜ[K] (∑ i : ℐ, xL i * b i₀ * xR i) +
          ∑ i ∈ s.erase i₀, 𝒜 i ⊗ₜ[K] (∑ j : ℐ, xL j * b i * xR j) := by
        dsimp only [Ω, ω]
        simp only [x_eq', mul_add, Algebra.TensorProduct.tmul_mul_tmul, one_mul, Finset.mul_sum,
          add_mul, mul_one, Finset.sum_mul, Finset.sum_add_distrib, TensorProduct.tmul_sum,
          add_right_inj]
        rw [Finset.sum_comm]
      rw [← one_eq] at Ω_eq

      have Ω_prop_1 (b : B) : (1 ⊗ₜ b) * Ω - Ω * (1 ⊗ₜ b) ∈ I :=
        I.sub_mem (I.mul_mem_left _ _ Ω_in_I) (I.mul_mem_right _ _ Ω_in_I)

      have Ω_prop_2 (x : B) : ((1 : A) ⊗ₜ[K] x) * Ω - Ω * ((1 : A) ⊗ₜ[K] x) =
          ∑ i ∈ s.erase i₀, 𝒜 i ⊗ₜ[K]
            (∑ j : ℐ, (x * (xL j * b i * xR j) - (xL j * b i * xR j) * x)) := by
        rw [Ω_eq]
        simp only [TensorProduct.tmul_sum, mul_add, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
          mul_one, Finset.mul_sum, add_mul, Finset.sum_mul, add_sub_add_left_eq_sub,
          Finset.sum_sub_distrib, TensorProduct.tmul_sub]

      have Ω_prop_3 (x : B) : ((1 : A) ⊗ₜ[K] x) * Ω - Ω * ((1 : A) ⊗ₜ[K] x) = 0 := by
        by_contra rid
        specialize H (n - 1) (((1 : A) ⊗ₜ[K] x) * Ω - Ω * ((1 : A) ⊗ₜ[K] x))
          ⟨Ω_prop_1 x, rid, ⟨s.erase i₀, by rw [Finset.card_erase_of_mem, card_s]; exact hi₀, _,
            Ω_prop_2 x⟩⟩
        omega

      simp_rw [Ω_prop_2] at Ω_prop_3
      have Ω_prop_4 : ∀ i ∈ s.erase i₀,
          ∑ j : ℐ, (xL j * b i * xR j) ∈ Subalgebra.center K B := by
        intro i hi
        rw [Subalgebra.mem_center_iff]
        intro x
        specialize Ω_prop_3 x
        simp only [Finset.mul_sum, Finset.sum_mul, ← sub_eq_zero, sub_zero]
        rw [← Finset.sum_sub_distrib]
        simpa using TensorProduct.sum_tmul_basis_left_eq_zero K A B 𝒜 (s.erase i₀) _ Ω_prop_3 i hi

      simp_rw [IsCentralSimple.center_eq, Algebra.mem_bot, Set.mem_range] at Ω_prop_4
      choose k hk using Ω_prop_4
      have Ω_eq2 := calc Ω
        _ = 𝒜 i₀ ⊗ₜ[K] 1 + ∑ i ∈ s.erase i₀, 𝒜 i ⊗ₜ[K] ∑ j : ℐ, xL j * b i * xR j := Ω_eq
        _ = 𝒜 i₀ ⊗ₜ[K] 1 + ∑ i ∈ (s.erase i₀).attach, 𝒜 i ⊗ₜ[K] ∑ j : ℐ, xL j * b i * xR j := by
            congr 1
            exact Finset.sum_attach _ _ |>.symm
        _ = 𝒜 i₀ ⊗ₜ[K] 1 + ∑ i ∈ (s.erase i₀).attach, 𝒜 i ⊗ₜ[K] algebraMap _ _ (k i.1 i.2) := by
            congr 1
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [hk i.1 i.2]
        _ = 𝒜 i₀ ⊗ₜ[K] 1 +  ∑ i ∈ (s.erase i₀).attach, 𝒜 i ⊗ₜ[K] (k i.1 i.2 • (1 : B) : B) := by
            congr 1
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [Algebra.algebraMap_eq_smul_one]
        _ = 𝒜 i₀ ⊗ₜ[K] 1 + ∑ i ∈ (s.erase i₀).attach, (k i.1 i.2 • 𝒜 i) ⊗ₜ[K] (1 : B) := by
            congr 1
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [TensorProduct.smul_tmul]
        _ = 𝒜 i₀ ⊗ₜ[K] 1 + (∑ i ∈ (s.erase i₀).attach, (k i.1 i.2 • 𝒜 i)) ⊗ₜ[K] (1 : B) := by
            rw [TensorProduct.sum_tmul]
        _ = (𝒜 i₀ + (∑ i ∈ (s.erase i₀).attach, (k i.1 i.2 • 𝒜 i))) ⊗ₜ[K] 1 := by
            rw [TensorProduct.add_tmul]

      rw [Ω_eq2] at Ω_in_I
      have hI : I.comap f = ⊤ := isSimple_A.2 _ |>.resolve_left fun r => by
        have mem : 𝒜 i₀ + (∑ i ∈ (s.erase i₀).attach, (k i.1 i.2 • 𝒜 i)) ∈ I.comap f := by
          rw [RingCon.mem_comap]
          exact Ω_in_I
        rw [r] at mem
        change _ = 0 at mem
        rw [mem, TensorProduct.zero_tmul] at Ω_eq2
        have LI := 𝒜.linearIndependent
        rw [linearIndependent_iff'] at LI
        specialize LI s (fun i =>
          if i = i₀ then 1
          else if h : i ∈ s.erase i₀ then k i h else 0) (by
          dsimp only
          simp_rw [ite_smul, one_smul, dite_smul, zero_smul]
          rw [Finset.sum_ite,
            show ∑ x ∈ Finset.filter (fun x ↦ x = i₀) s, 𝒜 x = ∑ x ∈ {i₀}, 𝒜 x by
            refine Finset.sum_congr ?_ fun _ _ => rfl
            ext
            simp only [Finset.mem_filter, Finset.mem_singleton, and_iff_right_iff_imp]
            rintro rfl
            exact hi₀, Finset.sum_singleton,
            show Finset.filter (fun x ↦ ¬x = i₀) s = s.erase i₀ by
            ext
            simp only [Finset.mem_filter, Finset.mem_erase, ne_eq]
            rw [and_comm], ← Finset.sum_attach]
          conv_rhs => rw [← mem]
          congr 1
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [dif_pos i.2]) i₀ hi₀
        rw [if_pos rfl] at LI
        exact zero_ne_one LI.symm
      rw [hI, RingCon.coe_top_set, RingCon.le_iff]
      rintro x -
      rw [SetLike.mem_coe]
      induction x using TensorProduct.induction_on with
      | zero => simp [RingCon.zero_mem]
      | tmul a b =>
        rw [show a ⊗ₜ[K] b = (a ⊗ₜ 1) * (1 ⊗ₜ b) by simp]
        exact RingCon.mul_mem_right _ _ _ $ RingCon.subset_span _ $ ⟨a, ⟨⟩, rfl⟩
      | add x y hx hy => exact RingCon.add_mem _ hx hy

  · rw [← RingCon.span_le]
    rintro _ ⟨x, hx, rfl⟩
    rw [SetLike.mem_coe, RingCon.mem_comap] at hx
    exact hx

instance TensorProduct.simple
    (A B : Type v) [Ring A] [Algebra K A] [Ring B] [Algebra K B]
    [isSimple_A : IsSimpleOrder $ RingCon A]
    [isCentralSimple_B : IsCentralSimple K B] :
    IsSimpleOrder (RingCon (A ⊗[K] B)) := by
  haveI := isCentralSimple_B.2
  let f : A →ₐ[K] A ⊗[K] B := Algebra.TensorProduct.includeLeft
  suffices eq1 : ∀ (I : RingCon (A ⊗[K] B)),
      I = RingCon.span (Set.image f $ I.comap f) by
    refine ⟨fun I => ?_⟩
    specialize eq1 I
    rcases isSimple_A.2 (I.comap f) with h|h
    · left
      rw [h, RingCon.coe_bot_set, Set.image_singleton, map_zero] at eq1
      rw [eq1, eq_bot_iff, RingCon.le_iff]
      rintro x hx
      rw [SetLike.mem_coe, RingCon.mem_span_iff_exists_fin] at hx
      obtain ⟨ι, inst, xL, xR, y, rfl⟩ := hx
      rw [SetLike.mem_coe]
      refine RingCon.sum_mem _ _ fun i _ => ?_
      have := (y i).2
      simp only [Set.mem_singleton_iff] at this
      rw [this, mul_zero, zero_mul]
      rfl
    · right
      rw [h, RingCon.coe_top_set] at eq1
      rw [eq1, eq_top_iff, RingCon.le_iff]
      rintro x -
      rw [SetLike.mem_coe]
      induction x using TensorProduct.induction_on with
      | zero => simp [RingCon.zero_mem]
      | tmul a b =>
        rw [show a ⊗ₜ[K] b = (a ⊗ₜ 1) * (1 ⊗ₜ b) by simp]
        exact RingCon.mul_mem_right _ _ _ $ RingCon.subset_span _ $ ⟨a, ⟨⟩, rfl⟩
      | add x y hx hy => exact RingCon.add_mem _ hx hy

  apply TensorProduct.map_comap_eq_of_isSimple_isCentralSimple

-- We can't have `L` to have different universe level of `D` in this proof, again due that we used
-- `flatness`
instance baseChange
    [Small.{v, u} K] (L : Type v) [Field L] [Algebra K L] [h : IsCentralSimple K D] :
    IsCentralSimple L (L ⊗[K] D) where
  is_central:= by
    intro _ H
    obtain ⟨x, rfl⟩ := le_of_eq (center_tensorProduct K L D) H; clear H
    induction x using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp⟩
    | tmul l d =>
      obtain ⟨k, hk⟩ := h.is_central d.2
      refine ⟨k • l, ?_⟩
      simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul,
        Subalgebra.coe_val, ← hk]
      simp only [Algebra.ofId_apply, Algebra.TensorProduct.algebraMap_apply, Algebra.id.map_eq_id,
        RingHom.id_apply]
      rw [TensorProduct.smul_tmul, Algebra.algebraMap_eq_smul_one]
    | add x y hx hy =>
      obtain ⟨kx, (hkx : kx ⊗ₜ 1 = _)⟩ := hx
      obtain ⟨ky, (hky : ky ⊗ₜ 1 = _)⟩ := hy
      exact ⟨kx + ky, by simp [map_add, Algebra.ofId_apply, hkx, hky]⟩

instance tensorProduct [Small.{v, u} K]
    {A B : Type v} [Ring A] [Algebra K A] [Ring B] [Algebra K B]
    [csA : IsCentralSimple K A] [csB : IsCentralSimple K B] :
    IsCentralSimple K (A ⊗[K] B) where
  is_central := TensorProduct.isCentral _ _ _ csA.1 csB.1
  is_simple := by
    haveI : IsSimpleOrder (RingCon A) := csA.2
    haveI : IsSimpleOrder (RingCon B) := csB.2
    exact TensorProduct.simple K A B

end IsCentralSimple

section CSA_implies_CSA
variable (K : Type u) [Field K]
variable (B : Type*) [Ring B]

lemma top_eq_ring (R :Type*)[Ring R] : (⊤ : RingCon R) = (⊤ : Set R) := by
  aesop

lemma _root_.AlgEquiv.isCentralSimple {K B C : Type*}
    [Field K] [Ring B] [Algebra K B] [hcs : IsCentralSimple K B]
    [Ring C] [Algebra K C] (e : B ≃ₐ[K] C):
    IsCentralSimple K C where
  is_central z hz := by
    obtain ⟨k, hk⟩ := hcs.is_central (show e.symm z ∈ _ by
      simp only [Subalgebra.mem_center_iff] at hz ⊢
      exact fun x => by simpa using congr(e.symm $(hz (e x))))
    exact ⟨k, by simpa [Algebra.ofId_apply] using congr(e $hk)⟩
  is_simple := by
    haveI := hcs.is_simple
    exact RingCon.orderIsoOfRingEquiv e.symm.toRingEquiv |>.isSimpleOrder

theorem CSA_implies_CSA (K : Type*) (B : Type*) [Field K] [Ring B] [Algebra K B]
    (n : ℕ) (D : Type*) (hn : 0 < n) (h : DivisionRing D) [Algebra K D]
    (Wdb: B ≃ₐ[K] (Matrix (Fin n) (Fin n) D)):
    IsCentralSimple K B → IsCentralSimple K D := by
  intro BCS
  letI : Nonempty (Fin n) := ⟨0, hn⟩
  haveI := RingCon.equivRingConMatrix' D (ι := (Fin n)) ⟨0, hn⟩ |>.isSimpleOrder
  refine ⟨fun d hd => ?_⟩
  obtain ⟨k, hk⟩ := Wdb.isCentralSimple.is_central (show (Matrix.diagonal fun _ => d)  ∈ _ by
    rw [Matrix.mem_center_iff']
    refine ⟨⟨d, hd⟩, ?_⟩
    ext i j
    simp only [Matrix.diagonal_apply, Matrix.smul_apply, Matrix.one_apply, smul_ite,
      Submonoid.mk_smul, smul_eq_mul, mul_one, smul_zero])
  refine ⟨k, ?_⟩
  apply_fun (· ⟨0, by omega⟩ ⟨0, by omega⟩) at hk
  simpa using hk

-- restrict to 4d case
-- theorem exists_quaternionAlgebra_iso (hK : (2 : K) ≠ 0) :
--     ∃ a b : K, Nonempty (D ≃ₐ[K] ℍ[K, a, b]) := sorry
