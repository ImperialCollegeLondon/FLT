/-
Copyright (c) 2024 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/

import Mathlib.Algebra.Quaternion -- probably get away with less
import FLT.for_mathlib.Con
import FLT.for_mathlib.CrazySimple

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

structure IsCentralSimple
    (K : Type u) [Field K] (D : Type v) [Ring D] [Algebra K D] : Prop where
  is_central : ∀ d : D, d ∈ Subring.center D → ∃ k : K, d = algebraMap K D k
  is_simple : IsSimpleOrder (RingCon D)

variable (K : Type u) [Field K]

open Matrix in
theorem MatrixRing.isCentralSimple (ι : Type v) (hι : Fintype ι) (hnonempty : Nonempty ι) [DecidableEq ι] :
    IsCentralSimple K (Matrix ι ι K) where
  is_central d hd := by
    rw [Subring.mem_center_iff] at hd
    convert mem_range_scalar_of_commute_stdBasisMatrix (M := d) fun i j _ => hd _
    simp_rw [Set.mem_range, eq_comm, algebraMap_eq_diagonal, Pi.algebraMap_def,
      Algebra.id.map_eq_self, scalar_apply]
  is_simple := inferInstance

namespace IsCentralSimple

variable (D : Type v) [Ring D] [Algebra K D] (h : IsCentralSimple K D)

/-
\begin{lemma}
    \label{IsCentralSimple.baseChange}
    If $D$ is a central simple algebra over~$K$ and $L/K$ is a field extension, then $L\otimes_KD$
    is a central simple algebra over~$L$.
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
    ∃ (b : ιC → B) (s : Finset ιC), ∑ i ∈ s, b i ⊗ₜ[K] 𝒞 i = x := by
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

lemma TensorProduct.submodule_tensor_inf_tensor_submodule
    (K B C : Type*) [Field K] [AddCommGroup B] [Module K B] [AddCommGroup C] [Module K C]
    (b : Submodule K B) (c : Submodule K C) :
    -- (b ⊗ C) ⊓ (B ⊗ c)
    LinearMap.range (TensorProduct.map b.subtype .id) ⊓
    LinearMap.range (TensorProduct.map .id c.subtype) =
    -- (b ⊗ c)
    LinearMap.range (TensorProduct.map b.subtype c.subtype) := by

  refine le_antisymm ?_ ?_
  · -- hard direction
    -- rw [TensorProduct.map_range_eq_span_tmul, TensorProduct.map_range_eq_span_tmul,
    --   TensorProduct.map_range_eq_span_tmul]
    intro z ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
    let fb : b ⊗[K] C →ₗ[K] B ⊗[K] C := TensorProduct.map b.subtype LinearMap.id -- this is injective
    let fc : B ⊗[K] c →ₗ[K] B ⊗[K] C := TensorProduct.map LinearMap.id c.subtype -- this is injective
    obtain ⟨gb, hgb⟩ := LinearMap.exists_leftInverse_of_injective fb sorry
    obtain ⟨gc, hgc⟩ := LinearMap.exists_leftInverse_of_injective fc sorry

    have eq1 : x = gb (fb x) := DFunLike.congr_fun hgb x |>.symm

    have eq2 : fb x = fc y := by
      apply_fun gb at hx
      sorry
    sorry
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
    obtain ⟨b, S, rfl⟩ := TensorProduct.eq_repr_basis_right K B C 𝒞 w

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

lemma center_tensorProduct
    (B : Type*) [Ring B] [Algebra K B]
    (C : Type*) [Ring C] [Algebra K C] :
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

-- the following proof may not work?
-- lemma baseChange (L : Type w) [Field L] [Algebra K L] : IsCentralSimple L (L ⊗[K] D) := sorry
-- lemma baseChange (L : Type w) [Field L] [Algebra K L] : IsCentralSimple L (L ⊗[K] D) :=
-- {
--   is_central:= by
--     intro z hz
--     induction z using TensorProduct.induction_on with
--     | zero => exact ⟨0, by simp_all⟩
--     | tmul l d =>
--       if l_ne_zero : l = 0
--       then
--         subst l_ne_zero
--         exact ⟨0, by simp⟩
--       else

--         have hcentral := h.is_central d
--         rw [Subring.mem_center_iff] at hz

--         have hd : d ∈ Subring.center D := by
--           rw [Subring.mem_center_iff]
--           intro d0
--           specialize hz (l⁻¹ ⊗ₜ[K] d0)
--           rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul,
--             inv_mul_cancel l_ne_zero, mul_inv_cancel l_ne_zero] at hz
--           have key : ∀ (x y : D), (1 : L) ⊗ₜ[K] (x * y) = (1 : L) ⊗ₜ[K] (y * x) → x * y = y * x:= by
--             intro x y hxy
--             have hzz: (1 : L) ⊗ₜ[K] (x * y - y * x) = 0 := by
--               rw [@TensorProduct.tmul_sub]
--               exact sub_eq_zero_of_eq hxy
--             -- rw [← TensorProduct.tmul_zero D l] at hzz
--             have hzzz: (1 : L) ⊗ₜ[K] (x * y - y * x) = 0 → (x * y - y * x) = 0 := by sorry
--             have auxx: x * y - y * x = 0 := by
--               exact hzzz hzz
--             rw [@sub_eq_zero] at auxx
--             exact auxx
--           simp_all
--           have aux (x y : D) (h : (1 : L) ⊗ₜ[K] x = (1 : L) ⊗ₜ[K] y) :
--               (1 : K) ⊗ₜ[K] x = (1 : K) ⊗ₜ[K] y := by
--             let g : K ⊗[K] D →ₗ[K] L ⊗[K] D :=
--               TensorProduct.map (Algebra.ofId K L).toLinearMap LinearMap.id
--             have hg : Function.Injective g := by
--               rw [← LinearMap.ker_eq_bot, eq_bot_iff]
--               intro x (h : g x = 0)
--               induction x using TensorProduct.induction_on with
--               | zero => simp
--               | tmul k d =>
--                 simp only [TensorProduct.map_tmul, AlgHom.toLinearMap_apply, LinearMap.id_coe,
--                   id_eq, g] at h
--                 sorry
--               | add x y hx hy => sorry
--             apply_fun g
--           sorry

--         have hdd := hcentral hd
--         obtain ⟨dk, hdk⟩ := hdd
--         simp only [Algebra.TensorProduct.algebraMap_apply, Algebra.id.map_eq_id, RingHom.id_apply]
--         use (dk • l)
--         rw [TensorProduct.smul_tmul, Algebra.smul_def]
--         simp only [mul_one]
--         exact congrArg (TensorProduct.tmul K l) hdk
--     | add x y hx hy =>
--       have hzx: x ∈ Subring.center (L ⊗[K] D) := by sorry
--       have hzy: y ∈ Subring.center (L ⊗[K] D) := by sorry
--       obtain ⟨kx, hx'⟩  := hx hzx
--       obtain ⟨ky, hy'⟩  := hy hzy
--       use kx + ky
--       rw[hx', hy']
--       simp only [Algebra.TensorProduct.algebraMap_apply, Algebra.id.map_eq_id, RingHom.id_apply,
--         map_add]
--   is_simple := by sorry
-- }

end IsCentralSimple

-- restrict to 4d case
-- theorem exists_quaternionAlgebra_iso (hK : (2 : K) ≠ 0) :
--     ∃ a b : K, Nonempty (D ≃ₐ[K] ℍ[K, a, b]) := sorry
