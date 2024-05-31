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

class IsCentralSimple
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

-- lemma baseChange (L : Type w) [Field L] [Algebra K L] : IsCentralSimple L (L ⊗[K] D) := sorry
-- We can't have `L` to have different universe level of `D` in this proof, again due that we used
-- `flatness`
instance baseChange [Small.{v, u} K] (L : Type v) [Field L] [Algebra K L] :
    IsCentralSimple L (L ⊗[K] D) where
  is_central:= by
    intro z hz
    replace hz : z ∈ Subalgebra.center K (L ⊗[K] D) := by
      rw [Subalgebra.mem_center_iff]
      intro x
      rw [Subring.mem_center_iff] at hz
      exact hz x

    rw [center_tensorProduct K L] at hz
    obtain ⟨x, rfl⟩ := hz
    induction x using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp⟩
    | tmul l d =>
      obtain ⟨k, hk⟩ := h.is_central (d := d.1)
        (Subring.mem_center_iff.2 <| fun x ↦ Subalgebra.mem_center_iff.mp d.2 x)
      simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul,
        Subalgebra.coe_val, Algebra.TensorProduct.algebraMap_apply, Algebra.id.map_eq_id,
        RingHom.id_apply]
      simp_rw [hk]
      refine ⟨k • l, ?_⟩
      rw [TensorProduct.smul_tmul, Algebra.algebraMap_eq_smul_one]
    | add x y hx hy =>
      obtain ⟨kx, hkx⟩ := hx
      obtain ⟨ky, hky⟩ := hy
      simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.algebraMap_apply,
        Algebra.id.map_eq_id, RingHom.id_apply] at hkx hky
      refine ⟨kx + ky, ?_⟩
      simp only [AlgHom.toRingHom_eq_coe, map_add, RingHom.coe_coe, hkx, hky,
        Algebra.TensorProduct.algebraMap_apply, Algebra.id.map_eq_id, RingHom.id_apply]
  is_simple := by sorry
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
  is_central := by
    intro z hz
    obtain ⟨k, hk⟩ := hcs.is_central (e.symm z) (by
      simp only [Subring.mem_center_iff] at hz ⊢
      exact fun x => by simpa using congr(e.symm $(hz (e x))))
    exact ⟨k, by simpa using congr(e $hk)⟩
  is_simple := by
    haveI := hcs.is_simple
    exact RingCon.orderIsoOfRingEquiv e.symm.toRingEquiv |>.isSimpleOrder


theorem CSA_implies_CSA (K : Type*) (B : Type*) [Field K] [Ring B] [Algebra K B]
    [IsSimpleOrder (RingCon B)] (n : ℕ)
    (D : Type*) (hn : 0 < n) (h : DivisionRing D) [Algebra K D]
    (Wdb: B ≃ₐ[K] (Matrix (Fin n) (Fin n) D)):
    IsCentralSimple K B → IsCentralSimple K D := by
  intro BCS
  letI inst1 := Wdb.isCentralSimple
  let hnone : Nonempty (Fin n) := ⟨0, hn⟩
  constructor
  · intro d hd
    obtain ⟨k, hk⟩ := inst1.is_central (Matrix.diagonal fun _ => d) (by
      rw [Matrix.mem_center_iff]
      refine ⟨⟨d, hd⟩, ?_⟩
      simp only [Submonoid.mk_smul]
      ext i j
      rw [Matrix.diagonal_apply, Matrix.smul_apply, Matrix.one_apply]
      split_ifs <;> simp)
    refine ⟨k, ?_⟩
    apply_fun (· ⟨0, by omega⟩ ⟨0, by omega⟩) at hk
    simp only [Matrix.diagonal_apply_eq] at hk
    rw [hk]
    rfl
  · exact RingCon.equivRingConMatrix' D (ι := (Fin n)) ⟨0, hn⟩ |>.isSimpleOrder


-- restrict to 4d case
-- theorem exists_quaternionAlgebra_iso (hK : (2 : K) ≠ 0) :
--     ∃ a b : K, Nonempty (D ≃ₐ[K] ℍ[K, a, b]) := sorry
