-- All of this is in
-- https://github.com/leanprover-community/mathlib4/pull/26377/

/-
Copyright (c) 2025 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang, Yunzhou Xie
-/
module

public import Mathlib.Algebra.Central.Basic
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.RingTheory.TwoSidedIdeal.Operations
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.TwoSidedIdeal.Instances

/-!
# Tensor product of simple algebras over a field

In this file, we show that the tensor product of a simple algebra and a central simple algebra is
simple, which in particular implies that the tensor product of two central simple algebras is
another central simple algebra. This is a prerequisite for defining the group law on the Brauer
group.

## Main Results

* `TensorProduct.simple`: The tensor product of a simple algebra and a central simple algebra
  is simple.

## References

* [StackProject 074B](https://stacks.math.columbia.edu/tag/074B)

## Tags
Noncommutative algebra, tensor product, simple algebra, central simple algebra

-/

@[expose] public section

section some_other_files


namespace TwoSidedIdeal

@[simp]
lemma span_eq_bot {R : Type*} [NonUnitalNonAssocRing R] {s : Set R} :
    span s = ⊥ ↔ ∀ x ∈ s, x = 0 := eq_bot_iff.trans
  ⟨fun H _ h => (mem_bot R).mp <| H <| subset_span h,
   fun H => span_le.mpr fun x h => (mem_bot R).mpr <| H x h⟩

lemma span_singleton_eq_bot {R : Type*} [NonUnitalNonAssocRing R] {x : R} :
  span ({x} : Set R) = ⊥ ↔ x = 0 := by simp

lemma map_bot {R S : Type*}
    [NonUnitalNonAssocRing R] [NonUnitalNonAssocRing S]
    {F : Type*} [FunLike F R S] [ZeroHomClass F R S] {f : F} :
    (⊥ : TwoSidedIdeal R).map f = ⊥ := by
  ext x
  simp [map, coe_bot, Set.image_singleton, map_zero f, mem_bot, span_singleton_eq_bot.2]

protected theorem mem_map_of_mem {R S : Type*}
    [NonUnitalNonAssocRing R] [NonUnitalNonAssocRing S]
    {F : Type*} [FunLike F R S] {f : F} {I : TwoSidedIdeal R}
    {x : R} (hx : x ∈ I) : f x ∈ I.map f :=
  TwoSidedIdeal.subset_span ⟨x, hx, rfl⟩

end TwoSidedIdeal

theorem Submodule.mem_span_range_iff_exists {α M R : Type*}
    [Semiring R] [AddCommMonoid M] [Module R M] {v : α → M} {x : M} :
    x ∈ Submodule.span R (Set.range v) ↔ ∃ (s : Finset α) (c : α → R), ∑ i ∈ s, c i • v i = x := by
  classical
  rw [← Set.image_univ, Submodule.mem_span_image_iff_exists_fun]
  simp only [Set.subset_univ, Finset.univ_eq_attach, true_and, ← Finset.sum_attach (ι := α)]
  refine ⟨fun ⟨s, c, hsc⟩ ↦ ⟨s, fun x ↦ if h : x ∈ s then c ⟨x, h⟩ else 0, ?_⟩,
    fun ⟨s, c, hsc⟩ ↦ ⟨s, c ∘ Subtype.val, by simpa⟩⟩
  convert hsc
  grind

end some_other_files


@[expose] public section

variable (K A B : Type*) [Field K] [Ring A] [Algebra K A] [Ring B] [Algebra K B]

open TensorProduct Module

open TwoSidedIdeal in
lemma TwoSidedIdeal.eq_bot_of_map_comap_eq_bot [hA : IsSimpleRing A]
    [isCentral_A : Algebra.IsCentral K A] [IsSimpleRing B] (I : TwoSidedIdeal (A ⊗[K] B))
    (hAB : letI f : B →ₐ[K] A ⊗[K] B := Algebra.TensorProduct.includeRight
      (I.comap f).map f = ⊥) : I = ⊥ := by
  set f : B →ₐ[K] A ⊗[K] B := Algebra.TensorProduct.includeRight
  obtain ⟨ι, 𝓑⟩ := Module.Free.exists_basis K B
  have main (s : Finset ι) (a : ι → A) (h : ∑ i ∈ s, a i ⊗ₜ[K] 𝓑 i ∈ I) :
      ∀ i ∈ s, a i = 0 := by
    classical
    induction s using Finset.induction_on generalizing a with
    | empty => simp
    | insert j s hjs ih =>
    rcases eq_or_ne (a j) 0 with hj | hj
    · aesop
    · rw [Finset.sum_insert hjs] at h
      have : span {a j} = ⊤ := hA.1.2 _|>.resolve_left fun h ↦ hj <| (mem_bot A).mp <|
        (SetLike.ext_iff.mp h (a j)).mp <| subset_span (by simp)
      have h' : ∀ (x : A) (hx : x ∈ span {a j}), ∃ (ι : Type) (_ : Fintype ι) (xL : ι → A)
          (xR : ι → A), x = ∑ i, xL i * a j * xR i := fun x hx ↦ by
        induction hx using span_induction with
        | mem x h => exact ⟨PUnit, inferInstance, fun _ ↦ 1, fun _ ↦ 1, by simp_all⟩
        | zero => exact ⟨Empty, inferInstance, fun _ ↦ 1, fun _ ↦ 1, by simp⟩
        | add x y hx hy hx1 hy1 =>
          obtain ⟨ι1, _, xL1, xR1, eq1⟩ := hx1
          obtain ⟨ι2, _, xL2, xR2, eq2⟩ := hy1
          exact ⟨(ι1 ⊕ ι2), inferInstance, Sum.elim xL1 xL2, Sum.elim xR1 xR2, by simp [eq1, eq2]⟩
        | neg x hx hx1 =>
          obtain ⟨ι, _, xL, xR, eq⟩ := hx1
          exact ⟨ι, inferInstance, fun i ↦ - (xL i), xR, by simp [eq]⟩
        | left_absorb a x hx hx1 =>
          obtain ⟨ι, _, xL, xR, eq⟩ := hx1
          exact ⟨ι, inferInstance, fun i ↦ a * xL i, xR, by simp [eq, Finset.mul_sum, ← mul_assoc]⟩
        | right_absorb b x hx hx1 =>
          obtain ⟨ι, _, xL, xR, eq⟩ := hx1
          exact ⟨ι, inferInstance, xL, fun i ↦ xR i * b, by simp [eq, Finset.sum_mul, ← mul_assoc]⟩
      obtain ⟨ι', _, xL, xR, eq1⟩ := h' 1 (by simp_all)
      let T' := ∑ i, xL i ⊗ₜ 1 * (a j ⊗ₜ[K] 𝓑 j + ∑ x ∈ s, a x ⊗ₜ[K] 𝓑 x) * xR i ⊗ₜ 1
      have hT'1 : T' ∈ I := sum_mem <| fun _ _ ↦ I.mul_mem_right _ _ <| I.mul_mem_left _ _ h
      have hT'2 : T' = 1 ⊗ₜ 𝓑 j + ∑ j ∈ s, (∑ i, xL i * a j * xR i) ⊗ₜ 𝓑 j := by
        simp +zetaDelta only [mul_add, Algebra.TensorProduct.tmul_mul_tmul, one_mul, Finset.mul_sum,
          add_mul, mul_one, Finset.sum_mul, Finset.sum_add_distrib]
        rw [← sum_tmul, ← eq1, Finset.sum_comm]
        simp_rw [← sum_tmul]
      have hT'3 (x : A) : (x ⊗ₜ 1) * T' - T' * (x ⊗ₜ 1) = ∑ j ∈ s, (x * (∑ i, (xL i * a j * xR i)) -
          (∑ i, xL i * a j * xR i) * x) ⊗ₜ 𝓑 j := by
        simp [hT'2, mul_add, add_mul, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib,
          ← sub_tmul]
      have hT'_mem (x : A) : (x ⊗ₜ 1) * T' - T' * (x ⊗ₜ 1) ∈ I :=
        I.sub_mem (I.mul_mem_left _ _ hT'1) (I.mul_mem_right _ _ hT'1)
      have : ∀ j ∈ s, ∑ i, xL i * a j * xR i ∈ Subalgebra.center K A := fun j hj ↦
        Subalgebra.mem_center_iff.2 fun x ↦ by
        specialize ih (fun j ↦ if j ∈ s then x * ∑ i, xL i * a j * xR i -
          (∑ i, xL i * a j * xR i) * x else 0) <| by
          convert (hT'_mem x)
          rw [hT'3]
          congr! with i hi
          simp [hi]
        simp +contextual only [↓reduceIte] at ih
        simpa [sub_eq_zero] using ih j hj
      simp_rw [isCentral_A.center_eq_bot, Algebra.mem_bot, Set.mem_range] at this
      choose k hk using this
      set key : B := 𝓑 j + ∑ i ∈ s.attach, k i i.2 • 𝓑 i
      have hkey : key = 0 := by
        refine (map_eq_zero_iff _ f.toRingHom.injective).mp ?_
        refine eq_bot_iff.mp hAB <| TwoSidedIdeal.mem_map_of_mem <|
          (TwoSidedIdeal.mem_comap _).mpr ?_
        rw [← Finset.sum_attach] at hT'2
        conv at hT'2 => enter [2, 2, 2, x]; rw [← hk x.1 x.2]
        convert hT'1 using 1
        rw [hT'2, map_add]
        simp +zetaDelta [Algebra.algebraMap_eq_smul_one, ← smul_tmul']
      set g : ι → K := fun i ↦ if h : i ∈ s then k i h else 1
      have hg : ∑ i ∈ insert j s, g i • 𝓑 i = 0 := by
        unfold g
        rw [Finset.sum_insert hjs, dif_neg hjs, one_smul, ← Finset.sum_attach]
        simp_rw [dif_pos (Subtype.prop _)]
        exact hkey
      have hb := linearIndependent_iff'.mp 𝓑.linearIndependent (insert j s) g hg j
        (Finset.mem_insert_self _ _)
      simp [g, dif_neg hjs] at hb
  refine eq_bot_iff.mpr fun x hx ↦ ?_
  obtain ⟨s, c, rfl⟩ := Submodule.mem_span_range_iff_exists.mp <|
    Submodule.eq_top_iff'.mp (𝓑.baseChange A).span_eq x
  specialize main s c (by simpa [← TensorProduct.tmul_eq_smul_one_tmul] using hx)
  simp +contextual [main]

lemma TensorProduct.map_comap_eq [IsSimpleRing A] [Algebra.IsCentral K A] [hB : IsSimpleRing B]
    (I : TwoSidedIdeal (A ⊗[K] B)) :
    letI f : B →ₐ[K] A ⊗[K] B := Algebra.TensorProduct.includeRight
    (I.comap f).map f = I := by
  let f : B →ₐ[K] A ⊗[K] B := Algebra.TensorProduct.includeRight
  refine (le_antisymm ?_ ?_).symm
  · obtain rfl | I_ne_bot := eq_or_ne I ⊥
    · exact bot_le
    rw [TwoSidedIdeal.map]
    have hI : I.comap f = ⊤ := hB.1.2 _ |>.resolve_left fun r => by
      refine I_ne_bot <| TwoSidedIdeal.eq_bot_of_map_comap_eq_bot (hAB := ?_)
      rw [r, TwoSidedIdeal.map_bot]
    rw [hI, TwoSidedIdeal.coe_top, TwoSidedIdeal.le_iff]
    rintro x -
    rw [SetLike.mem_coe]
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b =>
      rw [show a ⊗ₜ[K] b = (a ⊗ₜ 1) * (1 ⊗ₜ b) by simp]
      exact TwoSidedIdeal.mul_mem_left _ _ _ <| TwoSidedIdeal.subset_span ⟨b, ⟨⟩, rfl⟩
    | add x y hx hy => exact TwoSidedIdeal.add_mem _ hx hy
  · rw [TwoSidedIdeal.map, TwoSidedIdeal.span_le]
    rintro _ ⟨x, hx, rfl⟩
    rw [SetLike.mem_coe, TwoSidedIdeal.mem_comap] at hx
    exact hx

instance TensorProduct.simple {A B : Type*} [Ring A] [IsSimpleRing A] [Algebra K A] [Ring B]
    [Algebra K B] [Algebra.IsCentral K A] [isSimple_B : IsSimpleRing B] :
    IsSimpleRing (A ⊗[K] B) := by
  let f : B →ₐ[K] A ⊗[K] B := Algebra.TensorProduct.includeRight
  refine ⟨⟨fun I ↦ ?_⟩⟩
  rcases isSimple_B.1.2 (I.comap f) with h | h
  · left
    rw [← TensorProduct.map_comap_eq K _ _ I, h, TwoSidedIdeal.map, TwoSidedIdeal.span_eq_bot]
    simp
  · right
    rw [← TwoSidedIdeal.one_mem_iff, ← TensorProduct.map_comap_eq K _ _ I, h,
      TwoSidedIdeal.map]
    exact TwoSidedIdeal.subset_span ⟨1, by simp [Algebra.TensorProduct.one_def]⟩
