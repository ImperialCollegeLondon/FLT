/-
Copyright (c) 2024 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/

import Mathlib.Algebra.Quaternion -- probably get away with less


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

theorem RingCon.sum {R : Type u} [AddCommMonoid R] [Mul R] {ι : Type v} {s : Finset ι} {a b : ι → R}
    {r : RingCon R} (h : ∀ i ∈ s, r (a i) (b i)) : r (∑ i in s, a i) (∑ i in s, b i) := by
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact r.refl 0
  | insert hj ih =>
    next h' j s' =>
      simp_rw [Finset.sum_insert hj]
      apply RingCon.add
      · exact h j (Finset.mem_insert_self j s')
      · exact ih fun i hi ↦ h i (Finset.mem_insert_of_mem hi)

open Matrix in
theorem MatrixRing.isCentralSimple (ι : Type v) (hι : Fintype ι) [Nonempty ι] [DecidableEq ι] :
    IsCentralSimple K (Matrix ι ι K) where
  is_central d hd := by
    rw [Subring.mem_center_iff] at hd
    convert mem_range_scalar_of_commute_stdBasisMatrix (M := d) fun i j _ => hd _
    simp_rw [Set.mem_range, eq_comm, algebraMap_eq_diagonal, Pi.algebraMap_def,
      Algebra.id.map_eq_self, scalar_apply]
  is_simple.eq_bot_or_eq_top := by
    intro r
    obtain h | h := _root_.forall_or_exists_not (fun x ↦ r 0 x ↔ x = 0)
    · left
      apply RingCon.ext
      intro x y
      have : r x y ↔ r 0 (y - x) := by
        constructor
        · convert RingCon.add r (r.refl (-x)) using 1
          rw [neg_add_cancel, sub_eq_add_neg, add_comm]
        · convert RingCon.add r (r.refl x) using 1
          rw [add_sub_cancel, add_zero]
      rw [this, h, sub_eq_zero, eq_comm, RingCon.coe_bot]
    · right
      obtain ⟨x, hx⟩ := h
      have x_ne_zero : x ≠ 0 := by
        rintro rfl
        simp [eq_true (r.refl 0)] at hx
      have r_zero_x : r 0 x := by tauto
      have : ∃ i j, x i j ≠ 0 := by simpa using x_ne_zero ∘ Matrix.ext
      obtain ⟨i, j, hij⟩ := this
      have (k : ι) (_ : k ∈ Finset.univ) :
          r 0 ((stdBasisMatrix k i 1) * x * (stdBasisMatrix j k 1)) := by
        simpa using
          r.mul (r.mul (r.refl (stdBasisMatrix k i 1)) r_zero_x) (r.refl (stdBasisMatrix j k 1))
      have r_zero_sum := RingCon.sum this
      have sum_eq_scalar :
          ∑ k, (stdBasisMatrix k i 1) * x * (stdBasisMatrix j k 1) = scalar ι (x i j) := by
        ext i' j'
        simp [diagonal, sum_apply, mul_apply, stdBasisMatrix, ite_and, eq_comm]
      have r_zero_one : r 0 1 := by
        simpa [hij, Finset.sum_const_zero, sum_eq_scalar] using
          r.mul r_zero_sum (r.refl (scalar ι (x i j)⁻¹))
      have forall_r_zero a : r 0 a := by simpa using r.mul r_zero_one (r.refl a)
      have forall_forall_r a b : r a b := by simpa using r.add (forall_r_zero (b - a)) (r.refl a)
      apply RingCon.ext
      simp [forall_forall_r]

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

-- lemma baseChange (L : Type w) [Field L] [Algebra K L] : IsCentralSimple L (L ⊗[K] D) := sorry

end IsCentralSimple

-- restrict to 4d case
-- theorem exists_quaternionAlgebra_iso (hK : (2 : K) ≠ 0) :
--     ∃ a b : K, Nonempty (D ≃ₐ[K] ℍ[K, a, b]) := sorry
