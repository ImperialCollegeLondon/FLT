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
-- lemma Iscentral_def (D : Type v) [Ring D] [Algebra K D] (h : IsCentralSimple K D):
  -- K = Subring.center D := by sorry
open scoped TensorProduct

-- Lemma c (i); section 12.4
lemma centralizer_tensorProduct_tensorProduct_base
    (A : Type*) [Ring A] [Algebra K A]
    (B : Type*) [Ring B] [Algebra K B] :
    Set.centralizer (M := A ⊗[K] B)
      (Algebra.TensorProduct.map (.id K A) (Algebra.ofId K B)).range =
      Algebra.adjoin K { x | ∃ (a : A) (b : B), a ∈ Subring.center A ∧ x = a ⊗ₜ[K] b} :=
  sorry

-- the following proof may not work?
-- lemma baseChange (L : Type w) [Field L] [Algebra K L] : IsCentralSimple L (L ⊗[K] D) := sorry
lemma baseChange (L : Type w) [Field L] [Algebra K L] : IsCentralSimple L (L ⊗[K] D) :=
{
  is_central:= by
    intro z hz
    induction z using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp_all⟩
    | tmul l d =>
      if l_ne_zero : l = 0
      then
        subst l_ne_zero
        exact ⟨0, by simp⟩
      else

        have hcentral := h.is_central d
        rw [Subring.mem_center_iff] at hz

        have hd : d ∈ Subring.center D := by
          rw [Subring.mem_center_iff]
          intro d0
          specialize hz (l⁻¹ ⊗ₜ[K] d0)
          rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul,
            inv_mul_cancel l_ne_zero, mul_inv_cancel l_ne_zero] at hz
          have aux (x y : D) (h : (1 : L) ⊗ₜ[K] x = (1 : L) ⊗ₜ[K] y) :
              (1 : K) ⊗ₜ[K] x = (1 : K) ⊗ₜ[K] y := by
            let g : K ⊗[K] D →ₗ[K] L ⊗[K] D :=
              TensorProduct.map (Algebra.ofId K L).toLinearMap LinearMap.id
            have hg : Function.Injective g := by
              rw [← LinearMap.ker_eq_bot, eq_bot_iff]
              intro x (h : g x = 0)
              induction x using TensorProduct.induction_on with
              | zero => simp
              | tmul k d =>
                simp only [TensorProduct.map_tmul, AlgHom.toLinearMap_apply, LinearMap.id_coe,
                  id_eq, g] at h
                sorry
              | add x y hx hy => sorry
            apply_fun g
          sorry

        have hdd := hcentral hd
        obtain ⟨dk, hdk⟩ := hdd
        simp only [Algebra.TensorProduct.algebraMap_apply, Algebra.id.map_eq_id, RingHom.id_apply]
        use (dk • l)
        rw [TensorProduct.smul_tmul, Algebra.smul_def]
        simp only [mul_one]
        exact congrArg (TensorProduct.tmul K l) hdk
    | add x y hx hy =>
      have hzx: x ∈ Subring.center (L ⊗[K] D) := by sorry
      have hzy: y ∈ Subring.center (L ⊗[K] D) := by sorry
      obtain ⟨kx, hx'⟩  := hx hzx
      obtain ⟨ky, hy'⟩  := hy hzy
      use kx + ky
      rw[hx', hy']
      simp only [Algebra.TensorProduct.algebraMap_apply, Algebra.id.map_eq_id, RingHom.id_apply,
        map_add]
  is_simple := by sorry
}

end IsCentralSimple

-- restrict to 4d case
-- theorem exists_quaternionAlgebra_iso (hK : (2 : K) ≠ 0) :
--     ∃ a b : K, Nonempty (D ≃ₐ[K] ℍ[K, a, b]) := sorry
