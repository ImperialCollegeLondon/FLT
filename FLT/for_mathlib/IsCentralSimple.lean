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

instance (B : Type*) [Ring B] [Algebra K B]: Algebra K (Subring.center B) :=
  RingHom.toAlgebra <| (algebraMap K B).codRestrict _ <| fun x => by
    rw [Subring.mem_center_iff]
    exact fun y => Algebra.commutes x y |>.symm

lemma centralizer_tensorProduct_eq_center_tensorProduct_base
      (C : Type*) [Ring C] [Algebra K C]
      (B : Type*) [Ring B] [Algebra K B] :
      Subalgebra.centralizer K
        (Algebra.TensorProduct.map (AlgHom.id K B) (Algebra.ofId K C)).range =
        (Algebra.TensorProduct.map (Subalgebra.center K B).val (AlgHom.id K C)).range := by
    ext w; constructor
    · intro hw
      rw [Subalgebra.mem_centralizer_iff] at hw
      let ℬ := Basis.ofVectorSpace K B
      let 𝒞 := Basis.ofVectorSpace K C
      let 𝒯 := Basis.tensorProduct ℬ 𝒞
      have aux (i) (j) : 𝒯.repr w (i, j) • ℬ i ∈ Subalgebra.center K B := by
        rw [Subalgebra.mem_center_iff]
        have aux1 (x : B) :
            ∑ ij ∈ (𝒯.repr w).support, (x * (𝒯.repr w ij • ℬ ij.1)) ⊗ₜ[K] 𝒞 ij.2 =
            ∑ ij ∈ (𝒯.repr w).support, ((𝒯.repr w ij • ℬ ij.1) * x) ⊗ₜ[K] 𝒞 ij.2 := by
          specialize hw (x ⊗ₜ[K] 1) ⟨x ⊗ₜ[K] (1 : K), by simp⟩
          rw [← 𝒯.total_repr w] at hw
          convert hw
          · change _ = _ * ∑ ij ∈ (𝒯.repr w).support, _
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl ?_
            rintro ⟨i, j⟩ hij
            simp only [Algebra.mul_smul_comm, Basis.tensorProduct_apply, LinearMap.coe_smulRight,
              LinearMap.id_coe, id_eq, Algebra.TensorProduct.tmul_mul_tmul, one_mul, 𝒯]
            rfl
          · change _ = (∑ ij ∈ (𝒯.repr w).support, _) * _
            rw [Finset.sum_mul]
            refine Finset.sum_congr rfl ?_
            rintro ⟨i, j⟩ hij
            simp only [Algebra.smul_mul_assoc, Basis.tensorProduct_apply, LinearMap.coe_smulRight,
              LinearMap.id_coe, id_eq, Algebra.TensorProduct.tmul_mul_tmul, mul_one, 𝒯]
            rfl

        simp_rw [Algebra.mul_smul_comm, Algebra.smul_mul_assoc] at aux1

        sorry
      rw [← 𝒯.total_repr w]
      refine Subalgebra.sum_mem _ ?_
      rintro ⟨i, j⟩ hij
      simp only [LinearMap.coe_smulRight, LinearMap.id_coe, id_eq, AlgHom.mem_range]
      refine ⟨⟨𝒯.repr w (i, j) • ℬ i, aux i j⟩ ⊗ₜ[K] 𝒞 j, ?_⟩
      simp [𝒯, TensorProduct.smul_tmul]
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
