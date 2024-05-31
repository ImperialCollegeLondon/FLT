import Mathlib.RingTheory.Ideal.Basic
import Mathlib.RingTheory.SimpleModule
import Mathlib.RingTheory.Artinian
import FLT.for_mathlib.Con
import Mathlib.Algebra.Quaternion
import Mathlib.Algebra.Ring.Equiv
import Mathlib.LinearAlgebra.Matrix.IsDiag
import Mathlib.Algebra.Category.AlgebraCat.Basic



theorem mul_left_right_iterate {G : Type*} [Monoid G] (a b : G) (n : ℕ) : (a * · * b)^[n] =
    (a ^ n * · * b ^ n) := by
  sorry
  

theorem division_char_is_commutative {D : Type*} [DivisionRing D] {p : ℕ} [Fact p.Prime] [CharP D p]
  (h : ∀ x : D, ∃ (m : ℕ),  x ^ (p ^ (m + 1)) ∈ Subring.center D) : IsField D where
    exists_pair_ne := by
      exact exists_pair_ne D
    mul_comm := by
      intro x
      have eq1 : ∀ (y : D), y * x = x * y := by
        rw[← Subring.mem_center_iff]
        by_contra! hx
        let hx1 := h x
        cases' hx1 with m hxm
        let fun1 := fun (a : D) ↦ x * a * x⁻¹
        let id := fun (a : D) ↦ a
        have x_neq_0 : x ≠ 0 := by
          intro hx0
          rw[hx0] at hx
          exact hx (Set.zero_mem_center D)
        have fun_eq1 : fun1^[p ^ (m + 1)] - id = 0 := by
          ext d
          aesop
          rw[mul_left_right_iterate]
          simp only [inv_pow]
          rw[Subring.mem_center_iff] at hxm
          specialize hxm d 
          rw[← hxm, mul_assoc,DivisionRing.mul_inv_cancel, mul_one, sub_self]
          apply pow_ne_zero 
          rwa[ne_eq]
        have fun_eq2 : ((fun1 - id)^[p ^ (m + 1)]) = fun1 ^[p ^ (m + 1)] - id := by
          ext d
          aesop
          sorry
        rw[fun_eq1] at fun_eq2
        have fun_eq3 : fun1 - id ≠ 0 := by
          sorry
        have h1 : ∃ l : ℕ, (fun1 - id)^[l] ≠ 0 ∧ ∀ n : ℕ, n > l → (fun1 - id)^[n] = 0 := by 
          sorry
        cases' h1 with l hl 
        rcases hl with ⟨hl1, hl2⟩ 
        have h2 : ∃ b : D, (fun1 - id)^[l] b ≠ 0 := by
          by_contra! hb
          apply hl1 
          ext b
          specialize hb b 
          exact hb
        cases' h2 with b hb 
        set y := (fun1 - id)^[l - 1] b
        set z := (fun1 - id) y 
        have hz : z ≠ 0 := by
          sorry
        have hz1 : fun1 z = z := by 
          sorry
        set w := z⁻¹ * y
        have hw1 : fun1 w = w + 1 := by
          sorry 
        cases' h w with wm hwm
        have final : w ^ p ^ (wm + 1) = w ^ p ^ (wm + 1) + 1 := by
          calc 
          _ = w ^ p ^ (wm + 1) * 1 := by aesop
          _ = w ^ p ^ (wm + 1) * x * x⁻¹ := by aesop
          _ = x * w ^ p ^ (wm + 1) * x⁻¹ := by 
            rw[Subring.mem_center_iff] at hwm
            specialize hwm x
            rw[← hwm] 
          _ = (x * w * x⁻¹) ^ p ^ (wm + 1) := by
            set q := p ^ (wm + 1)
            induction' q with q1 hq1
            · simp only [pow_zero, mul_one]
              exact DivisionRing.mul_inv_cancel x x_neq_0
            · nth_rewrite 2 [pow_add]
              rw[pow_one, ← mul_assoc, ← mul_assoc, ← hq1]
              nth_rewrite 4 [mul_assoc]
              have x1 : x⁻¹ * x = 1 := by 
                rw[← mul_right_inj' x_neq_0, ← mul_assoc]
                obtain x11 := DivisionRing.mul_inv_cancel x x_neq_0
                rw[x11, one_mul, mul_one]
              rw[x1]
              nth_rewrite 3 [mul_assoc, mul_assoc]
              rw[one_mul, pow_add, pow_one]
          _ = (w + 1) ^ p ^ (wm + 1) := by aesop
          _ = w ^ p ^ (wm + 1) + 1 := by 
            rw[add_pow_char_pow_of_commute, one_pow]
            exact Commute.one_right w
        aesop
      intro y
      exact (eq1 y).symm
    mul_inv_cancel := by
      intro a ha
      use a⁻¹
      exact DivisionRing.mul_inv_cancel a ha
