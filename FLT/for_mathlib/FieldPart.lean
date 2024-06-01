import Mathlib.FieldTheory.SeparableClosure


theorem mul_left_right_iterate {G : Type*} [Monoid G] (a b : G) (n : ℕ) : (a * · * b)^[n] =
    (a ^ n * · * b ^ n) := by
  sorry

theorem division_char_is_commutative {D : Type*} [DivisionRing D] {p : ℕ} [Fact p.Prime] [CharP D p]
    (h : ∀ x : D, ∃ (m : ℕ),  x ^ (p ^ (m + 1)) ∈ Subring.center D) : IsField D where
    exists_pair_ne := exists_pair_ne D
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
        have x1 : x⁻¹ * x = 1 := by
          rw[← mul_right_inj' x_neq_0, ← mul_assoc]
          obtain x11 := DivisionRing.mul_inv_cancel x x_neq_0
          rw[x11, one_mul, mul_one]
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
          intro heq
          have H := congr_fun heq
          simp at H
          simp [fun1, id] at H
          apply hx
          rw[Subring.mem_center_iff]
          intro a
          specialize H a
          rw[← mul_left_inj' x_neq_0, zero_mul, sub_mul, mul_assoc, x1, mul_one, sub_eq_zero] at H
          exact H.symm
        have h1 : ∃ l : ℕ, (fun1 - id)^[l] ≠ 0 ∧ ∀ n : ℕ, (fun1 - id)^[n.succ + l] = 0 := by
          by_contra! h11
          have h12 := h11 1 fun_eq3
          sorry
          ---
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
        have l1 : l ≥ 1 := by
          by_contra! hl
          have l0 : l = 0 := by omega
          have l1 := hl2 0
          rw [l0] at hl1 l1
          exact fun_eq3 l1
        have hz : z ≠ 0 := by
          intro hzq
          simp [z, y] at hzq
          apply hb
          have hz1 : (fun1 - id) ((fun1 - id)^[l - 1] b) =
            fun1 ((fun1 - id)^[l - 1] b) - id ((fun1 - id)^[l - 1] b) := by simp
          rw [← hz1, ← Function.iterate_succ_apply' (f := fun1 - id) (n := l - 1)] at hzq
          rwa [show l = (l-1).succ by omega]
        have hz1 : fun1 z = z := by
          rw[← sub_eq_zero]
          simp [z] at *
          simp [y] at *
          rw[show fun1 (fun1 ((fun1 - id)^[l - 1] b) - id ((fun1 - id)^[l - 1] b))
            - (fun1 ((fun1 - id)^[l - 1] b) - id ((fun1 - id)^[l - 1] b))
            = (fun1 - id) (fun1 ((fun1 - id)^[l - 1] b) - id ((fun1 - id)^[l - 1] b)) by simp,
            show fun1 ((fun1 - id)^[l - 1] b) - id ((fun1 - id)^[l - 1] b)
            = (fun1 - id) ((fun1 - id)^[l - 1] b) by simp,
            ← Function.iterate_succ_apply' (f := fun1 - id) (n := l - 1),
            ← Function.iterate_succ_apply' (f := fun1 - id) (n := (l - 1).succ),
            show (l - 1).succ.succ = l + 1 by omega]
          obtain funl1 := hl2 0
          rw[show 0 + 1 = 1 by omega] at funl1
          rw[add_comm]
          sorry
        set w := z⁻¹ * y
        have hw1 : fun1 w = w + 1 := by
          simp[fun1, w] at *
          rw[← mul_assoc, mul_assoc, show y * x⁻¹ = 1 * (y * x⁻¹)  by rw[one_mul], ← x1, ← mul_assoc,
            ← mul_assoc, ← mul_assoc, mul_assoc, mul_assoc, x1]
          nth_rewrite 2 [← mul_assoc]
          calc
          _ = x * z⁻¹ * x⁻¹ * fun1 y := by aesop
          _ = (x * z * x⁻¹)⁻¹ * fun1 y := by group
          _ = z⁻¹ * fun1 y := by rw[hz1]
          _ = z⁻¹ * (y + z) := by aesop
          _ = z⁻¹ * y + z⁻¹ * z := by exact LeftDistribClass.left_distrib z⁻¹ y z
          _ = z⁻¹ * y + 1 := by
            have z1 : z⁻¹ * z = 1 := by
              rw[← mul_right_inj' hz, ← mul_assoc]
              obtain z11 := DivisionRing.mul_inv_cancel z hz
              rw[z11, one_mul, mul_one]
            rw[z1]
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
      intro a ha ; use a⁻¹
      exact DivisionRing.mul_inv_cancel a ha

abbrev p_radical_extension (K E: Type*) [Field K] [DivisionRing E] [Algebra K E] (p : ℕ) [CharP K p]
    (_ : p.Prime) := ∀(x : E), ∃(m : ℕ), x ^ p ^ m ∈ (Algebra.ofId K E).range


open Polynomial
lemma findim_divring_over_sep_closed (K : Type*) (D : Type*) [Field K]
    [IsSepClosed K] [DivisionRing D] [Algebra K D] [FiniteDimensional K D]
    (p : ℕ) (hp : p.Prime) [CharP K p]:
    ∀(x y : D), x * y = y * x := by
  have alg_ext: ∀(d : D), IsAlgebraic K d := sorry
  have p_rad : p_radical_extension K D p hp := by
    intro d ; let f := minpoly K d
    have hf: ∃(m : ℕ),
        f ∈ (Algebra.adjoin K {X^p^m} : Subalgebra K K[X]) ∧
        f ∉ (Algebra.adjoin K {X^p^(m+1)} : Subalgebra K K[X]):= by
      sorry
    obtain ⟨m, h1, h2⟩ := hf
    have : ∃(g : (Algebra.adjoin K {X^p^m} : Subalgebra K K[X])), f = g := by
      simp_all only [Subtype.exists, exists_prop, exists_eq_right', f]
    obtain ⟨g, hg⟩ := this
    haveI : Irreducible f := minpoly.irreducible (Algebra.IsIntegral.isIntegral d)
    have hg1 : Irreducible g := by
      simp_all only [SetLike.coe_mem] ; sorry
    have hg2 : ↑g ∉ (Algebra.adjoin K {X^2} : Subalgebra K K[X]) := sorry
    have hg3 : g = minpoly K d^p^m := sorry

    sorry

  sorry
