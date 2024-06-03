import Mathlib.FieldTheory.SeparableClosure
import Mathlib.FieldTheory.SplittingField.Construction
import Mathlib.Data.Num.Lemmas

open scoped Classical

variable (D : Type*) [DivisionRing D]

theorem mul_left_right_iterate {G : Type*} [Monoid G] (a b : G) (n : ℕ) : (a * · * b)^[n] =
    (a ^ n * · * b ^ n) := by
  induction' n with n hn
  · ext g ; simp only [Function.iterate_zero, id_eq, pow_zero, one_mul, mul_one]
  · ext g
    rw [Function.iterate_succ, Function.comp_apply, hn]
    simp only ; group
    rw [show a^n * a = a^(n + 1) by rw [← pow_succ a n], mul_assoc]
    rw [show b * b^n = b^(n + 1) by rw [← pow_succ' b n], add_comm]

abbrev fun1 (x : D)(hx : x ≠ 0): D →+* D where
  toFun a := x * a * x⁻¹
  map_one' := by
    simp_all only [ne_eq, mul_one, isUnit_iff_ne_zero, not_false_eq_true, IsUnit.mul_inv_cancel]
  map_mul' y1 y2 := by
    simp only
    have x1 : x⁻¹ * x = 1 := by simp_all
    rw [← mul_assoc, mul_assoc, show y2 * x⁻¹ = 1 * (y2 * x⁻¹)  by rw [one_mul], ← x1, ← mul_assoc,
      ← mul_assoc, ← mul_assoc, mul_assoc, mul_assoc] ; nth_rewrite 2 [← mul_assoc] ; rfl
  map_zero' := by simp only [mul_zero, zero_mul]
  map_add' := by simp only ; intro x1 y ; rw [mul_add, add_mul]

open BigOperators

lemma linear (n : ℕ) (d : D) (h : D → D) (hh : ∀ a b : D, h (a + b) = h a + h b) : h (n * d) = n * (h d) := by
    induction' n with m hm
    · simp only [Nat.cast_zero, zero_mul]
      set h11 := hh 0 0
      simp at h11
      exact h11
    · calc
      _ = h (∑ i in Finset.range (m + 1), d) := by aesop
      _ = h (∑ i in Finset.range (m), d + d) := by 
        rw[Finset.sum_range, Finset.sum_range, Fin.sum_univ_castSucc]
      _ = h (∑ i in Finset.range (m), d) + h d := by aesop
      _ = h (m * d) + (h d) := by aesop
      _ = m * (h d) + (h d) := by rw[hm]
      _ = ∑ i in Finset.range (m), h d + h d := by aesop
      _ = ∑ i in Finset.range (m + 1), h d := by 
        rw[Finset.sum_range, Finset.sum_range, Fin.sum_univ_castSucc]
      _ = ↑(m + 1) * h d := by aesop


lemma negmul (n : ℕ) (d : D) (h : D → D) (hneg : ∀ a : D, h (- a) = - h a) : h ((- 1) ^ n * d) = (- 1) ^ n * (h d) := by
    induction' n with n hn
    · simp only [pow_zero, one_mul]
    · calc
      _ = h ((-1) ^ n * (- 1) ^ 1 * d) := by rw[pow_add]
      _ = h (- ((-1) ^ n * d)) := by aesop
      _ = - h ((-1) ^ n * d) := by aesop
      _ = - ((-1) ^ n * h d) := by rw[hn]
      _ = (- 1) * (-1) ^ n * h d := by simp
      _ = ((- 1) ^ 1 * (-1) ^ n) * h d := by simp
      _ = (- 1) ^ (n + 1) * h d := by rw[← pow_add, add_comm]


theorem fun_freshers_dream (h : D → D) (hh : ∀ a b : D, h (a + b) = h a + h b) (hneg : ∀ a : D, h (- a) = - h a) {p : ℕ} [Fact p.Prime] [CharP D p] :
    (h - (fun a ↦ a))^[p] = ∑ i in Finset.range (p + 1), ((- 1) ^ (p - i) : ℤ) * (Nat.choose p i) * h^[i] := by
    induction' p with p hp
    · simp only [Function.iterate_zero, zero_add, Finset.range_one, Int.reduceNeg, ge_iff_le,
      zero_le, tsub_eq_zero_of_le, pow_zero, Int.cast_one, Pi.natCast_def, one_mul,
      Finset.sum_singleton, Nat.choose_self, Nat.cast_one]
      ext d
      simp only [id_eq, Pi.mul_apply, one_mul]
    · simp only [Function.iterate_succ', hp]
      ext d
      simp only [Int.reduceNeg, Int.cast_pow, Int.cast_neg, Int.cast_one, Pi.natCast_def,
        Function.comp_apply, Finset.sum_apply, Pi.mul_apply, Pi.pow_apply, Pi.neg_apply,
        Pi.one_apply, Pi.sub_apply]
      have h1 : h (∑ x ∈ Finset.range (p + 1), (-1) ^ (p - x) * ↑(p.choose x) * h^[x] d) = ∑ x ∈ Finset.range (p + 1), (-1) ^ (p - x) * ↑(p.choose x) * h (h^[x] d) := by
        induction' p + 1 with n hn
        · simp only [Finset.range_zero, Finset.sum_empty]
          set h11 := hh 0 0
          simp at h11
          exact h11
        · rw[Finset.sum_range, Finset.sum_range, Fin.sum_univ_castSucc, Fin.sum_univ_castSucc] at *
          simp only [Fin.coe_castSucc, Fin.val_last]
          rw[hh, hn]
          simp only [add_right_inj]
          rw[mul_assoc, negmul (h := h) (n := p - n) (hneg := hneg), linear (h := h) (n := ↑(p.choose n)) (hh := hh), ← mul_assoc]
      rw[h1]
      sorry

lemma p_div {p : ℕ} [Fact p.Prime] : ∀ i ∈ Finset.range (p - 1), p ∣ Nat.choose p (i + 1) := by
  intro i hi
  induction' i with n hn
  · simp
  · sorry


theorem division_char_is_commutative {p : ℕ} [Fact p.Prime] [CharP D p]
    (h : ∀ x : D, ∃ (m : ℕ),  x ^ (p ^ (m + 1)) ∈ Subring.center D) : IsField D where
    exists_pair_ne := by exact exists_pair_ne D
    mul_comm := by
      intro x
      have eq1 : ∀ (y : D), y * x = x * y := by
        rw [← Subring.mem_center_iff]
        by_contra! hx
        let hx1 := h x
        cases' hx1 with m hxm
        let fun1 := fun (a : D) ↦ x * a * x⁻¹
        let id := fun (a : D) ↦ a
        have x_neq_0 : x ≠ 0 := by
          intro hx0
          rw [hx0] at hx
          exact hx (Set.zero_mem_center D)
        have x1 : x⁻¹ * x = 1 := by simp_all
        have fun_eq1 : fun1^[p ^ (m + 1)] - id = 0 := by
          ext d
          simp only [Pi.sub_apply, Pi.zero_apply]
          rw [mul_left_right_iterate]
          simp only [inv_pow]
          rw [Subring.mem_center_iff] at hxm
          specialize hxm d
          rw [← hxm, mul_assoc,DivisionRing.mul_inv_cancel, mul_one, sub_self]
          apply pow_ne_zero ; rwa [ne_eq]
        have fun_eq2 : ((fun1 - id)^[p ^ (m + 1)]) = fun1 ^[p ^ (m + 1)] - id := by
          induction' (m + 1) with n hn
          · ext d
            simp only [pow_zero, Function.iterate_one, Pi.sub_apply]
          · ext d
            rw[pow_add, Function.iterate_mul, Function.iterate_mul, hn]
            simp only [pow_one, Pi.sub_apply]
            rw[fun_freshers_dream]
            · simp only [Int.reduceNeg, Int.cast_pow, Int.cast_neg, Int.cast_one, Pi.natCast_def,
              Finset.sum_apply, Pi.mul_apply, Pi.pow_apply, Pi.neg_apply, Pi.one_apply]
              calc
              _ = (-1) ^ p * ↑(p.choose 0) * fun1^[p ^ n]^[0] d + (-1) ^ 0 * ↑(p.choose p) * fun1^[p ^ n]^[p] d := by
                sorry
              _ = fun1^[p ^ n]^[p] d - fun1^[p ^ n]^[0] d := by
                rw[CharP.neg_one_pow_char]
                simp only [Nat.choose_zero_right, Nat.cast_one, mul_one, Function.iterate_zero,
                  id_eq, neg_mul, one_mul, pow_zero, Nat.choose_self]
                rw [add_comm, ← zero_sub, ← add_sub_assoc, add_zero]
              _ = fun1^[p ^ n]^[p] d - id d := by simp
            · intro a b
              rw [mul_left_right_iterate]
              simp only [inv_pow]
              rw[mul_add, add_mul]
            · intro a
              rw [mul_left_right_iterate]
              simp only [inv_pow]
              rw [show -a = 0 -a by rw [zero_sub]]
              simp
        rw[fun_eq1] at fun_eq2
        have fun_eq3 : fun1 - id ≠ 0 := by
          intro heq
          have H := congr_fun heq
          simp only [Pi.sub_apply, Pi.zero_apply, fun1, id] at H
          apply hx
          rw [Subring.mem_center_iff]
          intro a
          specialize H a
          rw [← mul_left_inj' x_neq_0, zero_mul, sub_mul, mul_assoc, x1, mul_one, sub_eq_zero] at H
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
            fun1 ((fun1 - id)^[l - 1] b) - id ((fun1 - id)^[l - 1] b) := by simp only [Pi.sub_apply]
          rw [← hz1, ← Function.iterate_succ_apply' (f := fun1 - id) (n := l - 1)] at hzq
          rwa [show l = (l-1).succ by omega]
        have hz1 : fun1 z = z := by
          rw[← sub_eq_zero]
          simp [z, y] at *
          rw[show fun1 (fun1 ((fun1 - id)^[l - 1] b) - id ((fun1 - id)^[l - 1] b))
            - (fun1 ((fun1 - id)^[l - 1] b) - id ((fun1 - id)^[l - 1] b))
            = (fun1 - id) (fun1 ((fun1 - id)^[l - 1] b) - id ((fun1 - id)^[l - 1] b)) by simp,
            show fun1 ((fun1 - id)^[l - 1] b) - id ((fun1 - id)^[l - 1] b)
            = (fun1 - id) ((fun1 - id)^[l - 1] b) by simp only [Pi.sub_apply],
            ← Function.iterate_succ_apply' (f := fun1 - id) (n := l - 1),
            ← Function.iterate_succ_apply' (f := fun1 - id) (n := (l - 1).succ),
            show (l - 1).succ.succ = l + 1 by omega]
          obtain funl1 := hl2 0
          rw [show 0 + 1 = 1 by omega] at funl1
          rw [add_comm]
          calc
          _ = (0 : D → D) b := by rw [funl1]
          _ = 0 := by simp
        set w := z⁻¹ * y
        have hw1 : fun1 w = w + 1 := by
          simp [fun1, w] at *
          rw [← mul_assoc, mul_assoc, show y * x⁻¹ = 1 * (y * x⁻¹)  by rw[one_mul], ← x1, ← mul_assoc,
            ← mul_assoc, ← mul_assoc, mul_assoc, mul_assoc, x1]
          nth_rewrite 2 [← mul_assoc]
          calc
          _ = x * z⁻¹ * x⁻¹ * fun1 y := by aesop
          _ = (x * z * x⁻¹)⁻¹ * fun1 y := by group
          _ = z⁻¹ * fun1 y := by rw [hz1]
          _ = z⁻¹ * (y + z) := by aesop
          _ = z⁻¹ * y + z⁻¹ * z := by exact LeftDistribClass.left_distrib z⁻¹ y z
          _ = z⁻¹ * y + 1 := by rw [show z⁻¹ * z = 1 by simp_all]
        cases' h w with wm hwm
        have final : w ^ p ^ (wm + 1) = w ^ p ^ (wm + 1) + 1 := by
          calc
          _ = w ^ p ^ (wm + 1) * 1 := by aesop
          _ = w ^ p ^ (wm + 1) * x * x⁻¹ := by aesop
          _ = x * w ^ p ^ (wm + 1) * x⁻¹ := by
            rw [Subring.mem_center_iff] at hwm
            specialize hwm x
            rw [← hwm]
          _ = (x * w * x⁻¹) ^ p ^ (wm + 1) := by
            set q := p ^ (wm + 1)
            induction' q with q1 hq1
            · simp only [pow_zero, mul_one]
              exact DivisionRing.mul_inv_cancel x x_neq_0
            · nth_rewrite 2 [pow_add]
              rw [pow_one, ← mul_assoc, ← mul_assoc, ← hq1]
              nth_rewrite 4 [mul_assoc]
              rw [x1]
              nth_rewrite 3 [mul_assoc, mul_assoc]
              rw [one_mul, pow_add, pow_one]
          _ = (w + 1) ^ p ^ (wm + 1) := by aesop
          _ = w ^ p ^ (wm + 1) + 1 := by rw [add_pow_char_pow_of_commute (h := Commute.one_right w), one_pow]
        aesop
      intro y
      exact (eq1 y).symm
    mul_inv_cancel := by
      intro a ha ; use a⁻¹
      exact DivisionRing.mul_inv_cancel a ha


abbrev p_radical_extension (K E: Type*) [Field K] [DivisionRing E] [Algebra K E] (p : ℕ) [CharP K p]
    [Fact p.Prime] := ∀(x : E), ∃(m : ℕ), x ^ p ^ m ∈ (Algebra.ofId K E).range

variable (K : Type*) [Field K] [IsSepClosed K]
variable (f : Polynomial K)
open Polynomial
noncomputable instance : Algebra K (Polynomial.SplittingField f) :=
  Ideal.Quotient.algebra _

lemma field_in_center (D : Type*) [DivisionRing D] [Algebra K D]:
    (Algebra.ofId K D).toRingHom.range ≤ Subring.center D := by
  rintro _ ⟨x, rfl⟩
  rw [Subring.mem_center_iff]
  exact (Algebra.commutes' x · |>.symm)

lemma findim_divring_over_sep_closed (D : Type*)
    [DivisionRing D] [Algebra K D] [FiniteDimensional K D]
    (p : ℕ) [Fact p.Prime] [CharP K p] [CharP D p] :
    ∀(x y : D), x * y = y * x := by
  have alg_ext: ∀(d : D), IsAlgebraic K d :=
    fun d ↦ Algebra.IsAlgebraic.isAlgebraic d
  have p_rad : p_radical_extension K D p := by
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
      simp_all only [SetLike.coe_mem];
      refine ⟨?_, ?_⟩ 
      · sorry
      · sorry
    have hg2 : ↑g ∉ (Algebra.adjoin K {X^2} : Subalgebra K K[X]) := sorry
    have hg3 : g = minpoly K d^p^m := sorry
    have p_pow_in_K : d^p^m ∈ (Algebra.ofId K D).range := sorry
    use m
  exact (division_char_is_commutative (D := D) (p := p)
    (by intro d; specialize p_rad d ; obtain ⟨m, hm⟩ := p_rad ;
        use m - 1 ; have := field_in_center K D ;
        suffices d^p^m ∈ Subring.center D by
          if m = 0 then aesop
          else
            have hm : 0 < m := by omega
            rw [Nat.sub_one_add_one_eq_of_pos hm]
            exact this
        tauto)).mul_comm
