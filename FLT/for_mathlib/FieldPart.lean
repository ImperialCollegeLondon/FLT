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

variable {D : Type*}[DivisionRing D](p : ℕ)[Fact p.Prime][char: CharP D p]

abbrev conj (x : D) : Module.End ℤ D where
  toFun := fun a ↦ x * a * x⁻¹
  map_add' := fun y1 y2 ↦ by simp only; rw [mul_add, add_mul]
  map_smul' := fun z d ↦ by 
    simp only [zsmul_eq_mul, eq_intCast, Int.cast_id]
    induction' z using Int.induction_on with a ha b hb
    · simp 
    · simp only [Int.cast_natCast, Int.cast_add, Int.cast_one] at ha ⊢
      rw [add_mul, mul_add, add_mul, ha, one_mul, add_mul, one_mul]
    · simp only [Int.cast_neg, Int.cast_sub, Int.cast_one] at hb ⊢
      rw [sub_mul, mul_sub, sub_mul, hb, one_mul, sub_mul, one_mul]

example : (1 : Module.End ℤ D) = LinearMap.id := rfl

instance Same_char : CharP (Module.End ℤ D) p where
  cast_eq_zero_iff' := by 
    intro x ; constructor 
    · intro hx; rw [DFunLike.ext_iff] at hx; specialize hx 1; 
      simp only [Module.End.natCast_apply,
        nsmul_eq_mul, mul_one, LinearMap.zero_apply] at hx
      exact (char.1 x).mp hx
    · intro hx
      have := (char.1 x).2 hx
      ext y; simp
      left; exact this


lemma freshers_end (x : D) : (conj x - (1 : Module.End ℤ D))^p = (conj x)^p - 1^p := 
  sub_pow_char_of_commute (Module.End ℤ D) (conj x) 1 (by simp)

lemma isnil_conj_sub_one (x : D) : IsNilpotent (conj x - 1) := by 
  sorry
  
lemma upper_bound (x : D) : ∃(l : ℕ), 
    (conj x - 1)^l ≠ 0 ∧ ∀ (n : ℕ), (conj x - 1)^(n + l + 1) = 0 := by
  use (nilpotencyClass (conj x - 1)) - 1
  constructor
  · apply pow_pred_nilpotencyClass (isnil_conj_sub_one x)
  · intro n 
    have : nilpotencyClass (conj x - 1) > 0 := pos_nilpotencyClass_iff.2 (isnil_conj_sub_one x)
    rw [show (n + (nilpotencyClass (conj x - 1) - 1) + 1) = 
      n + nilpotencyClass (conj x - 1) by omega]
    rw [pow_add, pow_nilpotencyClass, mul_zero]
    apply isnil_conj_sub_one

set_option maxHeartbeats 800000 in
theorem division_char_is_commutative {D : Type*} [DivisionRing D] {p : ℕ} [Fact p.Prime] [CharP D p]
    (h : ∀ x : D, ∃ (m : ℕ),  x ^ (p ^ (m + 1)) ∈ Subring.center D) : IsField D where
    exists_pair_ne := by exact exists_pair_ne D
    mul_comm := by
      intro x
      suffices x ∈ Subring.center D by
        rw [Subring.mem_center_iff] at this
        intro y ; exact Eq.symm (SemiconjBy.eq (this y))
      by_contra! hx
      let hx1 := h x
      cases' hx1 with m hxm
      -- have x_neq_0 : x ≠ 0 := by
      --     intro hx0
      --     rw [hx0] at hx
      --     exact hx (Set.zero_mem_center D)
      -- have x1 : x⁻¹ * x = 1 := by simp_all
      -- have fun_eq1 : fun1^[p ^ (m + 1)] - id = 0 := by
      --     ext d
      --     simp only [Pi.sub_apply, Pi.zero_apply]
      --     change (fun1.toFun)^[p ^ (m + 1)] d - id.toFun d = 0
      --     rw [mul_left_right_iterate]
      --     simp only [inv_pow]; rw [Subring.mem_center_iff] at hxm
      --     specialize hxm d
      --     rw [← hxm, mul_assoc,DivisionRing.mul_inv_cancel, mul_one, id_eq, sub_self]
      --     apply pow_ne_zero ; rwa [ne_eq]
      -- have fun_eq2 : ((fun1 - id)^[p ^ (m + 1)]) = fun1 ^[p ^ (m + 1)] - id := by
      --     induction' (m + 1) with n hn
      --     · ext d
      --       simp only [pow_zero, Function.iterate_one, LinearMap.sub_apply, Pi.sub_apply]
      --     · ext d
      --       rw[pow_add, Function.iterate_mul, Function.iterate_mul, hn]
      --       simp only [pow_one, Pi.sub_apply]
      --       sorry
      sorry
      -- have eq1 : ∀ (y : D), y * x = x * y := by




      --    --fun (a : D) ↦ a




      --   rw[fun_eq1] at fun_eq2
      --   -- have fun_eq3 : fun1 - id ≠ 0 := by
      --   --   intro heq
      --   --   have H := congr_fun heq
      --   --   simp only [Pi.sub_apply, Pi.zero_apply, fun1, id] at H
      --   --   apply hx
      --   --   rw [Subring.mem_center_iff]
      --   --   intro a
      --   --   specialize H a
      --   --   rw [← mul_left_inj' x_neq_0, zero_mul, sub_mul, mul_assoc, x1, mul_one, sub_eq_zero] at H
      --   --   exact H.symm
      --   have h1 : ∃ l : ℕ, (fun1 - id)^[l] ≠ 0 ∧ ∀ n : ℕ, (fun1 - id)^[n.succ + l] = 0 := by
      --     by_contra! h11
      --     sorry
      --     ---
      --   cases' h1 with l hl
      --   rcases hl with ⟨hl1, hl2⟩
      --   have h2 : ∃ b : D, (fun1 - id)^[l] b ≠ 0 := by
      --     by_contra! hb
      --     apply hl1
      --     ext b
      --     specialize hb b
      --     exact hb
      --   cases' h2 with b hb
      --   set y := (fun1 - id)^[l - 1] b
      --   set z := (fun1 - id) y
      --   have l1 : l ≥ 1 := by
      --     by_contra! hl
      --     have l0 : l = 0 := by omega
      --     have l1 := hl2 0
      --     rw [l0] at hl1 l1
      --     aesop?
      --   have hz : z ≠ 0 := by
      --     intro hzq
      --     simp [z, y] at hzq
      --     apply hb
      --     have hz1 : (fun1 - id) ((fun1 - id)^[l - 1] b) =
      --       fun1 ((fun1 - id)^[l - 1] b) - id ((fun1 - id)^[l - 1] b) := by simp only [Pi.sub_apply]
      --     rw [← hz1, ← Function.iterate_succ_apply' (f := fun1 - id) (n := l - 1)] at hzq
      --     rwa [show l = (l-1).succ by omega]
      --   have hz1 : fun1 z = z := by
      --     rw[← sub_eq_zero]
      --     simp [z, y] at *
      --     rw[show fun1 (fun1 ((fun1 - id)^[l - 1] b) - id ((fun1 - id)^[l - 1] b))
      --       - (fun1 ((fun1 - id)^[l - 1] b) - id ((fun1 - id)^[l - 1] b))
      --       = (fun1 - id) (fun1 ((fun1 - id)^[l - 1] b) - id ((fun1 - id)^[l - 1] b)) by simp,
      --       show fun1 ((fun1 - id)^[l - 1] b) - id ((fun1 - id)^[l - 1] b)
      --       = (fun1 - id) ((fun1 - id)^[l - 1] b) by simp only [Pi.sub_apply],
      --       ← Function.iterate_succ_apply' (f := fun1 - id) (n := l - 1),
      --       ← Function.iterate_succ_apply' (f := fun1 - id) (n := (l - 1).succ),
      --       show (l - 1).succ.succ = l + 1 by omega]
      --     obtain funl1 := hl2 0
      --     rw [show 0 + 1 = 1 by omega] at funl1
      --     rw [add_comm]
      --     calc
      --     _ = (0 : D → D) b := by rw [funl1]
      --     _ = 0 := by simp
      --   set w := z⁻¹ * y
      --   have hw1 : fun1 w = w + 1 := by
      --     simp [fun1, w] at *
      --     rw [← mul_assoc, mul_assoc, show y * x⁻¹ = 1 * (y * x⁻¹)  by rw[one_mul], ← x1, ← mul_assoc,
      --       ← mul_assoc, ← mul_assoc, mul_assoc, mul_assoc, x1]
      --     nth_rewrite 2 [← mul_assoc]
      --     calc
      --     _ = x * z⁻¹ * x⁻¹ * fun1 y := by aesop
      --     _ = (x * z * x⁻¹)⁻¹ * fun1 y := by group
      --     _ = z⁻¹ * fun1 y := by rw [hz1]
      --     _ = z⁻¹ * (y + z) := by aesop
      --     _ = z⁻¹ * y + z⁻¹ * z := by exact LeftDistribClass.left_distrib z⁻¹ y z
      --     _ = z⁻¹ * y + 1 := by rw [show z⁻¹ * z = 1 by simp_all]
      --   cases' h w with wm hwm
      --   have final : w ^ p ^ (wm + 1) = w ^ p ^ (wm + 1) + 1 := by
      --     calc
      --     _ = w ^ p ^ (wm + 1) * 1 := by aesop
      --     _ = w ^ p ^ (wm + 1) * x * x⁻¹ := by aesop
      --     _ = x * w ^ p ^ (wm + 1) * x⁻¹ := by
      --       rw [Subring.mem_center_iff] at hwm
      --       specialize hwm x
      --       rw [← hwm]
      --     _ = (x * w * x⁻¹) ^ p ^ (wm + 1) := by
      --       set q := p ^ (wm + 1)
      --       induction' q with q1 hq1
      --       · simp only [pow_zero, mul_one]
      --         exact DivisionRing.mul_inv_cancel x x_neq_0
      --       · nth_rewrite 2 [pow_add]
      --         rw [pow_one, ← mul_assoc, ← mul_assoc, ← hq1]
      --         nth_rewrite 4 [mul_assoc]
      --         rw [x1]
      --         nth_rewrite 3 [mul_assoc, mul_assoc]
      --         rw [one_mul, pow_add, pow_one]
      --     _ = (w + 1) ^ p ^ (wm + 1) := by aesop
      --     _ = w ^ p ^ (wm + 1) + 1 := by rw [add_pow_char_pow_of_commute (h := Commute.one_right w), one_pow]
      --   aesop
      -- intro y
      -- exact (eq1 y).symm
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

lemma char_pow_eq [Infinite K] (D : Type*)
    [DivisionRing D] [Algebra K D] [FiniteDimensional K D]
    (p : ℕ) [Fact p.Prime] [CharP K p] [CharP D p] (x : K) 
    (m : ℕ := FiniteDimensional.finrank K D):
    x^ p ^m = x := sorry

lemma findim_divring_over_sep_closed [Infinite K] (D : Type*)
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
      use FiniteDimensional.finrank K D
      let m := FiniteDimensional.finrank K D
      constructor
      · let g' := f.comp (X^p^m)
        have eq1 : f = g' := by 
          apply Polynomial.eq_of_infinite_eval_eq 
          have : Infinite (@Set.univ K) := by
            have := @Set.infinite_univ K
            exact Set.infinite_coe_iff.mpr this
          fapply Set.infinite_of_injective_forall_mem (α := @Set.univ K) (β := K)
            (f := Subtype.val) Subtype.val_injective 
          rintro ⟨x, _⟩ ; simp only [eval_comp, eval_pow, eval_X, Set.mem_setOf_eq, g']
          congr; sorry
        rw [eq1] ; simp only [g']
        rw [Polynomial.comp_eq_sum_left]
        apply Subalgebra.sum_mem  
        intro x hx ; simp only
        apply Subalgebra.mul_mem; 
        exact Subalgebra.algebraMap_mem _ (f.coeff x)
        apply Subalgebra.pow_mem; apply Algebra.subset_adjoin
        simp only [Set.mem_singleton_iff]
      · sorry
    obtain ⟨m, h1, h2⟩ := hf
    have : ∃(g : (Algebra.adjoin K {X^p^m} : Subalgebra K K[X])), f = g := by
      simp_all only [Subtype.exists, exists_prop, exists_eq_right', f]
    obtain ⟨g, hg⟩ := this
    haveI irr_f: Irreducible f := minpoly.irreducible (Algebra.IsIntegral.isIntegral d)
    have hg1 : Irreducible g := by
      simp_all only [SetLike.coe_mem];
      refine ⟨?_, ?_⟩ 
      · rintro ⟨⟨x, y, hx, hy⟩,rfl⟩ 
        simp only at h2 irr_f
        rw [Subtype.ext_iff] at hx hy
        refine irr_f.1 ⟨⟨x, y, ?_, ?_⟩, rfl⟩
        · exact hx 
        · exact hy

      · rintro a b rfl
        simp only [Submonoid.coe_mul, Subsemiring.coe_toSubmonoid, 
          Subalgebra.coe_toSubsemiring] at irr_f
        obtain (h|h) := irr_f.2 a b rfl
        · left
          rw [Polynomial.isUnit_iff] at h 
          obtain ⟨r, hr1, hr2⟩ := h 
          refine ⟨⟨Algebra.ofId _ _ r, Algebra.ofId _ _ r⁻¹, ?_, ?_⟩, 
            ?_⟩
          · rw [← map_mul, mul_inv_cancel, map_one]
            exact IsUnit.ne_zero hr1
          · rw [← map_mul, inv_mul_cancel, map_one]
            exact IsUnit.ne_zero hr1
          · simp only 
            ext : 1 ; exact hr2

        · right 
          rw [Polynomial.isUnit_iff] at h 
          obtain ⟨r, hr1, hr2⟩ := h 
          refine ⟨⟨Algebra.ofId _ _ r, Algebra.ofId _ _ r⁻¹, ?_, ?_⟩, 
            ?_⟩
          · rw [← map_mul, mul_inv_cancel, map_one]
            exact IsUnit.ne_zero hr1
          · rw [← map_mul, inv_mul_cancel, map_one]
            exact IsUnit.ne_zero hr1
          · simp only 
            ext : 1 ; exact hr2
        
    have hg2 : ↑g ∉ (Algebra.adjoin K {X^p} : Subalgebra K K[X]) := sorry
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
