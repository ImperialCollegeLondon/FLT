import Mathlib.FieldTheory.SeparableClosure
import Mathlib.FieldTheory.SplittingField.Construction

import Mathlib.RingTheory.LittleWedderburn
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


lemma freshers_end (x : D) (m : ℕ): (conj x - (1 : Module.End ℤ D))^p^m = (conj x)^p^m - 1^p^m :=
  sub_pow_char_pow_of_commute (Module.End ℤ D) (conj x) 1 (by simp)

lemma conj_pow_eq (x : D) (n : ℕ): (conj x) ^ n = (conj (x ^ n)) := by
    induction' n with n hn
    · ext d'
      simp only [pow_zero, LinearMap.one_apply, LinearMap.coe_mk, one_mul, inv_one,
      mul_one, AddHom.coe_mk]
    · ext d' ; rw [pow_add]; simp only [pow_one, LinearMap.mul_apply, LinearMap.coe_mk, AddHom.coe_mk]
      rw [hn] ; simp only [LinearMap.coe_mk, AddHom.coe_mk]
      rw [← mul_assoc, ← mul_assoc, ← pow_succ, mul_assoc, ← inv_pow]
      congr ; symm ; rw [← inv_pow] ; exact pow_succ' x⁻¹ n

lemma isnil_conj_sub_one (x : D) (hx' : x ≠ 0)
    (hx : ∃ (m : ℕ),  x ^ (p ^ (m + 1)) ∈ Subring.center D):
    IsNilpotent (conj x - 1) := by
  obtain ⟨m, hm⟩ := hx
  refine ⟨p ^ (m + 1), ?_⟩
  rw [freshers_end, one_pow]
  ext d ; simp only [LinearMap.sub_apply, LinearMap.one_apply, LinearMap.zero_apply]
  have conj_pow := conj_pow_eq x (p ^ (m + 1))
  rw [conj_pow]; simp only [LinearMap.coe_mk, AddHom.coe_mk]
  have := (Subring.mem_center_iff (R := D)).1 hm d
  rw [← this, mul_assoc, mul_inv_cancel]
  · simp only [mul_one, sub_self]
  · simp only [ne_eq, pow_eq_zero_iff', hx', add_eq_zero, one_ne_zero, and_false,
    not_false_eq_true, pow_eq_zero_iff, false_and]

lemma upper_bound (x : D) (hx' : x ≠ 0) (hx : ∃ (m : ℕ),  x ^ (p ^ (m + 1)) ∈ Subring.center D): ∃(l : ℕ),
    (conj x - 1)^l ≠ 0 ∧ ∀ (n : ℕ), (conj x - 1)^(n + l + 1) = 0 := by
  use (nilpotencyClass (conj x - 1)) - 1
  constructor
  · apply pow_pred_nilpotencyClass (isnil_conj_sub_one p x hx' hx)
  · intro n
    have : nilpotencyClass (conj x - 1) > 0 := pos_nilpotencyClass_iff.2 
      (isnil_conj_sub_one p x hx' hx)
    rw [show (n + (nilpotencyClass (conj x - 1) - 1) + 1) =
      n + nilpotencyClass (conj x - 1) by omega]
    rw [pow_add, pow_nilpotencyClass, mul_zero]
    exact isnil_conj_sub_one p x hx' hx

lemma conj_char_pow_eq_one (x : D) (hx' : x ≠ 0)
    (m : ℕ) (hx :  x ^ (p ^ (m + 1)) ∈ Subring.center D):
    (conj x) ^ p ^ (m + 1) - 1 = 0 := by 
  ext d ; simp only [LinearMap.sub_apply, LinearMap.one_apply, LinearMap.zero_apply]
  rw [conj_pow_eq]; simp only [LinearMap.coe_mk, AddHom.coe_mk]
  have := (Subring.mem_center_iff (R := D)).1 hx d 
  rw [← this, mul_assoc, mul_inv_cancel] 
  · simp only [mul_one, sub_self] 
  · exact pow_ne_zero (p ^ (m + 1)) hx'

lemma conj_compose (n : ℕ) (x y : D): (conj x - 1) (((conj x - 1) ^ n) y) = 
    ((conj x - 1) ^ (n + 1)) y := by 
  symm; rw [add_comm, pow_add, pow_one]; simp

theorem division_char_is_commutative {D : Type*} [DivisionRing D] {p : ℕ} [Fact p.Prime] [CharP D p]
    (h : ∀ x : D, ∃ (m : ℕ),  x ^ (p ^ (m + 1)) ∈ Subring.center D) : IsField D where
    exists_pair_ne := by exact exists_pair_ne D
    mul_comm := by
      intro x
      suffices ∀ (y : D), y * x = x * y by
        intro y ; exact (this y).symm
      obtain ⟨m, hm⟩ := h x
      by_contra! hy
      cases' hy with y hy
      have hx : x ≠ 0 := by
        intro hx
        simp_all only [mul_zero, zero_mul, ne_eq, not_true_eq_false, exists_const]
      have x1 : x⁻¹ * x = 1 := by simp_all
      have x2 : x * x⁻¹ = 1 := by simp_all
      have ineq1 : (conj x) - 1 ≠ 0 := by
        intro h1
        obtain h1 := (DFunLike.ext_iff.1 h1) y
        simp only [LinearMap.sub_apply, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.one_apply,
          LinearMap.zero_apply, sub_eq_zero] at h1
        apply hy; rw [← h1, mul_assoc, x1, h1, mul_one]
      obtain ⟨l, hl, hn⟩ := upper_bound p x hx ⟨m, hm⟩
      have h1 : ∃ b : D, (((conj x) - 1) ^ l) b ≠ 0 := by
        by_contra! hb; 
        exact hl (DFunLike.ext_iff.2 hb)
      cases' h1 with b hb
      set z := (((conj x) - 1)^ (l - 1)) b
      set w := ((conj x) - 1) z
      have l1 : l ≥ 1 := by
        by_contra! h
        have l0 : l = 0 := by linarith
        have l1 := hn 0 
        rw [l0, add_zero, zero_add] at l1; exact ineq1 l1
      have hw0 : w ≠ 0 := by
        intro hw
        simp only [w, z] at hw; apply hb
        rw [show l = 1 + (l - 1) by omega, pow_add] ; simp only [pow_one, LinearMap.mul_apply, hw]
      have hw : (conj x) w = w := by
        rw [← sub_eq_zero]; nth_rw 2 [show (w = (1 : Module.End ℤ D) w) by rw [LinearMap.one_apply]]
        rw [← LinearMap.sub_apply]; simp only [w, z] 
        rw [conj_compose (l - 1) x b, show (l - 1) + 1 = l by omega, conj_compose, 
          ← zero_add (l + 1), ← add_assoc]
        exact DFunLike.ext_iff.1 (hn 0) b
      set q := w⁻¹ * z
      have h1 : (conj x) z = z + w := by simp [w]
      have hq_add : (conj x) q = q + 1 := by
        simp only [LinearMap.coe_mk, AddHom.coe_mk, q]
        simp only [LinearMap.coe_mk, AddHom.coe_mk] at hw h1
        have : x * w⁻¹ * x⁻¹ = w⁻¹ := by nth_rewrite 2 [← hw] ; group
        nth_rewrite 1 [← one_mul z, ← x1]
        rw [← mul_assoc, ← mul_assoc, ← mul_assoc, this, mul_assoc, mul_assoc]
        nth_rewrite 2 [← mul_assoc]
        rw [h1, mul_add, inv_mul_cancel hw0]
      cases' h q with qm hq
      have final : q ^ p ^ (qm + 1) = q ^ p ^ (qm + 1) + 1 := by
        nth_rw 1 [← mul_one (q ^ p ^ (qm + 1)),← x2,← mul_assoc,← (Subring.mem_center_iff.1 hq) x] 
        calc
        _ = (x * q * x⁻¹) ^ p ^ (qm + 1) := by
          set e := p ^ (qm + 1)
          induction' e with e he
          · simp only [pow_zero, mul_one]
            exact DivisionRing.mul_inv_cancel x hx
          · nth_rewrite 2 [pow_add]
            rw [ pow_add, pow_one, pow_one, ← he]
            nth_rewrite 2 [← one_mul (a := q)]
            rw [← x1, ← mul_assoc, ← mul_assoc]
            nth_rewrite 2 [← mul_assoc, ← mul_assoc, ← mul_assoc] ; rfl
        _ = (q + 1) ^ p ^ (qm + 1) := by
          simp only [LinearMap.coe_mk, AddHom.coe_mk] at hq_add ; rw[hq_add]
        _ = q ^ p ^ (qm + 1) + 1 := by
          rw [add_pow_char_pow_of_commute (h := Commute.one_right q), one_pow]
        
      simp only [self_eq_add_right, one_ne_zero] at final
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
    (k : ℕ := FiniteDimensional.finrank K D):
    ∃(n : ℕ), n ≤ k ∧ x^ p ^n = x := by
  sorry

theorem fin_version [Finite K] [Algebra K D] [FiniteDimensional K D] :
    ∀(x y : D), x * y = y * x := by
  intro x y
  have fin_D : Finite D := FiniteDimensional.finite_of_finite K D
  exact Finite.isDomain_to_isField D |>.mul_comm x y

variable (R : Type*) [Semiring R]

abbrev unit_group : Group Rˣ where
  mul a b := a * b
  mul_assoc a b c := mul_assoc a b c
  one := 1
  one_mul := one_mul
  mul_one := mul_one
  npow n a := a^n
  npow_zero x := pow_zero x
  npow_succ n x := pow_succ x n
  inv a := a⁻¹
  div a b := a * b⁻¹
  div_eq_mul_inv _ _ := rfl
  zpow z x := x^z
  zpow_zero' a := pow_zero a
  zpow_succ' n a := pow_succ a n
  zpow_neg' _ _ := rfl
  mul_left_inv a := mul_left_inv a


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
          congr
          if x = 0
          then
            rename_i h0
            rw [h0, zero_pow]
            exact Ne.symm (NeZero.ne' (p ^ m))
          else
            have : IsUnit x := by
              rename_i hn0
              rw [← Ne.eq_def] at hn0
              exact Ne.isUnit hn0
            have : x ^ (p^m - 1) = 1 := by
              rw [← orderOf_dvd_iff_pow_eq_one]
              sorry
            symm
            calc
              x ^ p ^ m = x ^ (p^m - 1 + 1) := by
                rw [Nat.sub_add_cancel]
                exact NeZero.one_le
              _ = x ^ (p^m - 1) * x := by exact pow_succ x (p ^ m - 1)
              _ = 1 * x := by rw [this]
              _ = x := by simp
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
