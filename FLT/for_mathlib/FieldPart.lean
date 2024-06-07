import Mathlib.FieldTheory.SeparableClosure
import Mathlib.FieldTheory.SplittingField.Construction
import Mathlib.FieldTheory.PurelyInseparable
import Mathlib.RingTheory.LittleWedderburn
import Mathlib.Algebra.Field.Basic
open scoped Classical

-- variable (D : Type*) [DivisionRing D]


theorem mul_left_right_iterate {G : Type*} [Monoid G] (a b : G) (n : ℕ) : (a * · * b)^[n] =
    (a ^ n * · * b ^ n) := by
  induction' n with n hn
  · ext g ; simp only [Function.iterate_zero, id_eq, pow_zero, one_mul, mul_one]
  · ext g
    rw [Function.iterate_succ, Function.comp_apply, hn]
    simp only ; group
    rw [show a^n * a = a^(n + 1) by rw [← pow_succ a n], mul_assoc]
    rw [show b * b^n = b^(n + 1) by rw [← pow_succ' b n], add_comm]

variable {D : Type*} [DivisionRing D] (p : ℕ) [Fact p.Prime] [char: CharP D p]

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


theorem fin_version [Finite K] [Algebra K D] [FiniteDimensional K D] :
    ∀(x y : D), x * y = y * x := by
  intro x y
  have fin_D : Finite D := FiniteDimensional.finite_of_finite K D
  exact Finite.isDomain_to_isField D |>.mul_comm x y

variable (R : Type*) [Semiring R]

abbrev unit_group : Group Rˣ where
  mul_assoc _ _ _ := mul_assoc _ _ _
  one_mul := _
  mul_one := _
  npow_zero _ := pow_zero _
  npow_succ _ _ := pow_succ _ _
  zpow_zero' _ := pow_zero _
  zpow_succ' _ _ := pow_succ _ _
  mul_left_inv _ := mul_left_inv _

variable [Algebra K D] [FiniteDimensional K D] [CharP D p]

open BigOperators

lemma support_subset_finset_sum_monomial {ι : Type*}  (s : Finset ι)
    (deg : ι → ℕ)
    (coeff : ι → K) :
    (∑ i ∈ s, monomial (deg i) (coeff i)).support ⊆ s.image deg := by
  induction s using Finset.cons_induction with
  | empty => simp
  | @cons i s hi ih =>
    rw [Finset.sum_cons]
    trans
    · exact support_add
    simp only [Finset.cons_eq_insert, Finset.image_insert]
    intro x hx
    rw [Finset.mem_union] at hx
    rcases hx with (hx|hx)
    · if h : coeff i = 0
      then
        rw [h] at hx
        simp at hx
      else
        simp only [support_monomial _ h, Finset.mem_singleton] at hx
        simp only [Finset.mem_insert, Finset.mem_image]
        tauto
    · specialize ih hx
      simp only [Finset.mem_image, Finset.mem_insert] at ih ⊢
      right
      exact ih

lemma dvd_natDegree_of_mem_adjoin
    {m : ℕ} {p : K[X]} (h : p ∈ (Algebra.adjoin K {X^m} : Subalgebra K K[X])) :
    m ∣ p.natDegree := by
  if hp : p = 0 then rw [hp]; exact Nat.dvd_zero m
  else
  rw [Algebra.adjoin_singleton_eq_range_aeval, AlgHom.mem_range] at h
  obtain ⟨q, rfl⟩ := h
  rw [q.as_sum_range, map_sum]
  rw [natDegree_eq_support_max']
  pick_goal 2
  · rw [← map_sum, ← q.as_sum_range]; exact hp

  simp_rw [aeval_monomial, ← pow_mul, algebraMap_eq]
  have subset1:= support_subset_finset_sum_monomial K (Finset.range (q.natDegree + 1))
    (fun x => m * x) (fun x => q.coeff x)
  simp_rw [← C_mul_X_pow_eq_monomial] at subset1
  suffices ∀ i ∈ Finset.image (fun x ↦ m * x) (Finset.range (q.natDegree + 1)), m ∣ i from
    --this _ subset1 subset1  Finset.max'_mem _ _
    sorry
  intro i hi
  simp only [Finset.mem_image, Finset.mem_range] at hi
  obtain ⟨i, _, rfl⟩ := hi
  exact Nat.dvd_mul_right m i

lemma intersect_eq :
    ⨅ (m : ℕ), (Algebra.adjoin K {X^p^m} : Subalgebra K K[X]) = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Algebra.mem_iInf] at hx
  have (i : ℕ) : p^i ∣ x.natDegree := by
    apply dvd_natDegree_of_mem_adjoin; apply hx

  if h : x.natDegree = 0 then
    rw [natDegree_eq_zero] at h
    rw [Algebra.mem_bot]
    exact h
  else
    obtain ⟨i, hi⟩ : ∃ (i : ℕ), x.natDegree < p^i :=
      pow_unbounded_of_one_lt x.natDegree $ Nat.Prime.one_lt Fact.out
    have := Nat.le_of_dvd (by omega) $ this i
    omega

lemma minpoly_mem_aux (d : D) :
    ∃ (m : ℕ), minpoly K d ∉ (Algebra.adjoin K {X^p^m} : Subalgebra K K[X]) := by
  by_contra! r
  have := intersect_eq p K
  have mem1 : minpoly K d ∈ (⊥ : Subalgebra K K[X]) := by
    rw [← intersect_eq p, Algebra.mem_iInf]
    exact r
  rw [Algebra.mem_bot] at mem1
  obtain ⟨c, hc⟩ := mem1
  have alg_ext := Algebra.IsAlgebraic.of_finite K D
  have : 0 < (minpoly K d).natDegree := minpoly.natDegree_pos (Algebra.IsIntegral.isIntegral d)
  rw [← hc, algebraMap_eq, natDegree_C] at this
  exact lt_irrefl _ this

lemma minpoly_mem (d : D) :
    ∃ (m : ℕ), 0 < m ∧
      minpoly K d ∉ Algebra.adjoin K {X^p^m} ∧
      (∀ n : ℕ, n < m → minpoly K d ∈ Algebra.adjoin K {X^p^n}) := by
  let M := Nat.find (minpoly_mem_aux p K d)
  have hM : minpoly K d ∉ (Algebra.adjoin K {X^p^M} : Subalgebra K K[X]) :=
    Nat.find_spec (minpoly_mem_aux p K d)

  if M_ne_zero : M = 0
  then
    rw [M_ne_zero] at hM
    simp at hM
  else
    refine ⟨M, by omega, hM, fun n hn => ?_⟩
    simpa using Nat.find_min (minpoly_mem_aux p K d) hn

variable {K} in
lemma edison_lemma2 {a : K[X]} {m : ℕ} (ha : a ∈ Algebra.adjoin K {X^m}) :
    ∃ (b : K[X]), b.comp (X^m) = a := by
  refine Algebra.adjoin_induction ha ?_ ?_ ?_ ?_
  · rintro _ ⟨⟩
    exact ⟨X, by simp⟩
  · intro k
    refine ⟨C k, by simp⟩
  · rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
    exact ⟨a + b, by simp⟩
  · rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
    exact ⟨a * b, by simp⟩

lemma edison_lemma3 (d:D) {f : K[X]}{hff: f = minpoly K d}{m : ℕ}(g : K[X])
    (hq: g.comp (X^p^(m-1)) = f) : Irreducible g :=
  { not_unit:= by 
      by_contra! hg
      have f_ne_0 : f ≠ 0 := by
          rw [hff] ; exact minpoly.ne_zero (Algebra.IsIntegral.isIntegral d)
      have irr_f := minpoly.irreducible (A := K) (x := d) (Algebra.IsIntegral.isIntegral d)
      obtain ⟨hf1, hf2⟩ := irr_f
      rw [Polynomial.isUnit_iff_degree_eq_zero] at hg 
      have g_ne_zero: g ≠ 0 := by 
        suffices f ≠ 0 by 
          by_contra! hgg
          simp only [hgg, zero_comp] at hq
          exact this (id (Eq.symm hq))
        exact f_ne_0
      have g_nat : g.natDegree = 0 := (degree_eq_iff_natDegree_eq g_ne_zero).1 hg
      have comp_deg := natDegree_comp (R := K) (p := g) (q := X ^ p ^ (m - 1)) 
      simp only [hq, g_nat, natDegree_pow, natDegree_X, mul_one, zero_mul] at comp_deg 
      have : f.degree = 0 := by 
        exact (degree_eq_iff_natDegree_eq f_ne_0).2 comp_deg
      rw [← Polynomial.isUnit_iff_degree_eq_zero, hff] at this 
      exact hf1 this
    isUnit_or_isUnit':= by 
      intro a b hg 
      by_contra! hab 
      have f_ne_0 : f ≠ 0 := by
          rw [hff] ; exact minpoly.ne_zero (x := d) (by exact Algebra.IsIntegral.isIntegral d)
      have : g.comp (X^p^(m-1)) = a.comp (X^p^(m-1)) * b.comp (X^p^(m-1)):= by
        simp only [hg, mul_comp]
      rw [hq, hff] at this 
      have irr_f := minpoly.irreducible (A := K) (x := d) (Algebra.IsIntegral.isIntegral d)
      obtain ⟨hf1, hf2⟩ := irr_f ; obtain ⟨ha, hb⟩ := hab
      specialize hf2 (a.comp (X ^ p ^ (m - 1))) (b.comp (X ^ p ^ (m - 1))) this
      cases' hf2 with hf2 hf2
      · have ha' : IsUnit a := by
          rw [Polynomial.isUnit_iff_degree_eq_zero] at hf2 
          have comp_deg := natDegree_comp (R := K) (p := a) (q := X ^ p ^ (m - 1)) 
          rw [Polynomial.degree_eq_natDegree (by aesop)] at hf2
          have deg_zero: (a.comp (X ^ p ^ (m - 1))).natDegree = 0 := by aesop 
          simp only [deg_zero, natDegree_pow, natDegree_X, mul_one, zero_eq_mul, pow_eq_zero_iff',
            ne_eq] at comp_deg
          if ha': a.natDegree = 0 then 
            have a_ne : a ≠ 0 := by 
              by_contra! hh 
              simp only [hh, zero_mul] at hg 
              simp only [hg, zero_comp] at hq 
              exact f_ne_0 hq.symm
            exact Polynomial.isUnit_iff_degree_eq_zero.2 ((degree_eq_iff_natDegree_eq a_ne).2 ha')
          else 
            simp only [ha', false_or] at comp_deg
            have p_ne : p ≠ 0 := Ne.symm (NeZero.ne' p)
            tauto
        exact ha ha'
      · have hb' : IsUnit b := by
          rw [Polynomial.isUnit_iff_degree_eq_zero] at hf2 
          have comp_deg := natDegree_comp (R := K) (p := b) (q := X ^ p ^ (m - 1)) 
          rw [Polynomial.degree_eq_natDegree (by aesop)] at hf2
          have deg_zero: (b.comp (X ^ p ^ (m - 1))).natDegree = 0 := by aesop 
          simp only [deg_zero, natDegree_pow, natDegree_X, mul_one, zero_eq_mul, pow_eq_zero_iff',
            ne_eq] at comp_deg
          if hb': b.natDegree = 0 then 
            have a_ne : b ≠ 0 := by 
              by_contra! hh 
              simp only [hh, mul_zero] at hg 
              simp only [hg, zero_comp] at hq 
              exact f_ne_0 hq.symm
            exact Polynomial.isUnit_iff_degree_eq_zero.2 ((degree_eq_iff_natDegree_eq a_ne).2 hb')
          else 
            simp only [hb', false_or] at comp_deg
            have p_ne : p ≠ 0 := Ne.symm (NeZero.ne' p)
            tauto
        exact hb hb'}

variable {K} in
lemma edison_lemma4_helper {m n : ℕ} {x : K[X]}
  (hx : x ∈ Algebra.adjoin K {X^n}) :
  x.comp (X^m) ∈ Algebra.adjoin K {X^(m * n)} := by
  refine Algebra.adjoin_induction hx ?_ ?_ ?_ ?_
  · rintro _ ⟨⟩
    simp only [pow_comp, X_comp, ← pow_mul]
    exact Algebra.subset_adjoin $ by trivial
  · intro k
    simp only [algebraMap_eq, C_comp]
    exact Subalgebra.algebraMap_mem _ k
  · intro x y hx hy
    simpa using Subalgebra.add_mem _ hx hy
  · intro x y hx hy
    simpa using Subalgebra.mul_mem _ hx hy

abbrev K_d (d : D) := (Algebra.adjoin K {d} : Subalgebra K D)

lemma findim_divring_over_sep_closed [Infinite K] (D : Type*)
    [DivisionRing D] [Algebra K D] [FiniteDimensional K D]
    (p : ℕ) [Fact p.Prime] [CharP K p] [CharP D p] :
    ∀(x y : D), x * y = y * x := by
  have : 1 < p := Nat.Prime.one_lt Fact.out
  have alg_ext := Algebra.IsAlgebraic.of_finite K D
  have p_rad : p_radical_extension K D p := by
    intro d ;
    let f := minpoly K d
    obtain ⟨m, m_pos, (minpoly_not_mem : f ∉ _), (minpoly_mem : ∀ _, _ → f ∈ _)⟩ :=
      minpoly_mem p K d
    obtain ⟨g, (hg : _ = f)⟩ := edison_lemma2 (minpoly_mem (m - 1) (by omega))

    have g_mon : Monic g := by
      have hf' : f.leadingCoeff = 1 := minpoly.monic (Algebra.IsIntegral.isIntegral d)
      have : (g.comp (X^p^(m-1))).leadingCoeff = _ * _ := leadingCoeff_comp (by
        rw [natDegree_pow, natDegree_X, mul_one]
        simp only [ne_eq, pow_eq_zero_iff', not_and, Decidable.not_not]
        omega)
      rw [hg, hf'] at this
      simp only [monic_X_pow, Monic.leadingCoeff, one_pow, mul_one] at this
      exact this.symm
    have g_irr : Irreducible g := by 
      exact edison_lemma3 p K d g hg


    have g_nin : g ∉ Algebra.adjoin K {X^p} := by  -- lemma 4
      intro h
      have := edison_lemma4_helper (m := p ^ (m - 1)) h
      rw [hg, ← pow_succ, show m - 1 + 1 = m by omega] at this
      tauto

    have g_min : g = minpoly K (d^p^(m - 1)) := by -- lemma 5
      apply minpoly.unique (pmonic := g_mon)
      · have hf : aeval d f = 0 := minpoly.aeval K d
        rwa [← hg, aeval_comp, map_pow, aeval_X] at hf
      · intro q hq1 hq2
        have hq1' : Monic (q.comp (X^p^(m-1))) := by
          refine hq1.comp (monic_X_pow _) ?_
          simp only [natDegree_pow, natDegree_X, mul_one, ne_eq, pow_eq_zero_iff', not_and,
            Decidable.not_not]
          omega
        have hf : f.degree ≤ _ := minpoly.min K d hq1' (by
          rw [aeval_comp, map_pow, aeval_X, hq2])
        have eq1 := natDegree_comp (p := q) (q := X^p^(m-1))
        have eq2 := natDegree_comp (p := g) (q := X^p^(m-1))
        simp only [natDegree_pow, natDegree_X, mul_one] at eq1 eq2
        rw [hg] at eq2
        have hf' := natDegree_le_natDegree hf
        rw [eq1, eq2] at hf'
        replace hf' : g.natDegree ≤ q.natDegree :=
          Nat.le_of_mul_le_mul_right hf' (by apply Nat.pow_pos; omega)
        if g0 : g = 0 then subst g0; simp else
        if q0 : q = 0 then
          subst q0
          simp only [zero_comp, degree_zero, le_bot_iff, degree_eq_bot] at hf
          have hf' : f.leadingCoeff = 1 := minpoly.monic (Algebra.IsIntegral.isIntegral d)
          simp only [hf, leadingCoeff_zero, zero_ne_one] at hf'
        else
          rw [degree_eq_natDegree g0, degree_eq_natDegree q0]
          exact_mod_cast hf'

    have g_sep : Separable g := separable_or p g_irr |>.elim id $ by
      rintro ⟨h1, ⟨g, hg, rfl⟩⟩
      exfalso
      refine g_nin ?_
      rw [expand_eq_comp_X_pow]
      have := edison_lemma4_helper (n := 1) (m := p) (x := g) (by simp)
      simpa using this

    have coup_de_grace := IsSepClosed.degree_eq_one_of_irreducible K g_irr g_sep
    rw [g_min, minpoly.degree_eq_one_iff] at coup_de_grace
    exact ⟨_, coup_de_grace⟩

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
