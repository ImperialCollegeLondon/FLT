import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.Tactic
namespace AbsoluteValue

variable {F S : Type*} [Field F] [Field S] [LinearOrder S] [IsStrictOrderedRing S]
  {v w : AbsoluteValue F S}

theorem inv_pos {x : F} (h : 0 < v x) : 0 < v x⁻¹ := by
  rwa [IsAbsoluteValue.abv_inv v, _root_.inv_pos]

theorem ne_zero_of_lt_one {F S : Type*} [Field F] [Field S] [LinearOrder S] [IsStrictOrderedRing S]
    {v : AbsoluteValue F S} {x : F} (hv : 1 < v x) : x ≠ 0 :=
  fun hx => by linarith [map_zero v ▸ hx ▸ hv]

theorem isNontrivial_iff_exists_abv_gt_one {F S : Type*} [Field F] [Field S] [LinearOrder S]
    [IsStrictOrderedRing S] {v : AbsoluteValue F S} :
    v.IsNontrivial ↔ ∃ x, 1 < v x := by
  refine ⟨fun h => h.exists_abv_gt_one, fun ⟨x, hx⟩ => ?_⟩
  refine ⟨x⁻¹, ?_, ?_⟩
  · simp only [ne_eq, inv_eq_zero]; exact ne_zero_of_lt_one hx
  · simp only [map_inv₀, ne_eq, inv_eq_one]; linarith

theorem nonpos_iff (x : F) : v x ≤ 0 ↔ v x = 0 := by
  simp only [le_antisymm_iff, v.nonneg _, and_true]

theorem inv_lt_one_iff {x : F} : v x⁻¹ < 1 ↔ x = 0 ∨ 1 < v x := by
  simp only [map_inv₀, inv_lt_one_iff₀, nonpos_iff, map_eq_zero]

theorem mul_one_div_lt_iff {y : F} (x : F) (h : 0 < v y) : v (x * (1 / y)) < 1 ↔ v x < v y := by
  rw [map_mul, one_div, map_inv₀, mul_inv_lt_iff₀ h, one_mul]

theorem mul_one_div_pow_lt_iff {n : ℕ} {y : F} (x : F) (h : 0 < v y) :
    v (x * (1 / y ^ n)) < 1 ↔ v x < v y ^ n :=
  map_pow v _ _ ▸ mul_one_div_lt_iff x (map_pow v _ _ ▸ pow_pos h n)

theorem one_lt_of_lt_one  (h : ∀ x, v x < 1 → w x < 1) {x : F} (hv : 1 < v x) : 1 < w x :=
  (inv_lt_one_iff.1 <| h _ <| map_inv₀ v _ ▸ inv_lt_one_of_one_lt₀ hv).resolve_left <|
    ne_zero_of_lt_one hv

theorem one_lt_iff_of_lt_one_iff (h : ∀ x, v x < 1 ↔ w x < 1) (x : F) : 1 < v x ↔ 1 < w x :=
  ⟨fun hv => one_lt_of_lt_one (fun _ => (h _).1) hv,
    fun hw => one_lt_of_lt_one (fun _ => (h _).2) hw⟩

theorem eq_one_of_lt_one_iff (h : ∀ x, v x < 1 ↔ w x < 1) {x : F} (hv : v x = 1) : w x = 1 := by
  cases eq_or_lt_of_le (not_lt.1 <| (h x).not.1 hv.not_lt) with
  | inl hl => rw [← hl]
  | inr hr => rw [← one_lt_iff_of_lt_one_iff h] at hr; linarith

theorem eq_one_iff_of_lt_one_iff (h : ∀ x, v x < 1 ↔ w x < 1) (x : F) : v x = 1 ↔ w x = 1 :=
  ⟨fun hv => eq_one_of_lt_one_iff h hv, fun hw => eq_one_of_lt_one_iff (fun _ => (h _).symm) hw⟩

variable (w)

theorem pos_of_pos {a : F} (hv : 0 < v a) : 0 < w a := by
  rwa [AbsoluteValue.pos_iff] at hv ⊢

variable {R S : Type*} [Ring S] [PartialOrder S] [IsOrderedRing S] [Semiring R]
  (v : AbsoluteValue R S) [IsDomain S] [Nontrivial R]

theorem one_add_pow_le (a : R) (n : ℕ) : v (1 + a ^ n) ≤ 1 + v a ^ n :=
  le_trans (v.add_le _ _) (by rw [map_one, map_pow])

variable {R S : Type*} [CommRing S] [PartialOrder S] [IsOrderedRing S] [Ring R]
  (v : AbsoluteValue R S) [NoZeroDivisors S] [IsDomain S] [Nontrivial R]

theorem one_sub_pow_le (a : R) (n : ℕ) : 1 - v a ^ n ≤ v (1 + a ^ n) :=
  le_trans (by rw [map_one, map_pow]) (v.le_add 1 (a ^ n))

end AbsoluteValue
