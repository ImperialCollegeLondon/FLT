import Mathlib.Data.PNat.Prime
import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
import Mathlib.Tactic.Peel
import Mathlib.Analysis.Quaternion
import Mathlib.RingTheory.Flat.Basic
/-

# Example of a space of automorphic forms

-/

/-- We define the profinite completion of ℤ explicitly as compatible elements of ℤ/Nℤ for
all positive integers `N`. We declare it as a subring of `∏_{N ≥ 1} (ℤ/Nℤ)`, and then promote it
to a type. -/
def ZHat : Type := {
  carrier := { f : Π M : ℕ+, ZMod M | ∀ (D N : ℕ+) (h : (D : ℕ) ∣ N),
    ZMod.castHom h (ZMod D) (f N) = f D },
  zero_mem' := by simp
  neg_mem' := fun {x} hx => by
    simp only [ZMod.castHom_apply, Set.mem_setOf_eq, Pi.neg_apply] at *
    peel hx with D N hD hx
    rw [ZMod.cast_neg hD, hx]
  add_mem' := fun {a b} ha hb => by
    simp only [ZMod.castHom_apply, Set.mem_setOf_eq, Pi.add_apply] at *
    intro D N hD
    rw [ZMod.cast_add hD, ha _ _ hD, hb _ _ hD]
  one_mem' := by
    simp only [ZMod.castHom_apply, Set.mem_setOf_eq, Pi.one_apply]
    intro D N hD
    rw [ZMod.cast_one hD]
  mul_mem' := fun {a b} ha hb => by
    simp only [ZMod.castHom_apply, Set.mem_setOf_eq, Pi.mul_apply] at *
    intro D N hD
    rw [ZMod.cast_mul hD, ha _ _ hD, hb _ _ hD]
  : Subring (Π n : ℕ+, ZMod n)}
deriving CommRing

namespace ZHat

instance : DFunLike ZHat ℕ+ (fun (N : ℕ+) ↦ ZMod N) where
  coe z := z.1
  coe_injective' M N := by simp_all

lemma prop (z : ZHat) (D N : ℕ+) (h : (D : ℕ) ∣ N) : ZMod.castHom h (ZMod D) (z N) = z D := z.2 ..

@[ext]
lemma ext (x y : ZHat) (h : ∀ n : ℕ+, x n = y n) : x = y :=
  Subtype.ext <| funext <| h

@[simp] lemma zero_val (n : ℕ+) : (0 : ZHat) n = 0 := rfl
@[simp] lemma one_val (n : ℕ+) : (1 : ZHat) n = 1 := rfl
@[simp] lemma ofNat_val (m : ℕ) [m.AtLeastTwo] (n : ℕ+) :
  (OfNat.ofNat m : ZHat) n = (OfNat.ofNat m : ZMod n) := rfl
@[simp] lemma natCast_val (m : ℕ) (n : ℕ+) : (m : ZHat) n = (m : ZMod n) := rfl
@[simp] lemma intCast_val (m : ℤ) (n : ℕ+) : (m : ZHat) n = (m : ZMod n) := rfl

instance commRing : CommRing ZHat := inferInstance

lemma zeroNeOne : (0 : ZHat) ≠ 1 := by
  intro h
  have h2 : (0 : ZHat) 2 = (1 : ZHat) 2 := by simp [h]
  rw [zero_val, one_val] at h2
  revert h2 ; decide

instance nontrivial : Nontrivial ZHat := ⟨0, 1, zeroNeOne⟩

instance charZero : CharZero ZHat := ⟨ fun a b h ↦ by
  rw [ZHat.ext_iff] at h
  specialize h ⟨_, (max a b).succ_pos⟩
  apply_fun ZMod.val at h
  rwa [natCast_val, ZMod.val_cast_of_lt, natCast_val, ZMod.val_cast_of_lt] at h
  · simp [Nat.succ_eq_add_one, Nat.lt_add_one_iff]
  · simp [Nat.succ_eq_add_one, Nat.lt_add_one_iff]
  ⟩

open BigOperators Nat Finset in
/-- A nonarchimedean analogue `0! + 1! + 2! + ⋯` of `e = 1/0! + 1/1! + 1/2! + ⋯`.
It is defined as the function whose value at `ZMod n` is the sum of `i!` for `0 ≤ i < n`.-/
def e : ZHat := ⟨fun (n : ℕ+) ↦ ∑ i in range (n : ℕ), i !, by
  intros D N hDN
  dsimp only
  obtain ⟨k, hk⟩ := exists_add_of_le <| le_of_dvd N.pos hDN
  simp_rw [map_sum, map_natCast, hk, sum_range_add, add_right_eq_self]
  refine sum_eq_zero (fun i _ => ?_)
  rw [ZMod.natCast_zmod_eq_zero_iff_dvd]
  exact Nat.dvd_factorial D.pos le_self_add
⟩

open BigOperators Nat Finset

lemma e_def (n : ℕ+) : e n = ∑ i in range (n : ℕ), (i ! : ZMod n) := rfl

lemma _root_.Nat.sum_factorial_lt_factorial_succ {j : ℕ} (hj : 1 < j) :
    ∑ i ∈ range (j + 1), i ! < (j + 1) ! := by
  calc
    ∑ i ∈ range (j + 1), i ! < ∑ _i ∈ range (j + 1), j ! := ?_
    _ = (j + 1) * (j !) := by rw [sum_const, card_range, smul_eq_mul]
    _ = (j + 1)! := Nat.factorial_succ _
  apply sum_lt_sum
  apply (fun i hi => factorial_le <| by simpa only [mem_range, lt_succ] using hi)
  use 0
  rw [factorial_zero]
  simp [hj]

lemma _root_.Nat.sum_factorial_lt_two_mul_factorial {j : ℕ} (hj : 3 ≤ j) :
    ∑ i ∈ range (j + 1), i ! < 2 * j ! := by
  induction j, hj using Nat.le_induction with
  | base => simp [sum_range_succ, factorial_succ]
  | succ j hj ih =>
    rw [two_mul] at ih ⊢
    rw [sum_range_succ]
    gcongr
    apply sum_factorial_lt_factorial_succ
    omega

lemma e_factorial_succ (j : ℕ) :
    e ⟨(j + 1)!, by positivity⟩ = ∑ i ∈ range (j + 1), i ! := by
  simp_rw [e_def, PNat.mk_coe, cast_sum]
  obtain ⟨k, hk⟩ := exists_add_of_le <| self_le_factorial (j + 1)
  rw [hk, sum_range_add, add_right_eq_self]
  refine sum_eq_zero (fun i _ => ?_)
  rw [ZMod.natCast_zmod_eq_zero_iff_dvd, ← hk]
  exact factorial_dvd_factorial (Nat.le_add_right _ _)

/-- Nonarchimedean $e$ is not an integer. -/
lemma e_not_in_Int : ∀ a : ℤ, e ≠ a := by
  rintro (a|a) ha
  · obtain ⟨j, honelt, hj⟩ : ∃ j : ℕ, 1 < j ∧ a < ∑ i ∈ range (j + 1), i ! := by
      refine ⟨a + 2, ?_, ?_⟩
      · simp only [lt_add_iff_pos_left, add_pos_iff, zero_lt_one, or_true]
      rw [sum_range_add]
      apply lt_add_of_nonneg_of_lt
      · positivity
      rw [range_one, sum_singleton, add_zero]
      exact (Nat.lt_add_of_pos_right two_pos).trans_le (self_le_factorial _)
    let N : ℕ+ := ⟨(j + 1)!, by positivity⟩
    apply lt_irrefl (e N).val
    have h₀ : ∑ i ∈ range (j + 1), i ! < (j + 1) ! := sum_factorial_lt_factorial_succ honelt
    calc
      _ = _ := by simp [ha, N, mod_eq_of_lt (hj.trans h₀)]
      _ < _ := hj
      _ = _ := by simp only [PNat.mk_coe, e_factorial_succ, ZMod.val_natCast, mod_eq_of_lt h₀, N]
  · obtain ⟨j, honelt, hj⟩ : ∃ j, 1 < j ∧ (a + 1) + ∑ i ∈ range (j + 1), i ! < (j + 1)! := by
      refine ⟨a + 3, ?_, ?_⟩
      · omega
      calc
        _ < (a + 1) * 1 + 2 * (a + 3)! := ?_
        _ ≤ (a + 1) * (a + 3)! + 2 * (a + 3)! + 0 := ?_
        _ < (a + 1) * (a + 3)! + 2 * (a + 3)! + (a + 3)! := ?_
        _ = (a + 4)! := ?_
      · rw [mul_one]
        have : 3 ≤ a + 3 := by omega
        have := sum_factorial_lt_two_mul_factorial this
        gcongr
      · rw [add_zero]
        have : 1 ≤ (a + 3)! := Nat.one_le_of_lt (factorial_pos _)
        gcongr
      · gcongr
        exact factorial_pos _
      · rw [factorial_succ (a + 3)]
        ring
    let N : ℕ+ := ⟨(j + 1)!, by positivity⟩
    apply lt_irrefl (e N).val
    calc
      _ < N - (a + 1) := ?_
      _ = (e N).val := ?_
    · dsimp [N]
      apply lt_sub_of_add_lt
      rwa [add_comm, e_factorial_succ, ZMod.val_natCast,
        mod_eq_of_lt (sum_factorial_lt_factorial_succ honelt)]
    · have : a + 1 < N := lt_of_le_of_lt (Nat.le_add_right _ _) hj
      rw [ha, intCast_val, Int.cast_negSucc, ZMod.neg_val, ZMod.val_natCast, if_neg,
        mod_eq_of_lt this]
      rw [ZMod.natCast_zmod_eq_zero_iff_dvd]
      contrapose! this
      apply le_of_dvd (zero_lt_succ a) this
-- This isn't necessary but isn't too hard to prove.

lemma torsionfree_aux (a b : ℕ) [NeZero b] (h : a ∣ b) (x : ZMod b) (hx : a ∣ x.val) :
    ZMod.castHom h (ZMod a) x = 0 := by
  rw [ZMod.castHom_apply, ZMod.cast_eq_val]
  obtain ⟨y, hy⟩ := hx
  rw [hy]
  simp

@[simp]
lemma pnat_mul_apply (N : ℕ+) (z : ZHat) (k : ℕ+) : (N * z) k = N * (z k) := rfl

-- ZHat is torsion-free. LaTeX proof in the notes.
lemma torsionfree (N : ℕ+) : Function.Injective (fun z : ZHat ↦ N * z) := by
  rw [← AddMonoidHom.coe_mulLeft, injective_iff_map_eq_zero]
  intro a ha
  rw [AddMonoidHom.coe_mulLeft] at ha
  ext j
  rw [zero_val, ← a.prop j (N * j) (by simp)]
  apply torsionfree_aux
  apply Nat.dvd_of_mul_dvd_mul_left N.pos
  rw [← PNat.mul_coe]
  apply Nat.dvd_of_mod_eq_zero
  have : N * a (N * j) = 0 := by
    rw [← pnat_mul_apply]
    simp [ha]
  simpa only [ZMod.val_mul, ZMod.val_natCast, Nat.mod_mul_mod, ZMod.val_zero] using congrArg ZMod.val this

instance ZHat_flat : Module.Flat ℤ ZHat := sorry --by torsion-freeness

lemma y_mul_N_eq_z (N : ℕ+) (z : ZHat) (hz : z N = 0) (j : ℕ+) :
    N * ((z (N * j)).val / (N : ℕ) : ZMod j) = z j := by
  have hhj := z.prop N (N * j) (by simp only [PNat.mul_coe, dvd_mul_right])
  rw [hz, ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.natCast_zmod_eq_zero_iff_dvd] at hhj
  rw [← Nat.cast_mul, mul_comm, Nat.div_mul_cancel hhj]
  have hhj' := z.prop j (N * j) (by simp only [PNat.mul_coe, dvd_mul_left])
  rw [← hhj']
  rw [ZMod.castHom_apply, ZMod.cast_eq_val]

-- LaTeX proof in the notes.
lemma multiples (N : ℕ+) (z : ZHat) : (∃ (y : ZHat), N * y = z) ↔ z N = 0 := by
  constructor
  · intro ⟨y, hy⟩
    rw [← hy]
    change N * (y N) = 0
    simp [ZMod.natCast_self]
  · intro h
    let y : ZHat := {
      val := fun j ↦ (z (N * j)).val / (N : ℕ)
      property := by
        intro j k hjk
        have hj := z.prop N (N * j) (by simp only [PNat.mul_coe, dvd_mul_right])
        have hk := z.prop N (N * k) (by simp only [PNat.mul_coe, dvd_mul_right])
        rw [h, ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.natCast_zmod_eq_zero_iff_dvd] at hj
        rw [h, ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.natCast_zmod_eq_zero_iff_dvd] at hk
        have hNjk := z.prop (N * j) (N * k) (mul_dvd_mul (dvd_refl _) hjk)
        rw [ZMod.castHom_apply, ZMod.cast_eq_val] at hNjk
        simp only [PNat.mul_coe, map_natCast, ZMod.natCast_val, ZMod.eq_iff_modEq_nat]
        apply Nat.ModEq.mul_right_cancel' (c := N) (by simp)
        rw [Nat.div_mul_cancel hj, Nat.div_mul_cancel hk,
          mul_comm (j : ℕ) (N : ℕ), ← ZMod.eq_iff_modEq_nat, hNjk]
        simp
    }
    refine ⟨y, ?_⟩
    ext j
    exact y_mul_N_eq_z N z h j

-- `ZHat` has division by positive naturals, with remainder a smaller natural.
-- In other words, the naturals are dense in `ZHat`.
lemma nat_dense (N : ℕ+) (z : ZHat) : ∃ (q : ZHat) (r : ℕ), z = N * q + r ∧ r < N := by
  let r : ℕ := (z N : ZMod N).val
  have h : (z - r) N = 0 := by change z N - r = 0; simp [r]
  rw [← multiples] at h
  obtain ⟨q, hq⟩ := h
  exact ⟨q, r, by linear_combination -hq, ZMod.val_lt (z N)⟩

end ZHat

open scoped TensorProduct in
/-- The "profinite completion" of ℚ is defined to be `ℚ ⊗ ZHat`, with `ZHat` the profinite
completion of `ℤ`. -/
abbrev QHat := ℚ ⊗[ℤ] ZHat

noncomputable example : QHat := (22 / 7) ⊗ₜ ZHat.e

namespace QHat

lemma mul_swap (z : ℤ) (b : ℚ) (x : ZHat) : ((z * b) ⊗ₜ x : QHat) = b ⊗ₜ ((z) • x) := by
  rw [@TensorProduct.tmul_smul]
  rw [@TensorProduct.smul_tmul']
  simp only [zsmul_eq_mul]

lemma canonicalForm (z : QHat) : ∃ (N : ℕ+) (z' : ZHat), z = (1 / N : ℚ) ⊗ₜ z' := by
  induction z using TensorProduct.induction_on with
  | zero =>
    refine ⟨1, 0, ?_⟩
    simp
  | tmul q z =>
    refine ⟨⟨q.den, q.den_pos ⟩, q.num * z, ?_⟩
    simp_rw [← zsmul_eq_mul, TensorProduct.tmul_smul, TensorProduct.smul_tmul']
    simp only [PNat.mk_coe, zsmul_eq_mul]
    simp only [← q.mul_den_eq_num, LinearMap.mul_apply', mul_assoc,
      one_div, ne_eq, Nat.cast_eq_zero, Rat.den_ne_zero, not_false_eq_true,
      mul_inv_cancel, mul_one, mul_inv_cancel₀]
  | add x y hx hy =>
    obtain ⟨N₁, z₁, rfl⟩ := hx
    obtain ⟨N₂, z₂, rfl⟩ := hy
    refine ⟨N₁ * N₂, (N₁ : ℤ) * z₂ + (N₂ : ℤ) * z₁, ?_⟩
    simp only [TensorProduct.tmul_add, ← zsmul_eq_mul,
      TensorProduct.tmul_smul, TensorProduct.smul_tmul']
    simp only [one_div, PNat.mul_coe, Nat.cast_mul, mul_inv_rev, zsmul_eq_mul, Int.cast_natCast,
      ne_eq, Nat.cast_eq_zero, PNat.ne_zero, not_false_eq_true, mul_inv_cancel_left₀]
    rw [add_comm]
    congr
    simp [mul_comm]

def IsCoprime (N : ℕ+) (z : ZHat) : Prop := IsUnit (z N)

open ZMod in
lemma isUnit_iff_coprime (n : ℕ) (m : ZMod n) : IsUnit m ↔ m.val.Coprime n := by
  refine ⟨fun H ↦ ?_, fun H ↦ ?_⟩
  have H' := val_coe_unit_coprime H.unit
  rwa [IsUnit.unit_spec] at H'
  let m' : (ZMod n)ˣ := {
    val := m
    inv := m⁻¹
    val_inv := by rw [mul_inv_eq_gcd, H.gcd_eq_one, Nat.cast_one]
    inv_val := by rw [mul_comm, mul_inv_eq_gcd, H.gcd_eq_one, Nat.cast_one]
  }
  use m'

lemma isCoprime_iff_coprime (N : ℕ+) (z : ZHat) : IsCoprime N z ↔ Nat.Coprime N (z N).val := by
  unfold IsCoprime
  rw [isUnit_iff_coprime, Nat.coprime_comm]

noncomputable abbrev i₂ : ZHat →ₐ[ℤ] QHat := Algebra.TensorProduct.includeRight
lemma injective_zHat :
    Function.Injective i₂ := by
      intro a b h
      have h₁ := LinearMap.rTensor_tmul ZHat (f := Algebra.linearMap ℤ ℚ) a 1
      have h₂ := LinearMap.rTensor_tmul ZHat (f := Algebra.linearMap ℤ ℚ) b 1
      simp only [Algebra.linearMap_apply, map_one] at h₁ h₂
      dsimp at h
      rw [← h₁, ← h₂] at h
      replace h := Module.Flat.rTensor_preserves_injective_linearMap
        (M := ZHat) (Algebra.linearMap ℤ ℚ) (fun _ _ ↦ by simp) h
      simp at h
      have := congrArg (TensorProduct.lid ℤ ZHat) h
      simpa using this

instance nontrivial_QHat : Nontrivial QHat where
  exists_pair_ne := ⟨1 ⊗ₜ 0, 1 ⊗ₜ 1, injective_zHat.ne ZHat.zeroNeOne⟩

noncomputable abbrev i₁ : ℚ →ₐ[ℤ] QHat := Algebra.TensorProduct.includeLeft
lemma injective_rat :
    Function.Injective i₁ := RingHom.injective i₁.toRingHom

lemma lowestTerms (x : QHat) : (∃ N z, IsCoprime N z ∧ x = (1 / N : ℚ) ⊗ₜ z) ∧
    (∀ N₁ N₂ z₁ z₂,
    IsCoprime N₁ z₁ ∧ IsCoprime N₂ z₂ ∧ (1 / N₁ : ℚ) ⊗ₜ z₁ = (1 / N₂ : ℚ) ⊗ₜ[ℤ] z₂ →
      N₁ = N₂ ∧ z₁ = z₂) := by
  constructor
  · obtain ⟨N, z, h⟩ := canonicalForm x
    let D : PNat := ⟨Nat.gcd N (z N).val, Nat.gcd_pos_of_pos_left _ N.pos⟩
    have : 1 ≤ D := by
      apply PNat.one_le
    cases D.one_le.eq_or_gt with
    | inl hD =>
      use N, z, ?_, h
      simp_rw [D, ← PNat.coe_eq_one_iff, PNat.mk_coe] at hD
      rwa [isCoprime_iff_coprime, Nat.coprime_iff_gcd_eq_one]
    | inr hD =>
      have hDN : D ∣ N := PNat.dvd_iff.mpr (Nat.gcd_dvd_left N (z N).val)
      have hDzN : (D : ℕ) ∣ (z N).val := (Nat.gcd_dvd_right N (z N).val)
      obtain ⟨E, hE⟩  := id hDN
      let zz := z D
      have := z.prop D N (PNat.dvd_iff.mp hDN)
      have : z D = 0 := by
        rwa [← this, ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.natCast_zmod_eq_zero_iff_dvd]

      obtain ⟨y, hy⟩ : ∃ y, D * y = z := by
        rwa [ZHat.multiples]

      have hy' : z N = D * y N := by
        rw [← hy, ZHat.pnat_mul_apply]
      use E, y, ?_, ?_
      · rw [isCoprime_iff_coprime]
        apply Nat.coprime_of_dvd fun k hk hk1 hk2 => ?_
        have : D * k ∣ D := by
          apply dvd_gcd
          · rw [hE]
            simp only [PNat.mul_coe]
            apply mul_dvd_mul_left _ hk1
          · rw [hy']
            rw [@ZMod.val_mul]
            simp [hDN]
            by_cases hDN' : D = N
            · simp [hDN']
            · have := lt_of_le_of_ne (Nat.le_of_dvd N.pos (PNat.dvd_iff.mp hDN)) (by simpa)
              rw [hE]
              simp only [PNat.mul_coe]
              rw [Nat.mul_mod_mul_left]
              apply mul_dvd_mul_left
              rw [Nat.dvd_mod_iff hk1]
              suffices k ∣ (y N).val by
                rw [hE] at this
                simpa


              sorry
        have := Nat.le_of_dvd D.pos this
        apply this.not_lt
        refine (Nat.lt_mul_iff_one_lt_right D.pos).mpr hk.one_lt

      · rw [h, hE, ← hy]
        simp only [PNat.mul_coe, Nat.cast_mul, one_div, mul_inv]
        rw [← smul_eq_mul]
        rw [← smul_eq_mul]
        have : (D : ZHat) • y = (D : ℤ) • y := by
          rw [smul_eq_mul]
          rw [@zsmul_eq_mul]
          simp only [Int.cast_natCast]
        rw [this]
        rw [← TensorProduct.smul_tmul]
        simp
  · intros N₁ N₂ z₁ z₂ h'
    have : 1 ⊗ₜ (N₁ * z₁) = (1 : ℤ) ⊗ₜ[ℤ] (N₂ * z₂) := sorry
    have : i₂ (N₁ * z₁) = i₂ (N₂ * z₂) := sorry
    let y := (N₁ * z₁)
    have hNz := injective_zHat this
    have hy₁ : y = N₁ * z₁ := rfl
    have hy₂ : y = N₂ * z₂ := by rw [← hNz]
    let L : ℕ+ := PNat.lcm N₁ N₂
    have : y L = 0 := by
      suffices (L : ℕ) ∣ (y L).val by sorry
      apply lcm_dvd
      · rw [hy₁]
        simp only [ZHat.pnat_mul_apply]
        rw [ZMod.val_mul]
        simp [PNat.dvd_lcm_left N₁ N₂]
        refine (Nat.dvd_mod_iff ?_).mpr ?_
        simp [Nat.dvd_lcm_left N₁ N₂, L]
        exact Nat.dvd_mul_right _ _
      · rw [hy₂]
        simp only [ZHat.pnat_mul_apply]
        rw [ZMod.val_mul]
        simp [PNat.dvd_lcm_right N₁ N₂]
        refine (Nat.dvd_mod_iff ?_).mpr ?_
        simp [Nat.dvd_lcm_right N₁ N₂, L]
        exact Nat.dvd_mul_right _ _
    obtain ⟨x, hx⟩ := (ZHat.multiples _ _).mpr this
    obtain ⟨M₁, hM₁⟩ : N₁ ∣ L := PNat.dvd_lcm_left N₁ N₂
    obtain ⟨M₂, hM₂⟩ : N₂ ∣ L := PNat.dvd_lcm_right N₁ N₂
    have hz₁ : z₁ = M₁ * x := by
      apply ZHat.torsionfree N₁
      dsimp
      rw [← hy₁, ← hx, ← mul_assoc, ← Nat.cast_mul, ← PNat.mul_coe, ← hM₁]
    have hz₂ : z₂ = M₂ * x :=  by
      apply ZHat.torsionfree N₂
      dsimp
      rw [← hy₂, ← hx, ← mul_assoc, ← Nat.cast_mul, ← PNat.mul_coe, ← hM₂]
    have hN₁ : L = N₁ := sorry
    have hN₂ : L = N₂ := sorry
    have hM : M₁ = M₂ := by
      rw [← PNat.coe_inj]
      apply Nat.mul_left_cancel L.pos
      rw [← PNat.mul_coe]
      rw [← PNat.mul_coe]
      rw [PNat.coe_inj]
      conv_lhs =>
        rw [hN₁, ← hM₁]
      conv_rhs =>
        rw [hN₂, ← hM₂]
    rw [hz₁, hz₂, ← hN₁, ← hN₂, hM]
    exact ⟨rfl, rfl⟩

section additive_structure_of_QHat

noncomputable abbrev ratsub : AddSubgroup QHat :=
    (i₁ : ℚ →+ QHat).range

noncomputable abbrev zHatsub : AddSubgroup QHat :=
    (i₂ : ZHat →+ QHat).range

noncomputable abbrev zsub : AddSubgroup QHat :=
  (Int.castRingHom QHat : ℤ →+ QHat).range

lemma rat_meet_zHat : ratsub ⊓ zHatsub = zsub := sorry

lemma rat_join_zHat : ratsub ⊔ zHatsub = ⊤ := sorry

end additive_structure_of_QHat

section multiplicative_structure_of_QHat

noncomputable abbrev unitsratsub : Subgroup QHatˣ :=
  (Units.map (i₁ : ℚ →* QHat)).range

noncomputable abbrev unitszHatsub : Subgroup QHatˣ :=
  (Units.map (i₂ : ZHat →* QHat)).range

noncomputable abbrev unitszsub : Subgroup QHatˣ :=
  (Units.map (Int.castRingHom QHat : ℤ →* QHat)).range

lemma unitsrat_meet_unitszHat : unitsratsub ⊓ unitszHatsub = unitszsub := sorry

-- this needs that ℤ is a PID.
lemma unitsrat_join_unitszHat : unitsratsub ⊔ unitszHatsub = ⊤ := sorry

end multiplicative_structure_of_QHat

end QHat

@[ext]
structure Hurwitz : Type where
  re : ℤ -- 1
  im_o : ℤ -- ω
  im_i : ℤ -- i
  im_oi : ℤ -- ωi -- note iω + ωi + 1 + i = 0

notation "𝓞" => Hurwitz -- 𝓞 = \MCO
namespace Hurwitz

open Quaternion in
noncomputable def toQuaternion (z : 𝓞) : ℍ where
  re := z.re - 2⁻¹ * z.im_o - 2⁻¹ * z.im_oi
  imI := z.im_i + 2⁻¹ * z.im_o - 2⁻¹ * z.im_oi
  imJ := 2⁻¹ * z.im_o + 2⁻¹ * z.im_oi
  imK := 2⁻¹ * z.im_o - 2⁻¹ * z.im_oi

open Quaternion in
noncomputable def fromQuaternion (z : ℍ) : 𝓞 where
  re := Int.floor <| z.re + z.imJ
  im_o := Int.floor <| z.imJ + z.imK
  im_i := Int.floor <| z.imI - z.imK
  im_oi := Int.floor <| z.imJ - z.imK

lemma leftInverse_fromQuaternion_toQuaternion :
    Function.LeftInverse fromQuaternion toQuaternion := by
  intro z
  simp only [fromQuaternion, toQuaternion, sub_add_add_cancel, sub_add_cancel, Int.floor_intCast,
    add_add_sub_cancel, ← two_mul, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    mul_inv_cancel_left₀, sub_sub_sub_cancel_right, add_sub_cancel_right, add_sub_sub_cancel]

lemma toQuaternion_injective : Function.Injective toQuaternion :=
  leftInverse_fromQuaternion_toQuaternion.injective

open Quaternion in
lemma leftInvOn_toQuaternion_fromQuaternion :
    Set.LeftInvOn toQuaternion fromQuaternion
      { q : ℍ | ∃ a b c d : ℤ, q = ⟨a, b, c, d⟩ ∨ q = ⟨a + 2⁻¹, b + 2⁻¹, c + 2⁻¹, d + 2⁻¹⟩ } := by
  have h₀ (x y : ℤ) : (x + 2 ⁻¹ : ℝ) + (y + 2⁻¹) = ↑(x + y + 1) := by
    field_simp; norm_cast; ring
  intro q hq
  simp only [Set.mem_setOf] at hq
  simp only [toQuaternion, fromQuaternion]
  obtain ⟨a, b, c, d, rfl|rfl⟩ := hq <;>
  ext <;>
  simp only [h₀, add_sub_add_right_eq_sub, Int.floor_sub_int, Int.floor_intCast, Int.cast_sub,
    Int.cast_add, Int.cast_one, Int.floor_add_one, Int.floor_add_int] <;>
  field_simp <;>
  norm_cast <;>
  ring

open Quaternion in
lemma fromQuaternion_injOn :
    Set.InjOn fromQuaternion
      { q : ℍ | ∃ a b c d : ℤ, q = ⟨a, b, c, d⟩ ∨ q = ⟨a + 2⁻¹, b + 2⁻¹, c + 2⁻¹, d + 2⁻¹⟩ } :=
  leftInvOn_toQuaternion_fromQuaternion.injOn

/-! ## zero (0) -/

/-- The Hurwitz number 0 -/
def zero : 𝓞 := ⟨0, 0, 0, 0⟩

/-- notation `0` for `zero` -/
instance : Zero 𝓞 := ⟨zero⟩

@[simp] lemma zero_re : re (0 : 𝓞) = 0 := rfl
@[simp] lemma zero_im_o : im_o (0 : 𝓞) = 0 := rfl
@[simp] lemma zero_im_i : im_i (0 : 𝓞) = 0 := rfl
@[simp] lemma zero_im_oi : im_oi (0 : 𝓞) = 0 := rfl

lemma toQuaternion_zero : toQuaternion 0 = 0 := by
  ext <;> simp [toQuaternion]

@[simp]
lemma toQuaternion_eq_zero_iff {z} : toQuaternion z = 0 ↔ z = 0 :=
  toQuaternion_injective.eq_iff' toQuaternion_zero

lemma toQuaternion_ne_zero_iff {z} : toQuaternion z ≠ 0 ↔ z ≠ 0 :=
  toQuaternion_injective.ne_iff' toQuaternion_zero

/-! ## one (1) -/

def one : 𝓞 := ⟨1, 0, 0, 0⟩

/-- Notation `1` for `one` -/
instance : One 𝓞 := ⟨one⟩

@[simp] lemma one_re : re (1 : 𝓞) = 1 := rfl
@[simp] lemma one_im_o : im_o (1 : 𝓞) = 0 := rfl
@[simp] lemma one_im_i : im_i (1 : 𝓞) = 0 := rfl
@[simp] lemma one_im_oi : im_oi (1 : 𝓞) = 0 := rfl

lemma toQuaternion_one : toQuaternion 1 = 1 := by
  ext <;> simp [toQuaternion]

/-! ## Neg (-) -/

-- negation

/-- The negation `-z` of a Hurwitz number -/
def neg (z : 𝓞) : 𝓞 := ⟨-re z, -im_o z, -im_i z, -im_oi z⟩

/-- Notation `-` for negation -/
instance : Neg 𝓞 := ⟨neg⟩

-- how neg interacts with re and im_*
@[simp] lemma neg_re (z : 𝓞) : re (-z) = -re z  := rfl
@[simp] lemma neg_im_o (z : 𝓞) : im_o (-z) = -im_o z  := rfl
@[simp] lemma neg_im_i (z : 𝓞) : im_i (-z) = -im_i z  := rfl
@[simp] lemma neg_im_oi (z : 𝓞) : im_oi (-z) = -im_oi z  := rfl

lemma toQuaternion_neg (z : 𝓞) :
    toQuaternion (-z) = - toQuaternion z := by
  ext <;> simp [toQuaternion] <;> ring

/-! ## add (+) -/

-- Now let's define addition

/-- addition `z+w` of complex numbers -/
def add (z w : 𝓞) : 𝓞 := ⟨z.re + w.re, z.im_o + w.im_o, z.im_i + w.im_i, z.im_oi + w.im_oi⟩

/-- Notation `+` for addition -/
instance : Add 𝓞 := ⟨add⟩

-- basic properties
@[simp] lemma add_re (z w : 𝓞) : re (z + w) = re z  + re w  := rfl
@[simp] lemma add_im_o (z w : 𝓞) : im_o (z + w) = im_o z  + im_o w  := rfl
@[simp] lemma add_im_i (z w : 𝓞) : im_i (z + w) = im_i z  + im_i w  := rfl
@[simp] lemma add_im_oi (z w : 𝓞) : im_oi (z + w) = im_oi z  + im_oi w  := rfl

lemma toQuaternion_add (z w : 𝓞) :
    toQuaternion (z + w) = toQuaternion z + toQuaternion w := by
  ext <;> simp [toQuaternion] <;> ring

/-- Notation `+` for addition -/
instance : Sub 𝓞 := ⟨fun a b => a + -b⟩

lemma toQuaternion_sub (z w : 𝓞) :
    toQuaternion (z - w) = toQuaternion z - toQuaternion w := by
  convert toQuaternion_add z (-w) using 1
  rw [sub_eq_add_neg, toQuaternion_neg]


-- instance : AddCommGroup 𝓞 where
--   add_assoc := by intros; ext <;> simp [add_assoc]
--   zero_add := by intros; ext <;> simp
--   add_zero := by intros; ext <;> simp
--   nsmul := nsmulRec
--   zsmul := zsmulRec
--   add_left_neg := by intros; ext <;> simp
--   add_comm := by intros; ext <;> simp [add_comm]

instance : SMul ℕ 𝓞 where
  smul := nsmulRec

lemma preserves_nsmulRec {M N : Type*} [Zero M] [Add M] [AddMonoid N]
    (f : M → N) (zero : f 0 = 0) (add : ∀ x y, f (x + y) = f x + f y) (n : ℕ) (x : M) :
    f (nsmulRec n x) = n • f x := by
  induction n with
  | zero => rw [nsmulRec, zero, zero_smul]
  | succ n ih => rw [nsmulRec, add, add_nsmul, one_nsmul, ih]

lemma toQuaternion_nsmul (z : 𝓞) (n : ℕ) :
    toQuaternion (n • z) = n • toQuaternion z :=
  preserves_nsmulRec _ toQuaternion_zero toQuaternion_add _ _

instance : SMul ℤ 𝓞 where
  smul := zsmulRec

lemma preserves_zsmul {G H : Type*} [Zero G] [Add G] [Neg G] [SMul ℕ G] [SubNegMonoid H]
    (f : G → H) (nsmul : ∀ (g : G) (n : ℕ), f (n • g) = n • f g)
    (neg : ∀ x, f (-x) = - f x)
    (z : ℤ) (g : G) :
    f (zsmulRec (· • ·) z g) = z • f g := by
  induction z with
  | ofNat n =>
    rw [zsmulRec, nsmul, Int.ofNat_eq_coe, natCast_zsmul]
  | negSucc n =>
    rw [zsmulRec, neg, nsmul, negSucc_zsmul]

lemma toQuaternion_zsmul (z : 𝓞) (n : ℤ) :
    toQuaternion (n • z) = n • toQuaternion z :=
  preserves_zsmul _
    toQuaternion_nsmul
    toQuaternion_neg
    n z

-- noncomputable instance : AddCommGroup 𝓞 :=
--   toQuaternion_injective.addCommGroup
--     _
--     toQuaternion_zero
--     toQuaternion_add
--     toQuaternion_neg
--     toQuaternion_sub
--     toQuaternion_nsmul
--     toQuaternion_zsmul

/-! ## mul (*) -/

-- multiplication

/-- Multiplication `z*w` of two Hurwitz numbers -/
def mul (z w : 𝓞) : 𝓞 where
  re := z.re * w.re - z.im_o * w.im_o - z.im_i * w.im_o - z.im_i * w.im_i + z.im_i * w.im_oi - z.im_oi * w.im_oi
  im_o := z.im_o * w.re + z.re * w.im_o - z.im_o * w.im_o - z.im_oi * w.im_o - z.im_oi * w.im_i + z.im_i * w.im_oi
  im_i := z.im_i * w.re - z.im_i * w.im_o + z.im_oi * w.im_o + z.re * w.im_i - z.im_o * w.im_oi - z.im_i * w.im_oi
  im_oi := z.im_oi * w.re - z.im_i * w.im_o + z.im_o * w.im_i + z.re * w.im_oi - z.im_o * w.im_oi - z.im_oi * w.im_oi

/-- Notation `*` for multiplication -/
instance : Mul 𝓞 := ⟨mul⟩

-- how `mul` reacts with `re` and `im`
@[simp] lemma mul_re (z w : 𝓞) :
    re (z * w) = z.re * w.re - z.im_o * w.im_o - z.im_i * w.im_o - z.im_i * w.im_i + z.im_i * w.im_oi - z.im_oi * w.im_oi := rfl

@[simp] lemma mul_im_o (z w : 𝓞) :
    im_o (z * w) = z.im_o * w.re + z.re * w.im_o - z.im_o * w.im_o - z.im_oi * w.im_o - z.im_oi * w.im_i + z.im_i * w.im_oi := rfl

@[simp] lemma mul_im_i (z w : 𝓞) :
    im_i (z * w) = z.im_i * w.re - z.im_i * w.im_o + z.im_oi * w.im_o + z.re * w.im_i - z.im_o * w.im_oi - z.im_i * w.im_oi := rfl

@[simp] lemma mul_im_oi (z w : 𝓞) :
    im_oi (z * w) = z.im_oi * w.re - z.im_i * w.im_o + z.im_o * w.im_i + z.re * w.im_oi - z.im_o * w.im_oi - z.im_oi * w.im_oi := rfl

lemma toQuaternion_mul (z w : 𝓞) :
    toQuaternion (z * w) = toQuaternion z * toQuaternion w := by
  ext <;> simp [toQuaternion] <;> ring

lemma o_mul_i :
    { re := 0, im_o := 1, im_i := 0, im_oi := 0 } * { re := 0, im_o := 0, im_i := 1, im_oi := 0 }
      = ({ re := 0, im_o := 0, im_i := 0, im_oi := 1 } : 𝓞) := by
  ext <;> simp

instance : Pow 𝓞 ℕ := ⟨fun z n => npowRec n z⟩

lemma preserves_npowRec {M N : Type*} [One M] [Mul M] [Monoid N]
    (f : M → N) (one : f 1 = 1) (mul : ∀ x y : M, f (x * y) = f x * f y) (z : M) (n : ℕ) :
    f (npowRec n z) = (f z) ^ n := by
  induction n with
  | zero => rw [npowRec, one, pow_zero]
  | succ n ih => rw [npowRec, pow_succ, mul, ih]

lemma toQuaternion_npow (z : 𝓞) (n : ℕ) : toQuaternion (z ^ n) = (toQuaternion z) ^ n :=
  preserves_npowRec toQuaternion toQuaternion_one toQuaternion_mul z n

instance : NatCast 𝓞 := ⟨Nat.unaryCast⟩

lemma preserves_unaryCast {R S : Type*} [One R] [Zero R] [Add R] [AddMonoidWithOne S]
    (f : R → S) (zero : f 0 = 0) (one : f 1 = 1) (add : ∀ x y, f (x + y) = f x + f y)
    (n : ℕ) :
    f (Nat.unaryCast n) = n := by
  induction n with
  | zero => rw [Nat.unaryCast, zero, Nat.cast_zero]
  | succ n ih => rw [Nat.unaryCast, add, one, Nat.cast_add, Nat.cast_one, ih]

lemma toQuaternion_natCast (n : ℕ) : toQuaternion n = n :=
  preserves_unaryCast _ toQuaternion_zero toQuaternion_one toQuaternion_add n

instance : IntCast 𝓞 := ⟨Int.castDef⟩

lemma Int.castDef_ofNat {R : Type*} [One R] [Zero R] [Add R] [NatCast R] [Neg R] (n : ℕ) :
    (Int.castDef (Int.ofNat n) : R) = n := rfl

lemma Int.castDef_negSucc {R : Type*} [One R] [Zero R] [Add R] [NatCast R] [Neg R] (n : ℕ) :
    (Int.castDef (Int.negSucc n) : R) = -(n + 1 : ℕ) := rfl

lemma preserves_castDef
    {R S : Type*} [One R] [Zero R] [Add R] [NatCast R] [Neg R] [AddGroupWithOne S]
    (f : R → S) (natCast : ∀ n : ℕ, f n = n) (neg : ∀ x, f (-x) = - f x) (n : ℤ) :
    f (Int.castDef n) = n := by
  cases n with
  | ofNat n => rw [Int.castDef_ofNat, natCast, Int.ofNat_eq_coe, Int.cast_natCast]
  | negSucc _ => rw [Int.castDef_negSucc, neg, natCast, Int.cast_negSucc]

lemma toQuaternion_intCast (n : ℤ) : toQuaternion n = n :=
  preserves_castDef _ toQuaternion_natCast toQuaternion_neg n

noncomputable instance ring : Ring 𝓞 :=
  toQuaternion_injective.ring
    _
    toQuaternion_zero
    toQuaternion_one
    toQuaternion_add
    toQuaternion_mul
    toQuaternion_neg
    toQuaternion_sub
    (fun _ _ => toQuaternion_nsmul _ _) -- TODO for Yaël: these are inconsistent with addCommGroup
    (fun _ _ => toQuaternion_zsmul _ _) -- TODO for Yaël: these are inconsistent with addCommGroup
    toQuaternion_npow
    toQuaternion_natCast
    toQuaternion_intCast

@[simp] lemma natCast_re (n : ℕ) : (n : 𝓞).re = n := by
  induction n with
  | zero => simp
  | succ n ih => simpa
@[simp] lemma natCast_im_o (n : ℕ) : (n : 𝓞).im_o = 0 := by
  induction n with
  | zero => simp
  | succ n ih => simpa
@[simp] lemma natCast_im_i (n : ℕ) : (n : 𝓞).im_i = 0 := by
  induction n with
  | zero => simp
  | succ n ih => simpa
@[simp] lemma natCast_im_oi (n : ℕ) : (n : 𝓞).im_oi = 0 := by
  induction n with
  | zero => simp
  | succ n ih => simpa

@[simp] lemma intCast_re (n : ℤ) : (n : 𝓞).re = n := by
  cases n with
  | ofNat _ => simp
  | negSucc _ => simp [← Int.neg_ofNat_succ]
@[simp] lemma intCast_im_o (n : ℤ) : (n : 𝓞).im_o = 0 := by
  cases n with
  | ofNat _ => simp
  | negSucc _ => simp [← Int.neg_ofNat_succ]
@[simp] lemma intCast_im_i (n : ℤ) : (n : 𝓞).im_i = 0 := by
  cases n with
  | ofNat _ => simp
  | negSucc _ => simp [← Int.neg_ofNat_succ]
@[simp] lemma intCast_im_oi (n : ℤ) : (n : 𝓞).im_oi = 0 := by
  cases n with
  | ofNat _ => simp
  | negSucc _ => simp [← Int.neg_ofNat_succ]


/-- Conjugate; sends $a+bi+cj+dk$ to $a-bi-cj-dk$. -/
instance starRing : StarRing 𝓞 where
  star z := ⟨z.re - z.im_o - z.im_oi, -z.im_o, -z.im_i, -z.im_oi⟩
  star_involutive x := by ext <;> simp only <;> ring
  star_mul x y := by ext <;> simp <;> ring
  star_add x y := by ext <;> simp <;> ring

@[simp] lemma star_re (z : 𝓞) : (star z).re = z.re - z.im_o - z.im_oi := rfl
@[simp] lemma star_im_o (z : 𝓞) : (star z).im_o = -z.im_o := rfl
@[simp] lemma star_im_i (z : 𝓞) : (star z).im_i = -z.im_i := rfl
@[simp] lemma star_im_oi (z : 𝓞) : (star z).im_oi = -z.im_oi := rfl

lemma toQuaternion_star (z : 𝓞) : toQuaternion (star z) = star (toQuaternion z) := by
  ext <;>
  simp only [star_re, star_im_o, star_im_i, star_im_oi, toQuaternion,
    Quaternion.star_re, Quaternion.star_imI, Quaternion.star_imJ, Quaternion.star_imK] <;>
  field_simp <;>
  norm_cast <;>
  ring

lemma star_eq (z : 𝓞) : star z = (fromQuaternion ∘ star ∘ toQuaternion) z := by
  simp only [Function.comp_apply, ← toQuaternion_star]
  rw [leftInverse_fromQuaternion_toQuaternion]

instance : CharZero 𝓞 where
  cast_injective x y hxy := by simpa [Hurwitz.ext_iff] using hxy

def norm (z : 𝓞) : ℤ :=
  z.re * z.re + z.im_o * z.im_o + z.im_i * z.im_i + z.im_oi * z.im_oi
  - z.re * (z.im_o + z.im_oi) + z.im_i * (z.im_o - z.im_oi)

lemma norm_eq_mul_conj (z : 𝓞) : (norm z : 𝓞) = z * star z := by
  ext <;> simp [norm, ← Int.cast_add] <;> ring

lemma coe_norm (z : 𝓞) :
    (norm z : ℝ) =
      (z.re - 2⁻¹ * z.im_o - 2⁻¹ * z.im_oi) ^ 2 +
      (z.im_i + 2⁻¹ * z.im_o - 2⁻¹ * z.im_oi) ^ 2 +
      (2⁻¹ * z.im_o + 2⁻¹ * z.im_oi) ^ 2 +
      (2⁻¹ * z.im_o - 2⁻¹ * z.im_oi) ^ 2 := by
  rw [norm]
  field_simp
  norm_cast
  ring

lemma norm_zero : norm 0 = 0 := by simp [norm]

lemma norm_one : norm 1 = 1 := by simp [norm]

lemma norm_mul (x y : 𝓞) : norm (x * y) = norm x * norm y := by
  rw [← Int.cast_inj (α := 𝓞)]
  simp_rw [norm_eq_mul_conj, star_mul]
  rw [mul_assoc, ← mul_assoc y, ← norm_eq_mul_conj]
  rw [Int.cast_comm, ← mul_assoc, ← norm_eq_mul_conj, Int.cast_mul]

lemma norm_nonneg (x : 𝓞) : 0 ≤ norm x := by
  rw [← Int.cast_nonneg (R := ℝ), coe_norm]
  positivity

lemma norm_eq_zero (x : 𝓞) : norm x = 0 ↔ x = 0 := by
  constructor
  swap
  · rintro rfl; exact norm_zero
  intro h
  rw [← Int.cast_eq_zero (α := ℝ), coe_norm] at h
  field_simp at h
  norm_cast at h
  have h4 := eq_zero_of_add_nonpos_right (by positivity) (by positivity) h.le
  rw [sq_eq_zero_iff, sub_eq_zero] at h4
  have h1 := eq_zero_of_add_nonpos_left (by positivity) (by positivity) h.le
  have h3 := eq_zero_of_add_nonpos_right (by positivity) (by positivity) h1.le
  rw [h4] at h3
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff, add_self_eq_zero] at h3
  rw [h3] at h4
  simp only [h4, sub_zero, h3, add_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
    at h1
  have h2 := eq_zero_of_add_nonpos_right (by positivity) (by positivity) h1.le
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff, mul_eq_zero,
    or_false] at h2
  simp only [h2, zero_mul, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero,
    pow_eq_zero_iff, mul_eq_zero, or_false] at h1
  ext <;> assumption

open Quaternion in
lemma normSq_toQuaternion (z : 𝓞) : normSq (toQuaternion z) = norm z := by
  apply coe_injective
  rw [← self_mul_star, ← toQuaternion_star, ← toQuaternion_mul, ← norm_eq_mul_conj,
    toQuaternion_intCast, coe_intCast]

private lemma aux (x y z w : ℤ) : toQuaternion (fromQuaternion ⟨x,y,z,w⟩) = ⟨x,y,z,w⟩ := by
  apply leftInvOn_toQuaternion_fromQuaternion
  simp only [Set.mem_setOf]
  use x, y, z, w
  simp

private lemma aux2 (a b c d : ℝ) (ha : a ≤ 4⁻¹) (hb : b ≤ 4⁻¹) (hc : c ≤ 4⁻¹) (hd : d ≤ 4⁻¹)
    (H : ¬ (a = 4⁻¹ ∧ b = 4⁻¹ ∧ c = 4⁻¹ ∧ d = 4⁻¹)) :
    a + b + c + d < 1 := by
  apply lt_of_le_of_ne
  · calc
      _ ≤ (4 : ℝ)⁻¹ + 4⁻¹ + 4⁻¹ + 4⁻¹ := by gcongr
      _ = 1 := by norm_num
  contrapose! H
  have invs : (1 : ℝ) - 4⁻¹ = 4⁻¹ + 4⁻¹ + 4⁻¹ := by norm_num
  refine ⟨?_, ?_, ?_, ?_⟩ <;> apply le_antisymm ‹_› <;>
  [ (have : a = 1 - (b + c + d) := by rw [← H]; ring);
    (have : b = 1 - (a + c + d) := by rw [← H]; ring);
    (have : c = 1 - (a + b + d) := by rw [← H]; ring);
    (have : d = 1 - (a + b + c) := by rw [← H]; ring) ] <;>
  rw [this, le_sub_comm, invs] <;>
  gcongr

open Quaternion in
lemma exists_near (a : ℍ) : ∃ q : 𝓞, dist a (toQuaternion q) < 1 := by
  have four_inv : (4⁻¹ : ℝ) = 2⁻¹ ^ 2 := by norm_num
  have (r : ℝ) : (r - round r) ^ 2 ≤ 4⁻¹ := by
    rw [four_inv, sq_le_sq]
    apply (abs_sub_round _).trans_eq
    rw [abs_of_nonneg]
    all_goals norm_num
  let x := round a.re
  let y := round a.imI
  let z := round a.imJ
  let w := round a.imK
  by_cases H : |a.re - x| = 2⁻¹ ∧ |a.imI - y| = 2⁻¹ ∧ |a.imJ - z| = 2⁻¹ ∧ |a.imK - w| = 2⁻¹
  · use fromQuaternion a
    convert zero_lt_one' ℝ
    rw [NormedRing.dist_eq, ← sq_eq_zero_iff, sq, ← Quaternion.normSq_eq_norm_mul_self, normSq_def']
    rw [add_eq_zero_iff_of_nonneg (by positivity) (by positivity)]
    rw [add_eq_zero_iff_of_nonneg (by positivity) (by positivity)]
    rw [add_eq_zero_iff_of_nonneg (by positivity) (by positivity)]
    simp_rw [and_assoc, sq_eq_zero_iff, sub_re, sub_imI, sub_imJ, sub_imK, sub_eq_zero,
      ← Quaternion.ext_iff]
    symm
    apply leftInvOn_toQuaternion_fromQuaternion
    · simp only [Set.mem_setOf]
      have {r : ℝ} {z : ℤ} (h : |r - z| = 2⁻¹) : ∃ z' : ℤ, r = z' + 2⁻¹  := by
        cases (abs_eq (by positivity)).mp h with (rw [sub_eq_iff_eq_add'] at h)
        | inl h => use z
        | inr h => use z - 1; rw [h, Int.cast_sub, Int.cast_one, add_comm_sub]; norm_num

      obtain ⟨x', hx'⟩ := this H.1
      obtain ⟨y', hy'⟩ := this H.2.1
      obtain ⟨z', hz'⟩ := this H.2.2.1
      obtain ⟨w', hw'⟩ := this H.2.2.2
      use x', y', z', w', Or.inr ?_
      ext <;> simp [*]

  use fromQuaternion ⟨x,y,z,w⟩
  rw [aux]
  rw [NormedRing.dist_eq, ← sq_lt_one_iff (_root_.norm_nonneg _), sq,
    ← Quaternion.normSq_eq_norm_mul_self, normSq_def']

  simp only [sub_re, sub_imI, sub_imJ, sub_imK]

  apply aux2 <;> try apply this
  contrapose! H
  suffices ∀ r : ℝ, |r| = 2⁻¹ ↔ r ^ 2 = 4⁻¹ by
    simpa [this]
  intro r
  rw [four_inv, sq_eq_sq_iff_abs_eq_abs, abs_of_nonneg (a := (2⁻¹ : ℝ))]
  norm_num

open Quaternion in
lemma quot_rem (a b : 𝓞) (hb : b ≠ 0) : ∃ q r : 𝓞, a = q * b + r ∧ norm r < norm b := by
  let a' := toQuaternion a
  let b' := toQuaternion b
  have hb' : b' ≠ 0 := toQuaternion_ne_zero_iff.mpr hb
  let q' := a' / b'
  obtain ⟨q : 𝓞, hq : dist q' (toQuaternion q) < 1⟩ : ∃ _, _ := exists_near q'
  refine ⟨q, a - q * b, (add_sub_cancel _ _).symm, ?_⟩
  rw [← Int.cast_lt (R := ℝ), ← normSq_toQuaternion, ← normSq_toQuaternion]
  rw [normSq_eq_norm_mul_self, normSq_eq_norm_mul_self]
  refine mul_self_lt_mul_self ?_ ?_
  · exact _root_.norm_nonneg (a - q * b).toQuaternion
  rw [toQuaternion_sub, ← dist_eq_norm]
  calc
    _ = dist (q' * b') (q.toQuaternion * b') := ?_
    _ = dist q' (q.toQuaternion) * ‖b'‖ := ?_
    _ < _ := ?_
  · rw [toQuaternion_mul]
    dsimp only [b', q']
    rw [div_mul_cancel₀ a' hb']
  · -- Surprised that this doesn't seem to exist in mathlib.
    rw [dist_eq_norm_sub', ← sub_mul, _root_.norm_mul, ← dist_eq_norm_sub']
  · rw [← norm_pos_iff] at hb'
    exact mul_lt_of_lt_one_left hb' hq

lemma left_ideal_princ (I : Submodule 𝓞 𝓞) : ∃ a : 𝓞, I = Submodule.span 𝓞 {a} := by
  by_cases h_bot : I = ⊥
  · use 0
    rw [Eq.comm]
    simp only [h_bot, Submodule.span_singleton_eq_bot]
  let S := {a : 𝓞 // a ∈ I ∧ a ≠ 0}
  have : Nonempty S := by
    simp [S, ne_eq, norm_eq_zero]
    exact Submodule.exists_mem_ne_zero_of_ne_bot h_bot
  have hbdd : BddBelow <| Set.range (fun i : S ↦ norm i) := by
    use 0
    simp only [ne_eq, mem_lowerBounds, Set.mem_range]
    rintro _ ⟨_, rfl⟩
    exact norm_nonneg _
  obtain ⟨a, ha⟩ : ∃ a : S, norm a = ⨅ i : S, norm i :=
    exists_eq_ciInf_of_not_isPredPrelimit hbdd (Order.not_isPredPrelimit)
  use a
  apply le_antisymm
  · intro i hi
    rw [Submodule.mem_span_singleton]
    simp only [ne_eq]
    obtain ⟨q, r, hqr⟩ := quot_rem i a a.2.2
    rw [ha] at hqr
    have hrI : r ∈ I := by
      rw [show r = i - q • a by apply eq_sub_of_add_eq; rw [add_comm]; exact hqr.1.symm ]
      apply I.sub_mem hi (I.smul_mem _ a.2.1)
    have hr : r = 0 := by
      by_contra hr
      lift r to S using ⟨hrI, hr⟩
      apply (ciInf_le hbdd r).not_lt hqr.2
    rw [hr, add_zero] at hqr
    refine ⟨q, hqr.1.symm⟩
  · rw [Submodule.span_singleton_le_iff_mem]
    exact a.2.1

open scoped TensorProduct

noncomputable def HurwitzHat : Type := 𝓞 ⊗[ℤ] ZHat

scoped notation "𝓞^" => HurwitzHat

noncomputable instance : Ring 𝓞^ := Algebra.TensorProduct.instRing

noncomputable def HurwitzRat : Type := ℚ ⊗[ℤ] 𝓞

scoped notation "D" => HurwitzRat

noncomputable instance : Ring D := Algebra.TensorProduct.instRing

noncomputable def HurwitzRatHat : Type := D ⊗[ℤ] ZHat

scoped notation "D^" => HurwitzRatHat

noncomputable instance : Ring D^ := Algebra.TensorProduct.instRing

noncomputable abbrev j₁ : D →ₐ[ℤ] D^ := Algebra.TensorProduct.includeLeft -- (Algebra.TensorProduct.assoc ℤ ℚ 𝓞 ZHat).symm.trans Algebra.TensorProduct.includeLeft

lemma injective_hRat :
    Function.Injective j₁ := sorry -- flatness

noncomputable abbrev j₂ : 𝓞^ →ₐ[ℤ] D^ :=
  ((Algebra.TensorProduct.assoc ℤ ℚ 𝓞 ZHat).symm : ℚ ⊗ 𝓞^ ≃ₐ[ℤ] D ⊗ ZHat).toAlgHom.comp
  (Algebra.TensorProduct.includeRight : 𝓞^ →ₐ[ℤ] ℚ ⊗ 𝓞^)

lemma injective_zHat :
    Function.Injective j₂ := sorry -- flatness

-- should I rearrange tensors? Not sure if D^ should be (ℚ ⊗ 𝓞) ⊗ ℤhat or ℚ ⊗ (𝓞 ⊗ Zhat)
lemma canonicalForm (z : D^) : ∃ (N : ℕ+) (z' : 𝓞^), z = j₁ ((N⁻¹ : ℚ) ⊗ₜ 1 : D) * j₂ z' := by
  sorry

lemma completed_units (z : D^ˣ) : ∃ (u : Dˣ) (v : 𝓞^ˣ), (z : D^) = j₁ u * j₂ v := sorry

end Hurwitz
