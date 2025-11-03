import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Data.PNat.Prime
import Mathlib.RingTheory.Flat.TorsionFree
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
It is defined as the function whose value at `ZMod n` is the sum of `i!` for `0 ≤ i < n`. -/
def e : ZHat := ⟨fun (n : ℕ+) ↦ ∑ i ∈ range (n : ℕ), i !, by
  intros D N hDN
  dsimp only
  obtain ⟨k, hk⟩ := exists_add_of_le <| le_of_dvd N.pos hDN
  simp_rw [map_sum, map_natCast, hk, sum_range_add, add_eq_left]
  refine sum_eq_zero (fun i _ => ?_)
  rw [ZMod.natCast_eq_zero_iff]
  exact Nat.dvd_factorial D.pos le_self_add
⟩

open BigOperators Nat Finset

lemma e_def (n : ℕ+) : e n = ∑ i ∈ range (n : ℕ), (i ! : ZMod n) := rfl

lemma _root_.Nat.sum_factorial_lt_factorial_succ {j : ℕ} (hj : 1 < j) :
    ∑ i ∈ range (j + 1), i ! < (j + 1) ! := by
  calc
    ∑ i ∈ range (j + 1), i ! < ∑ _i ∈ range (j + 1), j ! := ?_
    _ = (j + 1) * (j !) := by rw [sum_const, card_range, smul_eq_mul]
    _ = (j + 1)! := Nat.factorial_succ _
  apply sum_lt_sum (fun i hi => factorial_le <| by simpa only [mem_range, lt_succ] using hi) ?_
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
  rw [hk, sum_range_add, add_eq_left]
  refine sum_eq_zero (fun i _ => ?_)
  rw [ZMod.natCast_eq_zero_iff, ← hk]
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
      rw [ZMod.natCast_eq_zero_iff]
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
lemma nat_mul_apply (N : ℕ) (z : ZHat) (k : ℕ+) : (N * z) k = N * (z k) := rfl

@[simp]
lemma pnat_mul_apply (N : ℕ+) (z : ZHat) (k : ℕ+) : (N * z) k = N * (z k) := rfl

theorem eq_zero_of_mul_eq_zero (N : ℕ+) (a : ZHat) (ha : N * a = 0) : a = 0 := by
  ext j
  rw [zero_val, ← a.prop j (N * j) (by simp)]
  apply torsionfree_aux
  apply Nat.dvd_of_mul_dvd_mul_left N.pos
  rw [← PNat.mul_coe]
  apply Nat.dvd_of_mod_eq_zero
  have : N * a (N * j) = 0 := by
    rw [← pnat_mul_apply]
    simp [ha]
  simpa only [ZMod.val_mul, ZMod.val_natCast, Nat.mod_mul_mod, ZMod.val_zero]
    using congrArg ZMod.val this

-- ZHat is torsion-free. LaTeX proof in the notes.
lemma torsionfree (N : ℕ+) : Function.Injective (fun z : ZHat ↦ N * z) := by
  rw [← AddMonoidHom.coe_mulLeft, injective_iff_map_eq_zero]
  intro a ha
  rw [AddMonoidHom.coe_mulLeft] at ha
  exact eq_zero_of_mul_eq_zero N a ha

instance ZHat_flat : Module.Flat ℤ ZHat := by
  rw [IsDedekindDomain.flat_iff_torsion_eq_bot]
  rw [eq_bot_iff]
  intro x hx
  simp only [Submodule.mem_torsion'_iff, Subtype.exists, Submonoid.mk_smul, zsmul_eq_mul,
    exists_prop, Submodule.mem_bot, mem_nonZeroDivisors_iff_ne_zero] at hx ⊢
  obtain ⟨N, hN⟩ := hx
  cases N
  case ofNat N =>
    simp only [Int.ofNat_eq_coe, ne_eq, cast_eq_zero, Int.cast_natCast] at hN
    lift N to ℕ+ using by omega -- lol
    exact eq_zero_of_mul_eq_zero _ _ hN.2
  case negSucc N =>
    simp only [ne_eq, Int.negSucc_ne_zero, not_false_eq_true, true_and, Int.cast_negSucc] at hN
    rw [neg_mul, neg_eq_zero] at hN
    exact eq_zero_of_mul_eq_zero ⟨N + 1, by omega⟩ _ hN

lemma y_mul_N_eq_z (N : ℕ+) (z : ZHat) (hz : z N = 0) (j : ℕ+) :
    N * ((z (N * j)).val / (N : ℕ) : ZMod j) = z j := by
  have hhj := z.prop N (N * j) (by simp only [PNat.mul_coe, dvd_mul_right])
  rw [hz, ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.natCast_eq_zero_iff] at hhj
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
    simp
  · intro h
    let y : ZHat := {
      val := fun j ↦ (z (N * j)).val / (N : ℕ)
      property := by
        intro j k hjk
        have hj := z.prop N (N * j) (by simp only [PNat.mul_coe, dvd_mul_right])
        have hk := z.prop N (N * k) (by simp only [PNat.mul_coe, dvd_mul_right])
        rw [h, ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.natCast_eq_zero_iff] at hj
        rw [h, ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.natCast_eq_zero_iff] at hk
        have hNjk := z.prop (N * j) (N * k) (mul_dvd_mul (dvd_refl _) hjk)
        rw [ZMod.castHom_apply, ZMod.cast_eq_val] at hNjk
        simp only [PNat.mul_coe, map_natCast, ZMod.natCast_eq_natCast_iff]
        apply Nat.ModEq.mul_right_cancel' (c := N) (by simp)
        rw [Nat.div_mul_cancel hj, Nat.div_mul_cancel hk,
          mul_comm (j : ℕ) (N : ℕ), ← ZMod.natCast_eq_natCast_iff, hNjk]
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

lemma canonicalForm (z : QHat) : ∃ (N : ℕ+) (z' : ZHat), z = (1 / N : ℚ) ⊗ₜ z' := by
  induction z using TensorProduct.induction_on with
  | zero =>
    refine ⟨1, 0, ?_⟩
    simp
  | tmul q z =>
    refine ⟨⟨q.den, q.den_pos ⟩, q.num * z, ?_⟩
    simp_rw [← zsmul_eq_mul, TensorProduct.tmul_smul, TensorProduct.smul_tmul']
    simp only [PNat.mk_coe, zsmul_eq_mul]
    simp only [← q.mul_den_eq_num, mul_assoc,
      one_div, ne_eq, Nat.cast_eq_zero, Rat.den_ne_zero, not_false_eq_true,
        mul_one, mul_inv_cancel₀]
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
  · have H' := val_coe_unit_coprime H.unit
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
      simp only at h
      have := congrArg (TensorProduct.lid ℤ ZHat) h
      simpa using this

instance nontrivial_QHat : Nontrivial QHat where
  exists_pair_ne := ⟨1 ⊗ₜ 0, 1 ⊗ₜ 1, injective_zHat.ne ZHat.zeroNeOne⟩

noncomputable abbrev i₁ : ℚ →ₐ[ℤ] QHat := Algebra.TensorProduct.includeLeft
lemma injective_rat :
    Function.Injective i₁ := RingHom.injective i₁.toRingHom

theorem PNat.lcm_comm (m n : ℕ+) : PNat.lcm m n = PNat.lcm n m := PNat.eq <| by
  simp [Nat.lcm_comm]

lemma lowestTerms (x : QHat) : (∃ N z, IsCoprime N z ∧ x = (1 / N : ℚ) ⊗ₜ z) ∧
    (∀ N₁ N₂ z₁ z₂,
    IsCoprime N₁ z₁ ∧ IsCoprime N₂ z₂ ∧ (1 / N₁ : ℚ) ⊗ₜ z₁ = (1 / N₂ : ℚ) ⊗ₜ[ℤ] z₂ →
      N₁ = N₂ ∧ z₁ = z₂) := by
  constructor
  · -- Existence: by the previous lemma, an arbitrary element [x] can be written as z/N;
    obtain ⟨N, z, h⟩ := canonicalForm x
    -- let D be the greatest common divisor of N and z_N (lifted to a natural).
    let D : PNat := ⟨Nat.gcd N (z N).val, Nat.gcd_pos_of_pos_left _ N.pos⟩
    cases D.one_le.eq_or_lt with
    | inl hD =>
      -- If D = 1 then the fraction is by definition in lowest terms.
      use N, z, ?_, h
      symm at hD
      simp_rw [D, ← PNat.coe_eq_one_iff, PNat.mk_coe] at hD
      rwa [isCoprime_iff_coprime, Nat.coprime_iff_gcd_eq_one]
    | inr hD =>
      -- However if 1 < D ∣ N then z_D is the reduction of z_N and is hence 0.
      have hDN : D ∣ N := PNat.dvd_iff.mpr (Nat.gcd_dvd_left N (z N).val)
      have := z.prop D N (PNat.dvd_iff.mp hDN)
      have : z D = 0 := by
        rw [← this, ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.natCast_eq_zero_iff]
        exact Nat.gcd_dvd_right N (z N).val

      -- By lemma 5.9 (ZHat.multiples) we deduce that z = Dy is a multiple of D,
      obtain ⟨y, hy⟩ : ∃ y, D * y = z := by rwa [ZHat.multiples]

      obtain ⟨E, hE⟩ := hDN
      use E, y, ?_, ?_
      swap
      · -- and hence [x = ] z / N = 1/N ⨂ₜ Dy = 1/E ⨂ y, where E = N / D.
        rw [h, hE, ← hy]
        have : (D : ZHat) • y = (D : ℤ) • y := by simp
        simp_rw [PNat.mul_coe, Nat.cast_mul, one_div, mul_inv, ← smul_eq_mul, this,
          ← TensorProduct.smul_tmul]
        simp
      · -- Now if a natural divided both y_E and E
        rw [isCoprime_iff_coprime]
        apply Nat.coprime_of_dvd fun k hk hk1 hk2 => ?_
        -- then this natural would divide both z_N/D [ = z_ED/D = y_N = y_ED] and N/D [ = E],
        -- contradicting the fact that D is the greatest common divisors
        suffices k ∣ (z N).val / D ∧ k ∣ N / D by
          have := Nat.dvd_gcd this.2 this.1
          simp [D, Nat.gcd_div_gcd_div_gcd_of_pos_left, hk.ne_one] at this
        constructor
        swap
        · simp [hE, hk1]
        simp only [← hy, ZHat.nat_mul_apply, ZMod.val_mul, ZMod.val_natCast, Nat.mod_mul_mod]
        nth_rw 3 [hE]
        have := y.prop E N (by simp [hE])
        simp only [ZMod.castHom_apply, ZMod.cast_eq_val] at this
        rwa [PNat.mul_coe, Nat.mul_mod_mul_left, Nat.mul_div_cancel_left _ (by simp),
          ← ZMod.val_natCast, this]
  · -- Uniqueness:
    rintro N M z w ⟨hcpz, hcpw, h⟩
    -- if z/N = w/M, we deduce 1 ⨂ₜ Mz = 1 ⨂ₜ Nw
    have : i₂ (M * z) = i₂ (N * w) := by
      apply_fun ((M * N : ℤ) • ·) at h
      conv_lhs at h => rw [mul_comm]
      simpa [← TensorProduct.smul_tmul_smul] using h
    let y := M * z
    -- and by injectivity of ZHat → QHat
    have hNz := injective_zHat this
    -- we deduce that Mz = Nw = y.
    have hy₁ : y = M * z := rfl
    have hy₂ : y = N * w := by rw [← hNz]
    -- In particular, if L is the lowest common multiple of M and N
    let L : ℕ+ := PNat.lcm N M
    -- then y_L is a multiple of both M and N and is hence zero,
    have : y L = 0 := by
      suffices (L : ℕ) ∣ (y L).val by
        simpa [← ZMod.natCast_eq_zero_iff]
      apply lcm_dvd <;> [rw [hy₂]; rw [hy₁]] <;>
      · simp only [ZHat.pnat_mul_apply, ZMod.val_mul, ZMod.val_natCast, Nat.mod_mul_mod]
        refine (Nat.dvd_mod_iff ?_).mpr (Nat.dvd_mul_right _ _)
        simp only [PNat.lcm_coe, Nat.dvd_lcm_left, Nat.dvd_lcm_right, L]
    -- so y = Lx is a multiple of L by 5.9 (ZHat.multiples),
    obtain ⟨x, hx⟩ := (ZHat.multiples _ _).mpr this
    -- and we deduce from torsionfreeness that z = (L/M)x [ = M'x] and w = (L/N)x [ = N'x].
    obtain ⟨N', hN'⟩ : N ∣ L := PNat.dvd_lcm_left N M
    have hN'' : (N' : ℕ) = L / N := by simp [hN']
    obtain ⟨M', hM'⟩ : M ∣ L := PNat.dvd_lcm_right N M
    have hM'' : (M' : ℕ) = L / M := by simp [hM']
    have hz : z = M' * x := by
      apply ZHat.torsionfree M
      dsimp
      rw [← hy₁, ← hx, ← mul_assoc, ← Nat.cast_mul, ← PNat.mul_coe, ← hM']
    have hw : w = N' * x :=  by
      apply ZHat.torsionfree N
      dsimp
      rw [← hy₂, ← hx, ← mul_assoc, ← Nat.cast_mul, ← PNat.mul_coe, ← hN']
    -- If some prime divided L/M [ = M'] then it would have to divide N
    -- which means that z is not in lowest terms;
    -- similarly if some prime divided L/N [ = N'] then w/M would not be in lowest terms.
    have dvd (n m p : Nat) (hm : 0 < m) : p ∣ (n.lcm m / m) → p ∣ n := by
      intro h
      rw [Nat.lcm_eq_mul_div] at h
      rw [Nat.div_div_eq_div_mul] at h
      rw [Nat.mul_div_mul_right _ _ hm] at h
      apply h.trans
      refine Nat.div_dvd_of_dvd ?_
      exact Nat.gcd_dvd_left n m

    -- We deduce that L = M = N and hence z = w by torsionfreeness.
    have {n m : ℕ+} {Z : ZHat} (hcp : IsCoprime m Z) (hZ : ((n.lcm m / n : ℕ) : ZHat) ∣ Z) :
        n.lcm m = n := by
      rw [isCoprime_iff_coprime] at *
      apply PNat.eq
      symm
      apply Nat.eq_of_dvd_of_div_eq_one
      · refine PNat.dvd_iff.mp ?_
        exact PNat.dvd_lcm_left n m
      contrapose! hcp
      let f := Nat.minFac (n.lcm m / n : ℕ)
      have hf : f ∣ _ := Nat.minFac_dvd (n.lcm m / n : ℕ)
      have hfprime : Nat.Prime f := Nat.minFac_prime <| by simpa
      have := dvd m n f (by simp) (by simpa [← PNat.lcm_coe, Nat.lcm_comm] using hf)
      apply Nat.not_coprime_of_dvd_of_dvd hfprime.one_lt this
      obtain ⟨g, hg⟩ : (f : ZHat) ∣ Z := by
        apply dvd_trans ?_ hZ
        obtain ⟨g, hg⟩ := hf
        simp only [PNat.lcm_coe] at hg
        simp [hg]
      rw [hg]
      simp only [ZHat.nat_mul_apply, ZMod.val_mul, Nat.dvd_mod_iff this]
      apply dvd_mul_of_dvd_left
      simp only [ZMod.val_natCast]
      rw [Nat.dvd_mod_iff this]
    have hw' : ((L / N : ℕ) : ZHat) ∣ w := by
      rw [hw, hN'']
      exact dvd_mul_right _ _
    have hz' : ((M.lcm N / M : ℕ) : ZHat) ∣ z := by
      rw [hz, hM'', PNat.lcm_comm]
      exact dvd_mul_right _ _
    have hN : L = N := this hcpw hw'
    have hM : L = M := PNat.lcm_comm _ _ |>.trans <| this hcpz hz'
    have hNM' : N' = M' := by
      apply mul_left_cancel (a := L)
      conv_lhs =>
        rw [hN, ← hN']
      conv_rhs =>
        rw [hM, ← hM']
    rw [hz, hw, ← hN, ← hM, hNM']
    exact ⟨rfl, rfl⟩

section additive_structure_of_QHat

noncomputable abbrev ratsub : AddSubgroup QHat :=
    (i₁ : ℚ →+ QHat).range

noncomputable abbrev zHatsub : AddSubgroup QHat :=
    (i₂ : ZHat →+ QHat).range

noncomputable abbrev zsub : AddSubgroup QHat :=
  (Int.castRingHom QHat : ℤ →+ QHat).range

lemma ZMod.isUnit_natAbs {z : ℤ} {N : ℕ} : IsUnit (z.natAbs : ZMod N) ↔ IsUnit (z : ZMod N) := by
  cases z.natAbs_eq with
  | inl h | inr h => rw [h]; simp

@[simp]
lemma _root_.Algebra.TensorProduct.one_tmul_intCast {R : Type*} {A : Type*} {B : Type*}
    [CommRing R] [Ring A] [Algebra R A] [Ring B] [Algebra R B] {z : ℤ} :
    (1 : A) ⊗ₜ[R] (z : B) = (z : TensorProduct R A B) := by
  rw [← map_intCast (F := B →ₐ[R] TensorProduct R A B),
    Algebra.TensorProduct.includeRight_apply]

lemma rat_meet_zHat : ratsub ⊓ zHatsub = zsub := by
  apply le_antisymm
  · intro x ⟨⟨l, hl⟩, ⟨r, hr⟩⟩
    simp only [AddMonoidHom.coe_coe, Algebra.TensorProduct.includeLeft_apply,
      Algebra.TensorProduct.includeRight_apply] at hl hr
    rcases lowestTerms x with ⟨⟨N, z, hNz, hx⟩, unique⟩
    have cop1 : IsCoprime l.den.toPNat' l.num := by
      simp_rw [IsCoprime, ZHat.intCast_val, ← ZMod.isUnit_natAbs, ZMod.isUnit_iff_coprime,
        PNat.toPNat'_coe l.den_pos]
      exact l.reduced
    have cop2 : IsCoprime 1 r := by
      simp only [IsCoprime, PNat.val_ofNat]
      exact isUnit_of_subsingleton _
    have hcanon : x = (1/(l.den : ℚ)) ⊗ₜ[ℤ] (l.num : ZHat) := by
      nth_rw 1 [← hl, ← Rat.num_div_den l, ← mul_one ((l.num : ℚ) / l.den), div_mul_comm,
      mul_comm, ← zsmul_eq_mul, TensorProduct.smul_tmul, zsmul_eq_mul, mul_one]
    rw [← PNat.toPNat'_coe l.den_pos, hx] at hcanon
    obtain ⟨rfl, rfl⟩ := unique _ _ _ _ ⟨hNz, cop1, hcanon⟩
    have : 1 = 1 / (((1 : ℕ+) : ℕ) : ℚ) := by simp
    nth_rw 1 [← hx, ← hr, this] at hcanon
    use l.num; rw [hx, (unique _ 1 _ r ⟨hNz, cop2, hcanon.symm⟩).1]
    simp
  · exact fun x ⟨k, hk⟩ ↦ by constructor <;>
      (use k; simp only [AddMonoidHom.coe_coe,
        map_intCast]; exact hk)

lemma rat_join_zHat : ratsub ⊔ zHatsub = ⊤ := by
  rw [eq_top_iff]
  intro x _
  rcases x.canonicalForm with ⟨N, z, hNz⟩
  rcases ZHat.nat_dense N z with ⟨q, r, hz, _⟩
  have h : z - r = N * q := sub_eq_of_eq_add hz
  rw [AddSubgroup.mem_sup]
  use ((r : ℤ) / N : ℚ) ⊗ₜ[ℤ] 1
  constructor
  · simp
  use 1 ⊗ₜ[ℤ] q
  constructor
  · simp
  nth_rw 1 [← mul_one ((r : ℤ) / N : ℚ), div_mul_comm,
    mul_comm, ← zsmul_eq_mul, TensorProduct.smul_tmul, zsmul_eq_mul, mul_one]
  have : 1 = 1 / (N : ℚ) * (N : ℤ) := by simp
  nth_rw 2 [this]
  rw [mul_comm, ← zsmul_eq_mul, TensorProduct.smul_tmul, zsmul_eq_mul]
  norm_cast; rw [← h, ← TensorProduct.tmul_add]
  simp [hNz]

end additive_structure_of_QHat

section multiplicative_structure_of_QHat

noncomputable abbrev unitsratsub : Subgroup QHatˣ :=
  (Units.map (i₁ : ℚ →* QHat)).range

noncomputable abbrev unitszHatsub : Subgroup QHatˣ :=
  (Units.map (i₂ : ZHat →* QHat)).range

noncomputable abbrev unitszsub : Subgroup QHatˣ :=
  (Units.map (Int.castRingHom QHat : ℤ →* QHat)).range

lemma unitsrat_meet_unitszHat : unitsratsub ⊓ unitszHatsub = unitszsub := by
  apply le_antisymm
  · intro x ⟨⟨q, hxq⟩, ⟨zHat, hxzHat⟩⟩
    obtain ⟨z, (hz : (z : QHat) = x)⟩ : (x : QHat) ∈ zsub := by
      rw [← rat_meet_zHat]
      exact ⟨⟨q, by simp [← hxq]⟩, zHat, by simp [← hxzHat]⟩
    have znez : z ≠ 0 := by
      rintro rfl
      simp [Eq.comm] at hz
    let a := Int.sign z
    let b := Int.natAbs z
    set zinvRat : ℚ := a / b with zinvRat_def
    have hzinvRat : z * zinvRat = 1 := by
      rw [mul_div, div_eq_one_iff_eq]
      · rw_mod_cast [Int.mul_sign_self z]
      · exact_mod_cast Int.natAbs_ne_zero.mpr znez
    let zinvZHat : ZHatˣ := zHat⁻¹
    have hzinvZHat : ↑zHat * ↑zinvZHat = (1 : ZHat) := Units.mul_inv zHat
    let xinv : QHatˣ := x⁻¹
    have h1 : zinvRat ⊗ₜ[ℤ] (1 : ZHat) = xinv := by
      apply Units.eq_inv_of_mul_eq_one_left
      rw [← hz, ← zsmul_eq_mul, TensorProduct.smul_tmul', zsmul_eq_mul,
        hzinvRat, Algebra.TensorProduct.one_def]
    have h2 : (1 : ℚ) ⊗ₜ[ℤ] (Units.val zinvZHat) = xinv := by
      apply Units.eq_inv_of_mul_eq_one_left
      have hzHat : (1 : ℚ) ⊗ₜ[ℤ] (zHat : ZHat) = (x : QHat) := by simp [← hxzHat]
      rw [← hzHat, Algebra.TensorProduct.tmul_mul_tmul, mul_one, hzinvZHat,
        Algebra.TensorProduct.one_def]
    have h3 : zinvRat ⊗ₜ[ℤ] (1 : ZHat) = (1 / b : ℚ) ⊗ₜ[ℤ] (a : ZHat) := by
      rw [zinvRat_def, ← mul_one (a : ℚ), ← mul_div,
      ← zsmul_eq_mul, TensorProduct.smul_tmul, zsmul_eq_mul, mul_one]
    have bpos : 0 < b := Int.natAbs_pos.2 znez
    have heq : (1 / (((Nat.toPNat b bpos) : ℕ) : ℚ)) ⊗ₜ[ℤ] (a : ZHat) =
        (1 / (((1 : ℕ+) : ℕ) : ℚ)) ⊗ₜ[ℤ] ↑zinvZHat := by
      have : ↑(Nat.toPNat b bpos) = b := by
        unfold Nat.toPNat
        rw [PNat.mk_coe]
      rw [PNat.val_ofNat, Nat.cast_one, div_self one_ne_zero, this, ← h3, h1, h2]
    have cop1 : IsCoprime (b.toPNat bpos) ↑a := by
      rw [IsCoprime, ZHat.intCast_val, ← ZMod.isUnit_natAbs,
        ZMod.isUnit_iff_coprime, Int.natAbs_sign_of_ne_zero znez]
      exact Nat.coprime_one_left _
    have cop2 : IsCoprime 1 ↑zinvZHat := by
      simp only [IsCoprime, PNat.val_ofNat, isUnit_of_subsingleton]
    obtain ⟨hb, ha⟩ := (lowestTerms ↑x).2 (Nat.toPNat b bpos) 1 ↑a ↑zinvZHat ⟨cop1, cop2, heq⟩
    have b1 : b = 1 := PNat.coe_eq_one_iff.2 hb
    obtain ⟨u, rfl⟩ := Int.isUnit_iff_natAbs_eq.2 b1
    use u
    ext
    norm_cast at hz
  · intro x ⟨xz, hxz⟩
    constructor
    · use (Units.map ↑(Int.castRingHom ℚ)) xz
      norm_cast
    · use (Units.map ↑(Int.castRingHom ZHat)) xz
      rw [← hxz, ← MonoidHom.comp_apply, ← Units.map_comp]
      congr
      ext x
      · simp only [MonoidHom.coe_comp, MonoidHom.coe_coe, Function.comp_apply, Int.coe_castRingHom,
        Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.one_tmul_intCast]
      simp

@[simp]
lemma _root_.Algebra.TensorProduct.intCast_tmul_one {R : Type*} {A : Type*} {B : Type*}
    [CommRing R] [Ring A] [Algebra R A] [Ring B] [Algebra R B] {z : ℤ} :
    (z : A) ⊗ₜ[R] (1 : B) = (z : TensorProduct R A B) := by
  rw [← map_intCast (F := A →ₐ[R] TensorProduct R A B),
    Algebra.TensorProduct.includeLeft_apply]

@[simp]
lemma _root_.Algebra.TensorProduct.one_tmul_natCast {R : Type*} {A : Type*} {B : Type*}
    [CommRing R] [Ring A] [Algebra R A] [Ring B] [Algebra R B] {n : ℕ} :
    (1 : A) ⊗ₜ[R] (n : B) = (n : TensorProduct R A B) := by
  rw [← map_natCast (F := B →ₐ[R] TensorProduct R A B),
    Algebra.TensorProduct.includeRight_apply]

-- this needs that ℤ is a PID.
lemma unitsrat_join_unitszHat : unitsratsub ⊔ unitszHatsub = ⊤ := by
  rw [eq_top_iff]
  rintro y -
  rcases canonicalForm y.val with ⟨N, x, hy⟩
  rcases canonicalForm (y⁻¹.val) with ⟨N2, x2, hy2⟩
  set xinv := (1 / (N * N2) : ℚ) ⊗ₜ[ℤ] x2 with xinv_def
  have : (i₂ x) * xinv = 1 := by
    rw [xinv_def, Algebra.TensorProduct.includeRight_apply, one_div, mul_inv_rev,
      Algebra.TensorProduct.tmul_mul_tmul,one_mul,mul_comm,← Algebra.TensorProduct.tmul_mul_tmul,
      ← one_div, ← one_div, ← hy, ← hy2, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  let xunit : QHatˣ := ⟨i₂ x, xinv, this, by rw [mul_comm]; exact this⟩
  suffices h : ∀ (u : QHatˣ), (u : QHat) ∈ zHatsub → u ∈ unitsratsub ⊔ unitszHatsub by
    specialize h xunit
    simp only [Algebra.TensorProduct.includeRight_apply, AddMonoidHom.mem_range,
      AddMonoidHom.coe_coe, exists_apply_eq_apply, forall_const, Subgroup.mem_sup, xunit] at h
    rcases h with ⟨w, ⟨v, rfl⟩, z, ⟨t, rfl⟩, wzx⟩
    rw [Subgroup.mem_sup]
    let q : ℚˣ := ⟨v / N, N / v, by field_simp, by field_simp⟩
    use ((Units.map ↑i₁) q)
    simp only [MonoidHom.mem_range, exists_exists_eq_and]
    refine ⟨⟨q, rfl⟩, t, ?_⟩
    simp only [← Units.val_inj, hy, Units.map_mk, MonoidHom.coe_coe,
      Algebra.TensorProduct.includeLeft_apply, Units.val_mul, one_div, q]
    rw [← mul_one (N⁻¹ : ℚ), ← one_mul x, ← Algebra.TensorProduct.tmul_mul_tmul, div_eq_mul_inv,
      mul_comm (v : ℚ), ← mul_one 1, ← Algebra.TensorProduct.tmul_mul_tmul, mul_assoc, mul_one]
    congr
    simpa only [← Units.val_inj, Units.val_mul, Units.coe_map, MonoidHom.coe_coe,
      Algebra.TensorProduct.includeLeft_apply, xunit, q] using wzx
  clear * -
  intro x hx
  rcases canonicalForm (x⁻¹.val) with ⟨M, y, hxinv⟩
  have : x * (i₂ y) = M := by
    rw [← one_mul (M : QHat), ← Units.val_one, ← mul_inv_cancel x, Units.val_mul, mul_assoc]
    congr!
    have h : (M : QHat) = (M : ℚ) ⊗ₜ[ℤ] 1 := by norm_cast
    rw [Algebra.TensorProduct.includeRight_apply, hxinv, h, Algebra.TensorProduct.tmul_mul_tmul,
      mul_one, one_div, inv_mul_cancel₀]
    simp only [ne_eq, Rat.natCast_eq_zero_iff, PNat.ne_zero, not_false_eq_true]
  rcases hx with ⟨X, hX⟩
  let I := Ideal.span {X}
  let J := I.comap (Int.castRingHom ZHat)
  have Jnonzero : (M : ℤ) ∈ J := by
    simp only [J, I, Ideal.mem_comap]
    rw [Ideal.mem_span_singleton']
    use y
    apply injective_zHat
    simp only [mul_comm, ← hX, AddMonoidHom.coe_coe, Algebra.TensorProduct.includeRight_apply,
      Algebra.TensorProduct.tmul_mul_tmul, mul_one] at this
    rw [Algebra.TensorProduct.includeRight_apply, this, map_natCast,
      Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.one_tmul_natCast]
  obtain ⟨g, hg⟩ := IsPrincipalIdealRing.principal (R := ℤ) J
  wlog gpos : 0 < g with H
  · specialize H x M y hxinv this X hX Jnonzero (-g)
    apply H (by rw [← Set.neg_singleton, Submodule.span_neg, ← hg])
    rw [Int.neg_pos, Int.lt_iff_le_and_ne, ← Int.not_gt_eq]
    refine ⟨gpos, ?_⟩
    rintro rfl
    rw [Submodule.span_zero_singleton, Submodule.eq_bot_iff] at hg
    specialize hg (M : ℤ) Jnonzero
    simp only [Int.natCast_eq_zero, PNat.ne_zero] at hg
  clear this hxinv y Jnonzero M
  let N : ℕ+ := ⟨g.toNat, Int.pos_iff_toNat_pos.1 gpos⟩
  suffices h : Ideal.span {X} = Ideal.span {(g : ZHat)} by
    obtain ⟨y, hy⟩ : ∃ y, y * X = g := by
      rw [← Ideal.mem_span_singleton', h, Ideal.mem_span_singleton]
    obtain ⟨z, hz⟩ : ∃ z, z * g = X := by
      rw [← Ideal.mem_span_singleton', ← h, Ideal.mem_span_singleton]
    have : y * z = 1 := by
      rw [mul_comm, ← sub_right_inj (a := (1 : ZHat)), sub_self]
      apply ZHat.eq_zero_of_mul_eq_zero N
      rw [PNat.mk_coe, ← Int.cast_natCast, Int.natCast_toNat_eq_self.2 (le_of_lt gpos), mul_sub,
        mul_one, sub_eq_zero, ← mul_assoc, mul_comm _ z, hz, mul_comm, hy]
    simp only [Subgroup.mem_sup, MonoidHom.mem_range, exists_exists_eq_and]
    set G : ℚ := 1 / g with G_def
    have gG : g * G = 1 := by
      rw [G_def, one_div, mul_inv_cancel₀]
      simp only [ne_eq, Rat.intCast_eq_zero_iff, Int.ne_of_gt gpos, not_false_eq_true]
    use ⟨g, G, gG, mul_comm _ G ▸ gG⟩
    use ⟨z, y, by rw[mul_comm]; exact this, this⟩
    simp only [← Units.val_inj, ← hX, Units.map_mk, MonoidHom.coe_coe, map_intCast,
      Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.includeRight_apply,
      Units.val_mul, AddMonoidHom.coe_coe]
    rw [← hz, ← mul_one 1, ← Algebra.TensorProduct.tmul_mul_tmul, mul_one, mul_comm,
      Algebra.TensorProduct.one_tmul_intCast]
  have hgx : Ideal.span {(g : ZHat)} ≤ Ideal.span {X} := by
    have : g ∈ J := by
      rw [hg, Ideal.submodule_span_eq]
      apply Ideal.mem_span_singleton_self
    simp only [J, I] at this
    exact (Ideal.span_singleton_le_iff_mem _).2 this
  refine le_antisymm ?_ hgx
  suffices h : X N = 0 by
    rcases (ZHat.multiples N X).2 h with ⟨y, hy⟩
    rw [Ideal.span_singleton_le_span_singleton, ← hy, PNat.mk_coe]
    exact ⟨y, by rw [← Int.cast_natCast, Int.natCast_toNat_eq_self.2 (le_of_lt gpos)]⟩
  let xg := (X N).val
  have : (xg - X) N = 0 := by
    simp only [ZHat, ZMod.castHom_apply, ZHat.instDFunLikePNatZModVal,
      AddSubgroupClass.coe_sub, SubringClass.coe_natCast, Pi.sub_apply, Pi.natCast_apply, xg]
    simp only [ZMod.natCast_val, ZMod.cast_id', id_eq, sub_self]
  rcases (ZHat.multiples N _).2 this with ⟨y, hy⟩
  have : (xg : ZHat) ∈ Ideal.span {X} := by
    rw [← sub_add_cancel (xg : ZHat) X]
    apply Ideal.add_mem
    · apply hgx
      rw [Ideal.mem_span_singleton', ← hy, mul_comm, PNat.mk_coe]
      exact ⟨y, by rw [← Int.cast_natCast, Int.natCast_toNat_eq_self.2 (le_of_lt gpos)]⟩
    apply Ideal.mem_span_singleton_self
  have hxg : (xg : ℤ) ∈ J := by
    rw [Ideal.mem_comap]
    simp only [Int.coe_castRingHom, Int.cast_natCast, I, this]
  rw [hg, Submodule.mem_span_singleton] at hxg
  rcases hxg with ⟨a, ha⟩
  rw [← ZMod.val_eq_zero, ← Int.natCast_eq_zero]
  apply Int.eq_zero_of_dvd_of_nonneg_of_lt (n := g) (Int.natCast_nonneg _)
  · exact Int.lt_of_toNat_lt (ZMod.val_lt (X N))
  exact ⟨a, by rw [mul_comm, ← smul_eq_mul, ha]⟩

end multiplicative_structure_of_QHat

end QHat
