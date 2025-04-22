import Mathlib.Algebra.CharZero.Infinite
import Mathlib.NumberTheory.Padics.PadicIntegers
import FLT.Mathlib.Algebra.Module.Submodule.Basic
import FLT.Mathlib.RingTheory.Ideal.Operations
import Mathlib.NumberTheory.Padics.RingHoms

/-!
# TODO

* Rename `Coe.ringHom` to `coeRingHom`
* Protect `PadicInt.norm_mul`, `PadicInt.norm_units`, `PadicInt.norm_pow`
-/

open Function Topology Subgroup
open scoped NNReal nonZeroDivisors Pointwise

variable {p : ℕ} [Fact p.Prime]

namespace PadicInt
variable {x : ℤ_[p]}

attribute [simp] coe_eq_zero

@[simp, norm_cast] lemma coe_coeRingHom : ⇑(Coe.ringHom (p := p)) = (↑) := rfl

lemma coe_injective : Injective ((↑) : ℤ_[p] → ℚ_[p]) := Subtype.val_injective

@[simp] lemma coe_inj {x y : ℤ_[p]} : (x : ℚ_[p]) = (y : ℚ_[p]) ↔ x = y := coe_injective.eq_iff

instance : Infinite ℤ_[p] := CharZero.infinite _

@[simp]
protected lemma nnnorm_mul (x y : ℤ_[p]) : ‖x * y‖₊ = ‖x‖₊ * ‖y‖₊ := by simp [nnnorm, NNReal]

@[simp]
protected lemma nnnorm_pow (x : ℤ_[p]) (n : ℕ) : ‖x ^ n‖₊ = ‖x‖₊ ^ n := by simp [nnnorm, NNReal]

@[simp] lemma nnnorm_p : ‖(p : ℤ_[p])‖₊ = (p : ℝ≥0)⁻¹ := by simp [nnnorm]; rfl

@[simp] protected lemma nnnorm_units (u : ℤ_[p]ˣ) : ‖(u : ℤ_[p])‖₊ = 1 := by simp [nnnorm, NNReal]

lemma exists_unit_mul_p_pow_eq (hx : x ≠ 0) : ∃ (u : ℤ_[p]ˣ) (n : ℕ), (u : ℤ_[p]) * p ^ n = x :=
  ⟨_, _, (unitCoeff_spec hx).symm⟩

lemma isOpenEmbedding_coe : IsOpenEmbedding ((↑) : ℤ_[p] → ℚ_[p]) := by
  refine (?_ : IsOpen {y : ℚ_[p] | ‖y‖ ≤ 1}).isOpenEmbedding_subtypeVal
  simpa only [Metric.closedBall, dist_eq_norm_sub, sub_zero] using
    IsUltrametricDist.isOpen_closedBall (0 : ℚ_[p]) one_ne_zero

@[simp] lemma image_coe_smul_set (x : ℤ_[p]) (s : Set ℤ_[p]) :
    ((↑) '' (x • s) : Set ℚ_[p]) = x • (↑) '' s := Set.image_comm fun _ ↦ rfl

-- Yaël: Do we really want this as a coercion?
noncomputable instance : Coe ℤ_[p]ˣ ℚ_[p]ˣ where coe := Units.map Coe.ringHom.toMonoidHom

lemma _root_.AddSubgroup.comap_smul_one (R A : Type*) [CommRing R] [CommRing A] [Algebra R A]
    [FaithfulSMul R A]
    (r : R) : AddSubgroup.comap (algebraMap R A) (r • (1 : Submodule R A).toAddSubgroup) =
    r • (1 : Submodule R R).toAddSubgroup := by
  ext s
  simp only [AddSubgroup.mem_comap, AddMonoidHom.coe_coe, AddSubgroup.mem_smul_pointwise_iff_exists,
    Submodule.mem_toAddSubgroup, Submodule.mem_one, exists_exists_eq_and, Ideal.one_eq_top,
    Submodule.top_toAddSubgroup, AddSubgroup.mem_top, smul_eq_mul, true_and]
  apply exists_congr (fun t ↦ ?_)
  rw [Algebra.smul_def, ← map_mul, Injective.eq_iff]
  rwa [← faithfulSMul_iff_algebraMap_injective R A]

lemma index_span_p_pow (hx: x ≠ 0):
    (Submodule.toAddSubgroup (Ideal.span {(p : ℤ_[p]) ^ x.valuation})).index = ‖↑x‖₊⁻¹ := by
  have quotient_equiv_zmod := RingHom.quotientKerEquivOfSurjective
    (f := PadicInt.toZModPow (x.valuation) (p := p)) (R := ℤ_[p])
    (ZMod.ringHom_surjective (PadicInt.toZModPow x.valuation))
  have card_eq_zmod := Nat.card_congr quotient_equiv_zmod.toEquiv
  have quotient_equiv_quotient :=
    Ideal.quotEquivOfEq (PadicInt.ker_toZModPow (x.valuation) (p := p))
  have card_eq_quotient := Nat.card_congr quotient_equiv_quotient.toEquiv
  rw [card_eq_quotient] at card_eq_zmod
  have quotients_defeq :
    (ℤ_[p] ⧸ (Submodule.toAddSubgroup (Ideal.span {(p : ℤ_[p]) ^ x.valuation}))) =
    (ℤ_[p] ⧸ Ideal.span {(p: ℤ_[p]) ^ x.valuation}) := rfl
  simp [AddSubgroup.index, quotients_defeq, card_eq_zmod, NNReal.eq_iff,
    norm_eq_zpow_neg_valuation hx]

lemma smul_submodule_one_index :
    (x • (1 : Submodule ℤ_[p] ℤ_[p])).toAddSubgroup.index = ‖(x : ℚ_[p])‖₊⁻¹ := by
  by_cases hx: x = 0
  . simp [hx]
  . have x_factor := PadicInt.unitCoeff_spec hx
    nth_rw 1 [x_factor]
    rw [Submodule.smul_one_eq_span, Ideal.span_singleton_mul_left_unit (Units.isUnit _)]
    exact index_span_p_pow hx

/-- `x • S` has index `‖x‖⁻¹` in `S`, where `S` is the copy of `ℤ_[p]` inside `ℚ_[p]` --/
lemma smul_submodule_one_relindex: (x • (1 : Submodule ℤ_[p] ℚ_[p]).toAddSubgroup).relindex
    (1 : Submodule ℤ_[p] ℚ_[p]).toAddSubgroup = ‖x.val‖₊⁻¹ := by
  have relindex_in_z_p : (x • (1 : Submodule ℤ_[p] ℤ_[p])).toAddSubgroup.index =
      ‖(x : ℚ_[p])‖₊⁻¹ := smul_submodule_one_index
  rw [← AddSubgroup.relindex_top_right] at relindex_in_z_p

  -- Use the coercion from ℤ_[p] to ℚ_[p] and `AddSubgroup.relindex_comap` to convert our
  -- result about subgroups of `Z_[p]` to a result about subgroups of `Q_[p]`.
  let z_q_coe: ℤ_[p] →+ ℚ_[p] := PadicInt.Coe.ringHom.toAddMonoidHom
  let K_Q : AddSubgroup ℚ_[p] := (1 : Submodule ℤ_[p] ℚ_[p]).toAddSubgroup
  let H_Q := (x : ℚ_[p]) • K_Q
  have hHK_Q : H_Q ≤ K_Q := (1 : Submodule ℤ_[p] ℚ_[p]).smul_le_self_of_tower (x : ℤ_[p])

  have relindex_preserved := AddSubgroup.relindex_comap (H := H_Q) (f := (z_q_coe))
      (K := (⊤ : AddSubgroup ℤ_[p]))
  have map_top: (AddSubgroup.map z_q_coe ⊤) = K_Q := by
    ext a
    simp [z_q_coe, K_Q]
  have map_H_Q : (AddSubgroup.comap z_q_coe H_Q) =
    (x • (1 : Submodule ℤ_[p] ℤ_[p])).toAddSubgroup := by
    simp only [z_q_coe, H_Q, K_Q, RingHom.toAddMonoidHom_eq_coe,
      Submodule.pointwise_smul_toAddSubgroup, Submodule.top_toAddSubgroup, z_q_coe,
      K_Q, ← AddSubgroup.comap_smul_one ℤ_[p] ℚ_[p]]
    rfl

  rw [map_top, map_H_Q] at relindex_preserved
  rwa [relindex_preserved] at relindex_in_z_p

/-- `x • S` has finite  in `S`, where `S` is the copy of `ℤ_[p]` inside `ℚ_[p]` --/
lemma smul_submodule_one_isFiniteRelIndex (hx : x ≠ 0):
    (x • (1 : Submodule ℤ_[p] ℚ_[p]).toAddSubgroup).IsFiniteRelIndex
    (1 : Submodule ℤ_[p] ℚ_[p]).toAddSubgroup where
  relindex_ne_zero := by
    rw [← Nat.cast_ne_zero (R := ℝ≥0)]
    simp [smul_submodule_one_relindex, hx]

-- Yaël: Do we really want this as a coercion?
noncomputable instance : Coe ℤ_[p]⁰ ℚ_[p]ˣ where
  coe x := .mk0 x.1 <| map_ne_zero_of_mem_nonZeroDivisors (M₀ := ℤ_[p])
    Coe.ringHom coe_injective x.2

/-- Non-zero p-adic integers generate non-zero p-adic numbers as a group. -/
lemma closure_nonZeroDivisors_padicInt :
    Subgroup.closure (Set.range ((↑) : ℤ_[p]⁰ → ℚ_[p]ˣ)) = ⊤ := by
  set H := Subgroup.closure (Set.range ((↑) : ℤ_[p]⁰ → ℚ_[p]ˣ))
  rw [eq_top_iff']
  intro x
  obtain ⟨y, z, hz, hyzx⟩ := IsFractionRing.div_surjective (A := ℤ_[p]) x.val
  have hy : y ∈ ℤ_[p]⁰ := by
    simp only [mem_nonZeroDivisors_iff_ne_zero, ne_eq]
    rintro rfl
    simp [eq_comm] at hyzx
  convert div_mem (H := H) (subset_closure <| Set.mem_range_self ⟨y, hy⟩)
    (subset_closure <| Set.mem_range_self ⟨z, hz⟩) using 1
  ext
  simpa using hyzx.symm

end PadicInt

namespace Padic

lemma submodule_one_eq_closedBall :
    (1 : Submodule ℤ_[p] ℚ_[p]) = Metric.closedBall (0 : ℚ_[p]) 1 := by ext x; simp; simp [PadicInt]

end Padic
