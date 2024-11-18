import Mathlib.Algebra.CharZero.Infinite
import Mathlib.NumberTheory.Padics.PadicIntegers
import FLT.Mathlib.Algebra.Group.Subgroup.Pointwise
import FLT.Mathlib.Algebra.Group.Units.Hom
import FLT.Mathlib.Algebra.GroupWithZero.NonZeroDivisors
import FLT.Mathlib.GroupTheory.Index

/-!
# TODO

* Make `PadicInt.valuation` `ℕ`-valued
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

-- TODO: Replace `valuation`
noncomputable def valuation' (a : ℤ_[p]) : ℕ := a.valuation.toNat

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

/-- `x • sℤ_[p]` has index `‖x‖⁻¹` in `sℤ_[p]`.

Note that `sℤ_[p]` is the form `yℤ_[p]` for some `y : ℚ_[p]`, but this is syntactically less
general. -/
lemma smul_submoduleSpan_relindex_submoduleSpan (x : ℤ_[p]) (s : Set ℚ_[p]) :
    (x • (Submodule.span ℤ_[p] s).toAddSubgroup).relindex (Submodule.span ℤ_[p] s).toAddSubgroup
      = ‖x‖₊⁻¹ :=
  -- https://github.com/ImperialCollegeLondon/FLT/issues/279
  -- Note: You might need to prove `smul_submoduleSpan_finiteRelIndex_submoduleSpan` first
  sorry

/-- `x • sℤ_[p]` has finite index in `sℤ_[p]` if `x ≠ 0`.

Note that `sℤ_[p]` is the form `yℤ_[p]` for some `y : ℚ_[p]`, but this is syntactically less
general. -/
lemma smul_submoduleSpan_finiteRelIndex_submoduleSpan (hx : x ≠ 0) (s : Set ℚ_[p]) :
    (x • (Submodule.span ℤ_[p] s).toAddSubgroup).FiniteRelIndex
      (Submodule.span ℤ_[p] s).toAddSubgroup where
  relIndex_ne_zero := by
    simpa [← Nat.cast_ne_zero (R := ℝ≥0), smul_submoduleSpan_relindex_submoduleSpan]

-- Yaël: Do we really want this as a coercion?
noncomputable instance : Coe ℤ_[p]⁰ ℚ_[p]ˣ where
  coe x := .mk0 x.1 <| map_ne_zero_of_mem_nonZeroDivisors (M := ℤ_[p]) Coe.ringHom coe_injective x.2

/-- Non-zero p-adic integers generate non-zero p-adic numbers as a group. -/
lemma closure_nonZeroDivisors_padicInt :
    Subgroup.closure (Set.range ((↑) : ℤ_[p]⁰ → ℚ_[p]ˣ)) = ⊤ := by
  set H := Subgroup.closure (Set.range ((↑) : ℤ_[p]⁰ → ℚ_[p]ˣ))
  rw [eq_top_iff']
  intro x
  obtain ⟨y, z, hz, hyzx⟩ := IsFractionRing.div_surjective (A := ℤ_[p]) x.val
  have hy : y ∈ ℤ_[p]⁰ := by simp; rintro rfl; simp [eq_comm] at hyzx
  convert div_mem (H := H) (subset_closure <| Set.mem_range_self ⟨y, hy⟩)
    (subset_closure <| Set.mem_range_self ⟨z, hz⟩) using 1
  ext
  simpa using hyzx.symm

end PadicInt

namespace Padic

lemma submoduleSpan_padicInt_one :
    Submodule.span ℤ_[p] (1 : Set ℚ_[p]) = Metric.closedBall (0 : ℚ_[p]) 1 := by
  rw [← Submodule.one_eq_span_one_set]
  ext x
  simp
  simp [PadicInt]

end Padic
