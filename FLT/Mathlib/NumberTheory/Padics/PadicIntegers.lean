import Mathlib.Algebra.CharZero.Infinite
import Mathlib.NumberTheory.Padics.PadicIntegers
import FLT.Mathlib.GroupTheory.Index

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

/-- For a `ℤ_[p]`-submodule `s` of `ℚ_[p]`, `x • s` has index `‖x‖⁻¹` in `s`.

Note that `s` is of the form `yℤ_[p]` for some `y : ℚ_[p]`, but this is syntactically less
general. -/
lemma smul_submodule_relindex (x : ℤ_[p]) (s : Submodule ℤ_[p] ℚ_[p]) :
    (x • s.toAddSubgroup).relindex s.toAddSubgroup = ‖x‖₊⁻¹ :=
  -- https://github.com/ImperialCollegeLondon/FLT/issues/279
  -- Note: You might need to prove `smul_submoduleSpan_finiteRelIndex_submoduleSpan` first
  sorry

/-- For a `ℤ_[p]`-submodule `s` of `ℚ_[p]`, `x • s` has finite index if `x ≠ 0`.

Note that `s` is the form `yℤ_[p]` for some `y : ℚ_[p]`, but this is syntactically less
general. -/
lemma smul_submodule_finiteRelIndex (hx : x ≠ 0) (s : Submodule ℤ_[p] ℚ_[p]) :
    (x • s.toAddSubgroup).FiniteRelIndex s.toAddSubgroup where
  relIndex_ne_zero := by simpa [← Nat.cast_ne_zero (R := ℝ≥0), smul_submodule_relindex]

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

lemma submodule_one_eq_closedBall :
    (1 : Submodule ℤ_[p] ℚ_[p]) = Metric.closedBall (0 : ℚ_[p]) 1 := by ext x; simp; simp [PadicInt]

end Padic
