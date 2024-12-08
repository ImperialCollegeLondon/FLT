import Mathlib.NumberTheory.Padics.PadicIntegers
import FLT.Mathlib.Algebra.Group.Units.Hom

/-!
# TODO

* Make `PadicInt.valuation` `ℕ`-valued
* Rename `Coe.ringHom` to `coeRingHom`
-/

-- This is cool notation. Should mathlib have it?
scoped[GroupTheory] notation "[" G ":" H "]" => @AddSubgroup.index G _ H

open Function
open scoped GroupTheory
open scoped Pointwise

namespace PadicInt
variable {p : ℕ} [Fact p.Prime]

@[simp, norm_cast] lemma coe_coeRingHom : ⇑(Coe.ringHom (p := p)) = (↑) := rfl

lemma coe_injective : Injective ((↑) : ℤ_[p] → ℚ_[p]) := Subtype.val_injective

@[simp] lemma coe_inj {x y : ℤ_[p]} : (x : ℚ_[p]) = (y : ℚ_[p]) ↔ x = y := coe_injective.eq_iff

noncomputable instance : Coe ℤ_[p]ˣ ℚ_[p]ˣ where coe := Units.map Coe.ringHom.toMonoidHom

--TODO(javierlcontreras): Waiting for a new mathlib refactor. Z_p valuation should return nat, not int
--lemma unit_ppown (a : ℤ_[p]) : ∃ u : ℤ_[p]ˣ, u * (p ^ a.valuation) = a := by
--  sorry

lemma index_ideal (a : ℤ_[p]) : (a • ⊤ : Ideal ℤ_[p]).toAddSubgroup.index = ‖a‖⁻¹ := by
  sorry

lemma index_ideal_unit (u : ℤ_[p]ˣ) :
    (u • ⊤ : Ideal ℤ_[p]).toAddSubgroup.index = ‖(u : ℤ_[p])‖⁻¹ := by
  simp
  sorry

lemma index_ideal_ppown (n : ℕ) :
    (p ^ n • ⊤ : Ideal ℤ_[p]).toAddSubgroup.index = ‖(p ^ n : ℤ_[p])‖⁻¹  := by
  simp
  rw [AddSubgroup.index_eq_card]
  sorry

-- (Yaël): Do we really want this as a coercion?
noncomputable instance : Coe (nonZeroDivisors ℤ_[p]) ℚ_[p]ˣ where
  coe x := .mk0 x.1 (map_ne_zero_of_mem_nonZeroDivisors (M := ℤ_[p])
    PadicInt.Coe.ringHom PadicInt.coe_injective x.2)

lemma closure_nonZeroDivisorsZp_eq_unitsQp :
    Subgroup.closure (Set.range ((↑) : (nonZeroDivisors ℤ_[p]) → ℚ_[p]ˣ)) = ⊤ :=
  sorry

end PadicInt
