import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.Data.Complex.Basic

namespace NumberField

-- #20542
class IsTotallyReal (F : Type*) [Field F] [NumberField F] : Prop where
  isTotallyReal : ∀ τ : F →+* ℂ, ∀ f : F, ∃ r : ℝ, τ f = r

instance : IsTotallyReal ℚ where
  isTotallyReal τ q := ⟨q, by simp⟩
