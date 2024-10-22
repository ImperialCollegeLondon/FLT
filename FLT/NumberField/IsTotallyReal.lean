import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.Data.Complex.Basic

class NumberField.IsTotallyReal (F : Type*) [Field F] [NumberField F] : Prop where
  isTotallyReal : ∀ τ : F →+* ℂ, ∀ f : F, ∃ r : ℝ, τ f = r
