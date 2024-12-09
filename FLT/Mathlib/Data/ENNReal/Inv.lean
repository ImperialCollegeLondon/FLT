import Mathlib.Data.ENNReal.Inv

namespace ENNReal
variable {a b : ℝ≥0∞}

protected lemma inv_mul_cancel_left (ha₀ : a = 0 → b = 0) (ha : a = ∞ → b = 0) :
    a⁻¹ * (a * b) = b := by
  obtain rfl | ha₀ := eq_or_ne a 0
  · simp_all
  obtain rfl | ha := eq_or_ne a ⊤
  · simp_all
  · simp [← mul_assoc, ENNReal.inv_mul_cancel, *]

protected lemma mul_inv_cancel_left (ha₀ : a = 0 → b = 0) (ha : a = ∞ → b = 0) :
    a * (a⁻¹ * b) = b := by
  obtain rfl | ha₀ := eq_or_ne a 0
  · simp_all
  obtain rfl | ha := eq_or_ne a ⊤
  · simp_all
  · simp [← mul_assoc, ENNReal.mul_inv_cancel, *]

protected lemma mul_inv_cancel_right (hb₀ : b = 0 → a = 0) (hb : b = ∞ → a = 0) :
    a * b * b⁻¹ = a := by
  obtain rfl | hb₀ := eq_or_ne b 0
  · simp_all
  obtain rfl | hb := eq_or_ne b ⊤
  · simp_all
  · simp [mul_assoc, ENNReal.mul_inv_cancel, *]

protected lemma inv_mul_cancel_right (hb₀ : b = 0 → a = 0) (hb : b = ∞ → a = 0) :
    a * b⁻¹ * b = a := by
  obtain rfl | hb₀ := eq_or_ne b 0
  · simp_all
  obtain rfl | hb := eq_or_ne b ⊤
  · simp_all
  · simp [mul_assoc, ENNReal.inv_mul_cancel, *]

protected lemma mul_div_cancel_right (hb₀ : b = 0 → a = 0) (hb : b = ∞ → a = 0) :
    a * b / b = a := ENNReal.mul_inv_cancel_right hb₀ hb

end ENNReal
