import Mathlib.Data.ENNReal.Inv

namespace ENNReal

protected lemma mul_div_cancel_right {b : ℝ≥0∞} (hb₀ : b ≠ 0) (hb : b ≠ ∞) (a : ℝ≥0∞) :
    a * b / b = a := by rw [ENNReal.mul_div_right_comm, ENNReal.div_mul_cancel hb₀ hb]

end ENNReal
