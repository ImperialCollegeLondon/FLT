import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.NumberTheory.Padics.PadicNumbers

variable (p : ℕ) [Fact p.Prime]

instance : MeasurableSpace ℚ_[p] := borel _

instance : BorelSpace ℚ_[p] := ⟨rfl⟩
