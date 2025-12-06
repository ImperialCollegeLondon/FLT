import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.NumberTheory.Padics.PadicNumbers

variable (p : ℕ) [Fact p.Prime] in
instance : MeasurableSpace ℚ_[p] := borel _

variable (p : ℕ) [Fact p.Prime] in
instance : BorelSpace ℚ_[p] := ⟨rfl⟩
