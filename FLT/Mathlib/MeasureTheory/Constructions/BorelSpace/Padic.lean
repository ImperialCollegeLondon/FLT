module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.NumberTheory.Padics.PadicNumbers

@[expose] public section

variable (p : ℕ) [Fact p.Prime]

noncomputable instance : MeasurableSpace ℚ_[p] := borel _

instance : BorelSpace ℚ_[p] := ⟨rfl⟩
