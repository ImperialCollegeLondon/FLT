import Mathlib.NumberTheory.NumberField.Discriminant.Defs
/-!

# Bounds for root discriminants of number fields

https://www.numdam.org/item/SDPP_1976-1977__18_1_A6_0/

Equation 26 apparently implies the below.

-/
open Polynomial NumberField Module

axiom Odlyzko_statement (K : Type*) [Field K] [NumberField K] [Normal ℚ K]
  (hIm : ¬ Irreducible (X ^ 2 - C (3 : K)))
  (hBound : |(discr K : ℝ)| < 8.25 ^ finrank ℚ K) : finrank ℚ K ≤ 17
