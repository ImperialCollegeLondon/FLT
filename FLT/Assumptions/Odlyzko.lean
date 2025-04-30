import Mathlib.NumberTheory.NumberField.Discriminant.Defs
/-!

# Bounds for root discriminants of number fields

Let `K` be a number field of degree `n` over the rationals.
Minkowski gave a lower bound (depending only on `n`) for the absolute value of
the discriminant of `K`. Using this bound
he was able to deduce that every number field was ramified at at least one prime.

In the proof of FLT being formalized, we need stronger bounds which do not follow
from Minkowski's elementary argument. By analysing the behaviour of the zeros
of the zeta function of `K`, Odlyzko was able to give stronger bounds. These bounds
were improved by Poitou in his 1977 paper "Sur les petits discriminants".
Equation 26 of the paper implies the below bound.

- [Stephen Lack and Paweł Sobociński, Adhesive Categories][adhesive2004]

https://www.numdam.org/item/SDPP_1976-1977__18_1_A6_0/

Equation 26 apparently implies the below.

-/
open Polynomial NumberField Module

axiom Odlyzko_statement (K : Type*) [Field K] [NumberField K] [Normal ℚ K]
  [IsTotallyComplex K]
  (hBound : |(discr K : ℝ)| < 8.25 ^ finrank ℚ K) : finrank ℚ K ≤ 17
