import Mathlib.NumberTheory.NumberField.Discriminant.Defs
import Mathlib.NumberTheory.NumberField.Embeddings

/-!

# Bounds for root discriminants of number fields

Let `K` be a number field of degree `n` over the rationals. Minkowski gave a lower bound
(depending only on `n`) for the absolute value of the discriminant of `K`. Using this bound
he was able to deduce that every number field other than the rationals
was ramified at at least one prime.

In the proof of FLT being formalized, we need stronger bounds which do not follow
from Minkowski's elementary argument. By analysing the behaviour of the zeros
of the zeta function of `K`, Odlyzko was able to give stronger bounds. These bounds
were improved by Poitou in his 1977 paper "Sur les petits discriminants".
Equation 26 of the paper implies the below bound, and an explicit reference for
it is the table on p17 of the paper (in fact 8.25 can be beefed up to 9.3, but
we do not need this).

## Why do we need this?

The original proof by Wiles and Taylor-Wiles of FLT contains a crucial step
where they "switch to the prime 3", and apply the Langlands--Tunnell theorem
to deduce that the 3-torsion in an elliptic curve over ℚ, if irreducible,
is modular. In the argument we are formalizing, we switch to 3 at a different
point. The advantage of this is that it avoids the Langlands-Tunnell theorem
(which needs non-Galois cubic cyclic base change); the analysis we need is
easier. We switch to 3 only after we have constructed a compatible family
of Galois representations with conductor 2 from the Frey curve (using hard
modularity lifting theorems), and we use this bound below to demonstrate
that such a family cannot exist. The argument involves a careful analysis of
the 3-torsion in the 3-adic specialization of the family; it is analogous to
Fontaine's proof that there is no nontrivial abelian variety over ℤ.

## References

- [Georges Poitou, Sur les petits discriminants][poitou_odlyzko_bounds]

Currently available at https://www.numdam.org/item/SDPP_1976-1977__18_1_A6_0/

The github tracking issue for this assumption is #458 on the FLT github repository.

-/
open Polynomial NumberField Module

/-- An "Odlyzko bound" for the root discriminant of a totally complex number field
of degree 18 and above. -/
axiom Odlyzko_statement (K : Type*) [Field K] [NumberField K] [IsTotallyComplex K]
  (hdim : finrank ℚ K ≥ 18) : |(discr K : ℝ)| ≥ 8.25 ^ finrank ℚ K
