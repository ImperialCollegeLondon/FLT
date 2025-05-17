import FLT.HaarMeasure.DistribHaarChar.Basic
/-!

# Some things we need about distribHaarChar

Two slightly deeper results about distribHaarChar.

-/
namespace MeasureTheory.Measure

open scoped NNReal

variable (R : Type*) [TopologicalSpace R] [LocallyCompactSpace R]
  [CommRing R] [IsTopologicalRing R]
  [MeasurableSpace R] [BorelSpace R]
/-
See the fascinating discussion here

https://leanprover.zulipchat.com/#narrow/channel/217875-Is-there-code-for-X.3F/topic/.22Haar.20measure.20is.20continuous.22/near/487299979

for how to prove this (tl;dr: interpret distribHaarChar as the factor by which the integral
of continuous functions with compact support is scaled)
-/
theorem distribHaarChar_continuous : Continuous (distribHaarChar R : Rˣ →* ℝ≥0) := by
  sorry

variable {S : Type*} [TopologicalSpace S] [LocallyCompactSpace S]
  [CommRing S] [IsTopologicalRing S]
  [MeasurableSpace S] [BorelSpace S]

/-
This theorem below is true even if neither R or S is second countable,
but without these assumptions it is difficult to *state* in Lean,
because typeclass inference gives `R × S` the product topology and
the product sigma algebra, but unfortunately the product of two
Borel sigma algebras is not the Borel sigma algebra without the
countability assumption, meaning that one has to fight the typeclass
system to talk about Haar measure on the product. See
https://leanprover.zulipchat.com/#narrow/channel/116395-maths/topic/Product.20of.20Borel.20spaces/near/487237491

Under the assumption `[SecondCountableTopologyEither R S]` we have
`Prod.borelSpace : BorelSpace (R × S)` and so we don't need to fight
the typeclass system to state the result.
-/
theorem distribHaarChar_prod_apply [SecondCountableTopologyEither R S] (r : Rˣ) (s : Sˣ) :
    distribHaarChar (R × S) (MulEquiv.prodUnits.symm (r, s)) =
      (distribHaarChar R r) * distribHaarChar S s := by
  sorry
