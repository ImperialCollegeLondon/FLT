/-
Standalone reproducer for the `=?=` printed after the `****` marker in
`slow_typeclass.txt`, coming from the `#synth AddCommMonoid Πʳ …` at
`FLT/DedekindDomain/FiniteAdeleRing/BaseChange.lean:403`.

The two huge `pp.all` terms separated by `=?=` were both
`@Submodule.setLike (Subtype …) ⟨CommSemiring instance⟩ (…)`. They differed
only in *which path through the typeclass DAG* produced the
`CommSemiring (v.adicCompletionIntegers K)` instance:

  LHS:  ValuationSubring.instSubringClass
        → SubringClass.toSubsemiringClass
        → SubsemiringClass.toCommSemiring

  RHS:  ValuationSubring.instCommRingSubtypeMem   (bespoke `CommRing A`)
        → CommRing.toCommSemiring

Both routes yield definitionally equal `CommSemiring` instances. The cost of
the synth was Lean unfolding both paths at `default` transparency to discover
that — `with_reducible_and_instances rfl` closes it instantly.
-/

import Mathlib.RingTheory.DedekindDomain.AdicValuation

namespace FLTTest2

open IsDedekindDomain

variable (A K : Type*) [CommRing A] [IsDedekindDomain A] [Field K] [Algebra A K]
    [IsFractionRing A K]

example (v : HeightOneSpectrum A) :
    (SubsemiringClass.toCommSemiring (s := v.adicCompletionIntegers K) :
      CommSemiring (v.adicCompletionIntegers K))
    =
    (CommRing.toCommSemiring :
      CommSemiring (v.adicCompletionIntegers K)) := rfl

example (v : HeightOneSpectrum A) :
    (SubsemiringClass.toCommSemiring (s := v.adicCompletionIntegers K) :
      CommSemiring (v.adicCompletionIntegers K))
    =
    (CommRing.toCommSemiring :
      CommSemiring (v.adicCompletionIntegers K)) := by
  with_reducible_and_instances rfl

end FLTTest2
