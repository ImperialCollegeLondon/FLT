import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
import Mathlib.NumberTheory.NumberField.Basic

universe u

section PRed
-- Don't try anything in this section because we are missing a definition.

-- see mathlib PR #16485
def NumberField.AdeleRing (K : Type u) [Field K] [NumberField K] : Type u := sorry

open NumberField

variable (K : Type*) [Field K] [NumberField K]

-- All these are already done in mathlib PRs, so can be assumed for now.
-- When they're in mathlib master we can update mathlib and then get these theorems/definitions
-- for free.
instance : CommRing (AdeleRing K) := sorry

instance : TopologicalSpace (AdeleRing K) := sorry

instance : TopologicalRing (AdeleRing K) := sorry

instance : Algebra K (AdeleRing K) := sorry

end PRed

section AdeleRingLocallyCompact
-- This theorem is proved in another project, so we may as well assume it.

-- see https://github.com/smmercuri/adele-ring_locally-compact

variable (K : Type*) [Field K] [NumberField K]

instance NumberField.AdeleRing.locallyCompactSpace : LocallyCompactSpace (AdeleRing K) := sorry

end AdeleRingLocallyCompact

-- these next two theorems can't be worked on yet because we don't have an actual definition
-- of the adele ring. We can work out a strategy when we do.

variable (K : Type*) [Field K] [NumberField K]

-- Maybe this isn't even stated in the best way?
theorem NumberField.AdeleRing.discrete : ∀ k : K, ∃ U : Set (AdeleRing K),
    IsOpen U ∧ (algebraMap K (AdeleRing K)) ⁻¹' U = {k} := sorry

open NumberField

-- ditto for this one
theorem NumberField.AdeleRing.cocompact :
    CompactSpace (AdeleRing K ⧸ AddMonoidHom.range (algebraMap K (AdeleRing K)).toAddMonoidHom) :=
  sorry

-- Do we have this already?

-- Modulo everything above, and possibly also some other things, we can start working on
-- Main Theorem 27.6.14 of John Voight's quaternion algebra book
-- (https://jvoight.github.io/quat-book.pdf), p458 of the book,
-- which is p478 of the pdf.
