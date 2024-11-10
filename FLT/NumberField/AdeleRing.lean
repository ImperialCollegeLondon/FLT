import Mathlib.NumberTheory.NumberField.AdeleRing

universe u

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
