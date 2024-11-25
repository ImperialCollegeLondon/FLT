import FLT.NumberField.InfiniteAdeleRing

universe u

section LocallyCompact

-- see https://github.com/smmercuri/adele-ring_locally-compact
-- for a proof of this

variable (K : Type*) [Field K] [NumberField K]

instance NumberField.AdeleRing.locallyCompactSpace : LocallyCompactSpace (AdeleRing K) :=
  sorry

end LocallyCompact

section BaseChange

end BaseChange

-- Maybe this discreteness isn't even stated in the best way?
-- I'm ambivalent about how it's stated

section Discrete

open NumberField

theorem Rat.AdeleRing.zero_discrete : ∃ U : Set (AdeleRing ℚ),
    IsOpen U ∧ (algebraMap ℚ (AdeleRing ℚ)) ⁻¹' U = {0} := sorry

theorem Rat.AdeleRing.discrete : ∀ q : ℚ, ∃ U : Set (AdeleRing ℚ),
    IsOpen U ∧ (algebraMap ℚ (AdeleRing ℚ)) ⁻¹' U = {q} := sorry

variable (K : Type*) [Field K] [NumberField K]

theorem NumberField.AdeleRing.discrete : ∀ k : K, ∃ U : Set (AdeleRing K),
    IsOpen U ∧ (algebraMap K (AdeleRing K)) ⁻¹' U = {k} := sorry

end Discrete

section Compact

open NumberField

theorem Rat.AdeleRing.cocompact :
    CompactSpace (AdeleRing ℚ ⧸ AddMonoidHom.range (algebraMap ℚ (AdeleRing ℚ)).toAddMonoidHom) :=
  sorry

variable (K : Type*) [Field K] [NumberField K]

theorem NumberField.AdeleRing.cocompact :
    CompactSpace (AdeleRing K ⧸ AddMonoidHom.range (algebraMap K (AdeleRing K)).toAddMonoidHom) :=
  sorry

end Compact
