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

open NumberField DedekindDomain

def V: Set (InfiniteAdeleRing ℚ) := {f | ∀ v, f v ∈ (Metric.ball 0 1)}
def W: Set (FiniteAdeleRing (𝓞 ℚ) ℚ) :=
  {f | ∀ v , f v ∈ IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ v}
def U: Set (NumberField.AdeleRing ℚ) := V ×ˢ W

theorem Rat.AdeleRing.zero_discrete : ∃ U : Set (AdeleRing ℚ),
    IsOpen U ∧ (algebraMap ℚ (AdeleRing ℚ)) ⁻¹' U = {0} := by
  use U
  unfold U
  refine ⟨sorry, ?_⟩
  apply subset_antisymm
  · intro x hx
    rw [Set.mem_preimage] at hx
    simp only [Set.mem_singleton_iff]
    have : (algebraMap ℚ (AdeleRing ℚ)) x = (algebraMap ℚ (InfiniteAdeleRing ℚ) x, algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) x)
    · rfl
    rw [this] at hx
    clear this
    rw [Set.mem_prod] at hx
    obtain ⟨h1, h2⟩ := hx
    dsimp only at h1 h2
    unfold V at h1
    simp only [Metric.mem_ball, dist_zero_right, Set.mem_setOf_eq,
      InfiniteAdeleRing.algebraMap_apply, UniformSpace.Completion.norm_coe] at h1
    sorry
  · intro x
    simp only [Set.mem_singleton_iff, Set.mem_preimage]
    rintro rfl
    simp only [map_zero]
    suffices (0,0) ∈ V ×ˢ W by simpa
    simp only [Prod.mk_zero_zero, Set.mem_prod, Prod.fst_zero, Prod.snd_zero]
    constructor
    · sorry
    · unfold W
      simp only [Set.mem_setOf_eq]
      intro v
      apply zero_mem


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
