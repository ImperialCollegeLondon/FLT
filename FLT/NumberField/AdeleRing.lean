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

-- Should surely be in mathlib
abbrev Rat.infinitePlace : InfinitePlace ℚ where
  val := {
    toFun := fun q ↦ |(q : ℝ)|
    map_mul' := fun x y ↦ by
      simp only [cast_mul]
      exact abs_mul (x : ℝ) y
    nonneg' := by
      intro x
      simp only [abs_nonneg]
    eq_zero' := by
      intro x
      simp
    add_le' := by
      intro x y
      simp only [cast_add]
      exact abs_add_le (x : ℝ) y
  }
  property := ⟨Rat.castHom ℂ, by
    ext x
    simp
    ⟩

theorem Rat.AdeleRing.zero_discrete : ∃ U : Set (AdeleRing ℚ),
    IsOpen U ∧ (algebraMap ℚ (AdeleRing ℚ)) ⁻¹' U = {0} := by
  use {f | ∀ v, f v ∈ (Metric.ball 0 1)} ×ˢ
    {f | ∀ v , f v ∈ IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ v}
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
    simp only [Metric.mem_ball, dist_zero_right, Set.mem_setOf_eq, InfiniteAdeleRing.algebraMap_apply, UniformSpace.Completion.norm_coe] at h1
    simp only [Set.mem_setOf_eq] at h2
    specialize h1 Rat.infinitePlace
    simp at h1
    change (|(x:ℝ)|) < 1 at h1
    norm_cast at h1
    have := padicNorm.not_int_of_not_padic_int
    have intx: ∃ (y:ℤ), y = x
    · by_contra h
      push_neg at h
      sorry
    sorry
  · intro x
    simp only [Set.mem_singleton_iff, Set.mem_preimage]
    rintro rfl
    simp only [map_zero]
    change (0, 0) ∈ _
    simp only [Prod.mk_zero_zero, Set.mem_prod, Prod.fst_zero, Prod.snd_zero]
    constructor
    · simp only [Metric.mem_ball, dist_zero_right, Set.mem_setOf_eq]
      intro v
      have : ‖(0:InfiniteAdeleRing ℚ) v‖ = 0
      · simp only [norm_eq_zero]
        rfl
      simp [this, zero_lt_one]
    · simp only [Set.mem_setOf_eq]
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
