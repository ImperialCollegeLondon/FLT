import Mathlib
import FLT.Mathlib.NumberTheory.NumberField.Basic

universe u

open NumberField

section LocallyCompact

-- see https://github.com/smmercuri/adele-ring_locally-compact
-- for a proof of this

variable (K : Type*) [Field K] [NumberField K]

instance NumberField.AdeleRing.locallyCompactSpace : LocallyCompactSpace (AdeleRing (𝓞 K) K) :=
  sorry -- issue #253

end LocallyCompact

section Discrete

open DedekindDomain

theorem Rat.AdeleRing.zero_discrete : ∃ U : Set (AdeleRing (𝓞 ℚ) ℚ),
    IsOpen U ∧ (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ)) ⁻¹' U = {0} := by
  use {f | ∀ v, f v ∈ (Metric.ball 0 1)} ×ˢ
    {f | ∀ v , f v ∈ IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ v}
  refine ⟨?_, ?_⟩
  · dsimp
    sorry -- issue #252 -- should be easy (product of opens is open, product of integers is surely
          -- known to be open)
  · apply subset_antisymm
    · intro x hx
      rw [Set.mem_preimage] at hx
      simp only [Set.mem_singleton_iff]
      have : (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ)) x =
        (algebraMap ℚ (InfiniteAdeleRing ℚ) x, algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) x)
      · rfl
      rw [this] at hx
      clear this
      rw [Set.mem_prod] at hx
      obtain ⟨h1, h2⟩ := hx
      dsimp only at h1 h2
      simp only [Metric.mem_ball, dist_zero_right, Set.mem_setOf_eq,
        InfiniteAdeleRing.algebraMap_apply, UniformSpace.Completion.norm_coe] at h1
      simp only [Set.mem_setOf_eq] at h2
      specialize h1 Rat.infinitePlace
      change ‖(x : ℂ)‖ < 1 at h1
      simp at h1
      have intx: ∃ (y:ℤ), y = x
      · obtain ⟨z, hz⟩ := IsDedekindDomain.HeightOneSpectrum.mem_integers_of_valuation_le_one
            ℚ x <| fun v ↦ by
          specialize h2 v
          letI : UniformSpace ℚ := v.adicValued.toUniformSpace
          rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers] at h2
          rwa [← IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
        use Rat.ringOfIntegersEquiv z
        rw [← hz]
        apply Rat.ringOfIntegersEquiv_eq_algebraMap
      obtain ⟨y, rfl⟩ := intx
      simp only [abs_lt] at h1
      norm_cast at h1 ⊢
      -- We need the next line because `norm_cast` is for some reason producing a `negSucc 0`.
      -- I haven't been able to isolate this behaviour even in a standalone lemma.
      -- We could also make `omega` more robust against accidental appearances of `negSucc`.
      rw [Int.negSucc_eq] at h1
      omega
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

-- Maybe this discreteness isn't even stated in the best way?
-- I'm ambivalent about how it's stated
open Pointwise in
theorem Rat.AdeleRing.discrete : ∀ q : ℚ, ∃ U : Set (AdeleRing (𝓞 ℚ) ℚ),
    IsOpen U ∧ (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ)) ⁻¹' U = {q} := by
  obtain ⟨V, hV, hV0⟩ := zero_discrete
  intro q
  set ι  := algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ)    with hι
  set qₐ := ι q                           with hqₐ
  set f  := Homeomorph.subLeft qₐ         with hf
  use f ⁻¹' V, f.isOpen_preimage.mpr hV
  have : f ∘ ι = ι ∘ Homeomorph.subLeft q := by ext; simp [hf, hqₐ]
  rw [← Set.preimage_comp, this, Set.preimage_comp, hV0]
  ext
  simp only [Set.mem_preimage, Homeomorph.subLeft_apply, Set.mem_singleton_iff, sub_eq_zero, eq_comm]

variable (K : Type*) [Field K] [NumberField K]

theorem NumberField.AdeleRing.discrete : ∀ k : K, ∃ U : Set (AdeleRing (𝓞 K) K),
    IsOpen U ∧ (algebraMap K (AdeleRing (𝓞 K) K)) ⁻¹' U = {k} := sorry -- issue #257

end Discrete

section Compact

open NumberField

theorem Rat.AdeleRing.cocompact :
    CompactSpace (AdeleRing (𝓞 ℚ) ℚ ⧸ AddMonoidHom.range (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ)).toAddMonoidHom) :=
  sorry -- issue #258

variable (K : Type*) [Field K] [NumberField K]

theorem NumberField.AdeleRing.cocompact :
    CompactSpace (AdeleRing (𝓞 K) K ⧸ AddMonoidHom.range (algebraMap K (AdeleRing (𝓞 K) K)).toAddMonoidHom) :=
  sorry -- issue #259

end Compact

section BaseChange

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

open NumberField

variable [Algebra K (AdeleRing (𝓞 L) L)] [IsScalarTower K L (AdeleRing (𝓞 L) L)]

/-- The canonical map from the adeles of K to the adeles of L -/
noncomputable def NumberField.AdeleRing.baseChange :
    AdeleRing (𝓞 K) K →A[K] AdeleRing (𝓞 L) L :=
  sorry -- product of finite and infinite adele maps

open scoped TensorProduct

noncomputable instance : Algebra (AdeleRing (𝓞 K) K) (L ⊗[K] AdeleRing (𝓞 K) K) :=
  Algebra.TensorProduct.rightAlgebra

instance : TopologicalSpace (L ⊗[K] AdeleRing (𝓞 K) K) :=
  moduleTopology (AdeleRing (𝓞 K) K) (L ⊗[K] AdeleRing (𝓞 K) K)
/-- The canonical `L`-algebra isomorphism from `L ⊗_K K_∞` to `L_∞` induced by the
`K`-algebra base change map `K_∞ → L_∞`. -/
def NumberField.AdeleRing.baseChangeEquiv :
    (L ⊗[K] (AdeleRing (𝓞 K) K)) ≃A[L] AdeleRing (𝓞 L) L :=
  sorry

end BaseChange
