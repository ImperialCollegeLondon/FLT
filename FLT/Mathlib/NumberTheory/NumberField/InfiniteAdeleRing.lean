import Mathlib.NumberTheory.NumberField.AdeleRing -- should be .InfiniteAdeleRing
import Mathlib.Topology.Algebra.Algebra.Equiv
import FLT.Mathlib.NumberTheory.NumberField.InfinitePlace.Completion

-- TODO upstream
variable (K : Type*) [Field K] [NumberField K]

open NumberField InfinitePlace

instance : T2Space (InfiniteAdeleRing K) :=
  inferInstanceAs <| T2Space (Π _, _)

instance : SecondCountableTopology (InfiniteAdeleRing K) :=
  inferInstanceAs <| SecondCountableTopology (Π _, _)

/-- The ℝ algebra structure on InfiniteAdeleRing K. -/
noncomputable instance : Algebra ℝ (InfiniteAdeleRing K) :=
  (InfiniteAdeleRing.ringEquiv_mixedSpace K|>.symm.toRingHom.comp (algebraMap ℝ _)).toAlgebra

/-- If `K` is a number field, this is the ℝ-linear iso between ∏_v|∞ K_v and ℝ^r × ℂ^s,
with the usual notation. -/
noncomputable def NumberField.InfiniteAdeleRing.algEquiv_mixedSpace :
    InfiniteAdeleRing K ≃ₗ[ℝ] (mixedEmbedding.mixedSpace K) := LinearEquiv.symm {
  __ := (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K).symm
  map_smul' m x := by
    rw [Algebra.smul_def]
    exact map_mul (InfiniteAdeleRing.ringEquiv_mixedSpace K).symm _ _
    }

instance : Module.Finite ℝ (InfiniteAdeleRing K) :=
  Module.Finite.equiv (NumberField.InfiniteAdeleRing.algEquiv_mixedSpace K).symm

-- should be elsewhere
instance : IsModuleTopology ℝ ℂ := .iso Complex.equivRealProdCLM.symm

/-- If `K` is a number field, this is the continuous ℝ-linear iso between ∏_v|∞ K_v and ℝ^r × ℂ^s,
with the usual notation. -/
noncomputable def NumberField.InfiniteAdeleRing.continuousAlgEquiv_mixedSpace :
    InfiniteAdeleRing K ≃L[ℝ] (mixedEmbedding.mixedSpace K)  where
  __ := NumberField.InfiniteAdeleRing.algEquiv_mixedSpace K
  continuous_toFun := by
    apply Continuous.prodMk
    · apply continuous_pi
      rintro ⟨v, hv⟩
      change Continuous fun (a : InfiniteAdeleRing K) ↦
        (Completion.isometryEquivRealOfIsReal hv) (a v)
      fun_prop
    · apply continuous_pi
      rintro ⟨v, hv⟩
      change Continuous fun (a : InfiniteAdeleRing K) ↦
        (Completion.isometryEquivComplexOfIsComplex hv) (a v)
      fun_prop
  continuous_invFun := by
    apply continuous_pi
    intro v
    classical
    change Continuous fun (a : mixedEmbedding.mixedSpace K) ↦ if h : v.IsReal then _ else _
    split_ifs with h
    · let f : v.Completion ≃+* ℝ := Completion.ringEquivRealOfIsReal h
      change Continuous fun (a : mixedEmbedding.mixedSpace K) ↦
        (Completion.isometryEquivRealOfIsReal h).symm (a.1 ⟨v, h⟩)
      fun_prop
    · rw [NumberField.InfinitePlace.not_isReal_iff_isComplex] at h
      change Continuous fun (a : mixedEmbedding.mixedSpace K) ↦
        (Completion.isometryEquivComplexOfIsComplex h).symm (a.2 ⟨v, h⟩)
      fun_prop

instance : IsModuleTopology ℝ (InfiniteAdeleRing K) :=
  .iso (NumberField.InfiniteAdeleRing.continuousAlgEquiv_mixedSpace K).symm

/-- The continuous `ℤ`-algebra isomorphism between `Rat.infinitePlace.Completion` and `ℝ`.
(We use continuous `ℤ`-algebra equivalences in place of continuous ring equivalences
since we don't have the latter.) -/
noncomputable def Rat.infinitePlace_completion_continuousAlgEquiv :
    Rat.infinitePlace.Completion ≃A[ℤ] ℝ :=
  {
    __ := (Completion.isometryEquivRealOfIsReal isReal_infinitePlace).toHomeomorph
    __ := Completion.ringEquivRealOfIsReal isReal_infinitePlace
    commutes' := by simp [Completion.isometryEquivRealOfIsReal]
  }

lemma Rat.infinitePlace_completion_continuousAlgEquiv_apply_algebraMap (x : ℚ) :
    infinitePlace_completion_continuousAlgEquiv
      (algebraMap ℚ infinitePlace.Completion x) = (x : ℝ) := by simp
