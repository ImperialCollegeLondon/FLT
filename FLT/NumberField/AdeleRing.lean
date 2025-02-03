import Mathlib
import FLT.DedekindDomain.FiniteAdeleRing.BaseChange
import FLT.Mathlib.NumberTheory.NumberField.Basic
import FLT.Mathlib.RingTheory.TensorProduct.Pi
import FLT.Mathlib.Topology.Algebra.Group.Quotient
import FLT.Mathlib.Topology.Algebra.ContinuousAlgEquiv
import FLT.NumberField.InfiniteAdeleRing

open scoped TensorProduct

universe u

open NumberField

section LocallyCompact

-- see https://github.com/smmercuri/adele-ring_locally-compact
-- for a proof of this

variable (K : Type*) [Field K] [NumberField K]

instance NumberField.AdeleRing.locallyCompactSpace : LocallyCompactSpace (AdeleRing (𝓞 K) K) :=
  sorry -- issue #253

end LocallyCompact

section BaseChange

-- TODO: Move this stuff
noncomputable def Module.Finite.equivPi (R M : Type*) [Ring R] [StrongRankCondition R]
    [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M] :
    M ≃ₗ[R] Fin (Module.finrank R M) → R :=
  LinearEquiv.ofFinrankEq _ _ <| by rw [Module.finrank_pi, Fintype.card_fin]

noncomputable abbrev TensorProduct.finiteEquivPi (R M N : Type*) [CommRing R] [AddCommMonoid N]
    [AddCommGroup M] [Module R N] [Module R M] [Module.Free R M] [Module.Finite R M]
    [StrongRankCondition R] :
    M ⊗[R] N ≃ₗ[R] Fin (Module.finrank R M) → N :=
  (TensorProduct.comm _ _ _).trans <|
    (TensorProduct.congr (LinearEquiv.refl R N) (Module.Finite.equivPi _ _)).trans
      (TensorProduct.piScalarRight _ _ _ _)

theorem Fintype.sum_pi_single_pi {α : Type*} {β : α → Type*} [DecidableEq α] [Fintype α]
    [(a : α) → AddCommMonoid (β a)] (f : (a : α) → β a) :
    ∑ (a : α), Pi.single a (f a) = f := by
  simp_rw [funext_iff, Fintype.sum_apply]
  exact fun _ => Fintype.sum_pi_single _ _

theorem TensorProduct.finiteEquivPi_symm_apply (R M N : Type*) [Field R] [CommSemiring N]
    [AddCommGroup M] [Algebra R N] [Module R M] [FiniteDimensional R M]
    (x : Fin (Module.finrank R M) → R) :
    (finiteEquivPi R M N).symm (fun i => algebraMap _ _ (x i)) =
      (Module.Finite.equivPi R M).symm x ⊗ₜ[R] 1 := by
  simp [Algebra.TensorProduct.piScalarRight_symm_apply_of_algebraMap, Fintype.sum_pi_single_pi]

namespace NumberField.AdeleRing

variable (K L : Type*) [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]

noncomputable instance : Algebra K (NumberField.AdeleRing (𝓞 L) L) :=
  Algebra.compHom _ (algebraMap K L)

local instance : TopologicalSpace K :=
    TopologicalSpace.induced (algebraMap K (AdeleRing (𝓞 K) K)) inferInstance

def IsModuleTopology.continuousLinearEquiv {A B R : Type*} [TopologicalSpace A]
    [TopologicalSpace B] [TopologicalSpace R] [Semiring R] [AddCommMonoid A] [AddCommMonoid B]
    [Module R A] [Module R B] [IsModuleTopology R A] [IsModuleTopology R B]
    (e : A ≃ₗ[R] B) :
    A ≃L[R] B where
  __ := e
  continuous_toFun :=
    letI := IsModuleTopology.toContinuousAdd
    IsModuleTopology.continuous_of_linearMap e.toLinearMap
  continuous_invFun :=
    letI := IsModuleTopology.toContinuousAdd
    IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap

@[simp]
theorem IsModuleTopology.continuousLinearEquiv_symm_apply {A B R : Type*} [TopologicalSpace A]
    [TopologicalSpace B] [TopologicalSpace R] [Semiring R] [AddCommMonoid A] [AddCommMonoid B]
    [Module R A] [Module R B] [IsModuleTopology R A] [IsModuleTopology R B]
    (e : A ≃ₗ[R] B) (b : B) :
    (continuousLinearEquiv e).symm b = e.symm b := rfl

/--
The motivation for this is that we eventually want to obtain a continuous `K`-linear isomorphism
L ⊗[K] 𝔸_K ≃ Π 𝔸_K. Without continuity, this is given above as
`TensorProduct.finiteEquivPi`. If both sides have the `K` module topology, then this
also gives a continuous isomorphism via `IsModuleTopology.continuousLinearEquiv` above.

We can easily show that the RHS has the `𝔸_K` module topology using
`IsModuleTopology.instPi` but it is not immediately obvious how to show, for example,
that `IsModuleTopology K (AdeleRing K)`. I think this is true because `K` is dense
inside `𝔸_K` and so the smul of `K` on `𝔸_K` extends to the smul of `𝔸_K` on `𝔸_K`.
-/
theorem IsModuleTopology.restrict {R S : Type*} (A : Type*) [τA : TopologicalSpace A]
    [Semiring A] [TopologicalSemiring A] [Semiring S] [TopologicalSpace S]
    [Semiring R] [TopologicalSpace R] [Module R A] [Module R S] [Module S A]
    [IsScalarTower R S A] [ContinuousSMul R S]
    -- `h_extend` is definitely not how we want to express the necessary condition here
    -- If R is a dense subset of S, does this guarantee `h_extend`? I'm thinking about something
    -- analogous to UniformSpace.Completion.continuous_mul but for smul and a dense inducing
    -- map between scalars, e.g., IsDenseInducing.extend_Z_bilin
    (h_extend : ∀ t, @ContinuousSMul R A _ _ t → @ContinuousSMul S A _ _ t)
    [ContinuousSMul R A] [IsModuleTopology S A] :
    IsModuleTopology R A where
  eq_moduleTopology' := by
    rw [eq_moduleTopology S A]
    simp_rw [moduleTopology]
    rw [← isGLB_iff_sInf_eq, isGLB_iff_le_iff]
    intro t
    simp
    constructor
    · intro h
      intro t' ht'
      letI := ht'.1
      apply h t'
      · exact IsScalarTower.continuousSMul S
      · exact ht'.2
    · intro h t' hc₁ hc₂
      exact h ⟨h_extend _ hc₁, hc₂⟩

theorem continuousSMul_extend (τ : TopologicalSpace (AdeleRing (𝓞 K) K))
    (h : @ContinuousSMul K (AdeleRing (𝓞 K) K) _ _ τ) :
    @ContinuousSMul (AdeleRing (𝓞 K) K) (AdeleRing (𝓞 K) K) _ (instTopologicalSpace _ _) τ := by
  sorry

instance : ContinuousSMul K (AdeleRing (𝓞 K) K) :=
  continuousSMul_of_algebraMap _ _ continuous_induced_dom

instance : IsModuleTopology K (AdeleRing (𝓞 K) K) :=
  IsModuleTopology.restrict (S := AdeleRing (𝓞 K) K) (AdeleRing (𝓞 K) K) (continuousSMul_extend K)

instance : IsModuleTopology K (Fin (Module.finrank K L) → AdeleRing (𝓞 K) K) :=
  IsModuleTopology.instPi

instance : TopologicalSpace (L ⊗[K] AdeleRing (𝓞 K) K) :=
  moduleTopology K _

instance : IsModuleTopology K (L ⊗[K] AdeleRing (𝓞 K) K) :=
  ⟨rfl⟩

def baseChange : L ⊗[K] AdeleRing (𝓞 K) K ≃A[L] AdeleRing (𝓞 L) L := sorry

variable {L}

theorem baseChange_tsum_apply_right (l : L) :
  baseChange K L (l ⊗ₜ[K] 1) = algebraMap L (AdeleRing (𝓞 L) L) l := sorry

variable (L)

instance : IsScalarTower K L (AdeleRing (𝓞 L) L) :=
  IsScalarTower.of_algebraMap_eq' rfl

noncomputable abbrev tensorProductContinuousLinearEquivPi :
    L ⊗[K] AdeleRing (𝓞 K) K ≃L[K] (Fin (Module.finrank K L) → AdeleRing (𝓞 K) K) :=
  IsModuleTopology.continuousLinearEquiv (TensorProduct.finiteEquivPi _ _ _)

noncomputable abbrev baseChangePi :
    (Fin (Module.finrank K L) → AdeleRing (𝓞 K) K) ≃L[K] AdeleRing (𝓞 L) L :=
  (tensorProductContinuousLinearEquivPi K L).symm.trans
    ((baseChange K L).restrictScalars K).toContinuousLinearEquiv

variable {K L}

theorem baseChangePi_apply_of_algebraMap
    {x : Fin (Module.finrank K L) → AdeleRing (𝓞 K) K}
    {y : Fin (Module.finrank K L) → K}
    (h : ∀ i, algebraMap K (AdeleRing (𝓞 K) K) (y i) = x i) :
    baseChangePi K L x = algebraMap L _ (Module.Finite.equivPi _ _ |>.symm y) := by
  rw [← funext h, ContinuousLinearEquiv.trans_apply,
    IsModuleTopology.continuousLinearEquiv_symm_apply, ContinuousAlgEquiv.coe_restrictScalars_apply,
    LinearEquiv.restrictScalars_apply, ContinuousLinearEquiv.coe_toLinearEquiv,
    TensorProduct.finiteEquivPi_symm_apply, ContinuousAlgEquiv.toContinuousLinearEquiv_apply,
    baseChange_tsum_apply_right]

theorem baseChangePi_mem_principalSubgroup
    {x : Fin (Module.finrank K L) → AdeleRing (𝓞 K) K}
    (h : x ∈ AddSubgroup.pi Set.univ (fun _ => principalSubgroup (𝓞 K) K)) :
    baseChangePi K L x ∈ principalSubgroup (𝓞 L) L := by
  simp only [AddSubgroup.mem_pi, Set.mem_univ, forall_const] at h
  choose y hy using h
  exact baseChangePi_apply_of_algebraMap hy ▸ ⟨Module.Finite.equivPi _ _ |>.symm y, rfl⟩

variable (K L)

theorem baseChangePi_map_principalSubgroup :
    (AddSubgroup.pi Set.univ (fun (_ : Fin (Module.finrank K L)) => principalSubgroup (𝓞 K) K)).map
      (baseChangePi K L).toAddMonoidHom = principalSubgroup (𝓞 L) L := by
  ext x
  simp only [AddSubgroup.mem_map, LinearMap.toAddMonoidHom_coe, LinearEquiv.coe_coe,
    ContinuousLinearEquiv.coe_toLinearEquiv]
  refine ⟨fun ⟨a, h, ha⟩ => ha ▸ baseChangePi_mem_principalSubgroup h, ?_⟩
  rintro ⟨a, rfl⟩
  use fun i => algebraMap K (AdeleRing (𝓞 K) K) (Module.Finite.equivPi _ _ a i)
  refine ⟨fun i _ => ⟨Module.Finite.equivPi _ _ a i, rfl⟩, ?_⟩
  rw [baseChangePi_apply_of_algebraMap (fun i => rfl), LinearEquiv.symm_apply_apply]

noncomputable def baseChangeQuotientPi :
    (Fin (Module.finrank K L) → AdeleRing (𝓞 K) K ⧸ principalSubgroup (𝓞 K) K) ≃ₜ+
      AdeleRing (𝓞 L) L ⧸ principalSubgroup (𝓞 L) L :=
  (ContinuousAddEquiv.quotientPi _).symm.trans <|
    QuotientAddGroup.continuousAddEquiv _ _ _ _ (baseChangePi K L).toContinuousAddEquiv
      (baseChangePi_map_principalSubgroup K L)

end NumberField.AdeleRing

end BaseChange

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
    CompactSpace (AdeleRing (𝓞 ℚ) ℚ ⧸ AdeleRing.principalSubgroup (𝓞 ℚ) ℚ) :=
  sorry -- issue #258

variable (K L : Type*) [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]

theorem NumberField.AdeleRing.cocompact :
    CompactSpace (AdeleRing (𝓞 K) K ⧸ AdeleRing.principalSubgroup (𝓞 K) K) :=
  letI := Rat.AdeleRing.cocompact
  (baseChangeQuotientPi ℚ K).compactSpace

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
