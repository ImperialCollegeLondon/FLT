import Mathlib
import FLT.Mathlib.RingTheory.TensorProduct.Pi
import FLT.Mathlib.Topology.Algebra.Group.Quotient
import FLT.Mathlib.Topology.Algebra.ContinuousAlgEquiv

open scoped TensorProduct

universe u

section LocallyCompact

-- see https://github.com/smmercuri/adele-ring_locally-compact
-- for a proof of this

variable (K : Type*) [Field K] [NumberField K]

instance NumberField.AdeleRing.locallyCompactSpace : LocallyCompactSpace (AdeleRing K) :=
  sorry -- issue #253

end LocallyCompact

section BaseChange

namespace NumberField.AdeleRing

variable (K L : Type*) [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]

noncomputable instance : Algebra K (NumberField.AdeleRing L) :=
  RingHom.toAlgebra <| (algebraMap L (NumberField.AdeleRing L)).comp <| algebraMap K L

noncomputable abbrev tensorProductLinearEquivPi : AdeleRing K ⊗[K] L ≃ₗ[K]
    (Fin (Module.finrank K L) → AdeleRing K) :=
  LinearEquiv.trans (TensorProduct.congr (LinearEquiv.refl K (AdeleRing K))
      (Basis.equivFun (Module.finBasis K L)))
    (TensorProduct.piScalarRight _ _ _ _)

variable {L}

theorem tensorProductLinearEquivPi_tsum_apply (l : L) :
    tensorProductLinearEquivPi K L (1 ⊗ₜ[K] l) =
      fun i => algebraMap _ _ (Module.finBasis K L |>.equivFun l i) := by
  simp [tensorProductLinearEquivPi, Algebra.algebraMap_eq_smul_one]

variable {K}

theorem tensorProductLinearEquivPi_symm_apply_of_algebraMap
    (x : Fin (Module.finrank K L) → K) :
    (tensorProductLinearEquivPi K L).symm (fun i => algebraMap _ _ (x i)) =
      1 ⊗ₜ[K] ((Module.finBasis K L).equivFun.symm x) := by
  simp only [LinearEquiv.trans_symm, LinearEquiv.trans_apply,
    Algebra.TensorProduct.piScalarRight_symm_apply_of_algebraMap, TensorProduct.congr_symm_tmul,
    LinearEquiv.refl_symm, LinearEquiv.refl_apply, map_sum, Basis.equivFun_symm_apply]
  rw [Finset.sum_comm]
  simp only [← Finset.sum_smul, Fintype.sum_pi_single]

/-
smmercuri: A possible alternative using `moduleTopology` is
```
instance :
    TopologicalSpace (NumberField.AdeleRing K ⊗[K] L) :=
  letI := TopologicalSpace.induced (algebraMap K (AdeleRing K)) inferInstance
  moduleTopology K _
```
However it is not clear to me how the inverse function is of `tensorProductLinearEquivPi`
is continuous in that case. Additionally,
https://math.mit.edu/classes/18.785/2017fa/LectureNotes25.pdf (just above Prop 25.10)
for an informal source where the tensor product is given the product topology. Maybe they
coincide!
-/
instance : TopologicalSpace (NumberField.AdeleRing K ⊗[K] L) :=
  TopologicalSpace.induced (NumberField.AdeleRing.tensorProductLinearEquivPi K L) inferInstance

variable (K L)

noncomputable def tensorProductContinuousLinearEquivPi :
    AdeleRing K ⊗[K] L ≃L[K] (Fin (Module.finrank K L) → AdeleRing K) where
  toLinearEquiv := tensorProductLinearEquivPi K L
  continuous_toFun := continuous_induced_dom
  continuous_invFun := by
    convert (tensorProductLinearEquivPi K L).toEquiv.coinduced_symm ▸ continuous_coinduced_rng

variable {K L}

theorem tensorProductContinuousLinearEquivPi_symm_apply_of_algebraMap
    (x : Fin (Module.finrank K L) → K) :
    (tensorProductContinuousLinearEquivPi K L).symm (fun i => algebraMap _ _ (x i)) =
      1 ⊗ₜ[K] ((Module.finBasis K L).equivFun.symm x) := by
  exact tensorProductLinearEquivPi_symm_apply_of_algebraMap _

variable (K L)

/-
smmercuri : The tensor product here is in a different order to the one
appearing in the finite adele ring base change, where `L ⊗[K] FiniteAdeleRing A K`
is used. Is there a preference between these orderings? One benefit
to using `AdeleRing K ⊗[K] L` is that it automatically gets
a `K` algebra instance via the instance `Algebra.TensorProduct.leftAlgebra`
(while `rightAlgebra` is a def), but maybe there are other reasons to
prefer the `rightAlgebra` set up.
-/
def baseChange : (AdeleRing K ⊗[K] L) ≃A[K] AdeleRing L := sorry

variable {L}

theorem baseChange_tsum_apply_right (l : L) :
  baseChange K L (1 ⊗ₜ[K] l) = algebraMap L (AdeleRing L) l := sorry

variable (L)

noncomputable def baseChangePi :
    (Fin (Module.finrank K L) → AdeleRing K) ≃L[K] AdeleRing L :=
  (tensorProductContinuousLinearEquivPi K L).symm.trans (baseChange K L).toContinuousLinearEquiv

variable {K L}

theorem baseChangePi_apply (x : Fin (Module.finrank K L) → AdeleRing K) :
    baseChangePi K L x = baseChange K L ((tensorProductContinuousLinearEquivPi K L).symm x) := rfl

theorem baseChangePi_apply_eq_algebraMap_comp
    {x : Fin (Module.finrank K L) → AdeleRing K}
    {y : Fin (Module.finrank K L) → K}
    (h : ∀ i, algebraMap K (AdeleRing K) (y i) = x i) :
    baseChangePi K L x = algebraMap L (AdeleRing L) ((Module.finBasis K L).equivFun.symm y) := by
  rw [← funext h, baseChangePi_apply, tensorProductContinuousLinearEquivPi_symm_apply_of_algebraMap,
    baseChange_tsum_apply_right]

theorem baseChangePi_mem_principalSubgroup
    {x : Fin (Module.finrank K L) → AdeleRing K}
    (h : x ∈ AddSubgroup.pi Set.univ (fun _ => principalSubgroup K)) :
    baseChangePi K L x ∈ principalSubgroup L := by
  simp only [AddSubgroup.mem_pi, Set.mem_univ, forall_const] at h
  choose y hy using h
  exact baseChangePi_apply_eq_algebraMap_comp hy ▸ ⟨(Module.finBasis K L).equivFun.symm y, rfl⟩

variable (K L)

theorem baseChangePi_map_principalSubgroup :
    (AddSubgroup.pi Set.univ (fun (_ : Fin (Module.finrank K L)) => principalSubgroup K)).map
      (baseChangePi K L).toAddMonoidHom = principalSubgroup L := by
  ext x
  simp only [AddSubgroup.mem_map, LinearMap.toAddMonoidHom_coe, LinearEquiv.coe_coe,
    ContinuousLinearEquiv.coe_toLinearEquiv]
  refine ⟨fun ⟨a, h, ha⟩ => ha ▸ baseChangePi_mem_principalSubgroup h, ?_⟩
  rintro ⟨a, rfl⟩
  use fun i => algebraMap K (AdeleRing K) ((Module.finBasis K L).equivFun a i)
  refine ⟨fun i _ => ⟨(Module.finBasis K L).equivFun a i, rfl⟩, ?_⟩
  rw [baseChangePi_apply_eq_algebraMap_comp (fun i => rfl), LinearEquiv.symm_apply_apply]
  rfl

noncomputable def baseChangeQuotientPi :
    (Fin (Module.finrank K L) → AdeleRing K ⧸ principalSubgroup K) ≃ₜ+
      AdeleRing L ⧸ principalSubgroup L :=
  (ContinuousAddEquiv.quotientPi _).symm.trans <|
    QuotientAddGroup.continuousAddEquiv _ _ _ _ (baseChangePi K L).toContinuousAddEquiv
      (baseChangePi_map_principalSubgroup K L)

end NumberField.AdeleRing

end BaseChange

section Discrete

open NumberField DedekindDomain

theorem Rat.AdeleRing.zero_discrete : ∃ U : Set (AdeleRing ℚ),
    IsOpen U ∧ (algebraMap ℚ (AdeleRing ℚ)) ⁻¹' U = {0} := by
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
      have : (algebraMap ℚ (AdeleRing ℚ)) x =
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
      · clear h1 -- not needed
        -- mathematically this is trivial:
        -- h2 says that no prime divides the denominator of x
        -- so x is an integer
        -- and the goal is that there exists an integer `y` such that `y = x`.
        suffices ∀ p : ℕ, p.Prime → ¬(p ∣ x.den) by
          use x.num
          rw [← den_eq_one_iff]
          contrapose! this
          exact ⟨x.den.minFac, Nat.minFac_prime this, Nat.minFac_dvd _⟩
        sorry -- issue #254
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
theorem Rat.AdeleRing.discrete : ∀ q : ℚ, ∃ U : Set (AdeleRing ℚ),
    IsOpen U ∧ (algebraMap ℚ (AdeleRing ℚ)) ⁻¹' U = {q} := by
  obtain ⟨V, hV, hV0⟩ := zero_discrete
  intro q
  set ι  := algebraMap ℚ (AdeleRing ℚ)    with hι
  set qₐ := ι q                           with hqₐ
  set f  := Homeomorph.subLeft qₐ         with hf
  use f ⁻¹' V, f.isOpen_preimage.mpr hV
  have : f ∘ ι = ι ∘ Homeomorph.subLeft q := by ext; simp [hf, hqₐ]
  rw [← Set.preimage_comp, this, Set.preimage_comp, hV0]
  ext
  simp only [Set.mem_preimage, Homeomorph.subLeft_apply, Set.mem_singleton_iff, sub_eq_zero, eq_comm]

variable (K : Type*) [Field K] [NumberField K]

theorem NumberField.AdeleRing.discrete : ∀ k : K, ∃ U : Set (AdeleRing K),
    IsOpen U ∧ (algebraMap K (AdeleRing K)) ⁻¹' U = {k} := sorry -- issue #257

end Discrete

section Compact

open NumberField

theorem Rat.AdeleRing.cocompact :
    CompactSpace (AdeleRing ℚ ⧸ AdeleRing.principalSubgroup ℚ) :=
  sorry -- issue #258

variable (K L : Type*) [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]

theorem NumberField.AdeleRing.cocompact :
    CompactSpace (AdeleRing K ⧸ principalSubgroup K) :=
  letI := Rat.AdeleRing.cocompact
  (baseChangeQuotientPi ℚ K).compactSpace

end Compact
