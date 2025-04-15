-- Code by Andrew Yang (erdOne)
-- I just moved it to my framework
import FLT.Deformation.BaseCat
import Mathlib

universe u uO uF uG un

open CategoryTheory IsLocalRing

namespace Deformation

open BaseCat

variable (𝓞 : Type uO) [CommRing 𝓞] [IsNoetherianRing 𝓞]
variable [IsLocalRing 𝓞] [IsAdicComplete (maximalIdeal 𝓞) 𝓞]
variable (G : Type uG) [TopologicalSpace G] [Group G] [IsTopologicalGroup G] [CompactSpace G]
variable (n : Type un) [DecidableEq n] [Fintype n]

variable {𝓞 G n}

variable (R : BaseCat.{uO} 𝓞)

abbrev BaseCat.Cotangent : Type _ :=
  maximalIdeal R.carrier ⧸ Submodule.comap (maximalIdeal R.carrier).subtype ((maximalIdeal 𝓞).map (algebraMap 𝓞 R.carrier) ⊔ maximalIdeal R.carrier ^ 2)

instance : Module (ResidueField 𝓞) R.Cotangent := Module.IsTorsionBySet.module <| by
  delta BaseCat.Cotangent
  refine (Module.isTorsionBySet_quotient_iff ((Submodule.comap (maximalIdeal R.carrier).subtype ((maximalIdeal 𝓞).map
    (algebraMap 𝓞 R.carrier) ⊔ maximalIdeal R.carrier ^ 2)).restrictScalars 𝓞) _).mpr ?_
  rintro ⟨s, hs⟩ r hr
  rw [← algebraMap_smul (R := 𝓞) R.carrier, pow_two]
  exact Submodule.mem_sup_right (Ideal.mul_mem_mul (fun h ↦ hr ((isUnit_map_iff _ _).mp h)) hs)

instance : MulAction (𝓴 𝓞) R.Cotangent where
  smul ko r := ko • r
  one_smul r := by sorry
  mul_smul ko ko' r := by sorry

instance : IsScalarTower 𝓞 (ResidueField 𝓞) R.Cotangent := .of_algebraMap_smul fun _ _ ↦ rfl
section CotangentToEquiv

variable {R}

noncomputable
def cotangentToEquivToFunApply (l : R.Cotangent →ₗ[ResidueField 𝓞] ResidueField 𝓞) (a : R.carrier) : DualNumber (ResidueField 𝓞) :=
  ⟨residue _ (preimage a), l (Submodule.Quotient.mk ⟨_, preimage_spec a⟩)⟩

lemma cotangentToEquivToFunApply_add (l : R.Cotangent →ₗ[ResidueField 𝓞] ResidueField 𝓞)
    (a : 𝓞) (b : R.carrier) (hb : b ∈ maximalIdeal R.carrier) : cotangentToEquivToFunApply l (algebraMap _ _ a + b) =
    ⟨residue _ a, l (Submodule.Quotient.mk ⟨b, hb⟩)⟩ := by
  ext
  · refine residue_preimage_eq_iff.mpr ?_
    simpa [ResidueField.map_residue] using hb
  · simp only [cotangentToEquivToFunApply, TrivSqZeroExt.snd_mk]
    congr 1
    rw [Submodule.Quotient.eq]
    refine Submodule.mem_sup_left ?_
    simp only [add_sub_right_comm, Submodule.mem_comap, Submodule.coe_subtype,
      AddSubgroupClass.coe_sub, sub_add_cancel, ← map_sub]
    refine Ideal.mem_map_of_mem _ ?_
    rw [← residue_eq_zero_iff]
    apply (R.isResidueAlgebra.bijective 𝓞).1
    --simpa [ResidueField.map_residue, residue_preimage] using hb
    sorry

lemma Submodule.zero_def {R M} [Semiring R] [AddCommMonoid M] [Module R M] (N : Submodule R M) :
    (0 : N) = ⟨0, zero_mem N⟩ := rfl

noncomputable
nonrec def BaseCat.DualNumber : BaseCat 𝓞 where
  carrier := DualNumber (ResidueField 𝓞)
  isLocalHom := by
    constructor
    intro x hx
    rw [TrivSqZeroExt.isUnit_iff_isUnit_fst, isUnit_iff_ne_zero] at hx
    exact not_not.mp ((residue_eq_zero_iff _).not.mp hx)
  isResidueAlgebra := sorry
  isProartinianRing := sorry

open BaseCat in
@[simps (config := .lemmasOnly)]
noncomputable
def cotangentToEquivToFun (l : R.Cotangent →ₗ[ResidueField 𝓞] ResidueField 𝓞) : R.carrier →ₐ[𝓞] DualNumber (ResidueField 𝓞) where
  toFun := cotangentToEquivToFunApply l
  map_one' := by simpa [← Submodule.zero_def] using cotangentToEquivToFunApply_add l 1 0 (zero_mem _)
  map_mul' x y := by
    have := cotangentToEquivToFunApply_add l (preimage x * preimage y)
      (x * y - algebraMap _ _ (preimage x * preimage y))
      ((residue_eq_zero_iff _).mp (by simp [residue_preimage]))
    simp only [map_mul, add_sub_cancel] at this
    simp only [this]
    unfold cotangentToEquivToFunApply
    ext
    · simp
    · simp only [TrivSqZeroExt.snd_mk, TrivSqZeroExt.snd_mul, TrivSqZeroExt.fst_mk, smul_eq_mul,
        MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op]
      simp only [← ResidueField.algebraMap_eq, ← Algebra.smul_def, ← LinearMap.map_smul_of_tower,
        ← map_add, mul_comm (l _), ← Submodule.mkQ_apply]
      congr 1
      refine (Submodule.Quotient.eq _).mpr (Submodule.mem_sup_right ?_)
      rw [pow_two]
      convert Ideal.mul_mem_mul (preimage_spec x) (preimage_spec y) using 1
      simp [Algebra.smul_def, mul_sub]
      ring
  map_zero' := by simpa [← Submodule.zero_def] using cotangentToEquivToFunApply_add l 0 0 (zero_mem _)
  map_add' x y := by
    have := cotangentToEquivToFunApply_add l (preimage x + preimage y)
      (x + y - algebraMap _ _ (preimage x + preimage y))
      ((residue_eq_zero_iff _).mp (by simp [residue_preimage]))
    simp only [map_add, add_sub_cancel] at this
    simp only [this]
    unfold cotangentToEquivToFunApply
    ext
    · simp
    · simp only [← map_add, TrivSqZeroExt.snd_mk, TrivSqZeroExt.snd_add, ← Submodule.Quotient.mk_add]
      congr 3
      rw [map_add, add_sub_add_comm]
  commutes' r := by simpa [← Submodule.zero_def] using cotangentToEquivToFunApply_add l r 0 (zero_mem _)

open BaseCat in
noncomputable
instance isLocalHom_cotangentToEquivToFun (l : R.Cotangent →ₗ[ResidueField 𝓞] ResidueField 𝓞) :
    IsLocalHom (cotangentToEquivToFun l).toRingHom := by
  constructor
  intro x hx
  replace hx := TrivSqZeroExt.isUnit_iff_isUnit_fst.mp hx
  rw [isUnit_iff_ne_zero] at hx
  simpa using residue_preimage_eq_iff.not.mp hx

instance {R} [CommRing R] : IsLocalHom (algebraMap R R) := ⟨fun _ ↦ id⟩

instance {R S T} [CommRing R] [CommRing S] [CommRing T] [IsLocalRing T] [Algebra R S] [Algebra R T]
    [Algebra S T] [IsScalarTower R S T] [IsLocalHom (algebraMap R T)] [IsLocalHom (algebraMap S T)] :
    IsScalarTower R S (ResidueField T) := IsScalarTower.of_algebraMap_eq' <| by
  show (algebraMap T _).comp (algebraMap R T) = _
  rw [IsScalarTower.algebraMap_eq R S]
  rfl

def cotangentToEquivInvFun (f : R.carrier →ₐ[𝓞] DualNumber (ResidueField 𝓞)) [IsLocalHom f] :
    R.Cotangent →ₗ[ResidueField 𝓞] ResidueField 𝓞 := by
  refine LinearMap.extendScalarsOfSurjective Ideal.Quotient.mk_surjective ?_
  refine Submodule.liftQ ((Submodule.comap (maximalIdeal R.carrier).subtype ((maximalIdeal 𝓞).map
    (algebraMap 𝓞 R.carrier) ⊔ maximalIdeal R.carrier ^ 2)).restrictScalars 𝓞) ?_ ?_
  · exact (TrivSqZeroExt.sndHom _ _).restrictScalars 𝓞 ∘ₗ f.toLinearMap ∘ₗ (maximalIdeal R.carrier).subtype.restrictScalars 𝓞
  · rintro ⟨x, hx₁⟩ hx
    obtain ⟨x, hx₂, y, hy, rfl⟩ := Submodule.mem_sup.mp hx
    have H₁ : f x = 0 := by
      clear! y
      induction hx₂ using Submodule.span_induction with
      | mem x h =>
        obtain ⟨x, hx, rfl⟩ := h
        simp only [AlgHom.commutes]
        ext
        · exact (residue_eq_zero_iff _).mpr hx
        · rfl
      | zero => simp
      | add x y hx hy _ _ => simp [*]
      | smul a x hx _ => simp [*]
    have H₂' (x) (hx : x ∈ maximalIdeal R.carrier) : (f x).fst = 0 := by
      rwa [← not_ne_iff, ← isUnit_iff_ne_zero, ← TrivSqZeroExt.isUnit_iff_isUnit_fst,
        isUnit_map_iff]
    have H₂ : f y = 0 := by
      clear! x
      rw [pow_two, Submodule.mul_eq_span_mul_set] at hy
      induction hy using Submodule.span_induction with
      | mem x h =>
        obtain ⟨a, ha, b, hb, rfl⟩ := h
        ext
        · simp [H₂' a ha, H₂' b hb]
        · simp [H₂' a ha, H₂' b hb]
      | zero => simp
      | add x y hx hy _ _ => simp [*]
      | smul a x hx _ => simp [*]
    simp [H₁, H₂]

lemma cotangentToEquivInvFun_apply (f : R.carrier →ₐ[𝓞] DualNumber (ResidueField 𝓞)) [IsLocalHom f] (x) :
    cotangentToEquivInvFun f (Submodule.Quotient.mk x) = (f x.1).snd := rfl

noncomputable
def cotangentToEquiv : (R.Cotangent →ₗ[ResidueField 𝓞] ResidueField 𝓞) ≃ (R ⟶ BaseCat.DualNumber) where
  toFun l := { hom := ⟨cotangentToEquivToFun l, by sorry⟩, isLocalHom := isLocalHom_cotangentToEquivToFun l }
  invFun f := @cotangentToEquivInvFun _ _ _ _ f.hom.toAlgHom ⟨f.isLocalHom.1⟩
  left_inv l := by
    apply LinearMap.ext
    intro x
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    dsimp [cotangentToEquivInvFun_apply, cotangentToEquivToFun, cotangentToEquivToFunApply]
    congr 1
    rw [Submodule.Quotient.eq]
    simp only [Submodule.mem_comap, Submodule.coe_subtype, AddSubgroupClass.coe_sub,
      sub_sub_cancel_left, neg_mem_iff]
    refine Submodule.mem_sup_left ?_
    refine Ideal.mem_map_of_mem _ ?_
    rw [← residue_eq_zero_iff, residue_preimage_eq_iff]
    simp
  right_inv f := by
    apply BaseCat.Hom.ext
    ext x
    have H (x) (hx : x ∈ maximalIdeal R.carrier) : (f.hom.toAlgHom x).fst = 0 := by
        rw [← not_ne_iff, ← isUnit_iff_ne_zero, ← TrivSqZeroExt.isUnit_iff_isUnit_fst]
        exact (isUnit_map_iff f.hom.toRingHom _).not.mpr hx
    apply TrivSqZeroExt.ext
    · show (algebraMap 𝓞 BaseCat.DualNumber.carrier _).fst = _
      rw [← f.hom.toAlgHom.commutes, eq_comm, ← sub_eq_zero, ← TrivSqZeroExt.fst_sub]
      change (f.hom.toAlgHom _ - f.hom.toAlgHom _).fst = _
      rw [← map_sub f.hom.toAlgHom, H]
      exact preimage_spec _
    · show (f.hom.toAlgHom (x - _)).snd = _
      rw [map_sub, TrivSqZeroExt.snd_sub, f.hom.toAlgHom.commutes]
      exact sub_zero _

end CotangentToEquiv

-- variable (𝒟 : DeformationProblem.{uO} 𝓞 G n) [𝒟.toFunctor.IsCorepresentable]

-- noncomputable
-- def cotangentToCoreprXEquiv :
--    (𝒟.toFunctor.coreprX.Cotangent →ₗ[ResidueField 𝓞] ResidueField 𝓞) ≃ 𝒟.obj BaseCat.DualNumber :=
--   cotangentToEquiv.trans 𝒟.toFunctor.corepresentableBy.homEquiv

end Deformation
