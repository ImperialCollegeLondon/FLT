import FLT.Deformations.Lemmas
import FLT.Deformations.RepresentationTheory.ContinuousSMulDiscrete
import Mathlib.Algebra.GCDMonoid.IntegrallyClosed
import Mathlib.Algebra.GroupWithZero.Action.Faithful
import Mathlib.RingTheory.Invariant.Basic

section

variable (R A : Type*) [CommRing R] [CommRing A] [Algebra R A]

/-- `IntegralClosure R A` is the integral closure of `R` in `A` as a type.
We don't use the subring directly to avoid horrendous timeouts. -/
def IntegralClosure : Type _ := integralClosure R A

instance : CommRing (IntegralClosure R A) := (integralClosure R A).toCommRing

instance : Algebra R (IntegralClosure R A) := (integralClosure R A).algebra

instance : Algebra (IntegralClosure R A) A := (integralClosure R A).toAlgebra

instance [IsDomain A] : IsDomain (IntegralClosure R A) := by
  delta IntegralClosure; infer_instance

instance : Algebra.IsIntegral R (IntegralClosure R A) := by
  delta IntegralClosure; infer_instance

instance : IsScalarTower R (IntegralClosure R A) A := (integralClosure R A).isScalarTower_mid

instance [FaithfulSMul R A] : FaithfulSMul R (IntegralClosure R A) := by
  refine (faithfulSMul_iff_algebraMap_injective _ _).mpr (.of_comp (f := algebraMap _ A) ?_)
  exact (FaithfulSMul.algebraMap_injective R A)

instance mulSemiringActionIntegralClosure
    {G R K : Type*} [CommRing R] [Field K] [Algebra R K] [Monoid G] [MulSemiringAction G K]
    [SMulCommClass G R K] :
    MulSemiringAction G (IntegralClosure R K) where
  smul σ x := ⟨σ • x.1, x.2.map (MulSemiringAction.toAlgHom R K σ)⟩
  one_smul _ := Subtype.ext (one_smul _ _)
  mul_smul _ _ _ := Subtype.ext (mul_smul _ _ _)
  smul_zero _ := Subtype.ext (smul_zero _)
  smul_add _ _ _ := Subtype.ext (smul_add _ _ _)
  smul_one _ := Subtype.ext (smul_one _)
  smul_mul _ _ _ := Subtype.ext (MulSemiringAction.smul_mul _ _ _)

instance smulCommClass_integralClosure
    {G R K : Type*} [CommRing R] [Field K] [Algebra R K] [Monoid G] [MulSemiringAction G K]
    [SMulCommClass G R K] :
    SMulCommClass G R (IntegralClosure R K) where
  smul_comm _ _ _ := Subtype.ext (smul_comm _ _ _)

lemma not_isField_integralClosure
    {K L : Type*} [Field K] [Field L] [Algebra K L] (R : ValuationSubring K) (hR : R ≠ ⊤) :
    ¬ IsField (IntegralClosure R L) := by
  have : FaithfulSMul K L := inferInstance
  contrapose! hR
  letI := hR.toField
  let F := IsFractionRing.liftAlgHom (K := K) (g := Algebra.ofId R (IntegralClosure R L))
    (FaithfulSMul.algebraMap_injective _ _)
  refine top_le_iff.mp fun x _ ↦ ?_
  have : IsIntegrallyClosed R := GCDMonoid.toIsIntegrallyClosed
  have := (isIntegral_algHom_iff F F.injective).mp (Algebra.IsIntegral.isIntegral (R := R) (F x))
  obtain ⟨x, rfl⟩ := (IsIntegralClosure.isIntegral_iff (A := R)).mp this
  exact x.2

instance isInvariant_integralClosure
    {G K L : Type*} [Field K] [Field L] [Algebra K L] [Group G] [MulSemiringAction G L]
    [SMulCommClass G K L] [Algebra.IsInvariant K L G] (R : ValuationSubring K) :
    Algebra.IsInvariant R (IntegralClosure R L) G where
  isInvariant := by
    rintro ⟨x, hx : IsIntegral _ _⟩ hx'
    obtain ⟨x, rfl⟩ := Algebra.IsInvariant.isInvariant (A := K) x fun g ↦ congr($(hx' g).1)
    rw [isIntegral_algebraMap_iff (algebraMap K L).injective] at hx
    have : IsIntegrallyClosed R := GCDMonoid.toIsIntegrallyClosed
    obtain ⟨x, rfl⟩ := (IsIntegralClosure.isIntegral_iff (A := R)).mp hx
    exact ⟨x, rfl⟩

instance continuousSMulDiscrete_integralClosure
    {G R L : Type*} [CommRing R] [Field L] [Algebra R L] [Group G] [MulSemiringAction G L]
    [SMulCommClass G R L] [TopologicalSpace G] [ContinuousSMulDiscrete G L] :
    ContinuousSMulDiscrete G (IntegralClosure R L) where
  isOpen_smul_eq x y := by
    simpa only [IntegralClosure, Subtype.ext_iff] using
      ContinuousSMulDiscrete.isOpen_smul_eq (G := G) x.1 y.1

instance {R S : Type*} [CommRing R] [CommRing S] {I : Ideal S} [Algebra R S]
    [Nontrivial R] [IsDomain S] [Algebra.IsIntegral R S] [NeZero I] : NeZero (I.under R) :=
  ⟨fun H ↦ NeZero.ne I (Ideal.eq_bot_of_comap_eq_bot H)⟩

end
