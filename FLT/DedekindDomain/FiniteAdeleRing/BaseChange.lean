import Mathlib.RingTheory.DedekindDomain.AdicValuation
import FLT.Mathlib.Algebra.Order.Hom.Monoid
import FLT.Mathlib.Algebra.Algebra.Hom
import FLT.Mathlib.Algebra.Algebra.Pi
import FLT.Mathlib.Algebra.Algebra.Bilinear
import FLT.Mathlib.Topology.Algebra.UniformRing
import FLT.Mathlib.Topology.Algebra.Valued.WithVal
import FLT.Mathlib.RingTheory.DedekindDomain.AdicValuation

/-!

# Base change of adele rings.

If `A` is a Dedekind domain with field of fractions `K`, if `L/K` is a finite separable
extension and if `B` is the integral closure of `A` in `L`, then `B` is also a Dedekind
domain. Hence the rings of finite adeles `𝔸_K^∞` and `𝔸_L^∞` (defined using `A` and `B`)
are defined. In this file we define the natural `K`-algebra map `𝔸_K^∞ → 𝔸_L^∞` and
the natural `L`-algebra map `𝔸_K^∞ ⊗[K] L → 𝔸_L^∞`, and show that the latter map
is an isomorphism.

## Main definition

* `FiniteAdeleRing.baseChangeEquiv : L ⊗[K] FiniteAdeleRing A K ≃ₐ[L] FiniteAdeleRing B L`

-/

open scoped Multiplicative Valued

-- The general set-up.

variable (A K L B : Type*) [CommRing A] [CommRing B] [Algebra A B] [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K] [Algebra B L] [IsDedekindDomain A]
    [Algebra K L] [Algebra A L] [IsScalarTower A B L] [IsScalarTower A K L]
    [IsIntegralClosure B A L] [FiniteDimensional K L]

variable [Algebra.IsSeparable K L]

example : Function.Injective (algebraMap B L) := IsIntegralClosure.algebraMap_injective' A

example : IsDomain B := by
  have foo : Function.Injective (algebraMap B L) := IsIntegralClosure.algebraMap_injective' A
  have bar : IsDomain L := inferInstance
  exact Function.Injective.isDomain _ foo -- exact? failed
variable [IsDomain B]

example : Algebra.IsIntegral A B := IsIntegralClosure.isIntegral_algebra A L
variable [Algebra.IsIntegral A B]

example : Module.Finite A B :=
  have := IsIntegralClosure.isNoetherian A K L B
  Module.IsNoetherian.finite A B
variable [Module.Finite A B]

example : IsDedekindDomain B := IsIntegralClosure.isDedekindDomain A K L B
variable [IsDedekindDomain B]

example : IsFractionRing B L := IsIntegralClosure.isFractionRing_of_finite_extension A K L B
variable [IsFractionRing B L]

-- We start by filling in some holes in the API for finite extensions of Dedekind domains.
namespace IsDedekindDomain

namespace HeightOneSpectrum

variable (v : HeightOneSpectrum A)

local notation "σ" => fun v w => algebraMap (WithVal (HeightOneSpectrum.valuation K v))
    (WithVal (HeightOneSpectrum.valuation L w))

-- first need a way to pull back valuations on B to A
variable {B L} in
def comap (w : HeightOneSpectrum B) : HeightOneSpectrum A where
  asIdeal := w.asIdeal.comap (algebraMap A B)
  isPrime := Ideal.comap_isPrime (algebraMap A B) w.asIdeal
  ne_bot := mt Ideal.eq_bot_of_comap_eq_bot w.ne_bot

variable {A} in
def Extension (v : HeightOneSpectrum A) := {w : HeightOneSpectrum B // w.comap A = v}

omit [Module.Finite A B] in
lemma mk_count_factors_map
    (hAB : Function.Injective (algebraMap A B))
    (w : HeightOneSpectrum B) (I : Ideal A) [DecidableEq (Associates (Ideal A))]
  [DecidableEq (Associates (Ideal B))] [∀ p : Associates (Ideal A), Decidable (Irreducible p)]
  [∀ p : Associates (Ideal B), Decidable (Irreducible p)] :
    (Associates.mk w.asIdeal).count (Associates.mk (Ideal.map (algebraMap A B) I)).factors =
    Ideal.ramificationIdx (algebraMap A B) (comap A w).asIdeal w.asIdeal *
      (Associates.mk (comap A w).asIdeal).count (Associates.mk I).factors := by
  classical
  induction I using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ =>
    rw [Associates.mk_zero, Ideal.zero_eq_bot, Ideal.map_bot, ← Ideal.zero_eq_bot,
      Associates.mk_zero]
    simp [Associates.count, Associates.factors_zero, w.associates_irreducible,
      associates_irreducible (comap A w), Associates.bcount]
  | h₂ I hI =>
    obtain rfl : I = ⊤ := by simpa using hI
    simp only [Submodule.zero_eq_bot, ne_eq, top_ne_bot, not_false_eq_true, Ideal.map_top]
    simp only [← Ideal.one_eq_top, Associates.mk_one, Associates.factors_one]
    rw [Associates.count_zero (associates_irreducible _),
      Associates.count_zero (associates_irreducible _), mul_zero]
  | h₃ I p hI hp IH =>
    simp only [Ideal.map_mul, ← Associates.mk_mul_mk]
    have hp_bot : p ≠ ⊥ := hp.ne_zero
    have hp_bot' := (Ideal.map_eq_bot_iff_of_injective hAB).not.mpr hp_bot
    have hI_bot := (Ideal.map_eq_bot_iff_of_injective hAB).not.mpr hI
    rw [Associates.count_mul (Associates.mk_ne_zero.mpr hp_bot) (Associates.mk_ne_zero.mpr hI)
      (associates_irreducible _), Associates.count_mul (Associates.mk_ne_zero.mpr hp_bot')
      (Associates.mk_ne_zero.mpr hI_bot) (associates_irreducible _)]
    simp only [IH, mul_add]
    congr 1
    by_cases hw : (w.comap A).asIdeal = p
    · have : Irreducible (Associates.mk p) := Associates.irreducible_mk.mpr hp.irreducible
      rw [hw, Associates.factors_self this, Associates.count_some this]
      simp only [UniqueFactorizationMonoid.factors_eq_normalizedFactors, Multiset.nodup_singleton,
        Multiset.mem_singleton, Multiset.count_eq_one_of_mem, mul_one]
      rw [count_associates_factors_eq hp_bot' w.2 w.3,
        Ideal.IsDedekindDomain.ramificationIdx_eq_normalizedFactors_count hp_bot' w.2 w.3]
    · have : (Associates.mk (comap A w).asIdeal).count (Associates.mk p).factors = 0 :=
        Associates.count_eq_zero_of_ne (associates_irreducible _)
          (Associates.irreducible_mk.mpr hp.irreducible)
          (by rwa [ne_eq, Associates.mk_eq_mk_iff_associated, associated_iff_eq])
      rw [this, mul_zero, eq_comm]
      by_contra H
      rw [eq_comm, ← ne_eq, Associates.count_ne_zero_iff_dvd hp_bot' (irreducible w),
        Ideal.dvd_iff_le, Ideal.map_le_iff_le_comap] at H
      apply hw (((Ideal.isPrime_of_prime hp).isMaximal hp_bot).eq_of_le (comap A w).2.ne_top H).symm

omit [Module.Finite A B] in
lemma intValuation_comap (hAB : Function.Injective (algebraMap A B))
    (w : HeightOneSpectrum B) (x : A) :
    (comap A w).intValuation x ^
    (Ideal.ramificationIdx (algebraMap A B) (comap A w).asIdeal w.asIdeal) =
    w.intValuation (algebraMap A B x) := by
  classical
  have h_ne_zero : Ideal.ramificationIdx (algebraMap A B) (comap A w).asIdeal w.asIdeal ≠ 0 :=
    Ideal.IsDedekindDomain.ramificationIdx_ne_zero
      ((Ideal.map_eq_bot_iff_of_injective hAB).not.mpr (comap A w).3) w.2 Ideal.map_comap_le
  by_cases hx : x = 0
  · simpa [hx]
  simp only [intValuation, Valuation.coe_mk, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk]
  show (ite _ _ _) ^ _ = ite _ _ _
  rw [map_eq_zero_iff _ hAB, if_neg hx, if_neg hx, ← Set.image_singleton, ← Ideal.map_span,
    mk_count_factors_map _ _ hAB, mul_comm]
  simp

-- Need to know how the valuation `w` and its pullback are related on elements of `K`.
omit [IsIntegralClosure B A L] [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [Module.Finite A B] in
lemma valuation_comap (w : HeightOneSpectrum B) (x : K) :
    (comap A w).valuation K x ^
      (Ideal.ramificationIdx (algebraMap A B) (comap A w).asIdeal w.asIdeal) =
    w.valuation L (algebraMap K L x) := by
  obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective (A := A) x
  simp [valuation, ← IsScalarTower.algebraMap_apply A K L, IsScalarTower.algebraMap_apply A B L,
    ← intValuation_comap A B (algebraMap_injective_of_field_isFractionRing A B K L), div_pow]

omit [IsIntegralClosure B A L] [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [Module.Finite A B] in
lemma _root_.IsDedekindDomain.HeightOneSpectrum.adicValued.continuous_algebraMap
    (v : HeightOneSpectrum A) (w : HeightOneSpectrum B) (hvw : w.comap A = v) :
    Continuous (σ v w) := by
  subst hvw
  refine continuous_of_continuousAt_zero (algebraMap _ _) ?hf
  delta ContinuousAt
  simp only [map_zero]
  rw [(@Valued.hasBasis_nhds_zero K _ _ _ (comap A w).adicValued).tendsto_iff
    (@Valued.hasBasis_nhds_zero L _ _ _ w.adicValued)]
  simp only [HeightOneSpectrum.adicValued_apply, Set.mem_setOf_eq, true_and, true_implies]
  rw [WithZero.unitsWithZeroEquiv.forall_congr_left, Multiplicative.forall]
  intro a
  rw [WithZero.unitsWithZeroEquiv.exists_congr_left, Multiplicative.exists]
  let m := Ideal.ramificationIdx (algebraMap A B) (comap A w).asIdeal w.asIdeal
  let e : ℤ ≃ ℤₘ₀ˣ := Multiplicative.ofAdd.trans OrderMonoidIso.unitsWithZero.symm.toEquiv
  have e_apply (a : ℤ) : e a = OrderMonoidIso.unitsWithZero.symm (Multiplicative.ofAdd a) := rfl
  have hm : m ≠ 0 := by
    refine Ideal.IsDedekindDomain.ramificationIdx_ne_zero ?_ w.2 Ideal.map_comap_le
    exact (Ideal.map_eq_bot_iff_of_injective
      (algebraMap_injective_of_field_isFractionRing A B K L)).not.mpr (comap A w).3
  refine ⟨a / m, fun x hx ↦ ?_⟩
  erw [← valuation_comap A]
  calc
    (comap A w).valuation K x ^ m < e (a / ↑m) ^ m := by gcongr; exacts [zero_le', hx]
  _ = e (m • (a / ↑m)) := by
    dsimp [e]
    norm_cast
    rw [map_pow]
  _ ≤ e a := by
    simp only [nsmul_eq_mul, e_apply, Units.val_le_val, OrderIsoClass.map_le_map_iff]
    rw [mul_comm]
    exact Int.mul_le_of_le_ediv (by positivity) le_rfl

noncomputable def adicCompletionComapSemialgHom (v : HeightOneSpectrum A) (w : HeightOneSpectrum B)
    (hvw : w.comap A = v) :
    v.adicCompletion K →ₛₐ[σ v w] w.adicCompletion L :=
  UniformSpace.Completion.mapSemialgHom _ <|
  IsDedekindDomain.HeightOneSpectrum.adicValued.continuous_algebraMap A K L B v w hvw

section ModuleTopology

-- Make (v.adicCompletion K) a normed field.
-- This exists for number fields in Mathlib, but not for general Dedekind Domains.
-- v.asIdeal.absNorm may be 0 so just use 2 as the base for the norm.

open WithZeroMulInt in
noncomputable local instance adicCompletion_RkOne :
    Valuation.RankOne (Valued.v : Valuation (v.adicCompletion K) ℤₘ₀) where
  hom := {
    toFun := toNNReal (by norm_num : (2 : NNReal) ≠ 0)
    map_zero' := rfl
    map_one' := rfl
    map_mul' := MonoidWithZeroHom.map_mul (toNNReal (by norm_num))
  }
  strictMono' := toNNReal_strictMono (by norm_num)
  nontrivial' := by
    rcases Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot with ⟨x, hx1, hx2⟩
    use algebraMap A K x
    dsimp [adicCompletion]
    rw [valuedAdicCompletion_eq_valuation' v (algebraMap A K x)]
    constructor
    · simpa only [ne_eq, map_eq_zero, FaithfulSMul.algebraMap_eq_zero_iff]
    · apply ne_of_lt
      rw [valuation_eq_intValuationDef, intValuation_lt_one_iff_dvd]
      exact Ideal.dvd_span_singleton.mpr hx1

noncomputable local instance adicCompletion_normedField : NormedField (adicCompletion K v) :=
  Valued.toNormedField (hv := adicCompletion_RkOne A K v)
      (adicCompletion K v) (WithZero (Multiplicative ℤ))

-- Doesn't exist at all in Mathlib
noncomputable local instance : NontriviallyNormedField (adicCompletion K v) := {
  non_trivial := by
    obtain ⟨π, hπ⟩ :=
      IsDedekindDomain.HeightOneSpectrum.valuation_exists_uniformizer K v
    use π⁻¹
    dsimp [(‖·‖), Valued.norm]
    unfold Valuation.RankOne.hom
    dsimp [adicCompletion_RkOne]
    apply lt_of_not_le
    rw [
      map_inv₀, NNReal.coe_le_one, WithZeroMulInt.toNNReal_le_one_iff (by norm_num),
      IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v π, hπ]
    simp only [Int.reduceNeg, ofAdd_neg, WithZero.coe_inv, inv_inv,
      WithZero.coe_le_one, not_le]
    decide
}

omit [IsIntegralClosure B A L] [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [Module.Finite A B] in
lemma adicCompletionComapSemialgHom_continuous
    (v : HeightOneSpectrum A) (w : HeightOneSpectrum B) (hvw : w.comap A = v) :
    Continuous (adicCompletionComapSemialgHom A K L B v w hvw) := by
  convert UniformSpace.Completion.continuous_extension (β := (adicCompletion L w))

noncomputable
def comap_algebra {v : HeightOneSpectrum A} {w : HeightOneSpectrum B} (h : w.comap A = v) :
    Algebra (v.adicCompletion K) (w.adicCompletion L) :=
  (adicCompletionComapSemialgHom A K L B v w h).toAlgebra

def comap_algebra_continuousSmul (v : HeightOneSpectrum A) (w : HeightOneSpectrum B)
  (hvw : comap A w = v) : letI := comap_algebra A K L B hvw
    ContinuousSMul (adicCompletion K v) (adicCompletion L w) := by
  let inst_alg := comap_algebra A K L B hvw
  constructor
  have leftCts := adicCompletionComapSemialgHom_continuous A K L B v w hvw
  exact Continuous.mul (Continuous.fst' leftCts) continuous_snd

open TensorProduct in
def comap_algebra_finite (v : HeightOneSpectrum A) (w : HeightOneSpectrum B) (hvw : comap A w = v)
  : letI := comap_algebra A K L B hvw
    Module.Finite (adicCompletion K v) (adicCompletion L w) := by
  let inst_alg := comap_algebra A K L B hvw
  let inst_cSmul : ContinuousSMul (adicCompletion K v) (adicCompletion L w) :=
    comap_algebra_continuousSmul A K L B v w hvw
  let uniformL : UniformSpace L := w.adicValued.toUniformSpace
  let sa : L →ₛₐ[algebraMap K (adicCompletion K v)] adicCompletion L w := {
    __ := (algebraMap L (adicCompletion L w))
    map_smul' x y := by
      simp only
      rw [Algebra.smul_def, Algebra.smul_def, MonoidHom.map_mul']
      congr 1
      symm
      apply (adicCompletionComapSemialgHom A K L B v w hvw).commutes x
  }
  let f : ((HeightOneSpectrum.adicCompletion K v) ⊗[K] L)
      →ₗ[(HeightOneSpectrum.adicCompletion K v)] adicCompletion L w :=
    (SemialgHom.baseChange_of_algebraMap sa).toLinearMap
  have isClosed : IsClosed (LinearMap.range f).carrier := by
    apply Submodule.closed_of_finiteDimensional
  let coeL : L → adicCompletion L w := UniformSpace.Completion.coe'
  have denseL : DenseRange coeL := UniformSpace.Completion.denseRange_coe
  have dense : Dense (LinearMap.range f).carrier := by
    apply Dense.mono _ denseL
    intro x ⟨l, hl⟩
    use (1 ⊗ₜ l)
    simp [f]
    show (algebraMap L (adicCompletion L w)) l = x
    exact hl
  have fdRange : Module.Finite (adicCompletion K v) (LinearMap.range f) :=
    LinearMap.finiteDimensional_range f
  rw [Module.finite_def]
  rw [Module.Finite.iff_fg] at fdRange
  convert fdRange
  symm
  rw [Submodule.eq_top_iff']
  simp_rw [← Submodule.mem_toAddSubmonoid, ← AddSubmonoid.mem_toSubsemigroup,
      ← AddSubsemigroup.mem_carrier]
  rw [← isClosed.closure_eq]
  exact dense

omit [IsIntegralClosure B A L] [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [Module.Finite A B] in
open TensorProduct in
noncomputable def uniqueFiniteDimTop (v : HeightOneSpectrum A) (w : HeightOneSpectrum B)
    (hvw : comap A w = v) :
  letI := comap_algebra A K L B hvw
  ((Fin (Module.finrank (HeightOneSpectrum.adicCompletion K v) (HeightOneSpectrum.adicCompletion L w))) → (HeightOneSpectrum.adicCompletion K v))
    ≃L[(HeightOneSpectrum.adicCompletion K v)]
    (HeightOneSpectrum.adicCompletion L w) := by
  let inst_alg := comap_algebra A K L B hvw
  let inst_cSmul : ContinuousSMul (adicCompletion K v) (adicCompletion L w) :=
    comap_algebra_continuousSmul A K L B v w hvw
  let inst_finite : Module.Finite (adicCompletion K v) (adicCompletion L w) :=
    comap_algebra_finite A K L B v w hvw
  apply ContinuousLinearEquiv.ofFinrankEq (Module.finrank_fin_fun (adicCompletion K v))

omit [IsIntegralClosure B A L] [Algebra.IsSeparable K L]
    [Module.Finite A B] in
lemma adicCompletionComap_isModuleTopology
    (v : HeightOneSpectrum A) (w : HeightOneSpectrum B) (hvw : w.comap A = v) :
    -- temporarily make L_w a K_v-algebra
    letI := comap_algebra A K L B hvw
    -- the claim that L_w has the module topology.
    IsModuleTopology (v.adicCompletion K) (w.adicCompletion L) := by
  let Kv := HeightOneSpectrum.adicCompletion K v
  let Lw := HeightOneSpectrum.adicCompletion L w
  have KvTop := IsTopologicalSemiring.toIsModuleTopology Kv
  let inst_alg : Algebra (HeightOneSpectrum.adicCompletion K v)
      (HeightOneSpectrum.adicCompletion L w) := comap_algebra A K L B hvw
  have e : (Fin (Module.finrank Kv Lw) → Kv) ≃L[Kv] (HeightOneSpectrum.adicCompletion L w) :=
    uniqueFiniteDimTop A K L B v w hvw
  apply IsModuleTopology.iso e

end ModuleTopology

omit [IsIntegralClosure B A L] [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [Module.Finite A B] in
lemma adicCompletionComap_coe
    (v : HeightOneSpectrum A) (w : HeightOneSpectrum B) (hvw : w.comap A = v) (x : K) :
    adicCompletionComapSemialgHom A K L B v w hvw x = algebraMap K L x :=
  (adicCompletionComapSemialgHom A K L B v w hvw).commutes x

omit [IsIntegralClosure B A L] [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [Module.Finite A B] in
open WithZeroTopology in
lemma valued_adicCompletionComap
  (v : HeightOneSpectrum A) (w : HeightOneSpectrum B) (hvw : w.comap A = v) (x) :
    Valued.v (adicCompletionComapSemialgHom A K L B v w hvw x) = Valued.v x ^
      Ideal.ramificationIdx (algebraMap A B) (comap A w).asIdeal w.asIdeal := by
  revert x
  apply funext_iff.mp
  symm
  apply UniformSpace.Completion.ext
  · exact Valued.continuous_valuation.pow _
  · exact Valued.continuous_valuation.comp UniformSpace.Completion.continuous_extension
  intro a
  simp_rw [adicCompletionComap_coe, adicCompletion, Valued.valuedCompletion_apply,
    adicValued_apply']
  subst hvw
  rw [← valuation_comap A K L B w a]

def noZeroSMulDivisors : NoZeroSMulDivisors A B := by
  constructor
  intro r x h
  suffices (algebraMap A K r) • (algebraMap B L x) = 0 by
    rw [smul_eq_zero] at this
    simpa using this
  have ht : Algebra.linearMap B L (r • x) = r • algebraMap B L x := by
    simp [LinearMap.map_smul_of_tower]
  rw [IsScalarTower.algebraMap_smul, ← ht, h, map_zero]

def finite (v : HeightOneSpectrum A) : Finite (v.Extension B) := by
  have := noZeroSMulDivisors A K L B
  rw [Extension, ← Set.coe_setOf]
  rw [@Set.finite_coe_iff]
  have := primesOver_finite v.asIdeal B
  refine Set.Finite.of_finite_image (f := HeightOneSpectrum.asIdeal) ?_ ?_
  · refine Set.Finite.subset this ?_
    simp only [Set.subset_def, Set.mem_image, Set.mem_setOf_eq, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂]
    rintro w rfl
    simp only [Ideal.primesOver, Set.mem_setOf_eq, isPrime, true_and]
    constructor
    simp [Ideal.under_def, comap]
  · intro x hx y hy hxy
    rwa [← @HeightOneSpectrum.ext_iff] at hxy

/-- The canonical map `K_v → ∏_{w|v} L_w` extending K → L. -/
noncomputable def adicCompletionComapSemialgHom' (v : HeightOneSpectrum A) :
  v.adicCompletion K →ₛₐ[algebraMap K L] ∀ w : v.Extension B, w.1.adicCompletion L :=
  Pi.semialgHom _ _ fun i ↦ adicCompletionComapSemialgHom A K L B v i.1 i.2

noncomputable instance comap_pi_algebra (v : HeightOneSpectrum A) :
    Algebra (v.adicCompletion K) (Π (w : v.Extension B), w.1.adicCompletion L) :=
  (adicCompletionComapSemialgHom' A K L B v).toAlgebra

lemma prodAdicCompletionComap_isModuleTopology (v : HeightOneSpectrum A) :
    -- TODO: the `let _` in the statement below should not be required as it is an instance
    -- see mathlib PR #22488 for potential fix to this.
    -- Note that this one does not involve `adicCompletionIntegers` so the
    -- issue may not be to do with subtype vs. type implementation of
    -- `adicCompletionIntegers`.
    let _ := comap_pi_algebra A K L B v |>.toSMul
    -- the claim that L_w has the module topology.
    IsModuleTopology (v.adicCompletion K) (Π (w : v.Extension B), w.1.adicCompletion L) := by
  -- these are defs or lemmas so are required
  let _ (w : v.Extension B) := comap_algebra A K L B w.2 |>.toModule
  let _ (w : v.Extension B) := adicCompletionComap_isModuleTopology A K L B v w.1 w.2
  let _ := finite A K L B v
  exact IsModuleTopology.instPi

open scoped TensorProduct -- ⊗ notation for tensor product

/-- The canonical L-algebra map `L ⊗_K K_v → ∏_{w|v} L_w`. -/
noncomputable def tensorAdicCompletionComapAlgHom (v : HeightOneSpectrum A) :
    L ⊗[K] adicCompletion K v →ₐ[L] Π w : v.Extension B, w.1.adicCompletion L :=
  SemialgHom.baseChange_of_algebraMap (adicCompletionComapSemialgHom' A K L B v)

omit [IsIntegralClosure B A L] [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [Module.Finite A B] in
lemma tensorAdicCompletionComapAlgHom_tmul_apply (v : HeightOneSpectrum A) (x y i) :
  tensorAdicCompletionComapAlgHom A K L B v (x ⊗ₜ y) i =
    x • adicCompletionComapSemialgHom A K L B v i.1 i.2 y := by
  simp_rw [Algebra.smul_def]
  rfl

theorem tensorAdicCompletionComapAlgHom_bijective (v : HeightOneSpectrum A) :
    Function.Bijective (tensorAdicCompletionComapAlgHom A K L B v) := by
  sorry -- issue FLT#231

noncomputable def adicCompletionComapAlgEquiv (v : HeightOneSpectrum A) :
    L ⊗[K] v.adicCompletion K ≃ₐ[L] (∀ w : v.Extension B, w.1.adicCompletion L) :=
  AlgEquiv.ofBijective (tensorAdicCompletionComapAlgHom A K L B v) <|
    tensorAdicCompletionComapAlgHom_bijective A K L B v

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
variable (v : HeightOneSpectrum A) in
noncomputable
instance : TopologicalSpace (L ⊗[K] adicCompletion K v) := moduleTopology (adicCompletion K v) _

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
variable (v : HeightOneSpectrum A) in
instance : IsModuleTopology (adicCompletion K v) (L ⊗[K] adicCompletion K v) :=
  ⟨rfl⟩

noncomputable def adicCompletionComapContinuousAlgEquiv (v : HeightOneSpectrum A) :
  L ⊗[K] v.adicCompletion K ≃A[L] ∀ w : v.Extension B, w.1.adicCompletion L
  where
    toAlgEquiv := adicCompletionComapAlgEquiv A K L B v
    continuous_toFun := sorry -- FLT#328
    continuous_invFun := sorry -- FLT#328

attribute [local instance 9999] SMulCommClass.of_commMonoid TensorProduct.isScalarTower_left IsScalarTower.right

-- TODO : this maxHeartbeats should not be required, see mathlib PR #22488 for potential fix
set_option synthInstance.maxHeartbeats 80000 in
instance (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] (v : HeightOneSpectrum R) :
    IsScalarTower R (v.adicCompletionIntegers K) (v.adicCompletion K) :=
  ⟨fun x y z ↦ by exact smul_mul_assoc x y.1 z⟩

noncomputable
def adicCompletionIntegersSubalgebra {R : Type*} (K : Type*) [CommRing R]
    [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K] (v : HeightOneSpectrum R) :
    Subalgebra R (HeightOneSpectrum.adicCompletion K v) where
  __ := HeightOneSpectrum.adicCompletionIntegers K v
  algebraMap_mem' r := coe_mem_adicCompletionIntegers v r

/-- The canonical map `B ⊗[A] A_v → L ⊗[K] K_v` -/
noncomputable def tensorAdicCompletionIntegersTo (v : HeightOneSpectrum A) :
    B ⊗[A] adicCompletionIntegers K v →ₐ[B] L ⊗[K] adicCompletion K v :=
  Algebra.TensorProduct.lift
    ((Algebra.TensorProduct.includeLeft).comp (Algebra.ofId B L))
    ((Algebra.TensorProduct.includeRight.restrictScalars A).comp (IsScalarTower.toAlgHom _ _ _))
    (fun _ _ ↦ .all _ _)

omit [IsIntegralClosure B A L] [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [Module.Finite A B] in
set_option linter.deprecated false in -- `map_zero` and `map_add` time-outs
theorem range_adicCompletionComapAlgIso_tensorAdicCompletionIntegersTo_le_pi
    (v : HeightOneSpectrum A) :
    AlgHom.range (((tensorAdicCompletionComapAlgHom A K L B v).restrictScalars B).comp
      (tensorAdicCompletionIntegersTo A K L B v)) ≤
      Subalgebra.pi Set.univ (fun _ ↦ adicCompletionIntegersSubalgebra _ _) := by
  rintro _ ⟨x, rfl⟩ i -
  simp only [Subalgebra.coe_toSubmodule, AlgEquiv.toAlgHom_eq_coe, AlgHom.toRingHom_eq_coe,
    RingHom.coe_coe, AlgHom.coe_comp, AlgHom.coe_restrictScalars', AlgHom.coe_coe,
    Function.comp_apply, SetLike.mem_coe]
  induction' x with x y x y hx hy
  · simp [map_zero, Pi.zero_apply, zero_mem]
  · simp only [tensorAdicCompletionIntegersTo, Algebra.TensorProduct.lift_tmul, AlgHom.coe_comp,
      Function.comp_apply, Algebra.ofId_apply, AlgHom.commutes,
      Algebra.TensorProduct.algebraMap_apply, AlgHom.coe_restrictScalars',
      IsScalarTower.coe_toAlgHom', ValuationSubring.algebraMap_apply,
      Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul,
      tensorAdicCompletionComapAlgHom_tmul_apply, algebraMap_smul]
    apply Subalgebra.smul_mem
    show _ ≤ (1 : ℤₘ₀)
    rw [valued_adicCompletionComap A K (L := L) (B := B) v i.1 i.2 y.1,
      ← one_pow (Ideal.ramificationIdx (algebraMap A B) (comap A i.1).asIdeal i.1.asIdeal),
      pow_le_pow_iff_left₀]
    · exact y.2
    · exact zero_le'
    · exact zero_le'
    · exact Ideal.IsDedekindDomain.ramificationIdx_ne_zero  ((Ideal.map_eq_bot_iff_of_injective
        (algebraMap_injective_of_field_isFractionRing A B K L)).not.mpr
        (comap A i.1).3) i.1.2 Ideal.map_comap_le
  · simp [map_add, Pi.add_apply, add_mem hx hy]

theorem adicCompletionComapAlgEquiv_integral : ∃ S : Finset (HeightOneSpectrum A), ∀ v ∉ S,
    AlgHom.range (((tensorAdicCompletionComapAlgHom A K L B v).restrictScalars B).comp
      (tensorAdicCompletionIntegersTo A K L B v)) =
    Subalgebra.pi Set.univ (fun _ ↦ adicCompletionIntegersSubalgebra _ _) := sorry -- FLT#329

end IsDedekindDomain.HeightOneSpectrum

namespace DedekindDomain

open IsDedekindDomain HeightOneSpectrum

noncomputable def ProdAdicCompletions.baseChange :
    ProdAdicCompletions A K →ₛₐ[algebraMap K L] ProdAdicCompletions B L :=
  Pi.semialgHomPi _ _ fun w => adicCompletionComapSemialgHom A K L B _ w rfl

open scoped TensorProduct -- ⊗ notation for tensor product

-- Note that this is only true because L/K is finite; in general tensor product doesn't
-- commute with infinite products, but it does here.
noncomputable def ProdAdicCompletions.baseChangeEquiv :
    L ⊗[K] ProdAdicCompletions A K ≃ₐ[L] ProdAdicCompletions B L :=
  AlgEquiv.ofBijective
    (SemialgHom.baseChange_of_algebraMap (ProdAdicCompletions.baseChange A K L B))
    sorry -- #239

-- I am unclear about whether these next two sorries are in the right order.
-- One direction of `baseChange_isFiniteAdele_iff` below (->) is easy, but perhaps the other way
-- should be deduced from the result after this one. See #240.
-- (`ProdAdicCompletions.baseChangeEquiv_isFiniteAdele_iff`).
theorem ProdAdicCompletions.baseChange_isFiniteAdele_iff
    (x : ProdAdicCompletions A K) :
    ProdAdicCompletions.IsFiniteAdele x ↔
    ProdAdicCompletions.IsFiniteAdele (ProdAdicCompletions.baseChange A K L B x) := sorry --#240

-- This theorem and the one before are probably equivalent, I'm not sure which one to prove first.
-- See #240
theorem ProdAdicCompletions.baseChangeEquiv_isFiniteAdele_iff
    (x : ProdAdicCompletions A K) :
    ProdAdicCompletions.IsFiniteAdele x ↔
    ProdAdicCompletions.IsFiniteAdele (ProdAdicCompletions.baseChangeEquiv A K L B (1 ⊗ₜ x)) :=
  sorry -- #240

theorem ProdAdicCompletions.baseChangeEquiv_isFiniteAdele_iff' (x : ProdAdicCompletions A K) :
    ProdAdicCompletions.IsFiniteAdele x ↔ ∀ (l : L), ProdAdicCompletions.IsFiniteAdele
    (ProdAdicCompletions.baseChangeEquiv A K L B (l ⊗ₜ x)) := by
  constructor
  · simp_rw [ProdAdicCompletions.baseChangeEquiv_isFiniteAdele_iff A K L B, baseChangeEquiv,
      AlgEquiv.coe_ofBijective, SemialgHom.baseChange_of_algebraMap ,
      Algebra.TensorProduct.lift_tmul, map_one, one_mul]
    intro h l
    exact ProdAdicCompletions.IsFiniteAdele.mul (ProdAdicCompletions.IsFiniteAdele.algebraMap' l) h
  · intro h
    rw [ProdAdicCompletions.baseChangeEquiv_isFiniteAdele_iff A K L B]
    exact h 1

-- Restriction of an algebra map is an algebra map; these should be easy. #242
noncomputable def FiniteAdeleRing.baseChange :
    FiniteAdeleRing A K →ₛₐ[algebraMap K L] FiniteAdeleRing B L where
  toFun ak := ⟨ProdAdicCompletions.baseChange A K L B ak.1,
    (ProdAdicCompletions.baseChange_isFiniteAdele_iff A K L B ak).1 ak.2⟩
  map_one' := by
    ext
    have h : (1 : FiniteAdeleRing A K) = (1 : ProdAdicCompletions A K) := rfl
    have t : (1 : FiniteAdeleRing B L) = (1 : ProdAdicCompletions B L) := rfl
    simp_rw [h, t, map_one]
  map_mul' x y := by
    have h : (x * y : FiniteAdeleRing A K) =
      (x : ProdAdicCompletions A K) * (y : ProdAdicCompletions A K) := rfl
    simp_rw [h, map_mul]
    rfl
  map_zero' := by
    ext
    have h : (0 : FiniteAdeleRing A K) = (0 : ProdAdicCompletions A K) := rfl
    have t : (0 : FiniteAdeleRing B L) = (0 : ProdAdicCompletions B L) := rfl
    simp_rw [h, t, map_zero]
  map_add' x y := by
    have h : (x + y : FiniteAdeleRing A K) =
      (x : ProdAdicCompletions A K) + (y : ProdAdicCompletions A K) := rfl
    simp_rw [h, map_add]
    rfl
  map_smul' k xv := by
    refine ext B L <| funext fun w ↦ ?_
    exact (adicCompletionComapSemialgHom A K L B _ w rfl).map_smul' k (xv (comap A w))

noncomputable instance : Algebra (FiniteAdeleRing A K) (L ⊗[K] FiniteAdeleRing A K) :=
  Algebra.TensorProduct.rightAlgebra

noncomputable
instance BaseChange.algebra : Algebra (FiniteAdeleRing A K) (FiniteAdeleRing B L) :=
  RingHom.toAlgebra (FiniteAdeleRing.baseChange A K L B)

lemma BaseChange.isModuleTopology : IsModuleTopology (FiniteAdeleRing A K) (FiniteAdeleRing B L) :=
  sorry

instance : TopologicalSpace (L ⊗[K] FiniteAdeleRing A K) :=
  moduleTopology (FiniteAdeleRing A K) (L ⊗[K] FiniteAdeleRing A K)
-- Follows from the above. Should be a continuous L-alg equiv but we don't have continuous
-- alg equivs yet so can't even state it properly.
noncomputable def FiniteAdeleRing.baseChangeAlgEquiv :
    L ⊗[K] FiniteAdeleRing A K ≃ₐ[L] FiniteAdeleRing B L where
  __ := AlgEquiv.ofBijective
    (SemialgHom.baseChange_of_algebraMap <| FiniteAdeleRing.baseChange A K L B)
    -- ⊢ Function.Bijective ⇑(baseChange A K L B).baseChange_of_algebraMap
    sorry -- #243

noncomputable def FiniteAdeleRing.baseChangeContinuousAlgEquiv :
    L ⊗[K] FiniteAdeleRing A K ≃A[L] FiniteAdeleRing B L where
  __ := FiniteAdeleRing.baseChangeAlgEquiv A K L B
  continuous_toFun := sorry
  continuous_invFun := sorry


end DedekindDomain
