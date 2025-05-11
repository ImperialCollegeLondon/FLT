/-
Copyright (c) 2025 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Andrew Yang, Matthew Jasper
-/
import FLT.Mathlib.Algebra.Algebra.Bilinear
import FLT.Mathlib.Algebra.Algebra.Pi
import FLT.Mathlib.Algebra.Module.Submodule.Basic
import FLT.Mathlib.Topology.Algebra.Module.Equiv
import FLT.Mathlib.Topology.Algebra.Module.ModuleTopology
import FLT.Mathlib.Topology.Algebra.UniformRing
import FLT.Mathlib.Topology.Algebra.Valued.ValuationTopology
import FLT.Mathlib.Topology.Algebra.Valued.WithVal
import FLT.Mathlib.RingTheory.TensorProduct.Finite
import FLT.Mathlib.RingTheory.TensorProduct.Basis
import FLT.Mathlib.RingTheory.Finiteness.Pi
import Mathlib.Algebra.Algebra.Subalgebra.Pi
import Mathlib.Algebra.Group.Int.TypeTags
import Mathlib.Data.Int.WithZero
import Mathlib.NumberTheory.RamificationInertia.Basic
import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
import Mathlib.Topology.Algebra.Algebra.Equiv
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.Algebra.Valued.NormedValued
import Mathlib.RingTheory.Valuation.RankOne
import Mathlib.Topology.Algebra.Module.FiniteDimension
import FLT.DedekindDomain.AdicValuation

/-!

# Base change of adele rings.

If `A` is a Dedekind domain with field of fractions `K`, if `L/K` is a finite separable
extension and if `B` is the integral closure of `A` in `L`, then `B` is also a Dedekind
domain. Hence the rings of finite adeles `𝔸_K^∞` and `𝔸_L^∞` (defined using `A` and `B`)
are defined. In this file we define the natural `K`-algebra map `𝔸_K^∞ → 𝔸_L^∞` and
the natural `L`-algebra map `𝔸_K^∞ ⊗[K] L → 𝔸_L^∞`, and show that the latter map
is an isomorphism.

## Main definitions

* `FiniteAdeleRing.baseChangeEquiv : L ⊗[K] FiniteAdeleRing A K ≃ₐ[L] FiniteAdeleRing B L`

## Main theorems

* `IsDedekindDomain.HeightOneSpectrum.valued_adicCompletionComap A K L B v w pf` :
  If w|v are nonzero primes of B and A, and if x ∈ K_v ⊆ L_w, then w(x)=v(x)^e
  where e is the global ramification index of w/v.

* `IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionComapLinearMap_surjective A K L B v` :
  The canonical map L ⊗ Kᵥ → ∏_{w|v} L_w is surjective.

## TODO

The canonical map L ⊗ Kᵥ → ∏_{w|v} L_w is injective.

-/

open scoped Multiplicative Valued

/-!

The general "AKLB" set-up. `K` is the field of fractions of the Dedekind domain `A`,
`L/K` is a finite separable extension, and `B` is the integral closure of `A` in `L`.

-/

variable (A K L B : Type*) [CommRing A] [CommRing B] [Algebra A B] [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K] [Algebra B L] [IsDedekindDomain A]
    [Algebra K L] [Algebra A L] [IsScalarTower A B L] [IsScalarTower A K L]
    [IsIntegralClosure B A L] [FiniteDimensional K L] [Algebra.IsSeparable K L]

/-!

Under these hypotheses, we can prove the following:

`[IsDomain B]`
`[Alegbra.IsIntegral A B]`
`[Module.Finite A B]`
`[IsDedekindDomain B]`
`[IsFractionRing B L]`

However none of these facts are available to typeclass inference because they all use
variables such as `K` which are not mentioned in the statement so are unfindable by
Lean 4's typeclass system. We thus introduce them as variables when needed.

-/
example : IsDomain B := by
  have foo : Function.Injective (algebraMap B L) := IsIntegralClosure.algebraMap_injective' A
  have bar : IsDomain L := inferInstance
  exact Function.Injective.isDomain _ foo -- exact? failed
variable [IsDomain B]

example : Algebra.IsIntegral A B := IsIntegralClosure.isIntegral_algebra A L
variable [Algebra.IsIntegral A B]

example : IsDedekindDomain B := IsIntegralClosure.isDedekindDomain A K L B
variable [IsDedekindDomain B]

example : IsFractionRing B L := IsIntegralClosure.isFractionRing_of_finite_extension A K L B
variable [IsFractionRing B L]

example : Module.Finite A B :=
  have := IsIntegralClosure.isNoetherian A K L B
  Module.IsNoetherian.finite A B
-- variable [Module.Finite A B] -- we'll need this later

example : FaithfulSMul A B := FaithfulSMul.of_field_isFractionRing A B K L
-- variable [FaithfulSMul A B] -- we'll need this later

namespace IsDedekindDomain

namespace HeightOneSpectrum

variable (v : HeightOneSpectrum A)

variable {B L} in
/-- If B/A is an integral extension of Dedekind domains, `comap w` is the pullback
of the nonzero prime `w` to `A`. -/
def comap (w : HeightOneSpectrum B) : HeightOneSpectrum A where
  asIdeal := w.asIdeal.comap (algebraMap A B)
  isPrime := Ideal.comap_isPrime (algebraMap A B) w.asIdeal
  ne_bot := mt Ideal.eq_bot_of_comap_eq_bot w.ne_bot

variable {A} in
/-- If `B` is an `A`-algebra and `v : HeightOneSpectrum A` is a nonzero prime,
then `v.Extension B` is the subtype of `HeightOneSpeectrum B` consisting of valuations of `B`
which restrict to `v`. -/
def Extension (v : HeightOneSpectrum A) := {w : HeightOneSpectrum B // w.comap A = v}

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

/-- If w | v then for a ∈ A we have w(a)=v(a)^e where e is the ramification index. -/
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

omit [IsIntegralClosure B A L] [FiniteDimensional K L] [Algebra.IsSeparable K L] in
/-- If w | v then for x ∈ K we have w(x)=v(x)^e where e is the ramification index. -/
lemma valuation_comap (w : HeightOneSpectrum B) (x : K) :
    (comap A w).valuation K x ^
      (Ideal.ramificationIdx (algebraMap A B) (comap A w).asIdeal w.asIdeal) =
    w.valuation L (algebraMap K L x) := by
  obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective (A := A) x
  simp [valuation, ← IsScalarTower.algebraMap_apply A K L, IsScalarTower.algebraMap_apply A B L,
    ← intValuation_comap A B (algebraMap_injective_of_field_isFractionRing A B K L), div_pow]

/--
If we have an AKLB set-up, and `w` is a valuation on `L` extending `v` on `K`,
then `σ v w` is the ring homomorphism from (K with valuation v) to (L with valuation w).
More precisely, by (K with valuation v) we mean the
type synonym `WithVal (HeightOneSpectrum.valuation K v)`, which is `K` equipped with
the instance `Valued K Γ₀` coming from `v`. In particular this type synonym has
a canonical valuation, topology, and uniform addive group structure. It is shown
that `σ v w` is continuous.
-/
local notation "σ" => fun v w => algebraMap (WithVal (HeightOneSpectrum.valuation K v))
    (WithVal (HeightOneSpectrum.valuation L w))

omit [IsIntegralClosure B A L] [FiniteDimensional K L] [Algebra.IsSeparable K L] in
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
  _ ≤ e a := by
    simp only [nsmul_eq_mul, e_apply, Units.val_le_val, OrderIsoClass.map_le_map_iff]
    rw [mul_comm]
    exact Int.mul_le_of_le_ediv (by positivity) le_rfl

/-- If w of L divides v of K, `adicCompletionComapSemialgHom v w pf` is the canonical map
`Kᵥ → L_w` lying above `K → L`. Here we actually use the type synonyms `WithVal K` and `WithVal L`.
-/
noncomputable def adicCompletionComapSemialgHom (v : HeightOneSpectrum A) (w : HeightOneSpectrum B)
    (hvw : w.comap A = v) :
    v.adicCompletion K →ₛₐ[σ v w] w.adicCompletion L :=
  UniformSpace.Completion.mapSemialgHom _ <|
  IsDedekindDomain.HeightOneSpectrum.adicValued.continuous_algebraMap A K L B v w hvw

omit [IsIntegralClosure B A L] [FiniteDimensional K L] [Algebra.IsSeparable K L] in
/-- The square with sides K → K_v → L_w and K → L → L_w commutes. -/
lemma adicCompletionComap_coe
    (v : HeightOneSpectrum A) (w : HeightOneSpectrum B) (hvw : w.comap A = v) (x : K) :
    adicCompletionComapSemialgHom A K L B v w hvw x = algebraMap K L x :=
  (adicCompletionComapSemialgHom A K L B v w hvw).commutes x

omit [IsIntegralClosure B A L] [FiniteDimensional K L] [Algebra.IsSeparable K L] in
open WithZeroTopology in
/--
The local ramification index for the extension L_w/K_v is equal to the global ramification
index for the extension w/v. In other words, if x in K_v and i:K_v->L_w then w(i(x))=v(x)^e
where e is computed globally.
-/
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

variable [FaithfulSMul A B] in
omit [IsIntegralClosure B A L] [FiniteDimensional K L] [Algebra.IsSeparable K L] in
/-- The canonical map K_v → L_w sends 𝓞_v to 𝓞_w. -/
lemma adicCompletionComapSemialgHom.mapadicCompletionIntegers (v : HeightOneSpectrum A)
    (w : HeightOneSpectrum B) (hvw : w.comap A = v) :
    (adicCompletionComapSemialgHom A K L B v w hvw) '' (v.adicCompletionIntegers K) ≤
    w.adicCompletionIntegers L := by
  rintro y ⟨x, hx, rfl⟩
  rw [SetLike.mem_coe, mem_adicCompletionIntegers] at hx ⊢
  rw [valued_adicCompletionComap A K L B v w hvw]
  rwa [pow_le_one_iff]
  apply Ideal.IsDedekindDomain.ramificationIdx_ne_zero _ w.isPrime
  · rw [Ideal.map_le_iff_le_comap]
    rfl
  · rw [hvw]
    apply Ideal.map_ne_bot_of_ne_bot v.ne_bot

include K L in
omit [IsDedekindDomain A] [IsIntegralClosure B A L] [FiniteDimensional K L]
    [Algebra.IsSeparable K L] [Algebra.IsIntegral A B] [IsDedekindDomain B] [IsFractionRing B L] in
lemma noZeroSMulDivisors : NoZeroSMulDivisors A B := by
  have := FaithfulSMul.of_field_isFractionRing A B K L
  infer_instance

include K L in
omit [IsIntegralClosure B A L] [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [IsFractionRing B L] in
/-- There are only finitely many nonzero primes of B above a nonzero prime of A. -/
theorem Extension.finite (v : HeightOneSpectrum A) : Finite (v.Extension B) := by
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

/-- The K_v-algebra structure on L_w when w | v. -/
noncomputable
def comap_algebra {v : HeightOneSpectrum A} {w : HeightOneSpectrum B} (h : w.comap A = v) :
    Algebra (v.adicCompletion K) (w.adicCompletion L) :=
  (adicCompletionComapSemialgHom A K L B v w h).toAlgebra

/-- The canonical map `K_v → ∏_{w|v} L_w` extending K → L. -/
noncomputable def adicCompletionComapSemialgHom' (v : HeightOneSpectrum A) :
  v.adicCompletion K →ₛₐ[algebraMap K L] ∀ w : v.Extension B, w.1.adicCompletion L :=
  Pi.semialgHom _ _ fun i ↦ adicCompletionComapSemialgHom A K L B v i.1 i.2

/-- The K_v-algebra structure on ∏_{w|v} L_w. -/
noncomputable instance comap_pi_algebra (v : HeightOneSpectrum A) :
    Algebra (v.adicCompletion K) (Π (w : v.Extension B), w.1.adicCompletion L) :=
  (adicCompletionComapSemialgHom' A K L B v).toAlgebra

open scoped TensorProduct -- ⊗ notation for tensor product

/-- The canonical ring homomorphism `L ⊗_K K_v → ∏_{w|v} L_w` as an `L`-algebra map. -/
noncomputable def tensorAdicCompletionComapAlgHom (v : HeightOneSpectrum A) :
    L ⊗[K] adicCompletion K v →ₐ[L] Π w : v.Extension B, w.1.adicCompletion L :=
  SemialgHom.baseChange_of_algebraMap (adicCompletionComapSemialgHom' A K L B v)

omit [IsIntegralClosure B A L] [FiniteDimensional K L] [Algebra.IsSeparable K L] in
lemma tensorAdicCompletionComapAlgHom_tmul_apply (v : HeightOneSpectrum A) (x y i) :
  tensorAdicCompletionComapAlgHom A K L B v (x ⊗ₜ y) i =
    x • adicCompletionComapSemialgHom A K L B v i.1 i.2 y := by
  simp_rw [Algebra.smul_def]
  rfl

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
/-- The canonical ring homomorphism `L ⊗_K K_v → ∏_{w|v} L_w` as an `K_v`-linear map. -/
noncomputable def tensorAdicCompletionComapLinearMap :
    letI := comap_pi_algebra A K L B v |>.toModule
    L ⊗[K] adicCompletion K v →ₗ[adicCompletion K v]
    (w : Extension B v) → adicCompletion L w.val :=
  SemialgHom.baseChangeRightOfAlgebraMap (adicCompletionComapSemialgHom' A K L B v)
    |>.toLinearMap

section ModuleTopology

open WithZeroMulInt Valued

-- Make (v.adicCompletion K) a normed field.
-- This exists for number fields in Mathlib, but not for general Dedekind Domains.
-- v.asIdeal.absNorm may be 0, so just use 2 as the base for the norm.
/-- The data of a rank 1 (ℝ-valued) valuation on K_v. -/
noncomputable local instance adicCompletion_RkOne :
    Valuation.RankOne (Valued.v : Valuation (adicCompletion K v) ℤₘ₀) where
  hom := {
    toFun := toNNReal (by norm_num : (2 : NNReal) ≠ 0)
    map_zero' := rfl
    map_one' := rfl
    map_mul' := MonoidWithZeroHom.map_mul (toNNReal (by norm_num))
  }
  strictMono' := toNNReal_strictMono (by norm_num)
  nontrivial' := by
    obtain ⟨x, hx1, hx2⟩ := Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot
    use algebraMap A K x
    rw [valuedAdicCompletion_eq_valuation' v (algebraMap A K x)]
    constructor
    · simpa only [ne_eq, map_eq_zero, FaithfulSMul.algebraMap_eq_zero_iff]
    · apply ne_of_lt
      rwa [valuation_eq_intValuationDef, intValuation_lt_one_iff_dvd, Ideal.dvd_span_singleton]

omit [IsIntegralClosure B A L] [FiniteDimensional K L] [Algebra.IsSeparable K L] in
/-- The map K_v → L_w is continuous. -/
lemma adicCompletionComapSemialgHom_continuous
    (v : HeightOneSpectrum A) (w : HeightOneSpectrum B) (hvw : w.comap A = v) :
    Continuous (adicCompletionComapSemialgHom A K L B v w hvw) :=
  UniformSpace.Completion.continuous_extension (β := (adicCompletion L w))

omit [IsIntegralClosure B A L] [FiniteDimensional K L] [Algebra.IsSeparable K L] in
/-- The K_v-action on L_w is continuous. -/
lemma comap_algebra_continuousSmul (v : HeightOneSpectrum A) (w : HeightOneSpectrum B)
    (hvw : comap A w = v) :
    letI := comap_algebra A K L B hvw
    ContinuousSMul (adicCompletion K v) (adicCompletion L w) := by
  let inst_alg := comap_algebra A K L B hvw
  constructor
  have leftCts := adicCompletionComapSemialgHom_continuous A K L B v w hvw
  exact Continuous.mul (Continuous.fst' leftCts) continuous_snd

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
omit [IsIntegralClosure B A L] [Algebra.IsSeparable K L] in
/-- The canonical map `L ⊗[K] K_v → ∏_{w|v} L_w` is surjective. -/
lemma tensorAdicCompletionComapLinearMap_surjective (v : HeightOneSpectrum A) :
    Function.Surjective (tensorAdicCompletionComapLinearMap A K L B v) := by
  letI : Module (adicCompletion K v) ((w : Extension B v) → adicCompletion L w.val) :=
    comap_pi_algebra A K L B v |>.toModule
  let _ (w : Extension B v) : SMul (adicCompletion K v) (adicCompletion L w.val) :=
    comap_algebra A K L B w.prop |>.toSMul
  let _ (w : Extension B v) : ContinuousSMul (adicCompletion K v) (adicCompletion L w.val) :=
    comap_algebra_continuousSmul A K L B v w.val w.prop
  let f' := tensorAdicCompletionComapLinearMap A K L B v
  let s : Submodule (adicCompletion K v) ((w : Extension B v) → adicCompletion L w.val) :=
    LinearMap.range f'
  have hFinite : Module.Finite (adicCompletion K v) s := Module.Finite.range f'
  have isClosed : IsClosed s.carrier :=
    Submodule.closed_of_finiteDimensional (E := (w : Extension B v) → adicCompletion L w.val) s
  rw [← LinearMap.range_eq_top, Submodule.eq_top_iff']
  simp_rw [← Submodule.mem_toAddSubmonoid, ← AddSubmonoid.mem_toSubsemigroup,
      ← AddSubsemigroup.mem_carrier]
  have denseL : DenseRange (algebraMap L ((w : Extension B v) → adicCompletion L w.val)) := by
    have := Extension.finite A K L B v
    let _ := Fintype.ofFinite <| Extension B v
    exact denseRange_of_prodAlgebraMap _ Subtype.val_injective
  rw [← isClosed.closure_eq]
  apply Dense.mono _ denseL
  rintro _ ⟨l, rfl⟩
  use (l ⊗ₜ 1)
  ext w
  simp [tensorAdicCompletionComapLinearMap, f']

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
omit [IsIntegralClosure B A L] [Algebra.IsSeparable K L] in
/-- ∏_{w|v} L_w is a finite K_v-module. -/
theorem comap_pi_algebra_finite (v : HeightOneSpectrum A) :
    letI := comap_pi_algebra A K L B v |>.toModule
    Module.Finite (adicCompletion K v) (Π w : v.Extension B, w.1.adicCompletion L) :=
  letI := comap_pi_algebra A K L B v |>.toModule
  Module.Finite.of_surjective (tensorAdicCompletionComapLinearMap A K L B v)
    (tensorAdicCompletionComapLinearMap_surjective A K L B v)

omit [IsIntegralClosure B A L] [Algebra.IsSeparable K L] in
/-- L_w is a finite K_v-module if w | v. -/
theorem comap_algebra_finite (v : HeightOneSpectrum A) (w : HeightOneSpectrum B)
    (hvw : comap A w = v) :
    letI := comap_algebra A K L B hvw
    Module.Finite (adicCompletion K v) (adicCompletion L w) :=
  have := comap_pi_algebra_finite A K L B v
  let _ (w : Extension B v) := comap_algebra A K L B w.prop |>.toModule
  Module.Finite.of_pi (fun (w : Extension B v) => w.1.adicCompletion L) ⟨w, hvw⟩

omit [IsIntegralClosure B A L] [Algebra.IsSeparable K L] in
/-- L_w has the K_v-module topology. -/
lemma adicCompletionComap_isModuleTopology
    (v : HeightOneSpectrum A) (w : HeightOneSpectrum B) (hvw : w.comap A = v) :
    -- temporarily make L_w a K_v-algebra
    letI := comap_algebra A K L B hvw
    -- then claim that L_w has the module topology.
    IsModuleTopology (v.adicCompletion K) (w.adicCompletion L) := by
  let Kv := adicCompletion K v
  let Lw := adicCompletion L w
  let _ : Algebra Kv Lw := comap_algebra A K L B hvw
  have : ContinuousSMul Kv Lw := comap_algebra_continuousSmul A K L B v w hvw
  have : Module.Finite Kv Lw := comap_algebra_finite A K L B v w hvw
  let iso : ((Fin (Module.finrank Kv Lw)) → Kv) ≃L[Kv] Lw :=
    ContinuousLinearEquiv.ofFinrankEq (Module.finrank_fin_fun Kv)
  apply IsModuleTopology.iso iso

omit [IsIntegralClosure B A L] [Algebra.IsSeparable K L] in
/-- ∏_{w|v} L_w has the K_v-module topology. -/
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
  let _ := Extension.finite A K L B v
  exact IsModuleTopology.instPi

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
variable (v : HeightOneSpectrum A) in
noncomputable
instance : TopologicalSpace (L ⊗[K] adicCompletion K v) := moduleTopology (adicCompletion K v) _

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
variable (v : HeightOneSpectrum A) in
instance : IsModuleTopology (adicCompletion K v) (L ⊗[K] adicCompletion K v) :=
  ⟨rfl⟩

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
omit [IsIntegralClosure B A L] [Algebra.IsSeparable K L] in
/-- `tensorAdicCompletionComapLinearMap` is continuous, open and surjective.
  We later show that it's a homeomorphism. -/
lemma tensorAdicCompletionComapLinearMap_isOpenQuotientMap (v : HeightOneSpectrum A) :
    IsOpenQuotientMap (tensorAdicCompletionComapLinearMap A K L B v) := by
  have : T2Space (L ⊗[K] adicCompletion K v) :=
    IsModuleTopology.t2Space' (K := (adicCompletion K v))
  let _ (w : Extension B v) : SMul (adicCompletion K v) (adicCompletion L w.val) :=
    comap_algebra A K L B w.prop |>.toSMul
  let _ (w : Extension B v) : ContinuousSMul (adicCompletion K v) (adicCompletion L w.val) :=
    comap_algebra_continuousSmul A K L B v w.val w.prop
  have := IsModuleTopology.topologicalAddGroup (adicCompletion K v) (L ⊗[K] adicCompletion K v)
  have := comap_pi_algebra_finite A K L B v
  have hsurj := tensorAdicCompletionComapLinearMap_surjective A K L B v

  exact ⟨hsurj, LinearMap.continuous_of_finiteDimensional _,
    LinearMap.isOpenMap_of_finiteDimensional _ hsurj⟩

-- TODO : this local instance should not be required, see mathlib PR #22488 for potential fix
attribute [local instance 9999] SMulCommClass.of_commMonoid TensorProduct.isScalarTower_left
  IsScalarTower.right Algebra.toSMul

/-- The triangle A → 𝓞_v → K_v commutes. -/
instance (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] (v : HeightOneSpectrum R) :
    IsScalarTower R (v.adicCompletionIntegers K) (v.adicCompletion K) :=
  ⟨fun x y z ↦ by exact smul_mul_assoc x y.1 z⟩

/-- 𝓞_v as an A-subalgebra of K_v. --/
noncomputable
def adicCompletionIntegersSubalgebra {R : Type*} (K : Type*) [CommRing R]
    [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K] (v : HeightOneSpectrum R) :
    Subalgebra R (HeightOneSpectrum.adicCompletion K v) where
  __ := HeightOneSpectrum.adicCompletionIntegers K v
  algebraMap_mem' r := coe_mem_adicCompletionIntegers v r

/-- The canonical B-algebra map `B ⊗[A] 𝓞_v → L ⊗[K] K_v` -/
noncomputable def tensorAdicCompletionIntegersTo (v : HeightOneSpectrum A) :
    B ⊗[A] adicCompletionIntegers K v →ₐ[B] L ⊗[K] adicCompletion K v :=
  Algebra.TensorProduct.lift
    ((Algebra.TensorProduct.includeLeft).comp (Algebra.ofId B L))
    ((Algebra.TensorProduct.includeRight.restrictScalars A).comp (IsScalarTower.toAlgHom _ _ _))
    (fun _ _ ↦ .all _ _)

omit [IsIntegralClosure B A L] [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [IsDomain B] [Algebra.IsIntegral A B] [IsDedekindDomain B]
    [IsFractionRing B L] in
/-- The image of `B ⊗[A] 𝓞_v` in `L ⊗[K] K_v` is contained in the closure of the image of `B`. -/
lemma tensorAdicCompletionIntegersToRange_subset_closureIntegers :
  (tensorAdicCompletionIntegersTo A K L B v).range.carrier ⊆
      closure (algebraMap B (L ⊗[K] adicCompletion K v)).range := by
  rintro _ ⟨s, rfl⟩
  induction s with
    | zero =>
        apply subset_closure
        use 0
        simp
    | add x y hx hy =>
        -- The closure of a subgroup is a subgroup
        rw [RingHom.map_add]
        letI : SMul (adicCompletion K v) (L ⊗[K] adicCompletion K v) :=
            Algebra.TensorProduct.rightAlgebra |>.toSMul
        apply map_mem_closure₂ _ hx hy _
        . exact (ModuleTopology.continuousAdd _ _).continuous_add
        intro _ ha _ hb
        exact add_mem ha hb
    | tmul b a' =>
        -- Rewrite `tensorAdicCompletionIntegersTo (b ⊗ₜ a')` to `b • (1 ⊗ₜ a')`
        simp only [RingHom.coe_range, tensorAdicCompletionIntegersTo, Algebra.comp_ofId,
          AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.lift_tmul,
          AlgHom.coe_comp, AlgHom.coe_restrictScalars', IsScalarTower.coe_toAlgHom',
          Function.comp_apply, ValuationSubring.algebraMap_apply,
          Algebra.TensorProduct.includeRight_apply]
        -- Now, `f : a' ↦ b • (1 ⊗ₜ a')` is continuous
        letI : SMul (adicCompletion K v) (L ⊗[K] adicCompletion K v) :=
            Algebra.TensorProduct.rightAlgebra |>.toSMul
        let f (y : ↥(adicCompletionIntegers K v)) : (L ⊗[K] adicCompletion K v) :=
          (Algebra.ofId B (L ⊗[K] adicCompletion K v)) b * (1 : L) ⊗ₜ[K] (y : adicCompletion K v)
        have hfval : f = fun (y : ↥(adicCompletionIntegers K v)) =>
              (y : adicCompletion K v) • (Algebra.ofId B (L ⊗[K] adicCompletion K v)) b := by
          ext y
          unfold f
          exact mul_comm _ _
        have hcf : ContinuousAt f a' := by
          apply Continuous.continuousAt
          rw [hfval]
          apply Continuous.smul continuous_subtype_val continuous_const
        -- So, because `A` is dense in `𝒪_v`, `b • (1 ⊗ₜ a') ∈ f '' closure A ⊆ closure f '' A`
        have hy : a' ∈ closure (Set.range (algebraMap A _)) := by
          apply denseRange_of_integerAlgebraMap
        apply mem_closure_image hcf hy
        constructor
        . exact isClosed_closure
        -- Finally, `b • (1 ⊗ₜ a) = (b * a) • (1 ⊗ₜ 1)`, so `f '' A ⊆ algebraMap '' B`
        rintro u ⟨_, ⟨a, rfl⟩, rfl⟩
        apply subset_closure
        use algebraMap A B a * b
        unfold f
        rw [Algebra.algebraMap_eq_smul_one (A := (adicCompletionIntegers K v)) a,
          coe_smul_adicCompletionIntegers, ← TensorProduct.smul_tmul, Algebra.ofId_apply,
          Algebra.TensorProduct.algebraMap_apply, RingHom.map_mul, ← Algebra.smul_def]
        simp

open TensorProduct.AlgebraTensorModule in
attribute [local instance] Algebra.TensorProduct.rightAlgebra in
omit [Algebra.IsSeparable K L] [IsDomain B] [Algebra.IsIntegral A B]
    [IsDedekindDomain B] [IsFractionRing B L]  in
/-- The image of `B ⊗[A] 𝓞_v` in `L ⊗[K] K_v` is clopen. -/
lemma tensorAdicCompletionIsClopenRange :
    IsClopen (SetLike.coe (tensorAdicCompletionIntegersTo A K L B v).range) := by
  -- `B ⊗[A] 𝒪_v` is a subgroup of `L ⊗[K] K_v`, so we can show it's closed
  -- by showing that it's open. **TODO** split into IsOpen + IsClosed lemmas?
  rw [← Subalgebra.coe_toSubring, ← Subring.coe_toAddSubgroup]
  have := ModuleTopology.continuousAdd (adicCompletion K v) (L ⊗[K] adicCompletion K v)
  refine OpenAddSubgroup.isClopen ⟨_, ?_⟩
  -- Further, we can show `B ⊗[A] 𝒪_v` is open by showing that it contains an
  -- open neighbourhood of 0.
  apply AddSubgroup.isOpen_of_zero_mem_interior
  rw [mem_interior, Subring.coe_toAddSubgroup, Subalgebra.coe_toSubring]

  -- Take a basis `b` of `L` over `K` with elements in `B` and use it to
  -- get a basis `b'` of `L ⊗[K] K_v` over `K_v`.
  obtain ⟨ι, b, hb⟩ := FiniteDimensional.exists_is_basis_integral A K L
  let b' : Basis ι (adicCompletion K v) (L ⊗[K] (adicCompletion K v)) := by
    classical
    exact Basis.rightBaseChange L b
  -- Use the basis to get a continuous equivalence from `L ⊗[K] K_v` to `ι → K_v`.
  let equiv : L ⊗[K] (adicCompletion K v) ≃L[K] (ι → adicCompletion K v) :=
    IsModuleTopology.continuousLinearEquiv (b'.equivFun) |>.restrictScalars K

  -- Use the preimage of `∏ 𝒪_v` as the open neighbourhood.
  use equiv.symm '' (Set.pi Set.univ (fun _ => SetLike.coe (adicCompletionIntegers K v)))
  refine ⟨?_, ?_, by simp [ValuationSubring.zero_mem]⟩
  . intro t ⟨g, hg, ht⟩
    -- We have `t = equiv g = ∑ i, b i ⊗ g i`, since `g in ∏ 𝒪_v` and
    -- `b i ∈ (algebraMap B L).range`, this is `tensorAdicCompletionIntegersTo`
    -- of some element of `B ⊗[A] 𝒪_v`
    have hf : ∀ (i : ι), ∃ (w : B), (algebraMap B L w) = (b i) := by
      intro i
      apply IsIntegralClosure.isIntegral_iff.mp (hb i)
    choose f hf_prop using hf
    have hf_prop' : ∀ (i : ι), (algebraMap B (L ⊗[K] adicCompletion K v) (f i)) = (b i) ⊗ₜ 1 := by
      intro i
      rw [Algebra.TensorProduct.algebraMap_apply, hf_prop]
    use ∑ (i : ι), (f i) ⊗ₜ ⟨g i, hg i trivial⟩
    let _ : NonAssocSemiring (B ⊗[A] (adicCompletionIntegers K v)) :=
      Algebra.TensorProduct.instNonAssocSemiring
    let _ : AddMonoidHomClass (B ⊗[A] (adicCompletionIntegers K v) →+* L ⊗[K] adicCompletion K v)
        (B ⊗[A] (adicCompletionIntegers K v)) (L ⊗[K] adicCompletion K v) :=
      RingHomClass.toAddMonoidHomClass
    rw [map_sum, ← ht]
    unfold equiv
    rw [ContinuousLinearEquiv.restrictScalars_symm_apply,
      IsModuleTopology.continuousLinearEquiv_symm_apply,
      Basis.equivFun_symm_apply]
    apply Finset.sum_congr rfl
    intro x
    have : (algebraMap _ (L ⊗[K] adicCompletion K v)) (g x) = 1 ⊗ₜ[K] (g x) := rfl
    simp [Algebra.smul_def, Algebra.ofId_apply, tensorAdicCompletionIntegersTo, hf_prop',
        b', this]
  . rw [ContinuousLinearEquiv.image_symm_eq_preimage]
    apply IsOpen.preimage equiv.continuous
    apply isOpen_set_pi Set.finite_univ
    rintro i -
    exact Valued.valuationSubring_isOpen (v.adicCompletion K)

omit [Algebra.IsSeparable K L] [IsDomain B] [Algebra.IsIntegral A B]
    [IsDedekindDomain B] [IsFractionRing B L] in
/-- The image of `B ⊗[A] 𝓞_v` in `L ⊗[K] K_v` is the closure of the image of `B`. -/
lemma tensorAdicCompletionIntegersToRange_eq_closureIntegers :
    SetLike.coe (tensorAdicCompletionIntegersTo A K L B v).range =
        closure (algebraMap B (L ⊗[K] adicCompletion K v)).range := by
  apply Set.Subset.antisymm
  . apply tensorAdicCompletionIntegersToRange_subset_closureIntegers
  . apply closure_minimal
    . rintro _ ⟨b, rfl⟩
      apply algebraMap_mem
    . apply IsClopen.isClosed
      apply tensorAdicCompletionIsClopenRange

omit [Algebra A L] [IsScalarTower A B L] [IsIntegralClosure B A L] in
/-- The `B`-subalgebra `∏_{w|v} 𝓞_w` of `∏_{w|v} L_w` is the closure of the image of `B`. -/
lemma prodAdicCompletionsIntegers_eq_closureIntegers :
    SetLike.coe (Subalgebra.pi (R := B) Set.univ
      (fun (w : Extension B v) ↦ adicCompletionIntegersSubalgebra L w.1)) =
    closure (SetLike.coe (algebraMap B _).range) := by
  rw [Subalgebra.coe_pi]
  let _ (w : Extension B v) : Module B (adicCompletion L w.val) :=
    UniformSpace.Completion.instModule
  show SetLike.coe (Submodule.pi _ _) = _
  rw [Submodule.coe_pi]
  let val := (fun (w : Extension B v) ↦ w.1)
  have hinj : Function.Injective val :=
    (Set.injective_codRestrict Subtype.property).mp fun _ _ a ↦ a
  rw [closureAlgebraMapIntegers_eq_prodIntegers L val hinj]
  rfl

omit [Algebra.IsSeparable K L] in
/-- The image of `B ⊗[A] 𝓞_v` (the closure of `B`) in `∏_w L_w` is closed. -/
lemma adicCompletionComapAlgHom_map_closure_is_closed :
    IsClosed ((tensorAdicCompletionComapAlgHom A K L B v) ''
        closure (algebraMap B (L ⊗[K] adicCompletion K v)).range) := by
  let S := AddSubgroup.map
      (tensorAdicCompletionComapAlgHom A K L B v).toAddMonoidHom
      (tensorAdicCompletionIntegersTo A K L B v).range.toSubring.toAddSubgroup
  have hSclosed : IsClosed S.carrier := by
    apply AddSubgroup.isClosed_of_isOpen
    apply (tensorAdicCompletionComapLinearMap_isOpenQuotientMap A K L B v).isOpenMap
    apply (tensorAdicCompletionIsClopenRange A K L B v).isOpen
  suffices h : (tensorAdicCompletionComapAlgHom A K L B v) ''
    closure ↑(algebraMap B (L ⊗[K] adicCompletion K v)).range = S.carrier by
    rwa [h]
  rw [← tensorAdicCompletionIntegersToRange_eq_closureIntegers]
  rfl

instance : MulActionHomClass
    (L ⊗[K] adicCompletion K v →ₐ[L] (w : Extension B v) → adicCompletion L w.1) B
    (L ⊗[K] adicCompletion K v) ((w : Extension B v) → adicCompletion L w.1) where
  map_smulₛₗ φ b x := by
    rw [← IsScalarTower.algebraMap_smul L, AlgHom.map_smul_of_tower,
      IsScalarTower.algebraMap_smul, id_def]

instance : OneHomClass
    (L ⊗[K] adicCompletion K v →ₐ[L] (w : Extension B v) → adicCompletion L w.1)
    (L ⊗[K] adicCompletion K v) ((w : Extension B v) → adicCompletion L w.1) where
  map_one f := f.toRingHom.map_one

omit [Algebra.IsSeparable K L] in
/-- The image of `B ⊗[A] 𝓞_v` in `∏_w L_w` is `∏_w 𝓞_w`. -/
theorem adicCompletionComapAlgEquiv_integral :
    AlgHom.range (((tensorAdicCompletionComapAlgHom A K L B v).restrictScalars B).comp
      (tensorAdicCompletionIntegersTo A K L B v)) =
    Subalgebra.pi Set.univ (fun _ ↦ adicCompletionIntegersSubalgebra _ _) := by
  have hlhs := tensorAdicCompletionIntegersToRange_eq_closureIntegers
  have hrhs := prodAdicCompletionsIntegers_eq_closureIntegers
  have hrange :
    SetLike.coe (algebraMap B ((w : Extension B v) → adicCompletion L w.1)).range =
      (tensorAdicCompletionComapAlgHom A K L B v) ''
      SetLike.coe (algebraMap B (L ⊗[K] adicCompletion K v)).range := by
    ext x
    simp [Algebra.algebraMap_eq_smul_one, AlgHom.map_smul_of_tower]
  have hrange' := adicCompletionComapAlgHom_map_closure_is_closed A K L B v
  rw [AlgHom.range_comp, ← SetLike.coe_set_eq, Subalgebra.coe_map, AlgHom.coe_restrictScalars',
      hlhs, hrhs, hrange, ← IsClosed.closure_eq hrange']
  exact closure_image_closure
    (tensorAdicCompletionComapLinearMap_isOpenQuotientMap A K L B v).continuous

attribute [local instance 9999] SMulCommClass.of_commMonoid TensorProduct.isScalarTower_left
  IsScalarTower.right

-- **TODO**: Mathlib#23590 will provide these instances in more generality.
/-- The restriction of `adicCompletionComapSemialgHom` to a map `𝓞_v → 𝓞_w`. -/
noncomputable def adicCompletionComapIntegerRingHom (v : HeightOneSpectrum A)
    (w : HeightOneSpectrum B) (h : w.comap A = v) :
    v.adicCompletionIntegers K →+* w.adicCompletionIntegers L where
  toFun x :=
    letI := FaithfulSMul.of_field_isFractionRing A B K L
    ⟨adicCompletionComapSemialgHom A K L B v w h x,
     adicCompletionComapSemialgHom.mapadicCompletionIntegers A K L B v w h ⟨x, x.prop, rfl⟩⟩
  map_zero' := by ext; simp
  map_one' := by ext; simp
  map_add' x y := by ext; simp
  map_mul' x y := by ext; simp

/-- If `w` is an extension of `v`, then `𝓞_w` is naturally an `𝓞_v`-algebra. -/
noncomputable
def comap_integer_algebra {v : HeightOneSpectrum A} {w : HeightOneSpectrum B} (h : w.comap A = v) :
    Algebra (v.adicCompletionIntegers K) (w.adicCompletionIntegers L) :=
  (adicCompletionComapIntegerRingHom A K L B v w h).toAlgebra

omit [IsIntegralClosure B A L] [FiniteDimensional K L] [Algebra.IsSeparable K L] in
lemma comap_integer_algebraMap {v : HeightOneSpectrum A} {w : HeightOneSpectrum B}
    (h : w.comap A = v) (x : v.adicCompletionIntegers K) :
    letI := comap_integer_algebra A K L B h
    algebraMap (v.adicCompletionIntegers K) (w.adicCompletionIntegers L) x =
    (adicCompletionComapSemialgHom A K L B v w h) x.val :=
  rfl

variable {v} in
/-- If `w` is an extension of `v`, then `L_w` is naturally an `𝓞_v`-algebra. -/
noncomputable def comap_integer_algebra' {w : HeightOneSpectrum B} (hvw : comap A w = v) :=
  letI := comap_algebra A K L B hvw
  RingHom.toAlgebra <| (algebraMap (adicCompletion K v) (adicCompletion L w)).comp
    (algebraMap (adicCompletionIntegers K v) (adicCompletion K v))

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
/-- `tensorAdicCompletionIntegersTo` as an 𝓞_v-linear map. -/
noncomputable def tensorAdicCompletionIntegersToLinearMap :
    (B ⊗[A] adicCompletionIntegers K v) →ₗ[adicCompletionIntegers K v]
      (L ⊗[K] adicCompletion K v) where
  __ := tensorAdicCompletionIntegersTo A K L B v
  map_smul' x y := by
    simp [Algebra.smul_def, tensorAdicCompletionIntegersTo, RingHom.algebraMap_toAlgebra]
    rfl

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
omit [Algebra.IsSeparable K L] in
/-- The map `B ⊗ 𝓞_v → L_w` for `w` an extension of `v` given by the algebra maps. -/
noncomputable def adicCompletionComapIntegerLinearMap (v : HeightOneSpectrum A)
    (w : HeightOneSpectrum B) (hvw : comap A w = v) :
    letI := comap_algebra A K L B hvw
    letI := RingHom.toAlgebra <| (algebraMap (adicCompletion K v) (adicCompletion L w)).comp
      (algebraMap (adicCompletionIntegers K v) (adicCompletion K v))
    B ⊗[A] (adicCompletionIntegers K v) →ₗ[adicCompletionIntegers K v] (adicCompletion L w) :=
  letI := comap_integer_algebra A K L B hvw
  letI (w' : Extension B v) := comap_algebra A K L B w'.prop
  let alg (w' : Extension B v) : Algebra _ _ :=
    RingHom.toAlgebra <| (algebraMap (adicCompletion K v) (adicCompletion L w'.val)).comp
      (algebraMap (adicCompletionIntegers K v) (adicCompletion K v))

  have : LinearMap.CompatibleSMul (L ⊗[K] adicCompletion K v)
      ((w : Extension B v) → adicCompletion L w.val)
      (adicCompletionIntegers K v) (adicCompletion K v) := {
    map_smul f x y := by
      obtain ⟨x, hx⟩ := x
      exact LinearMap.map_smul f x y
  }
  let f : L ⊗[K] adicCompletion K v →ₗ[adicCompletionIntegers K v]
      (w' : Extension B v) → adicCompletion L w'.val :=
    (tensorAdicCompletionComapLinearMap A K L B v).restrictScalars (adicCompletionIntegers K v)
  let g := LinearMap.comp f (tensorAdicCompletionIntegersToLinearMap A K L B v)
  @LinearMap.proj _ _ _ (fun (w : Extension B v) ↦ adicCompletion L w.val) _
    (fun w => (alg w).toModule) ⟨w, hvw⟩ |>.comp g

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
omit [Algebra.IsSeparable K L] in
/-- The range of `adicCompletionComapIntegerLinearMap` is `𝓞_w`. -/
lemma adicCompletionComapIntegerLinearMap_range_eq_integers (v : HeightOneSpectrum A)
    (w : HeightOneSpectrum B) (hvw : comap A w = v) :
    letI := comap_algebra A K L B hvw
    Set.range (adicCompletionComapIntegerLinearMap A K L B v w hvw) =
    adicCompletionIntegers L w := by
  ext x
  have memrange : (Set.range _) = _ :=
    congr_arg SetLike.coe (adicCompletionComapAlgEquiv_integral A K L B v)
  rw [Subalgebra.coe_pi, Submodule.carrier_eq_coe, Submodule.coe_pi, Set.ext_iff] at memrange
  let extension : Extension B v := ⟨w, hvw⟩
  constructor
  . rintro ⟨y, rfl⟩
    exact (memrange _).mp (Set.mem_range_self y) extension trivial
  . intro hx
    classical
    set x' : (w : Extension B v) → adicCompletion L w.val := Pi.single extension x with hx'
    obtain ⟨y, (hy : _ = x')⟩ : x' ∈ Set.range _ := by
      rw [memrange x', Set.mem_pi]
      intro w _
      by_cases h : extension = w
      . rw [← h, hx', Pi.single_eq_same, SetLike.mem_coe]
        exact hx
      . rw [hx', Pi.single_eq_of_ne' h]
        apply Subalgebra.zero_mem
    use y
    simpa [hx'] using congr_fun hy extension


attribute [local instance] Algebra.TensorProduct.rightAlgebra in
attribute [local instance 9999] Algebra.toModule Module.toDistribMulAction
  DistribMulAction.toMulAction in
/-- `𝓞_w` is finite over `𝓞_v`. -/
-- This can be proved for finite extensions of complete discretely valued fields without
-- reference to underlying fields being completed, but this is sufficient for our
-- purposes.
theorem comap_integer_algebra_finite (v : HeightOneSpectrum A) (w : HeightOneSpectrum B)
    (hvw : comap A w = v) :
    letI := comap_integer_algebra A K L B hvw
    Module.Finite (adicCompletionIntegers K v) (adicCompletionIntegers L w) := by
  letI := comap_integer_algebra A K L B hvw
  letI := comap_algebra A K L B hvw
  let hom : (adicCompletionIntegers K v) →+* (adicCompletion L w) :=
    (algebraMap (adicCompletion K v) (adicCompletion L w)).comp
      (algebraMap (adicCompletionIntegers K v) (adicCompletion K v))
  letI := RingHom.toAlgebra hom

  let integerSubmodule : Submodule (adicCompletionIntegers K v) (adicCompletion L w) :=
    have : IsScalarTower (adicCompletionIntegers K v) (adicCompletionIntegers L w)
        (adicCompletion L w) := by
      apply IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
    (adicCompletionIntegers L w).toSubring.toSubmodule.restrictScalars
      (adicCompletionIntegers K v)

  have heq : (LinearMap.range (adicCompletionComapIntegerLinearMap A K L B v w hvw)) =
      integerSubmodule := by
    ext x
    apply adicCompletionComapIntegerLinearMap_range_eq_integers A K L B v w hvw |> Set.ext_iff.mp
  have : Module.Finite A B :=
    have := IsIntegralClosure.isNoetherian A K L B
    Module.IsNoetherian.finite A B
  have := Module.Finite.range (adicCompletionComapIntegerLinearMap A K L B v w hvw)
  apply Module.Finite.equiv <|
    LinearEquiv.ofEq (LinearMap.range (adicCompletionComapIntegerLinearMap A K L B v w hvw)) _ heq

end ModuleTopology

/-- The canonical map `L ⊗[K] K_v → ∏_{w|v} L_w` is bijective. -/
theorem tensorAdicCompletionComapAlgHom_bijective (v : HeightOneSpectrum A) :
    Function.Bijective (tensorAdicCompletionComapAlgHom A K L B v) := by
  show Function.Bijective (tensorAdicCompletionComapLinearMap A K L B v)
  have hsurj := tensorAdicCompletionComapLinearMap_surjective A K L B v
  refine ⟨?_, hsurj⟩
  -- ⊢ Function.Injective ⇑(tensorAdicCompletionComapLinearMap_completion A K L B v)
  -- issue FLT#231; one proof is proof in blueprint at
  -- https://imperialcollegelondon.github.io/FLT/blueprint/Adele_miniproject.html#IsDedekindDomain.HeightOneSpectrum.adicCompletionComapAlgEquiv
  -- and another one might be deduce injectivity from a dimension count.
  -- For that we'd need that local and global e's and f's match up
  -- (e's we have and f's won't be so hard), and then the statement
  -- that the local extension is e*f (in general e * f <= degree (Prop 3.1.3.2 of BGR)
  -- and equality holds for L/K if L is K-cartesian (Prop 3.6.2.4) so for example if K
  -- is complete and discretely-valued (Cor 2.4.3.11).
  sorry

/-- The L-algebra isomorphism `L ⊗[K] K_v ≅ ∏_{w|v} L_w`. -/
noncomputable def adicCompletionComapAlgEquiv (v : HeightOneSpectrum A) :
    L ⊗[K] v.adicCompletion K ≃ₐ[L] (∀ w : v.Extension B, w.1.adicCompletion L) :=
  AlgEquiv.ofBijective (tensorAdicCompletionComapAlgHom A K L B v) <|
    tensorAdicCompletionComapAlgHom_bijective A K L B v


attribute [local instance] Algebra.TensorProduct.rightAlgebra in
/-- The continuous K_v-algebra isomorphism `L ⊗[K] K_v ≅ ∏_{w|v} L_w`. -/
noncomputable def adicCompletionComapRightContinuousAlgEquiv (v : HeightOneSpectrum A) :
    L ⊗[K] v.adicCompletion K ≃A[v.adicCompletion K] (∀ w : v.Extension B, w.1.adicCompletion L) :=
  let _ := comap_pi_algebra A K L B v |>.toSMul
  have : IsModuleTopology (v.adicCompletion K) (∀ w : v.Extension B, w.1.adicCompletion L) :=
    prodAdicCompletionComap_isModuleTopology A K L B v
  IsModuleTopology.continuousAlgEquivOfAlgEquiv {
    __ := SemialgHom.baseChangeRightOfAlgebraMap (adicCompletionComapSemialgHom' A K L B v)
    __ := adicCompletionComapAlgEquiv A K L B v
  }

/-- The continuous L-algebra isomorphism `L ⊗[K] K_v ≅ ∏_{w|v} L_w`. -/
noncomputable def adicCompletionComapContinuousAlgEquiv (v : HeightOneSpectrum A) :
    L ⊗[K] v.adicCompletion K ≃A[L] ∀ w : v.Extension B, w.1.adicCompletion L :=
  {
    __ := adicCompletionComapAlgEquiv A K L B v
    __ := adicCompletionComapRightContinuousAlgEquiv A K L B v
  }

end IsDedekindDomain.HeightOneSpectrum

namespace IsDedekindDomain

open IsDedekindDomain HeightOneSpectrum

open scoped TensorProduct -- ⊗ notation for tensor product

/-- The ring homomorphism `𝔸_K^∞ → 𝔸_L^∞` for `L/K` an extension of number fields.-/
noncomputable def FiniteAdeleRing.mapRingHom :
    FiniteAdeleRing A K →+* FiniteAdeleRing B L := RestrictedProduct.mapRingHom
  (fun (v : HeightOneSpectrum A) ↦ v.adicCompletion K)
  (fun (w : HeightOneSpectrum B) ↦ w.adicCompletion L)
  (HeightOneSpectrum.comap A)
  (Filter.Tendsto.cofinite_of_finite_preimage_singleton <| Extension.finite A K L B)
  (fun w ↦ adicCompletionComapSemialgHom A K L B (w.comap A) w rfl)
  (by
    apply Filter.Eventually.of_forall
    intro w
    have : FaithfulSMul A B := FaithfulSMul.of_field_isFractionRing A B K L
    have := adicCompletionComapSemialgHom.mapadicCompletionIntegers A K L B (comap A w) w rfl
    exact Set.image_subset_iff.1 this)

/-- The ring homomorphism `𝔸_K^∞ → 𝔸_L^∞` for `L/K` an extension of number fields,
as a morphism lying over the canonical map `K → L`. -/
noncomputable def FiniteAdeleRing.mapSemialgHom :
    FiniteAdeleRing A K →ₛₐ[algebraMap K L] FiniteAdeleRing B L where
      __ := FiniteAdeleRing.mapRingHom A K L B
      map_smul' k a := by
        ext w
        simpa only [Algebra.smul_def'] using
          (adicCompletionComapSemialgHom A K L B (comap A w) w rfl).map_smul' k (a (comap A w))

noncomputable instance : Algebra (FiniteAdeleRing A K) (L ⊗[K] FiniteAdeleRing A K) :=
  Algebra.TensorProduct.rightAlgebra

noncomputable
instance BaseChange.algebra : Algebra (FiniteAdeleRing A K) (FiniteAdeleRing B L) :=
  RingHom.toAlgebra (FiniteAdeleRing.mapRingHom A K L B)

attribute [instance 100] RestrictedProduct.instSMulCoeOfSMulMemClass
-- otherwise
-- #synth SMul (FiniteAdeleRing A K) (FiniteAdeleRing B L)
-- spends 2 seconds failing to find `SMul (FiniteAdeleRing A K) (adicCompletion L w)

lemma BaseChange.isModuleTopology : IsModuleTopology (FiniteAdeleRing A K) (FiniteAdeleRing B L) :=
  sorry -- this should follow from the fact that L_w has the K_v-module topology? Hopefully
  -- **TODO** this needs an issue number.

noncomputable instance : TopologicalSpace (L ⊗[K] FiniteAdeleRing A K) :=
  moduleTopology (FiniteAdeleRing A K) (L ⊗[K] FiniteAdeleRing A K)

/-- The `L`-algebra isomorphism `L ⊗_K 𝔸_K^∞ ≅ 𝔸_L^∞`. -/
noncomputable def FiniteAdeleRing.baseChangeAlgEquiv :
    L ⊗[K] FiniteAdeleRing A K ≃ₐ[L] FiniteAdeleRing B L where
  __ := AlgEquiv.ofBijective
    (SemialgHom.baseChange_of_algebraMap <| FiniteAdeleRing.mapSemialgHom A K L B)
    -- ⊢ Function.Bijective ⇑(mapSemialgHom A K L B).baseChange_of_algebraWMap
    sorry -- #243

/-- The continuous `L`-algebra isomorphism `L ⊗_K 𝔸_K^∞ ≅ 𝔸_L^∞` -/
noncomputable def FiniteAdeleRing.baseChangeContinuousAlgEquiv :
    L ⊗[K] FiniteAdeleRing A K ≃A[L] FiniteAdeleRing B L where
  __ := FiniteAdeleRing.baseChangeAlgEquiv A K L B
  continuous_toFun := sorry
  continuous_invFun := sorry
  -- TODO needs issue number

end IsDedekindDomain
