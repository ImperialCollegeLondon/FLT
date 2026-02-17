/-
Copyright (c) 2025 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Andrew Yang, Matthew Jasper
-/
import FLT.DedekindDomain.AdicValuation
import FLT.DedekindDomain.IntegralClosure
import FLT.Mathlib.Algebra.Algebra.Pi
import FLT.Mathlib.Algebra.Module.Submodule.Basic
import FLT.Mathlib.RingTheory.TensorProduct.Basis
import FLT.Mathlib.Topology.Algebra.Module.Equiv
import FLT.Mathlib.Topology.Algebra.UniformRing
import FLT.Mathlib.Topology.Algebra.Valued.WithVal
import Mathlib.Algebra.Algebra.Subalgebra.Pi
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.Valued.NormedValued

/-!

# Base change of adic completions.

If `A` is a Dedekind domain with field of fractions `K`, if `L/K` is a finite extension
and if `B/A` is also finite then `L ⊗_K K_v ≅ ∏_{w|v} L_w` as `L`-algebras. Further this
map is continuous, `K_v`-linear and restricts to an isomorphism `B ⊗_A 𝓞_v ≅ ∏_{w|v} 𝓞_w`.

## Main definitions

* `IsDedekindDomain.HeightOneSpectrum.adicCompletionComapContinuousAlgEquiv` :
   `L ⊗[K] K_v ≃A[L] ∏_{w|v} L_w`

## Main theorems

* `IsDedekindDomain.HeightOneSpectrum.valued_adicCompletionComap A K L B v w pf` :
  If w|v are nonzero primes of B and A, and if x ∈ K_v ⊆ L_w, then w(x)=v(x)^e
  where e is the global ramification index of w/v.

* `IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionComapAlgHom_bijective A K L B v` :
  The canonical map L ⊗ Kᵥ → ∏_{w|v} L_w is bijective.

## TODO

* Show that `B ⊗_A 𝓞_v → L ⊗_K K_v` is injective to finish the proof of `B ⊗_A 𝓞_v ≅ ∏_{w|v} 𝓞_w`.

-/

open scoped WithZero Valued

/-!

The general "AKLB" set-up. `K` is the field of fractions of the Dedekind domain `A`,
`L/K` is a finite separable extension, and `B` is the integral closure of `A` in `L`.

-/

variable (A K L B : Type*) [CommRing A] [CommRing B] [Algebra A B] [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K] [Algebra B L] [IsDedekindDomain A]
    [Algebra K L] [Algebra A L] [IsScalarTower A B L] [IsScalarTower A K L]
    [IsIntegralClosure B A L] [FiniteDimensional K L]

/-!

Under these hypotheses and `[Algebra.IsSeparable K L]`, we can prove the following:

`[IsDomain B]`
`[Algebra.IsIntegral A B]`
`[Module.Finite A B]`
`[IsDedekindDomain B]`
`[IsFractionRing B L]`

However none of these facts are available to typeclass inference because they all use
variables such as `K` which are not mentioned in the statement so are unfindable by
Lean 4's typeclass system. We thus introduce them as variables when needed.

-/
example : IsDomain B := by
  have foo : Function.Injective (algebraMap B L) := IsIntegralClosure.algebraMap_injective B A _
  have bar : IsDomain L := inferInstance
  exact Function.Injective.isDomain _ foo -- exact? failed

example : Algebra.IsIntegral A B := IsIntegralClosure.isIntegral_algebra A L
variable [Algebra.IsIntegral A B]

example [IsDomain B] [Algebra.IsSeparable K L] : IsDedekindDomain B :=
  IsIntegralClosure.isDedekindDomain A K L B
variable [IsDedekindDomain B]

example : IsFractionRing B L := IsIntegralClosure.isFractionRing_of_finite_extension A K L B
variable [IsFractionRing B L]

example [Algebra.IsSeparable K L] : Module.Finite A B :=
  have := IsIntegralClosure.isNoetherian A K L B
  Module.IsNoetherian.finite A B
-- variable [Module.Finite A B] -- we'll need this later

example : FaithfulSMul A B := FaithfulSMul.of_field_isFractionRing A B K L
-- variable [FaithfulSMul A B] -- we'll need this later

namespace IsDedekindDomain

namespace HeightOneSpectrum

variable (v : HeightOneSpectrum A)

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

omit [IsIntegralClosure B A L] [FiniteDimensional K L] in
lemma adicValued.continuous_algebraMap
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
  let e : ℤ ≃ ℤᵐ⁰ˣ := Multiplicative.ofAdd.trans OrderMonoidIso.unitsWithZero.symm.toEquiv
  have e_apply (a : ℤ) : e a = OrderMonoidIso.unitsWithZero.symm (Multiplicative.ofAdd a) := rfl
  have hm : m ≠ 0 := by
    refine ramificationIdx_ne_zero A B ?_ w
    exact algebraMap_injective_of_field_isFractionRing A B K L
  refine ⟨a / m, fun x hx ↦ ?_⟩
  erw [← valuation_comap A]
  calc
    (comap A w).valuation K x ^ m < e (a / ↑m) ^ m := by gcongr; exacts [zero_le', hx]
  _ = e (m • (a / ↑m)) := by
    dsimp [e]
    rfl
  _ ≤ e a := by
    simp only [nsmul_eq_mul, e_apply, Units.val_le_val, OrderIsoClass.map_le_map_iff]
    rw [mul_comm]
    exact Int.mul_le_of_le_ediv (by positivity) le_rfl

/-- If w of L divides v of K, `adicCompletionComapSemialgHom v w pf` is the canonical map
`Kᵥ → L_w` lying above `K → L`. Here we actually use the type synonyms `WithVal K` and `WithVal L`.
-/
noncomputable def adicCompletionComapSemialgHom (v : HeightOneSpectrum A) (w : v.Extension B) :
    v.adicCompletion K →ₛₐ[σ v w.1] w.1.adicCompletion L :=
  UniformSpace.Completion.mapSemialgHom _ <|
  adicValued.continuous_algebraMap A K L B v w.1 w.2

omit [IsIntegralClosure B A L] [FiniteDimensional K L] in
/-- The square with sides K → K_v → L_w and K → L → L_w commutes. -/
lemma adicCompletionComap_coe
    (v : HeightOneSpectrum A) (w : v.Extension B) (x : K) :
    adicCompletionComapSemialgHom A K L B v w x = algebraMap K L x :=
  (adicCompletionComapSemialgHom A K L B v w).commutes x

omit [IsIntegralClosure B A L] [FiniteDimensional K L] in
open WithZeroTopology in
/--
The local ramification index for the extension L_w/K_v is equal to the global ramification
index for the extension w/v. In other words, if x in K_v and i:K_v->L_w then w(i(x))=v(x)^e
where e is computed globally.
-/
lemma valued_adicCompletionComap
  (v : HeightOneSpectrum A) (w : v.Extension B) (x) :
    Valued.v (adicCompletionComapSemialgHom A K L B v w x) = Valued.v x ^
      Ideal.ramificationIdx (algebraMap A B) (comap A w.1).asIdeal w.1.asIdeal := by
  revert x
  apply funext_iff.mp
  symm
  apply UniformSpace.Completion.ext
  · exact Valued.continuous_valuation.pow _
  · exact Valued.continuous_valuation.comp UniformSpace.Completion.continuous_extension
  intro a
  simp_rw [adicCompletionComap_coe, adicCompletion, Valued.valuedCompletion_apply,
    adicValued_apply']
  simp_rw [← w.2]
  rw [← valuation_comap A K L B w.1 a]

omit [IsIntegralClosure B A L] [FiniteDimensional K L] in
/-- The canonical map K_v → L_w sends 𝓞_v to 𝓞_w. -/
lemma adicCompletionComapSemialgHom.mapadicCompletionIntegers (v : HeightOneSpectrum A)
    (w : v.Extension B) :
    (adicCompletionComapSemialgHom A K L B v w) '' (v.adicCompletionIntegers K) ≤
    w.1.adicCompletionIntegers L := by
  rintro y ⟨x, hx, rfl⟩
  rw [SetLike.mem_coe, mem_adicCompletionIntegers] at hx ⊢
  rw [valued_adicCompletionComap A K L B v w]
  rwa [pow_le_one_iff]
  exact ramificationIdx_ne_zero A B (algebraMap_injective_of_field_isFractionRing A B K L) w.1

/-- The K_v-algebra structure on L_w when w | v. -/
noncomputable
instance {v : HeightOneSpectrum A} {w : v.Extension B} :
    Algebra (v.adicCompletion K) (w.1.adicCompletion L) :=
  (adicCompletionComapSemialgHom A K L B v w).toAlgebra

/-- The canonical map `K_v → ∏_{w|v} L_w` extending K → L. -/
noncomputable def adicCompletionComapSemialgHom' (v : HeightOneSpectrum A) :
    v.adicCompletion K →ₛₐ[algebraMap K L] ∀ w : v.Extension B, w.1.adicCompletion L :=
  Pi.semialgHom _ _ fun i ↦ adicCompletionComapSemialgHom A K L B v i

/-- The K_v-algebra structure on ∏_{w|v} L_w. -/
noncomputable instance comap_pi_algebra (v : HeightOneSpectrum A) :
    Algebra (v.adicCompletion K) (Π (w : v.Extension B), w.1.adicCompletion L) :=
  (adicCompletionComapSemialgHom' A K L B v).toAlgebra

open scoped TensorProduct -- ⊗ notation for tensor product

/-- The canonical ring homomorphism `L ⊗_K K_v → ∏_{w|v} L_w` as an `L`-algebra map. -/
noncomputable def tensorAdicCompletionComapAlgHom (v : HeightOneSpectrum A) :
    L ⊗[K] adicCompletion K v →ₐ[L] Π w : v.Extension B, w.1.adicCompletion L :=
  SemialgHom.baseChange_of_algebraMap (adicCompletionComapSemialgHom' A K L B v)

omit [IsIntegralClosure B A L] [FiniteDimensional K L] in
lemma tensorAdicCompletionComapAlgHom_tmul_apply (v : HeightOneSpectrum A) (x y w) :
  --letI := comap_algebra A K L B w.prop
  tensorAdicCompletionComapAlgHom A K L B v (x ⊗ₜ y) w =
    (algebraMap _ (w.1.adicCompletion L) x) * (algebraMap _ (w.1.adicCompletion L) y) := by
  rfl

open scoped TensorProduct.RightActions in
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
    Valuation.RankOne (Valued.v : Valuation (adicCompletion K v) ℤᵐ⁰) where
  hom := {
    toFun := toNNReal (by norm_num : (2 : NNReal) ≠ 0)
    map_zero' := rfl
    map_one' := rfl
    map_mul' := MonoidWithZeroHom.map_mul (toNNReal (by norm_num))
  }
  strictMono' := toNNReal_strictMono (by norm_num)
  exists_val_nontrivial := by
    obtain ⟨x, hx1, hx2⟩ := Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot
    use algebraMap A K x
    rw [valuedAdicCompletion_eq_valuation' v (algebraMap A K x)]
    constructor
    · simpa only [ne_eq, map_eq_zero, FaithfulSMul.algebraMap_eq_zero_iff]
    · apply ne_of_lt
      rwa [valuation_of_algebraMap, intValuation_lt_one_iff_mem]

omit [IsIntegralClosure B A L] [FiniteDimensional K L] in
/-- The map K_v → L_w is continuous. -/
lemma adicCompletionComapSemialgHom_continuous
    (v : HeightOneSpectrum A) (w : v.Extension B) :
    Continuous (adicCompletionComapSemialgHom A K L B v w) :=
  UniformSpace.Completion.continuous_extension (β := (adicCompletion L w.1))

omit [IsIntegralClosure B A L] [FiniteDimensional K L] in
/-- The K_v-action on L_w is continuous. -/
instance (v : HeightOneSpectrum A) (w : v.Extension B) :
    --letI := comap_algebra A K L B hvw
    ContinuousSMul (adicCompletion K v) (adicCompletion L w.1) := by
  --let inst_alg := comap_algebra A K L B hvw
  constructor
  have leftCts := adicCompletionComapSemialgHom_continuous A K L B v w
  exact Continuous.mul (Continuous.fst' leftCts) continuous_snd

open scoped TensorProduct.RightActions in
omit [IsIntegralClosure B A L] in
/-- The canonical map `L ⊗[K] K_v → ∏_{w|v} L_w` is surjective. -/
lemma tensorAdicCompletionComapLinearMap_surjective (v : HeightOneSpectrum A) :
    Function.Surjective (tensorAdicCompletionComapLinearMap A K L B v) := by
  -- letI : Module (adicCompletion K v) ((w : Extension B v) → adicCompletion L w.val) :=
  --   comap_pi_algebra A K L B v |>.toModule
  -- let _ (w : Extension B v) : SMul (adicCompletion K v) (adicCompletion L w.val) :=
  --   comap_algebra A K L B w.prop |>.toSMul
  -- let _ (w : Extension B v) : ContinuousSMul (adicCompletion K v) (adicCompletion L w.val) :=
  --   comap_algebra_continuousSmul A K L B v w
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

open scoped TensorProduct.RightActions in
omit [IsIntegralClosure B A L] in
/-- ∏_{w|v} L_w is a finite K_v-module. -/
instance (v : HeightOneSpectrum A) :
    --letI := comap_pi_algebra A K L B v |>.toModule
    Module.Finite (adicCompletion K v) (Π w : v.Extension B, w.1.adicCompletion L) :=
  --letI := comap_pi_algebra A K L B v |>.toModule
  Module.Finite.of_surjective (tensorAdicCompletionComapLinearMap A K L B v)
    (tensorAdicCompletionComapLinearMap_surjective A K L B v)

omit [IsIntegralClosure B A L] in
/-- L_w is a finite K_v-module if w | v. -/
instance (v : HeightOneSpectrum A) (w : v.Extension B) :
    Module.Finite (adicCompletion K v) (adicCompletion L w.1) :=
  -- have := comap_pi_algebra_finite A K L B v
  -- let _ (w : Extension B v) := comap_algebra A K L B w.prop |>.toModule
  Module.Finite.of_pi (fun (w : Extension B v) => w.1.adicCompletion L) w

omit [IsIntegralClosure B A L] in
/-- L_w has the K_v-module topology. -/
instance (v : HeightOneSpectrum A) (w : v.Extension B) :
    -- temporarily make L_w a K_v-algebra
    --letI := comap_algebra A K L B hvw
    -- then claim that L_w has the module topology.
    IsModuleTopology (v.adicCompletion K) (w.1.adicCompletion L) := by
  let Kv := adicCompletion K v
  let Lw := adicCompletion L w.1
  --let _ : Algebra Kv Lw := comap_algebra A K L B hvw
  --have : ContinuousSMul Kv Lw := comap_algebra_continuousSmul A K L B v w hvw
  --have : Module.Finite Kv Lw := comap_algebra_finite A K L B v w hvw
  let iso : ((Fin (Module.finrank Kv Lw)) → Kv) ≃L[Kv] Lw :=
    ContinuousLinearEquiv.ofFinrankEq (Module.finrank_fin_fun Kv)
  apply IsModuleTopology.iso iso

omit [IsIntegralClosure B A L] in
/-- ∏_{w|v} L_w has the K_v-module topology. -/
instance prodAdicCompletionComap_isModuleTopology (v : HeightOneSpectrum A) :
    -- TODO: the `let _` in the statement below should not be required as it is an instance
    -- see mathlib PR #22488 for potential fix to this.
    -- Note that this one does not involve `adicCompletionIntegers` so the
    -- issue may not be to do with subtype vs. type implementation of
    -- `adicCompletionIntegers`.
    --let _ := comap_pi_algebra A K L B v |>.toSMul
    -- the claim that L_w has the module topology.
    IsModuleTopology (v.adicCompletion K) (Π (w : v.Extension B), w.1.adicCompletion L) := by
  -- these are defs or lemmas so are required
  --let _ (w : v.Extension B) := comap_algebra A K L B w.2 |>.toModule
  --let _ (w : v.Extension B) := adicCompletionComap_isModuleTopology A K L B v w.1 w.2
  let _ := Extension.finite A K L B v
  exact IsModuleTopology.instPi

open scoped TensorProduct.RightActions in
omit [IsIntegralClosure B A L] in
/-- `tensorAdicCompletionComapLinearMap` is continuous, open and surjective.
  We later show that it's a homeomorphism. -/
lemma tensorAdicCompletionComapLinearMap_isOpenQuotientMap (v : HeightOneSpectrum A) :
    IsOpenQuotientMap (tensorAdicCompletionComapLinearMap A K L B v) := by
  have : T2Space (L ⊗[K] adicCompletion K v) :=
    IsModuleTopology.t2Space' (K := (adicCompletion K v))
  -- let _ (w : Extension B v) : SMul (adicCompletion K v) (adicCompletion L w.val) :=
  --   comap_algebra A K L B w.prop |>.toSMul
  -- let _ (w : Extension B v) : ContinuousSMul (adicCompletion K v) (adicCompletion L w.val) :=
  --   comap_algebra_continuousSmul A K L B v w.val w.prop
  --have := IsModuleTopology.topologicalAddGroup (adicCompletion K v) (L ⊗[K] adicCompletion K v)
  -- have := comap_pi_algebra_finite A K L B v
  have hsurj := tensorAdicCompletionComapLinearMap_surjective A K L B v
  exact ⟨hsurj, LinearMap.continuous_of_finiteDimensional _,
    LinearMap.isOpenMap_of_finiteDimensional _ hsurj⟩

-- TODO : this local instance should not be required, see mathlib PR #22488 for potential fix
-- attribute [local instance 9999] SMulCommClass.of_commMonoid TensorProduct.isScalarTower_left
--   IsScalarTower.right Algebra.toSMul

/-- The triangle A → 𝓞_v → K_v commutes. -/
instance (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] (v : HeightOneSpectrum R) :
    IsScalarTower R (v.adicCompletionIntegers K) (v.adicCompletion K) :=
  ⟨fun x y z ↦ by exact smul_mul_assoc x y.1 z⟩

/-- 𝓞_v as an A-subalgebra of K_v. -/
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

omit [IsIntegralClosure B A L] [FiniteDimensional K L] [Algebra.IsIntegral A B]
  [IsDedekindDomain B] [IsFractionRing B L] in
@[simp]
lemma tensorAdicCompletionIntegersTo_tmul (v : HeightOneSpectrum A) (b : B)
    (x : v.adicCompletionIntegers K) : tensorAdicCompletionIntegersTo A K L B v (b ⊗ₜ x) =
      (algebraMap B L b) ⊗ₜ x.val := by
  simp [tensorAdicCompletionIntegersTo]

omit [IsIntegralClosure B A L]
    [Algebra.IsIntegral A B] [IsDedekindDomain B]
    [IsFractionRing B L] in
open scoped TensorProduct.RightActions in
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
        apply map_mem_closure₂ _ hx hy _
        · exact (ModuleTopology.continuousAdd _ _).continuous_add
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
        let f (y : ↥(adicCompletionIntegers K v)) : (L ⊗[K] adicCompletion K v) :=
          (Algebra.ofId B (L ⊗[K] adicCompletion K v)) b * (1 : L) ⊗ₜ[K] (y : adicCompletion K v)
        have hfval : f = fun (y : ↥(adicCompletionIntegers K v)) =>
              (y : adicCompletion K v) • (Algebra.ofId B (L ⊗[K] adicCompletion K v)) b := by
          ext y
          unfold f
          rw [Algebra.smul_def]
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
        · exact isClosed_closure
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
open scoped TensorProduct.RightActions in
omit [Algebra.IsIntegral A B] [IsDedekindDomain B] [IsFractionRing B L]  in
/-- The image of `B ⊗[A] 𝓞_v` in `L ⊗[K] K_v` is clopen. -/
lemma tensorAdicCompletionIsClopenRange :
    IsClopen (SetLike.coe (tensorAdicCompletionIntegersTo A K L B v).range) := by
  -- `B ⊗[A] 𝒪_v` is a subgroup of `L ⊗[K] K_v`, so we can show it's closed
  -- by showing that it's open. **TODO** split into IsOpen + IsClosed lemmas?
  rw [← Subalgebra.coe_toSubring, ← Subring.coe_toAddSubgroup]
  --have := ModuleTopology.continuousAdd (adicCompletion K v) (L ⊗[K] adicCompletion K v)
  refine OpenAddSubgroup.isClopen ⟨_, ?_⟩
  -- Further, we can show `B ⊗[A] 𝒪_v` is open by showing that it contains an
  -- open neighbourhood of 0.
  apply AddSubgroup.isOpen_of_zero_mem_interior
  rw [mem_interior, Subring.coe_toAddSubgroup, Subalgebra.coe_toSubring]
  -- Take a basis `b` of `L` over `K` with elements in `B` and use it to
  -- get a basis `b'` of `L ⊗[K] K_v` over `K_v`.
  obtain ⟨ι, b, hb⟩ := FiniteDimensional.exists_is_basis_integral A K L
  let b' : Module.Basis ι (adicCompletion K v) (L ⊗[K] (adicCompletion K v)) := by
    classical
    exact b.rightBaseChange L
  -- Use the basis to get a continuous equivalence from `L ⊗[K] K_v` to `ι → K_v`.
  let equiv : L ⊗[K] (adicCompletion K v) ≃L[K] (ι → adicCompletion K v) :=
    IsModuleTopology.continuousLinearEquiv (b'.equivFun) |>.restrictScalars K
  -- Use the preimage of `∏ 𝒪_v` as the open neighbourhood.
  use equiv.symm '' (Set.pi Set.univ (fun _ => SetLike.coe (adicCompletionIntegers K v)))
  refine ⟨?_, ?_, by simp⟩
  · intro t ⟨g, hg, ht⟩
    -- We have `t = equiv g = ∑ i, b i ⊗ g i`, since `g in ∏ 𝒪_v` and
    -- `b i ∈ (algebraMap B L).range`, this is `tensorAdicCompletionIntegersTo`
    -- of some element of `B ⊗[A] 𝒪_v`
    have hf : ∀ (i : ι), ∃ (w : B), (algebraMap B L w) = (b i) := by
      intro i
      apply IsIntegralClosure.isIntegral_iff.mp (hb i)
    choose f hf_prop using hf
    use ∑ (i : ι), (f i) ⊗ₜ ⟨g i, hg i trivial⟩
    -- let _ : NonAssocSemiring (B ⊗[A] (adicCompletionIntegers K v)) :=
    --   Algebra.TensorProduct.instNonAssocSemiring
    -- let _ : AddMonoidHomClass (B ⊗[A] (adicCompletionIntegers K v) →+* L ⊗[K] adicCompletion K v)
    --     (B ⊗[A] (adicCompletionIntegers K v)) (L ⊗[K] adicCompletion K v) :=
    --   RingHomClass.toAddMonoidHomClass
    rw [map_sum, ← ht]
    unfold equiv
    rw [ContinuousLinearEquiv.restrictScalars_symm_apply,
      IsModuleTopology.continuousLinearEquiv_symm_apply,
      Module.Basis.equivFun_symm_apply]
    apply Finset.sum_congr rfl
    intro x
    have : (algebraMap _ (L ⊗[K] adicCompletion K v)) (g x) = 1 ⊗ₜ[K] (g x) := rfl
    simp [Algebra.smul_def, tensorAdicCompletionIntegersTo_tmul, hf_prop, b', this]
  · rw [ContinuousLinearEquiv.image_symm_eq_preimage]
    apply IsOpen.preimage equiv.continuous
    apply isOpen_set_pi Set.finite_univ
    rintro i -
    exact Valued.isOpen_valuationSubring (v.adicCompletion K)

omit [Algebra.IsIntegral A B] [IsDedekindDomain B] [IsFractionRing B L] in
open scoped TensorProduct.RightActions in
/-- The image of `B ⊗[A] 𝓞_v` in `L ⊗[K] K_v` is the closure of the image of `B`. -/
lemma tensorAdicCompletionIntegersToRange_eq_closureIntegers :
    SetLike.coe (tensorAdicCompletionIntegersTo A K L B v).range =
        closure (algebraMap B (L ⊗[K] adicCompletion K v)).range := by
  apply Set.Subset.antisymm
  · apply tensorAdicCompletionIntegersToRange_subset_closureIntegers
  · apply closure_minimal
    · rintro _ ⟨b, rfl⟩
      apply algebraMap_mem
    · apply IsClopen.isClosed
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
  change SetLike.coe (Submodule.pi _ _) = _
  rw [Submodule.coe_pi]
  let val := (fun (w : Extension B v) ↦ w.1)
  have hinj : Function.Injective val :=
    (Set.injective_codRestrict Subtype.property).mp fun _ _ a ↦ a
  rw [closureAlgebraMapIntegers_eq_prodIntegers L val hinj]
  rfl

open scoped TensorProduct.RightActions in
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

-- instance : OneHomClass
--     (L ⊗[K] adicCompletion K v →ₐ[L] (w : Extension B v) → adicCompletion L w.1)
--     (L ⊗[K] adicCompletion K v) ((w : Extension B v) → adicCompletion L w.1) where
--   map_one f := f.toRingHom.map_one

open scoped TensorProduct.RightActions in
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
    simp [Algebra.algebraMap_eq_smul_one]
  have hrange' := adicCompletionComapAlgHom_map_closure_is_closed A K L B v
  rw [AlgHom.range_comp, ← SetLike.coe_set_eq, Subalgebra.coe_map, AlgHom.coe_restrictScalars',
      hlhs, hrhs, hrange, ← IsClosed.closure_eq hrange']
  exact closure_image_closure
    (tensorAdicCompletionComapLinearMap_isOpenQuotientMap A K L B v).continuous

-- attribute [local instance 9999] SMulCommClass.of_commMonoid TensorProduct.isScalarTower_left
--   IsScalarTower.right

-- **TODO**: Mathlib#23590 will provide these instances in more generality.
/-- The restriction of `adicCompletionComapSemialgHom` to a map `𝓞_v → 𝓞_w`. -/
noncomputable def adicCompletionComapIntegerRingHom (v : HeightOneSpectrum A)
    (w : v.Extension B) :
    v.adicCompletionIntegers K →+* w.1.adicCompletionIntegers L where
  toFun x :=
    letI := FaithfulSMul.of_field_isFractionRing A B K L
    ⟨adicCompletionComapSemialgHom A K L B v w x,
     adicCompletionComapSemialgHom.mapadicCompletionIntegers A K L B v w ⟨x, x.prop, rfl⟩⟩
  map_zero' := by ext; simp
  map_one' := by ext; simp
  map_add' x y := by ext; simp
  map_mul' x y := by ext; simp

/-- If `w` is an extension of `v`, then `𝓞_w` is naturally an `𝓞_v`-algebra. -/
noncomputable
instance {v : HeightOneSpectrum A} {w : v.Extension B} :
    Algebra (v.adicCompletionIntegers K) (w.1.adicCompletionIntegers L) :=
  (adicCompletionComapIntegerRingHom A K L B v w).toAlgebra

omit [IsIntegralClosure B A L] [FiniteDimensional K L] in
lemma comap_integer_algebraMap {v : HeightOneSpectrum A} {w : v.Extension B}
    (x : v.adicCompletionIntegers K) :
    -- letI := comap_integer_algebra A K L B h
    algebraMap (v.adicCompletionIntegers K) (w.1.adicCompletionIntegers L) x =
    (adicCompletionComapSemialgHom A K L B v w) x.val :=
  rfl

variable {v} in
/-- If `w` is an extension of `v`, then `L_w` is naturally an `𝓞_v`-algebra. -/
noncomputable instance {w : v.Extension B} :
    Algebra (v.adicCompletionIntegers K) (w.1.adicCompletion L) :=
  Algebra.compHom (w.1.adicCompletion L)
    (algebraMap (adicCompletionIntegers K v) (adicCompletion K v))
  -- --letI := comap_algebra A K L B hvw
  -- RingHom.toAlgebra <| (algebraMap (adicCompletion K v) (adicCompletion L w.1)).comp
  --   (algebraMap (adicCompletionIntegers K v) (adicCompletion K v))

open scoped TensorProduct.RightActions in
/-- `tensorAdicCompletionIntegersTo` as an 𝓞_v-linear map. -/
noncomputable def tensorAdicCompletionIntegersToLinearMap :
    (B ⊗[A] adicCompletionIntegers K v) →ₗ[adicCompletionIntegers K v]
      (L ⊗[K] adicCompletion K v) where
  __ := tensorAdicCompletionIntegersTo A K L B v
  map_smul' x y := by
    simp only [tensorAdicCompletionIntegersTo_tmul, AlgHom.toRingHom_eq_coe,
      RingHom.toMonoidHom_eq_coe, AlgHom.toRingHom_toMonoidHom, Algebra.smul_def,
      TensorProduct.RightActions.algebraMap_eval, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe,
      MonoidHom.coe_coe, map_mul, map_one, RingHom.id_apply]
    rfl

open scoped TensorProduct.RightActions in
/-- The map `B ⊗ 𝓞_v → L_w` for `w` an extension of `v` given by the algebra maps. -/
noncomputable def adicCompletionComapIntegerLinearMap (v : HeightOneSpectrum A)
    (w : v.Extension B) :
    -- letI := comap_algebra A K L B hvw
    -- letI := RingHom.toAlgebra <| (algebraMap (adicCompletion K v) (adicCompletion L w)).comp
    --   (algebraMap (adicCompletionIntegers K v) (adicCompletion K v))
    B ⊗[A] (adicCompletionIntegers K v) →ₗ[adicCompletionIntegers K v] (adicCompletion L w.1) :=
  -- letI := comap_integer_algebra A K L B hvw
  -- letI (w' : Extension B v) := comap_algebra A K L B w'.prop
  -- let alg (w' : Extension B v) : Algebra _ _ :=
  --   RingHom.toAlgebra <| (algebraMap (adicCompletion K v) (adicCompletion L w'.val)).comp
  --     (algebraMap (adicCompletionIntegers K v) (adicCompletion K v))
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
  let g := f.comp (tensorAdicCompletionIntegersToLinearMap A K L B v)
  LinearMap.proj w |>.comp g

open scoped TensorProduct.RightActions in
/-- The range of `adicCompletionComapIntegerLinearMap` is `𝓞_w`. -/
lemma adicCompletionComapIntegerLinearMap_range_eq_integers (v : HeightOneSpectrum A)
    (w : v.Extension B) :
    -- letI := comap_algebra A K L B hvw
    Set.range (adicCompletionComapIntegerLinearMap A K L B v w) =
    adicCompletionIntegers L w.1 := by
  ext x
  have memrange : (Set.range _) = _ :=
    congr_arg SetLike.coe (adicCompletionComapAlgEquiv_integral A K L B v)
  rw [Subalgebra.coe_pi, Submodule.carrier_eq_coe, Submodule.coe_pi, Set.ext_iff] at memrange
  --let extension : Extension B v := ⟨w, hvw⟩
  constructor
  · rintro ⟨y, rfl⟩
    exact (memrange _).mp (Set.mem_range_self y) w trivial
  · intro hx
    classical
    set x' : (w : Extension B v) → adicCompletion L w.val := Pi.single w x with hx'
    obtain ⟨y, (hy : _ = x')⟩ : x' ∈ Set.range _ := by
      rw [memrange x', Set.mem_pi]
      intro w' _
      by_cases h : w = w'
      · rw [← h, hx', Pi.single_eq_same, SetLike.mem_coe]
        exact hx
      · rw [hx', Pi.single_eq_of_ne' h]
        apply Subalgebra.zero_mem
    use y
    simpa [hx'] using congr_fun hy w


open scoped TensorProduct.RightActions in
/-- `𝓞_w` is finite over `𝓞_v`. -/
-- This can be proved for finite extensions of complete discretely valued fields without
-- reference to underlying fields being completed, but this is sufficient for our
-- purposes.
instance [Module.Finite A B] (v : HeightOneSpectrum A)
    (w : v.Extension B) :
    --letI := comap_integer_algebra A K L B hvw
    Module.Finite (adicCompletionIntegers K v) (adicCompletionIntegers L w.1) := by
  --letI := comap_integer_algebra A K L B hvw
  -- letI := comap_algebra A K L B hvw
  -- let hom : (adicCompletionIntegers K v) →+* (adicCompletion L w.1) :=
  --   (algebraMap (adicCompletion K v) (adicCompletion L w.1)).comp
  --     (algebraMap (adicCompletionIntegers K v) (adicCompletion K v))
  -- letI := RingHom.toAlgebra hom
  let integerSubmodule : Submodule (adicCompletionIntegers K v) (adicCompletion L w.1) :=
    letI : Algebra (v.adicCompletionIntegers K) (w.1.adicCompletionIntegers L).toSubring :=
      inferInstanceAs (Algebra (adicCompletionIntegers K v) (adicCompletionIntegers L w.1))
    have : IsScalarTower (adicCompletionIntegers K v) (adicCompletionIntegers L w.1).toSubring
        (adicCompletion L w.1) := by
      apply IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
    (adicCompletionIntegers L w.1).toSubmodule.restrictScalars
      (adicCompletionIntegers K v)
  have heq : (LinearMap.range (adicCompletionComapIntegerLinearMap A K L B v w)) =
      integerSubmodule := by
    ext x
    apply adicCompletionComapIntegerLinearMap_range_eq_integers A K L B v w |> Set.ext_iff.mp
  have := Module.Finite.range (adicCompletionComapIntegerLinearMap A K L B v w)
  have := adicCompletionComapIntegerLinearMap_range_eq_integers A K L B v w
  apply Module.Finite.equiv <|
    LinearEquiv.ofEq (LinearMap.range (adicCompletionComapIntegerLinearMap A K L B v w)) _ heq

end ModuleTopology

section RamificationInertia

lemma WithZero.ofAdd_neg_ofNat_pow (n : ℕ) :
    (WithZero.coe (Multiplicative.ofAdd (-n : ℤ))) = (Multiplicative.ofAdd (-1 : ℤ)) ^ n := by
  congr
  rw [← ofAdd_nsmul, nsmul_eq_mul, Int.mul_neg_one]

omit [IsIntegralClosure B A L] [FiniteDimensional K L] in
theorem adicCompletion.ramificationIdx_eq_ramificationIdx (w : v.Extension B) :
    --letI := comap_integer_algebra A K L B hvw
    Ideal.ramificationIdx (algebraMap _ _) (v.completionIdeal K) (w.1.completionIdeal L)
      = Ideal.ramificationIdx (algebraMap A B) v.asIdeal w.1.asIdeal := by
  apply Ideal.ramificationIdx_spec
  · rw [Ideal.map_le_iff_le_comap]
    intro x hx
    rw [mem_completionIdeal_iff'] at hx
    rw [Ideal.mem_comap, adicCompletion.mem_completionIdeal_pow, comap_integer_algebraMap,
      valued_adicCompletionComap]
    rw [WithZero.ofAdd_neg_ofNat_pow, w.2]
    apply pow_le_pow_left' hx
  · obtain ⟨ϖ, hϖ⟩ := adicCompletion.exists_uniformizer K v
    have hϖ' : ϖ ∈ v.completionIdeal K := by
      rw [mem_completionIdeal_iff, hϖ]
      decide
    rw [Ideal.map_le_iff_le_comap]
    intro h
    have hcomap := h hϖ'
    rw [Ideal.mem_comap, adicCompletion.mem_completionIdeal_pow, comap_integer_algebraMap,
      valued_adicCompletionComap, hϖ, ← WithZero.ofAdd_neg_ofNat_pow,
      WithZero.coe_le_coe, Multiplicative.ofAdd_le, w.2] at hcomap
    simp at hcomap

omit [IsIntegralClosure B A L] [FiniteDimensional K L] in
theorem adicCompletion.inertiaDeg_eq_inertiaDeg (w : v.Extension B) :
    --letI := comap_integer_algebra A K L B hvw
    v.asIdeal.inertiaDeg w.1.asIdeal = (v.completionIdeal K).inertiaDeg (w.1.completionIdeal L) :=
  letI := Algebra.compHom (adicCompletionIntegers L w.1) (algebraMap A B)
  -- letI := comap_integer_algebra A K L B hvw
  have : IsScalarTower A B (adicCompletionIntegers L w.1) :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower A (adicCompletionIntegers K v) (adicCompletionIntegers L w.1) := by
    apply IsScalarTower.of_algebraMap_eq
    intro x
    ext
    rw [Algebra.compHom_algebraMap_eq, RingHom.coe_comp, Function.comp_apply,
      algebraMap_completionIntegers, comap_integer_algebraMap, algebraMap_completionIntegers,
      IsScalarTower.algebraMap_apply B L (adicCompletion L w.1),
      ← IsScalarTower.algebraMap_apply A B L, IsScalarTower.algebraMap_apply A K L]
    symm
    apply SemialgHom.commutes
  have : w.1.asIdeal.LiesOver v.asIdeal := ⟨by simp_rw [← w.2]; rfl⟩
  have : (completionIdeal L w.1).LiesOver (completionIdeal K v) := {
    over := by
      rw [Ideal.under_def]
      ext x
      rw [Ideal.mem_comap, mem_completionIdeal_iff, mem_completionIdeal_iff,
        comap_integer_algebraMap, valued_adicCompletionComap A K L, pow_lt_one_iff]
      exact ramificationIdx_ne_zero A B (algebraMap_injective_of_field_isFractionRing A B K L) w.1
  }
  calc v.asIdeal.inertiaDeg w.1.asIdeal
      = v.asIdeal.inertiaDeg (w.1.completionIdeal L) := by
        rw [Ideal.inertiaDeg_algebra_tower v.asIdeal w.1.asIdeal (w.1.completionIdeal L),
          inertiaDeg_asIdeal_completionIdeal, mul_one]
    _ = (v.completionIdeal K).inertiaDeg (w.1.completionIdeal L) := by
        rw [Ideal.inertiaDeg_algebra_tower v.asIdeal (v.completionIdeal K) (w.1.completionIdeal L),
          inertiaDeg_asIdeal_completionIdeal, one_mul]

-- We use Ideal.sum_ramification_inertia_of_isLocalRing here to show this, but we could make use
-- of the more general results in BGR:
-- - in general e * f <= degree (Prop 3.1.3.2)
-- - equality holds for L/K if L is K-cartesian (Prop 3.6.2.4)
-- - so for example if K is complete and discretely-valued (Cor 2.4.3.11).
attribute [local instance 9999] Algebra.toModule Algebra.toSMul in
theorem ramification_mul_inertia_eq_finrank_completion [Module.Finite A B] (w : v.Extension B) :
    --letI := comap_algebra A K L B hvw |>.toModule
    v.asIdeal.ramificationIdx (algebraMap A B) w.1.asIdeal * v.asIdeal.inertiaDeg w.1.asIdeal =
    Module.finrank (adicCompletion K v) (adicCompletion L w.1) := by
  -- letI := comap_algebra A K L B hvw
  -- letI := comap_integer_algebra A K L B hvw
  -- have := comap_integer_algebra_finite A K L B v w hvw
  -- let hom : (adicCompletionIntegers K v) →+* (adicCompletion L w.1) :=
  --   (algebraMap (adicCompletion K v) (adicCompletion L w.1)).comp
  --     (algebraMap (adicCompletionIntegers K v) (adicCompletion K v))
  --let alg := RingHom.toAlgebra hom
  --letI := alg.toSMul
  have : IsScalarTower (adicCompletionIntegers K v) (adicCompletionIntegers L w.1)
      (adicCompletion L w.1) := by
    exact IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  have : IsScalarTower (adicCompletionIntegers K v) (adicCompletion K v)
      (adicCompletion L w.1) := by
    apply IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  rw [← Ideal.ramificationIdx_mul_inertiaDeg_of_isLocalRing (adicCompletionIntegers L w.1)
    (adicCompletion K v) (adicCompletion L w.1) (v.completionIdeal_ne_bot K),
    adicCompletion.ramificationIdx_eq_ramificationIdx A K L B v w,
    adicCompletion.inertiaDeg_eq_inertiaDeg A K L B v w]

end RamificationInertia

variable [Module.Finite A B]

open scoped TensorProduct.RightActions in
attribute [local instance 9999] Algebra.toModule in
/-- `L ⊗[K] K_v` and `∏_{w|v} L_w` have equal dimensions -/
lemma finrank_tensorProduct_adicCompletion_eq_finrank_pi_adicCompletion :
    --letI := comap_pi_algebra A K L B v
    Module.finrank (adicCompletion K v) (L ⊗[K] adicCompletion K v) =
    Module.finrank (adicCompletion K v) ((w : Extension B v) → adicCompletion L w.val) :=
  letI := Extension.fintype A K L B v
  --letI (w : Extension B v) := comap_algebra A K L B w.prop
  -- letI (w : Extension B v) : Module.Finite (adicCompletion K v) (adicCompletion L w.val) :=
  --   comap_algebra_finite A K L B v w.val w.prop
  -- letI (w : Extension B v) : Module.Free (adicCompletion K v) (adicCompletion L w.val) :=
  --   inferInstance
  calc Module.finrank (adicCompletion K v) (L ⊗[K] adicCompletion K v)
    _ = Module.finrank K L := by rw [TensorProduct.finrank_rightAlgebra]
    _ = ∑ (w : Extension B v), Ideal.ramificationIdx (algebraMap A B) v.asIdeal w.val.asIdeal *
        Ideal.inertiaDeg v.asIdeal w.val.asIdeal := by
        rw [Ideal.sum_ramification_inertia_extensions]
    _ = ∑ (w : Extension B v), Module.finrank (adicCompletion K v) (adicCompletion L w.val) :=
        Finset.sum_congr rfl fun w _ ↦
          ramification_mul_inertia_eq_finrank_completion A K L B v w
    _ = Module.finrank (adicCompletion K v) ((w : Extension B v) → adicCompletion L w.val) := by
        rw [Module.finrank_pi_fintype (adicCompletion K v)]

open scoped TensorProduct.RightActions in
/-- The canonical map `L ⊗[K] K_v → ∏_{w|v} L_w` is bijective. -/
theorem tensorAdicCompletionComapAlgHom_bijective (v : HeightOneSpectrum A) :
    Function.Bijective (tensorAdicCompletionComapAlgHom A K L B v) := by
  change Function.Bijective (tensorAdicCompletionComapLinearMap A K L B v)
  have hsurj := tensorAdicCompletionComapLinearMap_surjective A K L B v
  refine ⟨?_, hsurj⟩
  -- have hfin := comap_pi_algebra_finite A K L B v
  have hrank := finrank_tensorProduct_adicCompletion_eq_finrank_pi_adicCompletion A K L B v
  rwa [LinearMap.injective_iff_surjective_of_finrank_eq_finrank hrank]

/-- The L-algebra isomorphism `L ⊗[K] K_v ≅ ∏_{w|v} L_w`. -/
noncomputable def adicCompletionComapAlgEquiv (v : HeightOneSpectrum A) :
    L ⊗[K] v.adicCompletion K ≃ₐ[L] Π w : v.Extension B, w.1.adicCompletion L :=
  AlgEquiv.ofBijective (tensorAdicCompletionComapAlgHom A K L B v) <|
    tensorAdicCompletionComapAlgHom_bijective A K L B v

-- TODO : this should be automatically picked up
open scoped TensorProduct.RightActions in
instance : IsBiscalar L (v.adicCompletion K) (adicCompletionComapAlgEquiv A K L B v) :=
  instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap _

-- open scoped TensorProduct.RightActions in
-- /-- The continuous K_v-algebra isomorphism `L ⊗[K] K_v ≅ ∏_{w|v} L_w`. -/
-- noncomputable def adicCompletionComapRightContinuousAlgEquiv (v : HeightOneSpectrum A) :
--     L ⊗[K] v.adicCompletion K ≃A[v.adicCompletion K] Π w : v.Extension B, w.1.adicCompletion L :=
--   --let _ := comap_pi_algebra A K L B v |>.toSMul
--   -- have : IsModuleTopology (v.adicCompletion K) (∀ w : v.Extension B, w.1.adicCompletion L) :=
--   --   prodAdicCompletionComap_isModuleTopology A K L B v
--   IsModuleTopology.continuousAlgEquivOfAlgEquiv {
--     __ := SemialgHom.baseChangeRightOfAlgebraMap (adicCompletionComapSemialgHom' A K L B v)
--     __ := adicCompletionComapAlgEquiv A K L B v
--   }

open scoped TensorProduct.RightActions in
/-- The continuous L-algebra isomorphism `L ⊗[K] K_v ≅ ∏_{w|v} L_w`. -/
noncomputable def adicCompletionComapContinuousAlgEquiv (v : HeightOneSpectrum A) :
    L ⊗[K] v.adicCompletion K ≃A[L] Π w : v.Extension B, w.1.adicCompletion L :=
  have : IsBiscalar L (v.adicCompletion K) (adicCompletionComapAlgEquiv A K L B v).toAlgHom :=
    inferInstanceAs (IsBiscalar L (v.adicCompletion K) (adicCompletionComapAlgEquiv A K L B v))
  IsModuleTopology.continuousAlgEquivOfIsBiscalar K (v.adicCompletion K)
    (adicCompletionComapAlgEquiv A K L B v)
  -- {
  --   __ := adicCompletionComapAlgEquiv A K L B v
  --   __ := adicCompletionComapRightContinuousAlgEquiv A K L B v
  -- }

/-- The A-module isomorphism `B ⊗[A] K_v ≅ ∏_{w|v} L_w`. -/
noncomputable def adicCompletionComapIntegerLinearEquiv (v : HeightOneSpectrum A) :
    B ⊗[A] v.adicCompletion K ≃ₗ[A] ∀ w : v.Extension B, w.1.adicCompletion L :=
  (linearEquivTensorProductModule A K L B (v.adicCompletion K)).symm.trans
    ((adicCompletionComapAlgEquiv A K L B v).toLinearEquiv.restrictScalars A)

@[simp]
lemma adicCompletionComapIntegerLinearEquiv_tmul_apply (v : HeightOneSpectrum A) (b : B)
    (x : v.adicCompletion K) (w : Extension B v) :
    --letI := comap_algebra A K L B w.prop
    adicCompletionComapIntegerLinearEquiv A K L B v (b ⊗ₜ[A] x) w =
    (algebraMap B _ b) * (algebraMap _ _ x) := by
  rw [adicCompletionComapIntegerLinearEquiv, LinearEquiv.trans_apply,
    linearEquivTensorProductModule_symm_tmul]
  rfl

/-- The canonical A-linear map `B ⊗[A] 𝓞_v → B ⊗[A] K_v`. -/
noncomputable def adicCompletionTensorIntegerCoe :
    B ⊗[A] (v.adicCompletionIntegers K) →ₗ[A] B ⊗[A] (v.adicCompletion K) :=
  (Algebra.algHom A (adicCompletionIntegers K v) (adicCompletion K v)).toLinearMap.lTensor B

omit [Algebra.IsIntegral A B] [IsDedekindDomain B] [Module.Finite A B] in
@[simp]
lemma adicCompletionTensorIntegerCoe_tmul (b : B) (x : v.adicCompletionIntegers K) :
    adicCompletionTensorIntegerCoe A K B v (b ⊗ₜ x) = b ⊗ₜ x.val :=
  rfl

/-- `𝓞_v` as an `A`-submodule of `K_v`. -/
noncomputable def integerSubmodule (v : HeightOneSpectrum A) : Submodule A (adicCompletion K v) :=
  let s : Submodule (adicCompletionIntegers K v) _ := (adicCompletionIntegers K v).toSubmodule
  s.restrictScalars A

theorem adicCompletionComapIntegerLinearEquiv_bijOn (v : HeightOneSpectrum A) :
    Set.BijOn (adicCompletionComapIntegerLinearEquiv A K L B v)
    (LinearMap.range <| adicCompletionTensorIntegerCoe A K B v)
    (Submodule.pi Set.univ fun (w : Extension B v) ↦ integerSubmodule B L w.val) := by
  suffices h : ((adicCompletionComapIntegerLinearEquiv A K L B v).toEquiv ''
      (LinearMap.range (adicCompletionTensorIntegerCoe A K B v))) =
      Submodule.pi Set.univ
      (fun (w : Extension B v) ↦ (integerSubmodule B L w.val).restrictScalars A) from
    h ▸ Equiv.bijOn_image (adicCompletionComapIntegerLinearEquiv A K L B v).toEquiv
  apply Eq.trans _ congr(SetLike.coe $(adicCompletionComapAlgEquiv_integral A K L B v))
  rw [LinearMap.coe_range, ← Set.range_comp, AlgHom.coe_range,
    ← AlgHom.coe_restrictScalars' (R:=A), ← AlgHom.coe_toLinearMap,
    LinearEquiv.coe_toEquiv, ← LinearEquiv.coe_toLinearMap, ← LinearMap.coe_comp]
  congr
  refine TensorProduct.ext' (fun x y ↦ ?_)
  ext w
  simp [← IsScalarTower.algebraMap_apply, tensorAdicCompletionComapAlgHom_tmul_apply]

end IsDedekindDomain.HeightOneSpectrum
