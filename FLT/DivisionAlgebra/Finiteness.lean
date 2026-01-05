/-
Copyright (c) 2024 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, William Coram
-/
import FLT.HaarMeasure.HaarChar.AdeleRing
import FLT.Mathlib.GroupTheory.DoubleCoset
import FLT.Mathlib.Topology.HomToDiscrete
import FLT.HaarMeasure.HaarChar.RealComplex
import FLT.Mathlib.LinearAlgebra.TensorProduct.Basis
import FLT.Mathlib.MeasureTheory.Haar.Extension
import FLT.Mathlib.MeasureTheory.Measure.Haar.MulEquivHaarChar
import FLT.Mathlib.LinearAlgebra.TensorProduct.Basis
import FLT.Mathlib.Topology.HomToDiscrete
import FLT.Mathlib.Topology.Polish
import Mathlib.Topology.Metrizable.Urysohn
import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Topology.UniformSpace.Completion
import Mathlib.Topology.MetricSpace.Completion
/-

# Fujisaki's lemma

We prove a lemma which Voight (in his quaternion algebra book) attributes to Fujisaki:
if `D` is a finite-dimensional division algebra over a number field `K`
and if `U ⊆ (D ⊗[K] 𝔸_K^infty)ˣ` is a compact open subgroup then the double coset
space `Dˣ \ (D ⊗[K] 𝔸_K^infty)ˣ / U` is finite.

## Main definitions

Most of the definitions in this file are auxiliary definitions, in an `Aux` namespace.

## Main theorem

Fujisaki's lemma:

* NumberField.FiniteAdeleRing.DivisionAlgebra.finiteDoubleCoset

-/

suppress_compilation

open IsDedekindDomain MeasureTheory NumberField

-- this instance creates a nasty diamond for
-- `IsScalarTower K (FiniteAdeleRing A K) (FiniteAdeleRing B L)` when K = L and A = B, and
-- should probably be scoped (or even removed and statements changed so that they
-- don't need it).
attribute [-instance] instIsScalarTowerFiniteAdeleRing_fLT_1

-- this instance creates a nasty diamond for `IsScalarTower K K_∞ L_∞ when K = L and
-- should probably be scoped (or even removed and statements changed so that they
-- don't need it).
attribute [-instance] InfiniteAdeleRing.instIsScalarTower_fLT_1

open scoped TensorProduct

variable (K : Type*) [Field K] [NumberField K]
variable (D : Type*) [DivisionRing D] [Algebra K D]

-- notation for this file

set_option quotPrecheck false in
/-- `D_𝔸` is notation for `D ⊗[K] 𝔸_K`. -/
notation "D_𝔸" => (D ⊗[K] AdeleRing (𝓞 K) K)

-- abbrevs for this file, in an Aux namespace (as is most of this file;
-- it is local definitions and lemmas which we don't need. All we need
-- is the big result at the end.)

namespace NumberField.AdeleRing.DivisionAlgebra.Aux

/-- Df is notation for D ⊗ 𝔸_K^∞ -/
abbrev Df := D ⊗[K] (FiniteAdeleRing (𝓞 K) K)

/-- Dfx is notation for (D ⊗ 𝔸_K^∞)ˣ. -/
abbrev Dfx := (Df K D)ˣ

/-- Dinf is notation for D ⊗ 𝔸_K^∞ -/
abbrev Dinf := D ⊗[K] (NumberField.InfiniteAdeleRing K)

/-- Dinfx is notation for (D ⊗ 𝔸_K^∞)ˣ -/
abbrev Dinfx := (Dinf K D)ˣ

/-- The inclusion Dˣ → D_𝔸ˣ as a group homomorphism. -/
abbrev incl : Dˣ →* D_𝔸ˣ :=
  Units.map Algebra.TensorProduct.includeLeftRingHom.toMonoidHom

/-- The inclusion Dˣ → (D ⊗ 𝔸_K^∞)ˣ as a group homomorphism. -/
noncomputable abbrev incl₁ : Dˣ →* Dfx K D :=
  Units.map Algebra.TensorProduct.includeLeftRingHom.toMonoidHom

/-- The inclusion of K^n into 𝔸^n. -/
abbrev incl_Kn_𝔸Kn : (Fin (Module.finrank K D) → K) →
    (Fin (Module.finrank K D) → AdeleRing (𝓞 K) K) :=
  fun x i ↦ algebraMap K (AdeleRing (𝓞 K) K) (x i)

-- instances for Df, Dinf, D_𝔸

open scoped TensorProduct.RightActions

/-- The ℝ-algebra structure on Dinf K D. -/
instance : Algebra ℝ (Dinf K D) :=
  RingHom.toAlgebra' ((algebraMap (InfiniteAdeleRing K) (Dinf K D)).comp
  (algebraMap ℝ (InfiniteAdeleRing K))) <| by
    intro c x
    rw [RingHom.comp_apply, Algebra.commutes]

instance : IsScalarTower ℝ (InfiniteAdeleRing K) (Dinf K D) :=
  IsScalarTower.of_algebraMap_eq (fun _ ↦ rfl)

variable [FiniteDimensional K D]

/-- We put the Borel measurable space structure on D_𝔸 in this file. -/
instance : MeasurableSpace D_𝔸 := borel _

instance : BorelSpace D_𝔸 := ⟨rfl⟩

instance : Module.Finite ℝ (Dinf K D) :=
  Module.Finite.trans (InfiniteAdeleRing K) (Dinf K D)

/-- Dinf K D has the ℝ-module topology. -/
instance : IsModuleTopology ℝ (Dinf K D) := by
  /- (InfiniteAdeleRing K) has the ℝ-module topology.
    Now since (Dinf K D) has the (InfiniteAdeleRing K)-module topolology it also has the
    ℝ-module topology.
  -/
  rw [IsModuleTopology.trans ℝ (InfiniteAdeleRing K)]
  infer_instance

/-- Dinf K D is given the borel sigma algebra (for Haar measure). -/
instance : MeasurableSpace (Dinf K D) := borel (Dinf K D)

instance : BorelSpace (Dinf K D) := {measurable_eq := rfl }

/-- Df K D is given the borel sigma algebra (for Haar measure). -/
instance : MeasurableSpace (Df K D) := borel (Df K D)

instance : BorelSpace (Df K D) := { measurable_eq := rfl }

-- D ⊗ K_∞ is second countable because it's a finite ℝ-module
instance : SecondCountableTopology (Dinf K D) :=
  Module.Finite.secondCountabletopology ℝ (Dinf K D)

-- discreteness of K^n in 𝔸_K^n (which will be used to show discreteness of D in D_𝔸)
omit [FiniteDimensional K D] in
theorem Kn_discrete : ∀ x : (Fin (Module.finrank K D) → K),
    ∃ U : Set (Fin (Module.finrank K D) → AdeleRing (𝓞 K) K),
    IsOpen U ∧ (incl_Kn_𝔸Kn K D)⁻¹' U = {x} := by
  exact (DiscretePi (algebraMap K (AdeleRing (𝓞 K) K)) (Module.finrank K D))
    (NumberField.AdeleRing.discrete K)

/-- The K-algebra equivalence of D and K^n. -/
abbrev D_iso : (D ≃ₗ[K] ((Fin (Module.finrank K D) → K))) := Module.Finite.equivPi K D

-- Mathlib#29315....
attribute [local instance 1100] IsTopologicalSemiring.toIsModuleTopology

-- ...makes this work
example : IsModuleTopology (AdeleRing (𝓞 K) K)
    ((Fin (Module.finrank K D) → AdeleRing (𝓞 K) K)) := inferInstance

/-- The 𝔸_K-algebra equivalence of D_𝔸 and 𝔸_K^d. -/
abbrev D𝔸_iso : (D_𝔸 ≃ₗ[(AdeleRing (𝓞 K) K)] ((Fin (Module.finrank K D) → AdeleRing (𝓞 K) K))) :=
  ((TensorProduct.RightActions.Module.TensorProduct.comm _ _ _).symm).trans
    (TensorProduct.AlgebraTensorModule.finiteEquivPi K D (AdeleRing (𝓞 K) K))

/-- The topological 𝔸_K-linear equivalence D_𝔸 ≃ 𝔸_K^d. -/
abbrev D𝔸_iso_top : D_𝔸 ≃L[(AdeleRing (𝓞 K) K)]
    ((Fin (Module.finrank K D) → AdeleRing (𝓞 K) K)) :=
  IsModuleTopology.continuousLinearEquiv (D𝔸_iso K D)

theorem D_discrete_aux (U : Set (Fin (Module.finrank K D) → AdeleRing (𝓞 K) K)) :
    incl_Kn_𝔸Kn K D ⁻¹' U  =
    (D_iso K D) ''
      (⇑(D𝔸_iso_top K D) ∘ (Algebra.TensorProduct.includeLeft : D →ₐ[K] D_𝔸) ⁻¹' U) := by
  ext x
  constructor
  · intro hx
    use (D_iso K D).symm x
    simpa [← Algebra.algebraMap_eq_smul_one] using hx
  · intro ⟨y, hy1, hy2⟩
    have : (D𝔸_iso_top K D) ∘ (Algebra.TensorProduct.includeLeft : D →ₐ[K] D_𝔸) =
        (incl_Kn_𝔸Kn K D) ∘ (D_iso K D) := by
      ext d n
      simp [← Algebra.algebraMap_eq_smul_one]
    simpa [← hy2, this] using hy1

theorem D_discrete : ∀ x : D, ∃ U : Set D_𝔸,
    IsOpen U ∧ (Algebra.TensorProduct.includeLeft : D →ₐ[K] D_𝔸) ⁻¹' U = {x} := by
  apply Discrete_of_HomeoDiscrete (Y' := ((Fin (Module.finrank K D) → AdeleRing (𝓞 K) K)))
    (Algebra.TensorProduct.includeLeft : D →ₐ[K] D_𝔸) (D𝔸_iso_top K D)
  apply Discrete_of_HomDiscrete (X' := Fin (Module.finrank K D) → K)
    ((D𝔸_iso_top K D) ∘ (Algebra.TensorProduct.includeLeft : D →ₐ[K] D_𝔸)) (D_iso K D)
  simpa [D_discrete_aux] using Kn_discrete K D

/-- The additive subgroup D of D_𝔸. -/
def includeLeft_subgroup : AddSubgroup D_𝔸 :=
  AddMonoidHom.range (G := D) (Algebra.TensorProduct.includeLeft : D →ₐ[K] D_𝔸)

instance discrete_includeLeft_subgroup :
    DiscreteTopology (includeLeft_subgroup K D).carrier := by
  rw [includeLeft_subgroup, discreteTopology_iff_isOpen_singleton]
  rintro ⟨a, a', rfl⟩
  obtain ⟨U, hUopen, hUeq⟩ := (D_discrete K D) a'
  refine isOpen_mk.mpr ⟨U, hUopen, Set.image_val_inj.mp ?_⟩
  simp only [Subtype.image_preimage_coe, Set.image_singleton]
  let f : D → D ⊗[K] AdeleRing (𝓞 K) K :=
    (Algebra.TensorProduct.includeLeft : D →ₐ[K] D ⊗[K] AdeleRing (𝓞 K) K)
  change Set.range f ∩ U = {f a'}
  change f ⁻¹' U = {a'} at hUeq
  ext d
  simp [Set.ext_iff] at hUeq
  grind

instance : T2Space (D ⊗[K] AdeleRing (𝓞 K) K) := IsModuleTopology.t2Space (AdeleRing (𝓞 K) K)

instance discrete_principalSubgroup :
    DiscreteTopology (principalSubgroup (𝓞 K) K : Set (AdeleRing (𝓞 K) K)) := by
  rw [discreteTopology_iff_isOpen_singleton]
  rintro ⟨-, y, rfl⟩
  obtain ⟨U, hUopen, hU⟩ := NumberField.AdeleRing.discrete K y
  refine isOpen_mk.mpr ⟨U, hUopen, Set.image_val_inj.mp ?_⟩
  simp only [Subtype.image_preimage_coe, Set.image_singleton]
  let f : K → AdeleRing (𝓞 K) K := algebraMap K (AdeleRing (𝓞 K) K)
  change Set.range f ∩ U = {f y}
  change f ⁻¹' U = {y} at hU
  ext d
  simp [Set.ext_iff] at hU
  grind

-- we seem to have this twice?
instance compact_includeLeft_subgroup :
    CompactSpace (D_𝔸 ⧸ (includeLeft_subgroup K D)) := by
  let H := includeLeft_subgroup K D
  change CompactSpace (D_𝔸 ⧸ H)
  have key := NumberField.AdeleRing.cocompact K
  let π : (Fin (Module.finrank K D) → AdeleRing (𝓞 K) K) →+
      (Fin (Module.finrank K D) → AdeleRing (𝓞 K) K ⧸ principalSubgroup (𝓞 K) K) :=
    AddMonoidHom.compLeft (QuotientAddGroup.mk' _) _
  have hπ1 : Continuous π := by
    simp only [π, AddMonoidHom.compLeft, QuotientAddGroup.coe_mk', AddMonoidHom.coe_mk,
      ZeroHom.coe_mk]
    fun_prop
  have hπ2 : IsOpenQuotientMap π := by
    have : DiscreteTopology (principalSubgroup (𝓞 K) K : Set (AdeleRing (𝓞 K) K)) :=
      discrete_principalSubgroup K
    have key := TopologicalAddGroup.IsSES.ofClosedAddSubgroup (principalSubgroup (𝓞 K) K)
    exact IsOpenQuotientMap.piMap (fun _ ↦ key.isOpenQuotientMap)
  let φ : (Fin (Module.finrank K D) → AdeleRing (𝓞 K) K) →+ (D_𝔸 ⧸ H) :=
    AddMonoidHom.comp (QuotientAddGroup.mk' _) (D𝔸_iso_top K D).symm.toAddMonoidHom
  have hφ0 : π.ker ≤ φ.ker := by
    intro x hx
    replace hx : ∀ i, x i ∈ Set.range (algebraMap K (AdeleRing (𝓞 K) K)) := by
      simpa [π, funext_iff] using hx
    choose q hq using hx
    let d := (D_iso K D).symm q
    simp only [Algebra.algebraMap_eq_smul_one] at hq
    simp only [φ, AddMonoidHom.mem_ker, AddMonoidHom.comp_apply,
      QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff]
    use d
    simp only [LinearMap.toAddMonoidHom_coe, ContinuousLinearEquiv.toLinearEquiv_symm,
      LinearEquiv.coe_coe, LinearEquiv.eq_symm_apply]
    simp [d, hq]
  have hφ1 : Continuous φ := by
    simp only [φ, AddMonoidHom.coe_comp, QuotientAddGroup.coe_mk', LinearMap.toAddMonoidHom_coe]
    fun_prop
  have hφ2 : Function.Surjective φ :=
    (QuotientAddGroup.mk'_surjective _).comp (D𝔸_iso_top K D).symm.surjective
  let f : (Fin (Module.finrank K D) → AdeleRing (𝓞 K) K ⧸ principalSubgroup (𝓞 K) K) →+
    (D_𝔸 ⧸ H) := AddMonoidHom.liftOfSurjective π hπ2.surjective ⟨φ, hφ0⟩
  have hf0 : f ∘ π = φ := by ext; simp [f]
  have hf1 : Continuous f := by rwa [← hπ2.continuous_comp_iff, hf0]
  have hf2 : Function.Surjective f := by rwa [← hπ2.surjective.of_comp_iff, hf0]
  rw [← isCompact_univ_iff, ← Set.image_univ_of_surjective hf2]
  exact isCompact_univ.image hf1

open scoped NNReal in
lemma not_injective_of_large_measure : ∃ B : ℝ≥0, ∀ U : Set D_𝔸,
   IsOpen U → B < MeasureTheory.Measure.addHaar U →
    ¬ U.InjOn (QuotientAddGroup.mk : D_𝔸 →
        D_𝔸 ⧸ (Algebra.TensorProduct.includeLeftRingHom : D →+* D_𝔸).range.toAddSubgroup) := by
  let H := includeLeft_subgroup K D
  have : DiscreteTopology H := discrete_includeLeft_subgroup K D
  have : SecondCountableTopology (D ⊗[K] AdeleRing (𝓞 K) K) :=
    Homeomorph.secondCountableTopology (D𝔸_iso_top K D).toHomeomorph
  have : PolishSpace (D ⊗[K] AdeleRing (𝓞 K) K) := polish_of_locally_compact_second_countable _
  exact TopologicalAddGroup.IsSES.not_injOn_of_measure_gt H

section FiniteAdeleRing

/-- The K-algebra isomorphism `D_𝔸 ≃ D_∞ × D_f` -- adelic D is infinite adele D times
finite adele D. -/
abbrev D𝔸_prodRight : D_𝔸 ≃ₐ[K] Dinf K D × Df K D :=
  (Algebra.TensorProduct.prodRight K K D (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K))

/-- The (InfiniteAdeleRing K × FiniteAdeleRing (𝓞 K) K)-module structure on (Dinf K D × Df K D). -/
instance : Module (AdeleRing (𝓞 K) K) (Dinf K D × Df K D) where
  smul rs mn := (rs.1 • mn.1, rs.2 • mn.2)
  one_smul mn := by cases mn; ext; exacts [one_smul _ _, one_smul _ _]
  mul_smul rs rs' mn := by
    cases rs; cases rs'; cases mn
    ext <;>
    exact mul_smul _ _ _
  smul_zero rs := by cases rs; ext <;> exact smul_zero _
  smul_add rs mn mn' := by
    cases rs; cases mn; cases mn'
    ext <;>
    exact smul_add _ _ _
  add_smul rs rs' mn := by
    cases rs; cases rs'; cases mn
    ext <;>
    exact add_smul _ _ _
  zero_smul mn := by cases mn; ext <;> exact zero_smul _ _

/-- (Dinf K D × Df K D) has the 𝔸_K module topology. -/
instance [FiniteDimensional K D] :
    IsModuleTopology (AdeleRing (𝓞 K) K) (Dinf K D × Df K D) :=
  IsModuleTopology.instProd'

/-- The 𝔸_K linear map `D_𝔸 ≃ D_∞ × D_f`. -/
abbrev D𝔸_prodRight' : D_𝔸 ≃ₗ[AdeleRing (𝓞 K) K] (Dinf K D × Df K D) := {
  toFun := D𝔸_prodRight K D
  __ := D𝔸_prodRight K D
  map_add' a b := by
    exact RingHom.map_add (D𝔸_prodRight K D).toRingHom a b
  map_smul' m x := by
    simp only [RingHom.id_apply]
    obtain ⟨s, hx⟩ := TensorProduct.exists_finset x
    simp_rw [hx, Finset.smul_sum, map_sum, TensorProduct.RightActions.smul_def,
      TensorProduct.comm_tmul, TensorProduct.smul_tmul', TensorProduct.comm_symm_tmul,
      Finset.smul_sum]
    -- missing lemma probably
    rfl
}

/-- The continuous additive isomorphism `D_𝔸 ≃ D_∞ × D_f`. -/
abbrev D𝔸_prodRight'' : D_𝔸 ≃ₜ+ Dinf K D × Df K D where
  __ := D𝔸_prodRight K D
  continuous_toFun := IsModuleTopology.continuous_of_linearMap (D𝔸_prodRight' K D).toLinearMap
  continuous_invFun := IsModuleTopology.continuous_of_linearMap (D𝔸_prodRight' K D).symm.toLinearMap

/-- The equivalence of the units of D_𝔸 and the product of the
units of (D ⊗ 𝔸_K^f) and (D ⊗ 𝔸_K^∞). -/
abbrev D𝔸_prodRight_units : D_𝔸ˣ ≃* (Dinfx K D) × (Dfx K D) :=
  (Units.mapEquiv (D𝔸_prodRight K D)).trans (MulEquiv.prodUnits)

omit [FiniteDimensional K D] in
lemma smul_D𝔸_prodRight_symm (a : (Dinf K D)ˣ) (b : (Df K D)ˣ)
    (di : Dinf K D) (df : Df K D) :
  ((D𝔸_prodRight_units K D).symm (a, b)) • ((D𝔸_prodRight K D).symm (di, df)) =
    (D𝔸_prodRight K D).symm (a • di, b • df) :=
  (map_mul _ _ _).symm


lemma D𝔸_prodRight_units_cont : Continuous (D𝔸_prodRight_units K D) := by
  rw [ MulEquiv.coe_trans]
  -- annoying that fun_prop and continuity can't seem to do this
  -- it's about monoid and ring homs, it's the usual problem.
  apply Continuous.comp ?_ ?_
  · apply Continuous.prodMk
    · apply Continuous.units_map
      exact continuous_fst
    · apply Continuous.units_map
      exact continuous_snd
  · apply Continuous.units_map
    exact IsModuleTopology.continuous_of_linearMap (D𝔸_prodRight' K D).toLinearMap

lemma ringHaarChar_D𝔸 (a : Dinfx K D) (b : Dfx K D) :
    ringHaarChar ((D𝔸_prodRight_units K D).symm (a, b)) =
    ringHaarChar (MulEquiv.prodUnits.symm (a, b)) := by
  apply MeasureTheory.addEquivAddHaarChar_eq_addEquivAddHaarChar_of_continuousAddEquiv
    (D𝔸_prodRight'' K D)
  simp [MulEquivClass.map_mul]

/-- For any positive real `r`, there's some `ρ ∈ ℝˣ` such that the haar character of
`(ρ, 1) ∈ D_f × D_∞` is `r`. -/
lemma ringHaarChar_D𝔸_real_surjective (r : ℝ) (h : r > 0) :
    ∃ (ρ : ℝˣ), ringHaarChar
      ((D𝔸_prodRight_units K D).symm (((Units.map (algebraMap ℝ (Dinf K D))) ρ),1)) = r := by
  have a : IsUnit (r ^ (1 / Module.finrank ℝ (Dinf K D) : ℝ)) := by
    simp only [one_div, isUnit_iff_ne_zero, ne_eq]
    refine (Real.rpow_ne_zero (by positivity) ?_).mpr (by positivity)
    simp [Nat.ne_zero_iff_zero_lt, Module.finrank_pos]
  have := ringHaarChar_ModuleFinite_unit (K := ℝ) (R := Dinf K D) (a.unit)
  use a.unit
  rw [ringHaarChar_D𝔸, ringHaarChar_prod, map_one, mul_one]
  simp_all only [gt_iff_lt, RingHom.toMonoidHom_eq_coe, NNReal.coe_pow]
  have t : (ringHaarChar a.unit) = r ^ ((1 / Module.finrank ℝ (Dinf K D) : ℝ)) := by
    simp_rw [MeasureTheory.ringHaarChar_real, IsUnit.unit_spec, coe_nnnorm, Real.norm_eq_abs,
      one_div, abs_eq_self]
    positivity
  simp_rw [t, one_div]
  exact Real.rpow_inv_natCast_pow (by positivity) (Nat.ne_zero_iff_zero_lt.mpr Module.finrank_pos)

end FiniteAdeleRing

section AdeleRing

instance (vi : InfinitePlace K) : SecondCountableTopology (D ⊗[K] vi.Completion) :=
  Module.Finite.secondCountabletopology vi.Completion _

open scoped TensorProduct.RightActions in
variable
  [(vi : InfinitePlace K) → MeasurableSpace (D ⊗[K] vi.Completion)]
  [(vi : InfinitePlace K) → BorelSpace (D ⊗[K] vi.Completion)] in
lemma isCentralSimple_infinite_addHaarScalarFactor_left_mul_eq_right_mul_aux
    [Algebra.IsCentral K D] (u : (Π vi : InfinitePlace K, (D ⊗[K] vi.Completion))ˣ) :
    addEquivAddHaarChar (ContinuousAddEquiv.mulLeft u) =
    addEquivAddHaarChar (ContinuousAddEquiv.mulRight u) := by
  open MeasureTheory in
  have : BorelSpace (Π vi : InfinitePlace K, (D ⊗[K] vi.Completion)) := Pi.borelSpace
  let u' := MulEquiv.piUnits u
  have hl :
      addEquivAddHaarChar (ContinuousAddEquiv.mulLeft u)
      = ∏ vi, addEquivAddHaarChar (ContinuousAddEquiv.mulLeft (u' vi)) := by
    rw [← addEquivAddHaarChar_piCongrRight (fun vi ↦ ContinuousAddEquiv.mulLeft (u' vi))]
    congr
  have hr :
      addEquivAddHaarChar (ContinuousAddEquiv.mulRight u)
      = ∏ vi, addEquivAddHaarChar (ContinuousAddEquiv.mulRight (u' vi)) := by
    rw [← addEquivAddHaarChar_piCongrRight (fun vi ↦ ContinuousAddEquiv.mulRight (u' vi))]
    congr
  rw [hl, hr]; congr; funext vi
  apply
    IsSimpleRing.ringHaarChar_eq_addEquivAddHaarChar_mulRight (F := vi.Completion) (u' vi)

open Classical in
/-- The canonical `ℝ`-algebra structure on `InfinitePlace.Completion`. -/
def real_to_completion (vi : InfinitePlace K) : ℝ →+* vi.Completion :=
  if h : vi.IsReal
  then (InfinitePlace.Completion.ringEquivRealOfIsReal h).symm.toRingHom
  else
    (InfinitePlace.Completion.ringEquivComplexOfIsComplex (by simpa using h)).symm.toRingHom.comp
    Complex.ofRealHom

-- TODO: fix this approach in view of the diamond created with things like
-- `instAlgebraRealInfiniteAdeleRing_fLT`
-- (but everything below works, so I'm hesitant to touch it for now)

instance (vi : InfinitePlace K) : Algebra ℝ vi.Completion :=
  (real_to_completion K vi).toAlgebra

omit [NumberField K] in
lemma algebraMap_completion_def (vi : InfinitePlace K) :
    (algebraMap ℝ vi.Completion) = (real_to_completion K vi) := rfl

instance (vi : InfinitePlace K) : Module.Finite ℝ vi.Completion := by
  by_cases h : vi.IsReal
  · let e : vi.Completion ≃ₗ[ℝ] ℝ := {
      __ := InfinitePlace.Completion.ringEquivRealOfIsReal h
      map_smul' r x := by
        simp_all [Algebra.smul_def, algebraMap_completion_def, real_to_completion, ↓reduceDIte]
    }
    exact Module.Finite.of_injective _ e.injective
  · let e : vi.Completion ≃ₗ[ℝ] ℂ := {
      __ := InfinitePlace.Completion.ringEquivComplexOfIsComplex (by simpa using h)
      map_smul' r x := by
        simp_all [Algebra.smul_def, algebraMap_completion_def, real_to_completion, ↓reduceDIte]
    }
    exact Module.Finite.of_injective _ e.injective

instance (vi : InfinitePlace K) : ContinuousSMul ℝ vi.Completion := by
  refine continuousSMul_of_algebraMap ℝ vi.Completion ?_
  rw [algebraMap_completion_def]
  by_cases h : vi.IsReal
  · convert (InfinitePlace.Completion.isometryEquivRealOfIsReal h).symm.isometry_toFun.continuous
    funext x; simp_all [real_to_completion, ↓reduceDIte]; rfl
  · convert (InfinitePlace.Completion.isometryEquivComplexOfIsComplex
      (by simpa using h)).symm.isometry_toFun.continuous.comp Complex.continuous_ofReal
    funext x; simp_all [real_to_completion, ↓reduceDIte]; rfl

instance (vi : InfinitePlace K) : IsModuleTopology ℝ vi.Completion :=
  isModuleTopologyOfFiniteDimensional

open scoped TensorProduct.RightActions in
instance (vi : InfinitePlace K) : Algebra ℝ (D ⊗[K] vi.Completion) :=
  Algebra.compHom _ <| real_to_completion K vi

open scoped TensorProduct.RightActions in
instance (vi : InfinitePlace K) : IsScalarTower ℝ vi.Completion (D ⊗[K] vi.Completion) :=
  IsScalarTower.of_compHom ..

open scoped TensorProduct.RightActions in
instance (vi : InfinitePlace K) : IsModuleTopology ℝ (D ⊗[K] vi.Completion) := by
  rw [IsModuleTopology.trans ℝ vi.Completion]
  infer_instance

open scoped TensorProduct.RightActions in
instance : IsModuleTopology ℝ (Π vi : InfinitePlace K, (D ⊗[K] vi.Completion)) :=
  IsModuleTopology.instPi

omit [NumberField K] in
lemma algebraMap_completion {vi : InfinitePlace K} {x : ℝ} :
    (algebraMap ℝ (InfiniteAdeleRing K)) x vi = (algebraMap ℝ vi.Completion) x := by
  change
    ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm.toRingHom.comp (algebraMap ℝ _)) x vi
    = real_to_completion K vi x
  by_cases h : vi.IsReal
  · simp_all [real_to_completion, ↓reduceDIte,
      RingEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd]
    rfl
  · simp_all [-InfinitePlace.not_isReal_iff_isComplex, real_to_completion, ↓reduceDIte,
      RingEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd]
    rfl

lemma tensorPi_equiv_piTensor_map_mul {x y : Dinf K D} :
    tensorPi_equiv_piTensor K D InfinitePlace.Completion (x * y)
    = tensorPi_equiv_piTensor K D InfinitePlace.Completion x
      * tensorPi_equiv_piTensor K D InfinitePlace.Completion y :=
  -- we need that `tensorPi_equiv_piTensor` is a ring hom
  sorry

open scoped TensorProduct.RightActions in
/-- `tensorPi_equiv_piTensor` applied to `Dinf`, as a `ℝ`-linear map. -/
def Dinf_tensorPi_equiv_piTensor_aux :
    (Dinf K D) ≃ₗ[ℝ] Π vi : InfinitePlace K, (D ⊗[K] vi.Completion) := {
  __ := tensorPi_equiv_piTensor K D InfinitePlace.Completion
  map_smul' x y := by
    change tensorPi_equiv_piTensor K D InfinitePlace.Completion (x • y)
      = x • tensorPi_equiv_piTensor K D InfinitePlace.Completion y
    simp only [Algebra.smul_def, tensorPi_equiv_piTensor_map_mul];
    congr
    have h₁ : (algebraMap ℝ (Dinf K D)) x = 1 ⊗ₜ[K] (algebraMap ℝ (InfiniteAdeleRing K) x) := rfl
    have h₂ :
        (algebraMap ℝ ((i : InfinitePlace K) → D ⊗[K] i.Completion)) x
        = fun (i : InfinitePlace K) ↦ 1 ⊗ₜ[K] (algebraMap ℝ i.Completion x) := rfl
    rw [h₁, h₂, tensorPi_equiv_piTensor_apply]
    funext vi
    congr
    exact algebraMap_completion _
}

open scoped TensorProduct.RightActions in
/-- `tensorPi_equiv_piTensor` applied to `Dinf`, as a continuous `ℝ`-linear equiv. -/
def Dinf_tensorPi_equiv_piTensor :
    (Dinf K D) ≃L[ℝ] Π vi : InfinitePlace K, (D ⊗[K] vi.Completion) := {
  __ := Dinf_tensorPi_equiv_piTensor_aux ..
  continuous_toFun :=
    IsModuleTopology.continuous_of_linearMap (Dinf_tensorPi_equiv_piTensor_aux K D).toLinearMap
  continuous_invFun :=
    IsModuleTopology.continuous_of_linearMap (Dinf_tensorPi_equiv_piTensor_aux K D).symm.toLinearMap
}

open scoped TensorProduct.RightActions in
/-- `tensorPi_equiv_piTensor` applied to `Dinf`, as a monoid hom. -/
def Dinf_tensorPi_equiv_piTensor_monoidHom :
    (Dinf K D) →* Π vi : InfinitePlace K, (D ⊗[K] vi.Completion) := {
  __ := Dinf_tensorPi_equiv_piTensor K D
  map_one' := by
    rw [Algebra.TensorProduct.one_def]
    simp [Dinf_tensorPi_equiv_piTensor, Dinf_tensorPi_equiv_piTensor_aux,
      Dinf, InfiniteAdeleRing, tensorPi_equiv_piTensor_apply]
    rfl
  map_mul' _ _ := tensorPi_equiv_piTensor_map_mul ..
}

open scoped TensorProduct.RightActions in
lemma isCentralSimple_infinite_addHaarScalarFactor_left_mul_eq_right_mul
    [Algebra.IsCentral K D] (u : (Dinf K D)ˣ) :
    addEquivAddHaarChar (ContinuousAddEquiv.mulLeft u) =
    addEquivAddHaarChar (ContinuousAddEquiv.mulRight u) := by
  -- infinite places
  open MeasureTheory in
  let (vi : InfinitePlace K) : MeasurableSpace (D ⊗[K] vi.Completion) := borel _
  have (vi : InfinitePlace K) : BorelSpace (D ⊗[K] vi.Completion) := ⟨rfl⟩
  let e := Dinf_tensorPi_equiv_piTensor K D
  let u' := Units.map (Dinf_tensorPi_equiv_piTensor_monoidHom K D) u
  have hl :
      addEquivAddHaarChar (ContinuousAddEquiv.mulLeft u)
      = addEquivAddHaarChar (ContinuousAddEquiv.mulLeft u') := by
    apply addEquivAddHaarChar_eq_addEquivAddHaarChar_of_continuousAddEquiv {__ := e}
    intro x; have : e (u * x) = u' * e x := tensorPi_equiv_piTensor_map_mul ..
    simpa
  have hr :
      addEquivAddHaarChar (ContinuousAddEquiv.mulRight u)
      = addEquivAddHaarChar (ContinuousAddEquiv.mulRight u') := by
    apply addEquivAddHaarChar_eq_addEquivAddHaarChar_of_continuousAddEquiv {__ := e}
    intro x; have : e (x * u) = e x * u' := tensorPi_equiv_piTensor_map_mul ..
    simpa
  rw [hl, hr]
  apply isCentralSimple_infinite_addHaarScalarFactor_left_mul_eq_right_mul_aux

open scoped TensorProduct.RightActions in
lemma isCentralSimple_addHaarScalarFactor_left_mul_eq_right_mul
    [Algebra.IsCentral K D] (u : D_𝔸ˣ) :
    addEquivAddHaarChar (ContinuousAddEquiv.mulLeft u) =
    addEquivAddHaarChar (ContinuousAddEquiv.mulRight u) := by
  open IsDedekindDomain MeasureTheory in
  let u' := D𝔸_prodRight_units K D u
  have hl :
      addEquivAddHaarChar (ContinuousAddEquiv.mulLeft u)
      = addEquivAddHaarChar (ContinuousAddEquiv.mulLeft u'.1)
      * addEquivAddHaarChar (ContinuousAddEquiv.mulLeft u'.2) := by
    rw [← addEquivAddHaarChar_prodCongr
      (ContinuousAddEquiv.mulLeft u'.1) (ContinuousAddEquiv.mulLeft u'.2)]
    apply addEquivAddHaarChar_eq_addEquivAddHaarChar_of_continuousAddEquiv (D𝔸_prodRight'' K D)
    intro x; simp; rfl
  have hr :
      addEquivAddHaarChar (ContinuousAddEquiv.mulRight u)
      = addEquivAddHaarChar (ContinuousAddEquiv.mulRight u'.1)
      * addEquivAddHaarChar (ContinuousAddEquiv.mulRight u'.2) := by
    rw [← addEquivAddHaarChar_prodCongr
      (ContinuousAddEquiv.mulRight u'.1) (ContinuousAddEquiv.mulRight u'.2)]
    apply addEquivAddHaarChar_eq_addEquivAddHaarChar_of_continuousAddEquiv (D𝔸_prodRight'' K D)
    intro x; simp; rfl
  simp [hl, hr, Dinfx, Dfx, Df,
    isCentralSimple_infinite_addHaarScalarFactor_left_mul_eq_right_mul _,
    isCentralSimple_finite_addHaarScalarFactor_left_mul_eq_right_mul K D _]

end AdeleRing

section auxiliary_defs
-- We need a subset of D ⊗[K] 𝔸_K^f with positive finite measure
-- and a subset of D ⊗[K] K_∞ with positive finite measure. We build them
-- as compact neighbourhoods of 0.

/-- An auxiliary compact subset of D_𝔸^f with nonempty interior -/
def Uf : Set (D ⊗[K] (FiniteAdeleRing (𝓞 K) K)) := (exists_compact_mem_nhds 0).choose

theorem Uf.spec : IsCompact (Uf K D) ∧ (Uf K D) ∈ nhds 0 := (exists_compact_mem_nhds 0).choose_spec

/-- An auxiliary compact subset of D_∞ with nonempty interior -/
def Ui : Set (D ⊗[K] (InfiniteAdeleRing K)) := (exists_compact_mem_nhds 0).choose

theorem Ui.spec : IsCompact (Ui K D) ∧ (Ui K D) ∈ nhds 0 := (exists_compact_mem_nhds 0).choose_spec

end auxiliary_defs

open scoped Pointwise

open InfinitePlace.Completion Set Rat RestrictedProduct in
/-- An auxiliary definition of an increasing family of compact
subsets of D_𝔸, defined as the product of a compact neighbourhood of 0
at the finite places and a compact neighbourhood of 0, scaled by `r`,
at the infinite places.
-/
def Efamily (r : ℝ) : Set (D_𝔸) :=
  (D𝔸_prodRight'' K D).symm '' (r • Ui K D) ×ˢ (Uf K D)

lemma E_family_compact (r : ℝ) : IsCompact (Efamily K D r) := by
  refine IsCompact.image ?_ (by fun_prop)
  refine IsCompact.prod ?_ (Uf.spec K D).1
  exact IsCompact.image (Ui.spec K D).1 (show Continuous (fun x ↦ r • x) by fun_prop)

lemma E_family_nonempty_interior : (interior (Efamily K D 1)).Nonempty := by
  unfold Efamily
  rw [one_smul]
  change (interior ((D𝔸_prodRight'' K D).toHomeomorph.symm '' Ui K D ×ˢ Uf K D)).Nonempty
  rw [← Homeomorph.image_interior, Set.image_nonempty]
  use 0
  rw [mem_interior_iff_mem_nhds, Prod.zero_eq_mk, mem_nhds_prod_iff]
  exact ⟨Ui K D, (Ui.spec K D).2, Uf K D, (Uf.spec K D).2, subset_rfl⟩

open NNReal ENNReal in
lemma E_family_unbounded (B : ℝ≥0) :
    ∃ r, MeasureTheory.Measure.addHaar (Efamily K D r) > B := by
  -- For r a nonzero real, let di(r) be the image of r in D_∞ˣ
  let di (r : ℝˣ) : (Dinf K D)ˣ := ((Units.map (algebraMap ℝ (Dinf K D))) r)
  -- For r a nonzero real, let d(r) be the element (r,1)=(di(r),i) in D_𝔸ˣ, so it's
  -- r at the infinite places.
  let d : ℝˣ → D_𝔸ˣ :=
    fun r ↦ (D𝔸_prodRight_units K D).symm (di r, 1)
  -- By definition, scaling a set by `u` changes its measure by the Haar character of u.
  have hscale := ringHaarChar_mul_volume
    (MeasureTheory.Measure.addHaar : Measure (D ⊗[K] AdeleRing (𝓞 K) K))
    (X := Efamily K D 1)
  -- We now make the obvious claim that the r'th element of the family
  -- is what you get by scaling the 1st element by d(r) -- this is
  -- true by definition.
  have hfamily (r : ℝˣ) : Efamily K D r = (d r) • Efamily K D 1 := by
    ext x
    -- this is just unfolding definitions
    unfold Efamily
    rw [Set.mem_smul_set, Set.mem_image]
    constructor
    · rintro ⟨⟨xi, xf⟩, ⟨⟨a, ha, rfl⟩, hf⟩, rfl⟩
      use (D𝔸_prodRight'' K D).symm (a, xf)
      simp only [one_smul, Set.mem_image, Set.mem_prod, EmbeddingLike.apply_eq_iff_eq,
        exists_eq_right]
      refine ⟨⟨ha, hf⟩, ?_⟩
      simp only [d, Units.smul_def]
      nth_rw 2 [← one_smul (Df K D) xf]
      convert smul_D𝔸_prodRight_symm K D ((Units.map ↑(algebraMap ℝ (Dinf K D))) r) 1 a xf
    · rintro ⟨-, ⟨⟨a, b⟩, ⟨hzi, hzf⟩, rfl⟩, rfl⟩
      use (r • a, b)
      simp only [one_smul] at hzi
      refine ⟨⟨⟨a, hzi, rfl⟩, hzf⟩, ?_⟩
      convert (smul_D𝔸_prodRight_symm K D ((Units.map ↑(algebraMap ℝ (Dinf K D))) r) 1 a b).symm
      simp
  -- Now Efamily 1 is a compact neighbourhood of 1 so it has Haar measure which isn't 0 or ∞
  have hpos : Measure.addHaar (Efamily K D 1) ≠ 0 := by
    refine (MeasureTheory.Measure.measure_pos_of_nonempty_interior _ ?_).ne'
    apply E_family_nonempty_interior
  have hfin : Measure.addHaar (Efamily K D 1) ≠ ∞ :=
    IsCompact.measure_ne_top (E_family_compact K D 1)
  have hm : (Measure.addHaar (Efamily K D 1)).toNNReal ≠ 0 := by
    rw [toNNReal_ne_zero]
    exact ⟨hpos, hfin⟩
  -- Choose ρ such that the Haar charaacter of d(ρ) is (B + 1) / μ (Efamily 1)
  obtain ⟨ρ, hρ⟩ := ringHaarChar_D𝔸_real_surjective K D
    ((B + 1 : ℝ≥0) / (Measure.addHaar (Efamily K D 1)).toNNReal) (by positivity)
  -- this ρ works
  use ρ
  rw [hfamily, hscale, ← coe_toNNReal hfin]
  norm_cast
  change (ringHaarChar (d ρ) : ℝ) = _ at hρ
  -- indeed we need to show B < haar_char(d(ρ))*μ(Efamily 1)
  suffices ((B : ℝ) < ringHaarChar (d ρ) * (Measure.addHaar (Efamily K D 1)).toNNReal) by
    exact_mod_cast this
  rw [hρ]
  -- which simplifies to B < (B + 1)
  convert_to (B : ℝ) < (B + 1)
  · push_cast
    convert div_mul_cancel₀ _ _
    exact mt (NNReal.eq (m := 0)) hm
  · linarith

lemma existsE : ∃ E : Set (D_𝔸), IsCompact E ∧
    ∀ φ : D_𝔸 ≃ₜ+ D_𝔸, addEquivAddHaarChar φ = 1 → ∃ e₁ ∈ E, ∃ e₂ ∈ E,
    e₁ ≠ e₂ ∧ φ e₁ - φ e₂ ∈ Set.range (Algebra.TensorProduct.includeLeft : D →ₐ[K] D_𝔸) := by
  obtain ⟨B, hB⟩ := not_injective_of_large_measure K D
  obtain ⟨r, hr⟩ := E_family_unbounded K D B
  let E := Efamily K D r
  obtain ⟨U, hU, hKU, hU'⟩ := exists_isOpen_superset_and_isCompact_closure (E_family_compact K D r)
  use closure U, hU'
  intro φ hφ
  specialize hB (φ.symm ⁻¹' U) (hU.preimage φ.symm.continuous)
  replace hr : B < Measure.addHaar U := hr.trans_le (measure_mono hKU)
  replace hφ : addEquivAddHaarChar φ.symm = 1 := by
    simpa [hφ] using (addEquivAddHaarChar_trans (φ := φ) (ψ := φ.symm)).symm
  have foo : Measure.addHaar U = Measure.addHaar (⇑φ.symm ⁻¹' U) := by
    rw [← one_smul NNReal (Measure.addHaar (φ.symm ⁻¹' U)), ← hφ,
      addEquivAddHaarChar_smul_preimage]
  rw [foo] at hr
  specialize hB hr
  simp only [Set.InjOn, not_forall] at hB
  obtain ⟨x, hx, y, hy, h, hne⟩ := hB
  rw [QuotientAddGroup.eq_iff_sub_mem] at h
  exact ⟨φ.symm x, subset_closure hx, φ.symm y, subset_closure hy, by simpa, by simpa⟩

/-- An auxiliary set E used in the proof of Fujisaki's lemma. -/
def E : Set D_𝔸 := (existsE K D).choose

lemma E_compact : IsCompact (E K D) := (existsE K D).choose_spec.1

lemma E_noninjective_left {x : D_𝔸ˣ} (h : x ∈ ringHaarChar_ker D_𝔸) :
    ∃ e₁ ∈ E K D, ∃ e₂ ∈ E K D, e₁ ≠ e₂ ∧
    x * e₁ - x * e₂ ∈ Set.range (Algebra.TensorProduct.includeLeft : D →ₐ[K] D_𝔸) :=
  (existsE K D).choose_spec.2 (ContinuousAddEquiv.mulLeft x) h

lemma E_noninjective_right [Algebra.IsCentral K D] {x : D_𝔸ˣ} (h : x ∈ ringHaarChar_ker D_𝔸) :
    ∃ e₁ ∈ E K D, ∃ e₂ ∈ E K D, e₁ ≠ e₂ ∧
    e₁ * x⁻¹ - e₂ * x⁻¹  ∈ Set.range (Algebra.TensorProduct.includeLeft : D →ₐ[K] D_𝔸) := by
  let φ : D_𝔸 ≃ₜ+ D_𝔸 := ContinuousAddEquiv.mulRight x⁻¹
  have hφ : addEquivAddHaarChar φ = 1 := by
    rwa [ ← inv_mem_iff, mem_ringHaarChar_ker, ringHaarChar_apply,
      isCentralSimple_addHaarScalarFactor_left_mul_eq_right_mul K D x⁻¹] at h
  exact (existsE K D).choose_spec.2 φ hφ

open scoped Pointwise in
/-- An auxiliary set X used in the proof of Fukisaki's lemma. Defined as E - E. -/
def X : Set D_𝔸 := E K D - E K D

open scoped Pointwise in
/-- An auxiliary set Y used in the proof of Fukisaki's lemma. Defined as X * X. -/
def Y : Set D_𝔸 := X K D * X K D

lemma X_compact : IsCompact (X K D) := by
  simpa only [Set.image_prod, Set.image2_sub] using (IsCompact.image_of_continuousOn
    ((E_compact K D).prod (E_compact K D)) ((continuous_fst.sub continuous_snd).continuousOn))

lemma Y_compact : IsCompact (Y K D) := by
  simpa only [Set.image_prod, Set.image2_mul] using (IsCompact.image_of_continuousOn
    ((X_compact K D).prod (X_compact K D)) ((continuous_fst.mul continuous_snd).continuousOn))

lemma X_meets_kernel {β : D_𝔸ˣ} (hβ : β ∈ ringHaarChar_ker D_𝔸) :
    ∃ x ∈ X K D, ∃ d ∈ Set.range (incl K D : Dˣ → D_𝔸ˣ), β * x = d := by
  obtain ⟨e1, he1, e2, he2, noteq, b, hb⟩ := E_noninjective_left K D hβ
  refine ⟨e1 - e2, by simpa only using (Set.sub_mem_sub he1 he2), ?_⟩
  obtain ⟨b1, rfl⟩ : IsUnit b := by
    simp_rw [← mul_sub_left_distrib, Algebra.TensorProduct.includeLeft_apply] at hb
    have h1 : ↑β * (e1 - e2) ≠ 0 := by
      simpa only [ne_eq, not_not, Units.mul_right_eq_zero] using (sub_ne_zero_of_ne noteq)
    simp only [isUnit_iff_ne_zero, ne_eq]
    rintro rfl
    simp only [← hb, TensorProduct.zero_tmul, ne_eq, not_true_eq_false] at h1
  exact ⟨incl K D b1, ⟨b1, rfl⟩, by simpa [mul_sub] using hb.symm⟩

lemma X_meets_kernel' [Algebra.IsCentral K D] {β : D_𝔸ˣ} (hβ : β ∈ ringHaarChar_ker D_𝔸) :
    ∃ x ∈ X K D, ∃ d ∈ Set.range (incl K D : Dˣ → D_𝔸ˣ), x * β⁻¹ = d := by
  obtain ⟨e1, he1, e2, he2, noteq, b, hb⟩ := E_noninjective_right K D hβ
  refine ⟨e1 - e2, by simpa only using (Set.sub_mem_sub he1 he2), ?_⟩
  obtain ⟨b1, rfl⟩ : IsUnit b := by
    simp_rw [← mul_sub_right_distrib, Algebra.TensorProduct.includeLeft_apply] at hb
    have h1 : (e1 - e2) * ↑β⁻¹ ≠ 0 := by
      simpa only [ne_eq, Units.mul_left_eq_zero] using (sub_ne_zero_of_ne noteq)
    simp only [isUnit_iff_ne_zero, ne_eq]
    rintro rfl
    simp only [← hb, TensorProduct.zero_tmul, ne_eq, not_true_eq_false] at h1
  exact ⟨incl K D b1, ⟨b1, rfl⟩, by simpa [sub_mul] using hb.symm⟩

/-- An auxiliary set T used in the proof of Fukisaki's lemma. Defined as Y ∩ Dˣ. -/
def T : Set D_𝔸ˣ := ((↑) : D_𝔸ˣ → D_𝔸) ⁻¹' (Y K D) ∩ Set.range ((incl K D : Dˣ → D_𝔸ˣ))

lemma T_finite_extracted1 : IsCompact (Y K D ∩
    Set.range (Algebra.TensorProduct.includeLeft : D →ₐ[K] D_𝔸)) := by
  refine IsCompact.inter_right (Y_compact K D) ?_
  have : DiscreteTopology (includeLeft_subgroup K D).carrier := by
    infer_instance
  simpa [includeLeft_subgroup] using AddSubgroup.isClosed_of_discrete
    (H := includeLeft_subgroup K D)

lemma T_finite : Set.Finite (T K D) := by
  have h := IsCompact.finite (T_finite_extracted1 K D)
    ⟨(inter_Discrete (includeLeft_subgroup K D).carrier (Y K D))⟩
  have h1 : Units.val '' T K D ⊆ (Y K D) ∩
      (Set.range (Algebra.TensorProduct.includeLeft : D →ₐ[K] D_𝔸)) := by
    rintro _ ⟨t, ⟨ht1, d, rfl⟩, rfl⟩
    exact ⟨ht1, d, rfl⟩
  exact Set.Finite.of_finite_image (Set.Finite.subset h h1)
    (Function.Injective.injOn Units.val_injective)

open scoped Pointwise in
/-- An auxiliary set C used in the proof of Fukisaki's lemma. Defined as T⁻¹X × X. -/
def C : Set (D_𝔸 × D_𝔸) := ((((↑) : D_𝔸ˣ → D_𝔸) '' (T K D)⁻¹) * X K D) ×ˢ X K D

lemma C_compact : IsCompact (C K D) := by
  refine IsCompact.prod ?_ (X_compact K D)
  simpa only [Set.image_prod, Set.image2_mul] using
    (IsCompact.image_of_continuousOn (IsCompact.prod (IsCompact.image_of_continuousOn
    (IsCompact.inv (Set.Finite.isCompact (T_finite K D))) (Continuous.comp_continuousOn'
    (Units.continuous_val) (continuousOn_id' (T K D)⁻¹)))
    (X_compact K D)) ((continuous_fst.mul continuous_snd).continuousOn))

lemma antidiag_mem_C [Algebra.IsCentral K D] {β : D_𝔸ˣ} (hβ : β ∈ ringHaarChar_ker D_𝔸) :
    ∃ b ∈ Set.range (incl K D : Dˣ → D_𝔸ˣ),
    ∃ ν ∈ ringHaarChar_ker D_𝔸,
    β = b * ν ∧ ((ν : D_𝔸), ((ν⁻¹ : D_𝔸ˣ) : D_𝔸)) ∈ C K D := by
  obtain ⟨x1, hx1, b1, ⟨b1, rfl⟩, eq1⟩ := X_meets_kernel K D hβ
  obtain ⟨x2, hx2, b2, ⟨b2, rfl⟩, eq2⟩ := X_meets_kernel' K D hβ
  obtain ⟨x1, rfl⟩ : IsUnit x1 := ⟨↑β⁻¹ * incl K D b1,
    ((Units.eq_inv_mul_iff_mul_eq β).mpr eq1).symm⟩
  obtain ⟨x2, rfl⟩ : IsUnit x2 := ⟨incl K D b2 * β, ((Units.mul_inv_eq_iff_eq_mul β).mp eq2).symm⟩
  have h : x2 * x1 ∈ T K D := ⟨by simpa only [Y] using Set.mul_mem_mul hx2 hx1,
    b2 * b1, by norm_cast at eq1 eq2; rw [map_mul, ← eq2, ← eq1]; group⟩
  refine ⟨incl K D b1, by simp only [Set.mem_range, exists_apply_eq_apply],  x1⁻¹, ?_,
    eq_mul_inv_of_mul_eq (Units.val_inj.mp eq1), ?_, hx1⟩
  · rw [(Eq.symm (inv_mul_eq_of_eq_mul (eq_mul_inv_of_mul_eq (Units.val_inj.mp eq1))))]
    exact (Subgroup.mul_mem_cancel_right (ringHaarChar_ker (D ⊗[K] AdeleRing (𝓞 K) K)) hβ).mpr
      ((Subgroup.inv_mem_iff (ringHaarChar_ker (D ⊗[K] AdeleRing (𝓞 K) K))).mpr
      (NumberField.AdeleRing.units_mem_ringHaarCharacter_ker K D b1))
  · obtain ⟨t, ht, ht1⟩ := exists_eq_right'.mpr h
    simp_rw [(Eq.symm (inv_mul_eq_of_eq_mul (eq_mul_inv_of_mul_eq ht1)))]
    exact Set.mem_mul.mpr ⟨↑t⁻¹, Set.mem_image_of_mem Units.val ht, x2, hx2, rfl⟩



/-- The inclusion of `ringHaarChar_ker D_𝔸` into the product space `D_𝔸 × D_𝔸ᵐᵒᵖ`. -/
def incl₂ : ringHaarChar_ker D_𝔸 → Prod D_𝔸 D_𝔸ᵐᵒᵖ :=
  fun u => Units.embedProduct D_𝔸 (Subgroup.subtype (ringHaarChar_ker D_𝔸) u)

/-- An auxiliary set used in the proof of compact_quotient'. -/
def M : Set (ringHaarChar_ker D_𝔸) := Set.preimage (incl₂ K D)
  (Set.image (fun p => (p.1, MulOpposite.op p.2)) (Aux.C K D))

/-- The map from `ringHaarChar_ker D_𝔸` to the quotient `Dˣ \ ringHaarChar_ker D_𝔸`. -/
abbrev toQuot (a : ringHaarChar_ker D_𝔸) : (_root_.Quotient (QuotientGroup.rightRel
    ((MonoidHom.range (incl K D)).comap (ringHaarChar_ker D_𝔸).subtype))) :=
  (Quotient.mk (QuotientGroup.rightRel ((MonoidHom.range (incl K D)).comap
  (ringHaarChar_ker D_𝔸).subtype)) a)

lemma toQuot_cont : Continuous (toQuot K D) where
  isOpen_preimage := fun _ a ↦ a

lemma toQuot_surjective [Algebra.IsCentral K D] : (toQuot K D) '' (M K D) = Set.univ := by
  rw [Set.eq_univ_iff_forall]
  rintro ⟨a, ha⟩
  obtain ⟨c, hc, ν, hν, rfl, h31⟩ := Aux.antidiag_mem_C K D ha
  simp only [toQuot, Subgroup.comap_subtype, Set.mem_image, Subtype.exists]
  refine ⟨ν, hν, ?_, ?_ ⟩
  · simp only [M, Set.mem_preimage, Set.mem_image, Prod.exists]
    exact ⟨ν, Units.val (ν⁻¹), h31, rfl⟩
  · have : Quot.mk ⇑(QuotientGroup.rightRel ((incl K D).range.subgroupOf
        (ringHaarChar_ker (D ⊗[K] AdeleRing (𝓞 K) K)))) ⟨c * ν, ha⟩ =
        Quot.mk ⇑(QuotientGroup.rightRel ((incl K D).range.subgroupOf
        (ringHaarChar_ker (D ⊗[K] AdeleRing (𝓞 K) K))))
        ⟨ν, hν⟩ := by
      refine Quot.sound ?_
      rw [@QuotientGroup.rightRel_apply]
      refine Subgroup.mem_subgroupOf.mpr ?_
      simp only [@Subgroup.coe_mul, InvMemClass.coe_inv, mul_inv_rev, mul_inv_cancel_left,
        inv_mem_iff, MonoidHom.mem_range]
      exact hc
    rw [this]
    rfl

lemma incl₂_isClosedEmbedding : Topology.IsClosedEmbedding (incl₂ K D) := by
  apply Units.isClosedEmbedding_embedProduct.comp
  refine Topology.IsClosedEmbedding.of_continuous_injective_isClosedMap
    (continuous_iff_le_induced.mpr fun U a ↦ a)
    (Subgroup.subtype_injective (ringHaarChar_ker (D ⊗[K] AdeleRing (𝓞 K) K))) ?_
  simp only [Subgroup.coe_subtype]
  refine Topology.IsInducing.isClosedMap ({ eq_induced := rfl }) ?_
  simp only [Subtype.range_coe_subtype, SetLike.setOf_mem_eq]
  exact IsClosed.preimage (continuous_id')
    (IsClosed.preimage (map_continuous ringHaarChar) (by simp))

lemma ImAux_isCompact : IsCompact ((fun p ↦ (p.1, MulOpposite.op p.2)) '' Aux.C K D) :=
  IsCompact.image (Aux.C_compact K D) <| by fun_prop

lemma M_compact : IsCompact (M K D) := Topology.IsClosedEmbedding.isCompact_preimage
  (incl₂_isClosedEmbedding K D) (ImAux_isCompact K D)

/-- The restriction of ringHaarChar_ker D_𝔸 to (D ⊗ 𝔸_K^∞)ˣ via D𝔸_iso_prod_units. -/
abbrev rest₁ : ringHaarChar_ker D_𝔸 → Dfx K D :=
  fun a => (D𝔸_prodRight_units K D) a.val |>.2

lemma rest₁_continuous : Continuous (rest₁ K D) :=
  Continuous.comp continuous_snd
  (Continuous.comp (D𝔸_prodRight_units_cont K D) continuous_subtype_val)

lemma ringHaarChar_D𝔸_prodRight_units_aux (r : ℝ) (h : r > 0) :
    ∃ y, ringHaarChar ((D𝔸_prodRight_units K D).symm (y,1)) = r := by
  obtain ⟨ρ, hρ⟩ := ringHaarChar_D𝔸_real_surjective K D r h
  use ((Units.map (algebraMap ℝ (Dinf K D))) ρ)

open scoped NNReal in
lemma rest₁_surjective : Function.Surjective (rest₁ K D) := by
  intro x
  simp only [Subtype.exists]
  set r : ℝ≥0 := ringHaarChar ((D𝔸_prodRight_units K D).symm (1,x)) with hr_def
  have hr : r > 0 := addEquivAddHaarChar_pos _
  obtain ⟨y, hy⟩ : ∃ y, ringHaarChar ((D𝔸_prodRight_units K D).symm (y,1)) = r := by
    obtain ⟨y, hy⟩ := ringHaarChar_D𝔸_prodRight_units_aux K D r hr
    use y
    exact_mod_cast hy
  use (D𝔸_prodRight_units K D).symm (y⁻¹, x)
  constructor
  · rw [rest₁]
    refine Units.val_inj.mp ?_
    simp only [MulEquiv.apply_symm_apply]
  · ext
    simp only [ContinuousMonoidHom.coe_toMonoidHom, MonoidHom.coe_coe, NNReal.coe_one,
      NNReal.coe_eq_one]
    have : (y⁻¹, x) = (y, 1)⁻¹ * (1, x) := by
      ext <;> simp
    simp_rw [this, map_mul, map_inv, hy, ← hr_def, inv_mul_cancel₀ hr.ne']

-- the goal that comes up when you define the map `Dˣ \ D_𝔸^(1) to Dˣ \ (Dfx K D)`
-- below using Quot.lift
lemma incl_D𝔸quot_equivariant : ∀ (a b : ↥(ringHaarChar_ker D_𝔸)),
    (QuotientGroup.rightRel (Subgroup.comap (ringHaarChar_ker D_𝔸).subtype
    (AdeleRing.DivisionAlgebra.Aux.incl K D).range)) a b →
    (Quotient.mk (QuotientGroup.rightRel (incl₁ K D).range) (rest₁ K D a) =
     Quotient.mk (QuotientGroup.rightRel (incl₁ K D).range) (rest₁ K D b)) := by
  refine fun a b hab ↦ Quotient.eq''.mpr ?_
  obtain ⟨⟨t, t', ht⟩, rfl⟩ := hab
  simp_rw [QuotientGroup.rightRel, MulAction.orbitRel, MulAction.orbit, Set.mem_range,
    Subtype.exists, Subgroup.mk_smul, smul_eq_mul, MonoidHom.mem_range, exists_prop,
    exists_exists_eq_and]
  use t'
  have : incl₁ K D t' =
      ((D𝔸_prodRight_units K D) (AdeleRing.DivisionAlgebra.Aux.incl K D t')).2 := by
    rfl
  simp_rw [this, ht, ← Prod.snd_mul, Subgroup.subtype_apply, Subgroup.comap_subtype, ← map_mul]
  rfl

/-- The obvious map Dˣ \ D_𝔸^(1) to Dˣ \ (Dfx K D). -/
abbrev incl_D𝔸quot : Quotient (QuotientGroup.rightRel
    ((MonoidHom.range (NumberField.AdeleRing.DivisionAlgebra.Aux.incl K D)).comap
    (ringHaarChar_ker D_𝔸).subtype)) →
    Quotient (QuotientGroup.rightRel (incl₁ K D).range) :=
  Quot.lift
    (fun a => Quotient.mk (QuotientGroup.rightRel (incl₁ K D).range) (rest₁ K D a))
    (incl_D𝔸quot_equivariant K D)

lemma incl_D𝔸quot_continuous : Continuous (incl_D𝔸quot K D) := by
  refine Continuous.quotient_lift ?_ (incl_D𝔸quot_equivariant K D)
  exact Continuous.comp' ({isOpen_preimage := fun s a ↦ a}) (rest₁_continuous K D)

lemma incl_D𝔸quot_surjective : Function.Surjective (incl_D𝔸quot K D) := by
  refine (Quot.surjective_lift (f := fun a => Quotient.mk (QuotientGroup.rightRel (incl₁ K D).range)
    (rest₁ K D a)) (incl_D𝔸quot_equivariant K D)).mpr ?_
  refine Set.range_eq_univ.mp ?_
  ext x
  simp only [Set.mem_range, Subtype.exists, Set.mem_univ, iff_true]
  obtain ⟨a, ha⟩ : ∃ a : (ringHaarChar_ker D_𝔸),
      (rest₁ K D) a = x.out := rest₁_surjective K D _
  use a
  simp [ha]

end Aux

open Aux

variable [FiniteDimensional K D]

open scoped TensorProduct.RightActions

/-- Dˣ \ D_𝔸^{(1)} is compact. -/
lemma compact_quotient [Algebra.IsCentral K D] :
    CompactSpace (_root_.Quotient (QuotientGroup.rightRel
    ((MonoidHom.range (incl K D)).comap (ringHaarChar_ker D_𝔸).subtype))) :=
  isCompact_univ_iff.mp (by simpa only [toQuot_surjective, Set.image_univ] using
    (((IsCompact.image (M_compact K D) (toQuot_cont K D)))))

variable [Algebra.IsCentral K D]

/-- Dˣ \ D_𝔸^fˣ is compact. -/
theorem _root_.NumberField.FiniteAdeleRing.DivisionAlgebra.units_cocompact :
    CompactSpace (_root_.Quotient (QuotientGroup.rightRel (incl₁ K D).range)) := by
  have := isCompact_univ_iff.mpr (NumberField.AdeleRing.DivisionAlgebra.compact_quotient K D)
  apply isCompact_univ_iff.mp
  have := IsCompact.image (this) (incl_D𝔸quot_continuous K D)
  rw [Set.image_univ_of_surjective (incl_D𝔸quot_surjective K D)] at this
  exact this

-- Voight "Main theorem 27.6.14(b) (Fujisaki's lemma)"
/-!
If `D` is a finite-dimensional division `K`-algebra with centre a number field `K`
then the double coset space `Dˣ \ (D ⊗ 𝔸_K^infty)ˣ / U` is finite for any open subgroup `U`
of `(D ⊗ 𝔸_K^infty)ˣ`.
-/
open scoped TensorProduct.RightActions in
theorem _root_.NumberField.FiniteAdeleRing.DivisionAlgebra.finiteDoubleCoset
    {U : Subgroup (Dfx K D)} (hU : IsOpen (U : Set (Dfx K D))) :
    Finite (DoubleCoset.Quotient (Set.range (incl₁ K D)) U) := by
  have ToFinCover := IsCompact.elim_finite_subcover
    (ι := (DoubleCoset.Quotient (Set.range (incl₁ K D)) U))
    (U := fun q ↦ Quot.mk ⇑(QuotientGroup.rightRel (incl₁ K D).range) ''
    DoubleCoset.doubleCoset (Quotient.out q) (Set.range ⇑(incl₁ K D)) U) (isCompact_univ_iff.mpr
    (NumberField.FiniteAdeleRing.DivisionAlgebra.units_cocompact K D))
  have ⟨t, FinCover_descended⟩ := ToFinCover (DoubleCoset.isOpen_doubleCoset_rightrel_mk
    ((incl₁ K D).range) U hU) (DoubleCoset.union_image_mk_rightRel (incl₁ K D).range U
    ▸ Set.Subset.rfl)
  apply (DoubleCoset.iUnion_finset_quotTodoubleCoset ((incl₁ K D).range) U).mp
  exact ⟨t, DoubleCoset.union_finset_rightrel_cover ((incl₁ K D).range) U t FinCover_descended⟩

end DivisionAlgebra

end AdeleRing

end NumberField
