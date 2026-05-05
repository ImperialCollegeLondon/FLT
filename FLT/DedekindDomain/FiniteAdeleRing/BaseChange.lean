/-
Copyright (c) 2025 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Matthew Jasper
-/
module

public import FLT.DedekindDomain.Completion.BaseChange
public import FLT.DedekindDomain.FiniteAdeleRing.TensorRestrictedProduct
public import FLT.Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import FLT.Mathlib.Topology.Algebra.RestrictedProduct.Module
public import FLT.Mathlib.Topology.Algebra.Algebra.Hom
public import FLT.Mathlib.LinearAlgebra.Pi
public import Mathlib.RingTheory.Flat.TorsionFree

/-!

# Base change of adele rings.

If `A` is a Dedekind domain with field of fractions `K`, if `L/K` is a finite separable
extension and if `B` is the integral closure of `A` in `L`, then `B` is also a Dedekind
domain. Hence the rings of finite adeles `𝔸_K^∞` and `𝔸_L^∞` (defined using `A` and `B`)
are defined. In this file we define the natural `K`-algebra map `𝔸_K^∞ → 𝔸_L^∞` and
the natural `L`-algebra map `𝔸_K^∞ ⊗[K] L → 𝔸_L^∞`, and show that the latter map
is an isomorphism.

## Main definitions

* `FiniteAdeleRing.baseChangeAlgEquiv : L ⊗[K] 𝔸ᶠ[A, K] ≃ₐ[L] 𝔸ᶠ[B, L]`

## Main theorems

* `𝔸ᶠ[B, L]` has the `𝔸ᶠ[A, K]`-module topology, shown as an instance.

-/

@[expose] public section

variable (A K L B : Type*) [CommRing A] [CommRing B] [Algebra A B] [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K] [Algebra B L] [IsDedekindDomain A]
    [Algebra K L] [Algebra A L] [IsScalarTower A B L] [IsScalarTower A K L] [Module.Finite A B]
    [IsDedekindDomain B] [IsFractionRing B L]

namespace IsDedekindDomain

open IsDedekindDomain HeightOneSpectrum adicCompletion Extension

open scoped TensorProduct -- ⊗ notation for tensor product

lemma tendsTo_comap_cofinite [FaithfulSMul A B] :
    Filter.Tendsto (under A (B:=B)) Filter.cofinite Filter.cofinite :=
  have : FaithfulSMul A (FractionRing B) := FractionRing.instFaithfulSMul A B
  letI : Algebra (FractionRing A) (FractionRing B) :=
    FractionRing.liftAlgebra A (FractionRing B)
  (Filter.Tendsto.cofinite_of_finite_preimage_singleton <|
    Extension.finite A (FractionRing A) (FractionRing B) B)

lemma cofinite_mapsTo_adicCompletionSemialgHom :
    ∀ᶠ (w : HeightOneSpectrum B) in Filter.cofinite,
    Set.MapsTo (Extension.adicCompletionSemialgHom K L (v := under A w) ⟨w, rfl⟩)
      (adicCompletionIntegers K (under A w)) (adicCompletionIntegers L w) := by
  apply Filter.Eventually.of_forall
  intro w
  exact Set.image_subset_iff.1 <| adicCompletionSemialgHom_image_adicCompletionIntegers K L ⟨w, rfl⟩

namespace FiniteAdeleRing

@[inherit_doc]
scoped notation:max "𝔸ᶠ[" A ", " K "]" => FiniteAdeleRing A K

/-- The ring homomorphism `𝔸_K^∞ → 𝔸_L^∞` for `L/K` an extension of number fields. -/
noncomputable def mapRingHom : 𝔸ᶠ[A, K] →+* 𝔸ᶠ[B, L] :=
  have : FaithfulSMul A B := FaithfulSMul.of_field_isFractionRing A B K L
  RestrictedProduct.mapAlongRingHom (adicCompletion K) (adicCompletion L) (under A)
    (tendsTo_comap_cofinite A B) (fun w ↦ adicCompletionSemialgHom K L (v := w.under A) ⟨w, rfl⟩)
    (cofinite_mapsTo_adicCompletionSemialgHom A K L B)

/-- The ring homomorphism `𝔸_K^∞ → 𝔸_L^∞` for `L/K` an extension of number fields,
as a morphism lying over the canonical map `K → L`. -/
noncomputable def mapSemialgHom :
    𝔸ᶠ[A, K] →SA[algebraMap K L] 𝔸ᶠ[B, L] where
  __ := FiniteAdeleRing.mapRingHom A K L B
  map_smul' k a := by
    ext w
    simpa only [Algebra.smul_def'] using
      (adicCompletionSemialgHom K L (v := w.under A) ⟨w, rfl⟩).map_smul' k (a (under A w))
  continuous_toFun :=
    have : FaithfulSMul A B := FaithfulSMul.of_field_isFractionRing A B K L
    RestrictedProduct.mapAlong_continuous _ _ _ (tendsTo_comap_cofinite A B) _
      (cofinite_mapsTo_adicCompletionSemialgHom A K L B)
      fun w ↦ adicCompletionSemialgHom_continuous K L ⟨w, rfl⟩

variable {A K B} in
lemma mapSemialgHom_apply (x : 𝔸ᶠ[A, K]) (w : HeightOneSpectrum B) :
    mapSemialgHom A K L B x w = adicCompletionSemialgHom K L ⟨w, rfl⟩ (x (under A w)) := rfl

open scoped TensorProduct.RightActions RestrictedProduct

variable [Algebra 𝔸ᶠ[A, K] 𝔸ᶠ[B, L]]

instance : Algebra (Πʳ v : HeightOneSpectrum A, [v.adicCompletion K, v.adicCompletionIntegers K])
    (Πʳ w: HeightOneSpectrum B, [w.adicCompletion L, w.adicCompletionIntegers L]) :=
  inferInstanceAs (Algebra 𝔸ᶠ[A, K] 𝔸ᶠ[B, L])

attribute [local instance 9999] Algebra.toSMul in
/-- Utility class which specialises `RestrictedProduct.FiberwiseSMul` to the case of
finite adele rings. -/
class ComapFiberwiseSMul extends RestrictedProduct.FiberwiseSMul (α := HeightOneSpectrum B)
    (under A) (adicCompletion K) (fun v ↦ adicCompletionIntegers K v) Filter.cofinite
    (adicCompletion L) (fun w ↦ adicCompletionIntegers L w) Filter.cofinite

variable [ComapFiberwiseSMul A K L B]

variable {A K L B} in
theorem ComapFiberwiseSMul.map_smul' (x : 𝔸ᶠ[A, K]) (y : 𝔸ᶠ[B, L]) (v : HeightOneSpectrum A)
    (w : v.Extension B) : (x • y) w.1 = x v • y w.1 :=
  ComapFiberwiseSMul.toFiberwiseSMul.map_smul x y v w

variable {A K B} in
lemma BaseChange.algebraMap_apply (w : HeightOneSpectrum B) (x : 𝔸ᶠ[A, K]) :
    algebraMap _ 𝔸ᶠ[B, L] x w = adicCompletionSemialgHom K L ⟨w, rfl⟩ (x (under A w)) := by
  simp [Algebra.algebraMap_eq_smul_one, ComapFiberwiseSMul.map_smul' x 1 (w.under A) ⟨w, rfl⟩,
    RingHom.smul_toAlgebra, SemialgHom.toLinearMap_eq_coe]

noncomputable section bijection

/-- The canonical linear isomorphism `L ⊗[K] 𝔸_K^∞ ≅ B ⊗[A] 𝔸_K^∞`. -/
def tensorEquivTensor [FiniteDimensional K L] : L ⊗[K] 𝔸ᶠ[A, K] ≃ₗ[B] B ⊗[A] 𝔸ᶠ[A, K] := by
  exact linearEquivTensorProductModuleLeft A K L B 𝔸ᶠ[A, K]

omit [Algebra 𝔸ᶠ[A, K] 𝔸ᶠ[B, L]] [ComapFiberwiseSMul A K L B] in
lemma tensorEquivTensor_tmul [FiniteDimensional K L] (b : B) (x : 𝔸ᶠ[A, K]) :
    tensorEquivTensor A K L B (algebraMap B L b ⊗ₜ[K] x) = b ⊗ₜ[A] x := by
  simp [tensorEquivTensor, linearEquivTensorProductModuleLeft_tmul]

-- shortcuts: note these help remove heartbeats in the below, but probably not the "right" fix
-- local instance : AddCommMonoid (Πʳ v, [B ⊗[A] (adicCompletion K v),
--       RestrictedProduct.rangeLTensorLeft A B (adicCompletion K) (integerSubmodule K) v]) :=
--     RestrictedProduct.instAddCommMonoidCoeOfAddSubmonoidClass
--       (R := (B ⊗[A] adicCompletion K ·)) (S := fun v ↦ Submodule B (B ⊗[A] adicCompletion K v))

-- local instance : Module B (Πʳ v, [B ⊗[A] (adicCompletion K v),
--     RestrictedProduct.rangeLTensorLeft A B (adicCompletion K) (integerSubmodule K) v]) :=
--   RestrictedProduct.instModuleCoeOfSMulMemClass (R := (B ⊗[A] adicCompletion K ·))
--     (S := fun v ↦ Submodule B (B ⊗[A] adicCompletion K v))

set_option synthInstance.maxHeartbeats 40000 in
-- see https://github.com/ImperialCollegeLondon/FLT/issues/889
set_option maxHeartbeats 400000 in
/-- The `B`-linear isomorphism `φ : B ⊗[K] 𝔸_K^∞ ≅ ∏'_v [B ⊗[A] K_v, B ⊗[A] 𝓞_v]`
given by `φ (b ⊗ x) v = b ⊗ (x v)`. -/
def tensorEquivRestrictedProduct : B ⊗[A] 𝔸ᶠ[A, K] ≃ₗ[B] Πʳ v, [B ⊗[A] (adicCompletion K v),
    RestrictedProduct.rangeLTensorLeft A B (adicCompletion K) (integerSubmodule K) v] := by
  have := Module.finitePresentation_of_finite A B
  have := isTorsionFree A K L B
  let f := RestrictedProduct.lTensorEquivLeft A B (adicCompletion K) (integerSubmodule K) .cofinite
  apply LinearEquiv.trans (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl B B) ?_) f
  exact {
    __ := AddEquiv.refl _
    map_smul' a x := by
      ext v
      exact Algebra.smul_def a (x v) |>.symm
  }

set_option backward.isDefEq.respectTransparency false in
omit [IsFractionRing B L] in
lemma tensorEquivRestrictedProduct_tmul (b : B) (x : 𝔸ᶠ[A, K]) (v : HeightOneSpectrum A) :
    tensorEquivRestrictedProduct A K L B (b ⊗ₜ[A] x) v = b ⊗ₜ[A] (x v) := by
  simp [tensorEquivRestrictedProduct]

set_option synthInstance.maxHeartbeats 40000 in
-- see https://github.com/ImperialCollegeLondon/FLT/issues/889
set_option maxHeartbeats 400000 in
/-- The `B`-linear isomorphism `∏'_v [B ⊗[A] K_v, B ⊗[A] 𝓞_v] ≅ ∏'_v [∏_{w|v} L_w, ∏_{w|v} 𝓞_w]`
given by `adicCompletionComapIntegerLinearEquiv`. -/
def restrictedProduct_tensorProduct_equiv_restrictedProduct_prod [FiniteDimensional K L] :
    Πʳ v, [B ⊗[A] (adicCompletion K v),
      RestrictedProduct.rangeLTensorLeft A B (adicCompletion K) (integerSubmodule K) v] ≃ₗ[B]
    Πʳ (v : HeightOneSpectrum A), [(w : Extension B v) → adicCompletion L w.val,
      Submodule.pi Set.univ fun w : Extension B v ↦ (integerSubmodule L w.val)] :=
  LinearEquiv.restrictedProductCongrRight (R₁ := (B ⊗[A] adicCompletion K ·))
    (S₁ := fun v ↦ Submodule B (B ⊗[A] adicCompletion K v)) (integerBaseChangeLinearEquiv K L B)
      (.of_forall <| integerBaseChangeLinearEquiv_bijOn K L)

omit [Algebra 𝔸ᶠ[A, K] 𝔸ᶠ[B, L]] [ComapFiberwiseSMul A K L B] in
lemma restrictedProduct_tensorProduct_equiv_restrictedProduct_prod_apply [FiniteDimensional K L]
    (f) (v : HeightOneSpectrum A) :
    FiniteAdeleRing.restrictedProduct_tensorProduct_equiv_restrictedProduct_prod A K L B f v =
    integerBaseChangeLinearEquiv K L B v (f v) := rfl

set_option synthInstance.maxHeartbeats 40000 in
-- see https://github.com/ImperialCollegeLondon/FLT/issues/889
set_option maxHeartbeats 400000 in
/-- The `B`-linear isomorphism `∏'_v [∏_{w|v} L_w, ∏_{w|v} 𝓞_w] → 𝔸_L^∞` given by
`RestrictedProduct.flatten_equiv'`. -/
def restrictedProduct_prod_equiv :
    Πʳ (v : HeightOneSpectrum A), [(w : Extension B v) → adicCompletion L w.val,
      Submodule.pi .univ fun w : Extension B v ↦ (integerSubmodule L w.val)] ≃ₗ[B]
    𝔸ᶠ[B, L] :=
  have : FaithfulSMul A B := FaithfulSMul.of_field_isFractionRing A B K L
  {
    __ := RestrictedProduct.flatten_equiv'
      (fun w : HeightOneSpectrum B ↦ SetLike.coe <| w.adicCompletionIntegers L)
      (tendsTo_comap_cofinite A B)
    map_add' x y := rfl
    map_smul' a x := by
      ext w
      change a • (x (under A w) ⟨w, rfl⟩) = _
      simp [Submodule.coe_pi,Algebra.smul_def, RingHom.id_apply, Equiv.toFun_as_coe]
      rfl
  }

omit [Algebra 𝔸ᶠ[A, K] 𝔸ᶠ[B, L]] [ComapFiberwiseSMul A K L B] in
lemma restrictedProduct_prod_equiv_apply (f) (w : HeightOneSpectrum B) :
    restrictedProduct_prod_equiv A K L B f w = f (under A w) ⟨w, rfl⟩ := rfl

set_option synthInstance.maxHeartbeats 40000 in
-- see https://github.com/ImperialCollegeLondon/FLT/issues/889
set_option maxHeartbeats 400000 in
/-- The `L`-linear isomorphism `L ⊗ A_K^∞ ≅ A_L^∞` given by composing the previous four maps. -/
def baseChangeLinearEquiv [FiniteDimensional K L] : L ⊗[K] 𝔸ᶠ[A, K] ≃ₗ[L] 𝔸ᶠ[B, L] :=
  let f₁ := tensorEquivTensor A K L B
  let f₂ := tensorEquivRestrictedProduct A K L B
  let f₃ := restrictedProduct_tensorProduct_equiv_restrictedProduct_prod A K L B
  let f₄ := restrictedProduct_prod_equiv A K L B
  let f := f₁ ≪≫ₗ f₂ ≪≫ₗ f₃ ≪≫ₗ f₄
  LinearEquiv.extendScalarsOfIsLocalization (nonZeroDivisors B) L f

@[simp]
lemma algebraMap_apply (x : K) (v : HeightOneSpectrum A) :
    algebraMap K 𝔸ᶠ[A, K] x v = algebraMap K (v.adicCompletion K) x := rfl

set_option synthInstance.maxHeartbeats 40000 in
-- see https://github.com/ImperialCollegeLondon/FLT/issues/889
set_option maxHeartbeats 400000 in
@[simp]
lemma baseChangeLinearEquiv_tmul [FiniteDimensional K L] (b : B) (x : 𝔸ᶠ[A, K]) :
    baseChangeLinearEquiv A K L B (algebraMap B L b ⊗ₜ x) =
      (algebraMap _ 𝔸ᶠ[B, L] b) * (algebraMap _ 𝔸ᶠ[B, L] x) := by
  ext w
  simpa [baseChangeLinearEquiv, restrictedProduct_prod_equiv_apply, tensorEquivTensor_tmul,
    restrictedProduct_tensorProduct_equiv_restrictedProduct_prod_apply,
    tensorEquivRestrictedProduct_tmul, BaseChange.algebraMap_apply,
    IsScalarTower.algebraMap_apply B L 𝔸ᶠ[B, L],
    IsScalarTower.algebraMap_apply B L (w.adicCompletion L), -Submodule.coe_pi] using .inl rfl

theorem baseChange_bijective [FiniteDimensional K L] :
    Function.Bijective (SemialgHom.baseChange_of_algebraMap <|
      (mapSemialgHom A K L B).toSemialgHom) := by
  suffices ⇑(SemialgHom.baseChange_of_algebraMap <| FiniteAdeleRing.mapSemialgHom A K L B) =
      ⇑(FiniteAdeleRing.baseChangeLinearEquiv A K L B) by
    rw [ContinuousSemialgHom.toSemialgHom_eq_coe, this]
    exact (FiniteAdeleRing.baseChangeLinearEquiv A K L B).bijective
  rw [← AlgHom.coe_toLinearMap, ← LinearEquiv.coe_toLinearMap]
  -- TODO
  -- we used to use `IsLocalization.tensorProduct_ext` when this was K-linear
  -- not L-linear; maybe write `IsLocalization.tensorProduct_ext'` which allows
  -- for L-linear maps out of a K-linear tensor product?
  apply congr_arg _ <| LinearMap.ext fun x ↦ ?_
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul l x =>
    ext w
    obtain ⟨⟨b, s⟩, hl : (s : B) • l = algebraMap B L b⟩ :=
      IsLocalizedModule.surj (M := B) (M' := L) (nonZeroDivisors B) (Algebra.linearMap B L) l
    rw [LinearEquiv.coe_coe, ← IsUnit.smul_left_cancel <| IsLocalization.map_units L s]
    simp only [Algebra.smul_def, ← algebraMap_apply, ← mul_apply]
    simp only [← Algebra.smul_def, ← map_smul]
    simp [hl, baseChangeLinearEquiv_tmul, BaseChange.algebraMap_apply, mapSemialgHom_apply,
      SemialgHom.baseChange_of_algebraMap_tmul, Algebra.compHom_algebraMap_apply,
      ← IsScalarTower.algebraMap_apply B L (w.adicCompletion L), TensorProduct.smul_tmul']
  | add => simp_all

/-- The `L`-algebra isomorphism `L ⊗_K 𝔸_K^∞ ≅ 𝔸_L^∞`. -/
def baseChangeAlgEquiv [FiniteDimensional K L] :
    L ⊗[K] 𝔸ᶠ[A, K] ≃ₐ[L] 𝔸ᶠ[B, L] :=
  .ofBijective (SemialgHom.baseChange_of_algebraMap <| FiniteAdeleRing.mapSemialgHom A K L B)
    (FiniteAdeleRing.baseChange_bijective A K L B)

/-- The `𝔸_K^∞`-algebra isomorphism `L ⊗_K 𝔸_K^∞ ≅ 𝔸_L^∞`. -/
def baseChangeAdeleAlgEquiv [FiniteDimensional K L] :
    L ⊗[K] 𝔸ᶠ[A, K] ≃ₐ[𝔸ᶠ[A, K]] 𝔸ᶠ[B, L] where
  __ := SemialgHom.baseChangeRightOfAlgebraMap <|
    (FiniteAdeleRing.mapSemialgHom A K L B).toSemialgHom
  __ := FiniteAdeleRing.baseChangeAlgEquiv A K L B
  commutes' x := by
    ext
    simp [BaseChange.algebraMap_apply]
    rfl

instance [FiniteDimensional K L] : Module.Finite 𝔸ᶠ[A, K] 𝔸ᶠ[B, L] :=
  Module.Finite.equiv (FiniteAdeleRing.baseChangeAdeleAlgEquiv A K L B).toLinearEquiv

end bijection

section moduleTopology

attribute [local instance 9999] Algebra.toModule in
/-- `𝓞_v`-module structure on `∏ L_w` from restricting the scalars of the `K_v`-module structure. -/
noncomputable local instance (v : HeightOneSpectrum A) : Module (adicCompletionIntegers K v)
    ((w : Extension B v) → adicCompletion L w.val) :=
  Module.compHom _ (algebraMap (adicCompletionIntegers K v) (adicCompletion K v))

/-- SMul instance from the module structure. -/
noncomputable local instance (v : HeightOneSpectrum A) : SMul (adicCompletionIntegers K v)
    ((w : Extension B v) → adicCompletion L w.val) :=
  Module.toDistribMulAction.toDistribSMul.toSMul

/-- A shortcut instance for the action of `𝓞ᵥ` on `Kᵥ`. -/
noncomputable local instance (v : HeightOneSpectrum A) : MulAction (v.adicCompletionIntegers K)
    (v.adicCompletion K) := LieAlgebra.ofAssociativeAlgebra.toMulAction

attribute [local instance 9999] Algebra.toModule Algebra.toSMul in
/-- `∏_{w∣v} 𝓞_w` as an `𝓞_v`-submodule of `∏_{w∣v} L_w` -/
noncomputable def piAdicIntegerSubmodule (v : HeightOneSpectrum A) :
    Submodule (adicCompletionIntegers K v) ((w : Extension B v) → adicCompletion L w.val) :=
  let module (w : Extension B v) := Module.compHom (adicCompletion L w.val)
    (algebraMap (adicCompletionIntegers K v) (adicCompletion K v))
  Submodule.pi Set.univ fun (w : Extension B v) ↦
    letI := (module w).toDistribMulAction.toDistribSMul.toSMul
    have : IsScalarTower (adicCompletionIntegers K v) (adicCompletionIntegers L w.val)
        (adicCompletion L w.val) :=
      IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
    let s := (adicCompletionIntegers L w.val).toSubmodule
    letI : Algebra (v.adicCompletionIntegers K) (w.1.adicCompletionIntegers L).toSubring :=
      inferInstanceAs (Algebra (adicCompletionIntegers K v) (adicCompletionIntegers L w.1))
    s.restrictScalars (adicCompletionIntegers K v)

-- Help instance synthesis
private noncomputable local instance (priority := 9999) (v : HeightOneSpectrum A) :
    Module (adicCompletion K v) ((w : Extension B v) → adicCompletion L w.val) :=
  Algebra.toModule

-- went up from 40000 when switched to module system
set_option synthInstance.maxHeartbeats 80000 in
-- see https://github.com/ImperialCollegeLondon/FLT/issues/889
set_option maxHeartbeats 400000 in -- caused by bump to v4.29
/-- An auxiliary 𝔸_K-module structure on restricted product over v of (product of w's dividing v
of L_w wrt 𝓞_w). Only used in this file to compare L ⊗ 𝔸_K and 𝔸_L.
-/
noncomputable local instance : Module 𝔸ᶠ[A, K]
    Πʳ (v : HeightOneSpectrum A), [(w : Extension B v) → adicCompletion L w.1,
    ↑(piAdicIntegerSubmodule A K L B v)] :=
  RestrictedProduct.instModuleCoe_fLT

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 80000 in
-- see https://github.com/ImperialCollegeLondon/FLT/issues/889
set_option maxHeartbeats 400000 in
/-- The continuous `𝔸 K`-Linear equivalence between `∏'_v ∏_{w∣v} L_w` and `𝔸 L` given by
reaindexing the elements. -/
noncomputable def restrictedProduct_pi_equiv :
    Πʳ (v : HeightOneSpectrum A), [(w : Extension B v) → adicCompletion L w.val,
      piAdicIntegerSubmodule A K L B v] ≃L[𝔸ᶠ[A, K]] 𝔸ᶠ[B, L] :=
  have := FaithfulSMul.of_field_isFractionRing A B K L
  let f : _ ≃ₜ 𝔸ᶠ[B, L] := RestrictedProduct.flatten_homeomorph'
    (G := adicCompletion L) (fun w ↦ adicCompletionIntegers L w) (tendsTo_comap_cofinite A B)
  {
    __ := f
    map_add' x y := rfl
    map_smul' r x := by
      ext w
      rw [RingHom.id_apply, Algebra.smul_def, RestrictedProduct.mul_apply,
        BaseChange.algebraMap_apply]
      rfl
  }

-- needed for the below lemmas for some reason
attribute [instance 100] RestrictedProduct.instSMulCoeOfSMulMemClass

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 160000 in
-- see https://github.com/ImperialCollegeLondon/FLT/issues/889
set_option maxHeartbeats 800000 in
lemma restrictedProduct_pi_isModuleTopology [FiniteDimensional K L] : IsModuleTopology 𝔸ᶠ[A, K]
    (Πʳ (v : HeightOneSpectrum A), [(w : Extension B v) → adicCompletion L w.val,
      piAdicIntegerSubmodule A K L B v]) := by
  have :=
    Module.Finite.equiv (FiniteAdeleRing.restrictedProduct_pi_equiv A K L B).symm.toLinearEquiv
  unfold FiniteAdeleRing at this
  apply RestrictedProduct.isModuleTopology
  · exact fun v ↦ Valued.isOpen_integer (adicCompletion K v)
  · intro v
    simp only [piAdicIntegerSubmodule, Submodule.coe_pi, Submodule.coe_restrictScalars]
    apply isOpen_set_pi _ (fun _ _ ↦ Valued.isOpen_integer _)
    rw [Set.finite_univ_iff]
    exact Extension.finite A K L B v

set_option synthInstance.maxHeartbeats 40000 in
-- see https://github.com/ImperialCollegeLondon/FLT/issues/889
set_option maxHeartbeats 400000 in
instance [FiniteDimensional K L] : IsModuleTopology 𝔸ᶠ[A, K] 𝔸ᶠ[B, L] :=
  have := restrictedProduct_pi_isModuleTopology A K L B
  IsModuleTopology.iso (FiniteAdeleRing.restrictedProduct_pi_equiv A K L B)

end moduleTopology

/-- The continuous `𝔸_K^∞`-algebra isomorphism `L ⊗_K 𝔸_K^∞ ≅ 𝔸_L^∞` -/
noncomputable def baseChangeAdeleContinuousAlgEquiv [FiniteDimensional K L] :
    L ⊗[K] 𝔸ᶠ[A, K] ≃A[𝔸ᶠ[A, K]] 𝔸ᶠ[B, L] :=
  IsModuleTopology.continuousAlgEquivOfAlgEquiv <| baseChangeAdeleAlgEquiv A K L B

/-- The continuous `L`-algebra isomorphism `L ⊗_K 𝔸_K^∞ ≅ 𝔸_L^∞` -/
noncomputable def baseChangeContinuousAlgEquiv [FiniteDimensional K L] :
    L ⊗[K] 𝔸ᶠ[A, K] ≃A[L] 𝔸ᶠ[B, L] where
  __ := FiniteAdeleRing.baseChangeAlgEquiv A K L B
  __ := FiniteAdeleRing.baseChangeAdeleContinuousAlgEquiv A K L B

end IsDedekindDomain.FiniteAdeleRing
