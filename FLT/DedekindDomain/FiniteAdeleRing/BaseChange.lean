/-
Copyright (c) 2025 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Matthew Jasper
-/
import FLT.DedekindDomain.Completion.BaseChange
import FLT.DedekindDomain.FiniteAdeleRing.TensorRestrictedProduct
import FLT.Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
import FLT.Mathlib.Topology.Algebra.RestrictedProduct.Module
import FLT.Mathlib.Topology.Algebra.Algebra.Hom
import FLT.Mathlib.LinearAlgebra.Pi
import Mathlib.RingTheory.Flat.TorsionFree

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

variable (A K L B : Type*) [CommRing A] [CommRing B] [Algebra A B] [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K] [Algebra B L] [IsDedekindDomain A]
    [Algebra K L] [Algebra A L] [IsScalarTower A B L] [IsScalarTower A K L] [Module.Finite A B]
    [IsDedekindDomain B] [IsFractionRing B L]

namespace IsDedekindDomain

open IsDedekindDomain HeightOneSpectrum adicCompletion Extension

open scoped TensorProduct -- ⊗ notation for tensor product

lemma tendsTo_comap_cofinite [FaithfulSMul A B] :
    Filter.Tendsto (comap A (B:=B)) Filter.cofinite Filter.cofinite :=
  have : FaithfulSMul A (FractionRing B) := FractionRing.instFaithfulSMul A B
  letI : Algebra (FractionRing A) (FractionRing B) :=
    FractionRing.liftAlgebra A (FractionRing B)
  (Filter.Tendsto.cofinite_of_finite_preimage_singleton <|
    Extension.finite A (FractionRing A) (FractionRing B) B)

lemma cofinite_mapsTo_adicCompletionSemialgHom :
    ∀ᶠ (w : HeightOneSpectrum B) in Filter.cofinite,
    Set.MapsTo (Extension.adicCompletionSemialgHom K L (v := comap A w) ⟨w, rfl⟩)
      (adicCompletionIntegers K (comap A w)) (adicCompletionIntegers L w) := by
  apply Filter.Eventually.of_forall
  intro w
  exact Set.image_subset_iff.1 <| adicCompletionSemialgHom_image_adicCompletionIntegers K L ⟨w, rfl⟩

namespace FiniteAdeleRing

@[inherit_doc]
scoped notation:max "𝔸ᶠ[" A ", " K "]" => FiniteAdeleRing A K

/-- The ring homomorphism `𝔸_K^∞ → 𝔸_L^∞` for `L/K` an extension of number fields. -/
noncomputable def mapRingHom : 𝔸ᶠ[A, K] →+* 𝔸ᶠ[B, L] :=
  have : FaithfulSMul A B := FaithfulSMul.of_field_isFractionRing A B K L
  RestrictedProduct.mapAlongRingHom (adicCompletion K) (adicCompletion L) (comap A)
    (tendsTo_comap_cofinite A B) (fun w ↦ adicCompletionSemialgHom K L (v := w.comap A) ⟨w, rfl⟩)
    (cofinite_mapsTo_adicCompletionSemialgHom A K L B)

/-- The ring homomorphism `𝔸_K^∞ → 𝔸_L^∞` for `L/K` an extension of number fields,
as a morphism lying over the canonical map `K → L`. -/
noncomputable def mapSemialgHom :
    𝔸ᶠ[A, K] →SA[algebraMap K L] 𝔸ᶠ[B, L] where
  __ := FiniteAdeleRing.mapRingHom A K L B
  map_smul' k a := by
    ext w
    simpa only [Algebra.smul_def'] using
      (adicCompletionSemialgHom K L (v := w.comap A) ⟨w, rfl⟩).map_smul' k (a (comap A w))
  continuous_toFun :=
    have : FaithfulSMul A B := FaithfulSMul.of_field_isFractionRing A B K L
    RestrictedProduct.mapAlong_continuous _ _ _ (tendsTo_comap_cofinite A B) _
      (cofinite_mapsTo_adicCompletionSemialgHom A K L B)
      fun w ↦ adicCompletionSemialgHom_continuous K L ⟨w, rfl⟩

variable {A K B} in
lemma mapSemialgHom_apply (x : 𝔸ᶠ[A, K]) (w : HeightOneSpectrum B) :
    mapSemialgHom A K L B x w = adicCompletionSemialgHom K L ⟨w, rfl⟩ (x (comap A w)) := rfl

open scoped TensorProduct.RightActions RestrictedProduct

variable [Algebra 𝔸ᶠ[A, K] 𝔸ᶠ[B, L]]

instance : Algebra (Πʳ v : HeightOneSpectrum A, [v.adicCompletion K, v.adicCompletionIntegers K])
    (Πʳ w: HeightOneSpectrum B, [w.adicCompletion L, w.adicCompletionIntegers L]) :=
  inferInstanceAs (Algebra 𝔸ᶠ[A, K] 𝔸ᶠ[B, L])

/-- Utility class which specialises `RestrictedProduct.FiberwiseSMul` to the case of
finite adele rings. -/
class ComapFiberwiseSMul extends RestrictedProduct.FiberwiseSMul (α := HeightOneSpectrum B)
    (comap A) (adicCompletion K) (fun v ↦ adicCompletionIntegers K v) Filter.cofinite
    (adicCompletion L) (fun w ↦ adicCompletionIntegers L w) Filter.cofinite

variable [ComapFiberwiseSMul A K L B]

variable {A K L B} in
theorem ComapFiberwiseSMul.map_smul' (x : 𝔸ᶠ[A, K]) (y : 𝔸ᶠ[B, L]) (v : HeightOneSpectrum A)
    (w : v.Extension B) : (x • y) w.1 = x v • y w.1 :=
  ComapFiberwiseSMul.toFiberwiseSMul.map_smul x y v w

variable {A K B} in
lemma BaseChange.algebraMap_apply (w : HeightOneSpectrum B) (x : 𝔸ᶠ[A, K]) :
    algebraMap _ 𝔸ᶠ[B, L] x w = adicCompletionSemialgHom K L ⟨w, rfl⟩ (x (comap A w)) := by
  simp [Algebra.algebraMap_eq_smul_one, ComapFiberwiseSMul.map_smul' x 1 (w.comap A) ⟨w, rfl⟩,
    RingHom.smul_toAlgebra, SemialgHom.toLinearMap_eq_coe]

noncomputable section bijection

omit [Module.Finite A B] [IsDedekindDomain B] in
theorem range_adicCompletionTensorIntegerCoe_eq_lTensorRestriction (v : HeightOneSpectrum A) :
    LinearMap.range (adicCompletionIntegers.tensorCoe K B v) =
    RestrictedProduct.rangeLTensor A B (adicCompletion K) (integerSubmodule K) v := rfl

/-- The canonical linear isomorphism `L ⊗[K] 𝔸_K^∞ ≅ B ⊗[A] 𝔸_K^∞`. -/
def tensorEquivTensor [FiniteDimensional K L] : L ⊗[K] 𝔸ᶠ[A, K] ≃ₗ[A] B ⊗[A] 𝔸ᶠ[A, K] := by
  exact linearEquivTensorProductModule A K L B 𝔸ᶠ[A, K]

omit [Algebra 𝔸ᶠ[A, K] 𝔸ᶠ[B, L]] [ComapFiberwiseSMul A K L B] in
lemma tensorEquivTensor_tmul [FiniteDimensional K L] (b : B) (x : 𝔸ᶠ[A, K]) :
    tensorEquivTensor A K L B (algebraMap B L b ⊗ₜ[K] x) = b ⊗ₜ[A] x := by
  simp [tensorEquivTensor, linearEquivTensorProductModule_tmul]

/-- The `A`-linear isomorphism `φ : B ⊗[K] 𝔸_K^∞ ≅ ∏'_v [B ⊗[A] K_v, B ⊗[A] 𝓞_v]`
given by `φ (b ⊗ x) v = b ⊗ (x v)`. -/
def tensorEquivRestrictedProduct :
    B ⊗[A] 𝔸ᶠ[A, K] ≃ₗ[A]
      Πʳ v, [B ⊗[A] (adicCompletion K v), RestrictedProduct.rangeLTensor A
      B (adicCompletion K) (integerSubmodule K) v]:= by
  have := Module.finitePresentation_of_finite A B
  have := isTorsionFree A K L B
  let map :=
    RestrictedProduct.lTensorEquiv A B (adicCompletion K) Filter.cofinite (integerSubmodule K)
  apply LinearEquiv.trans (TensorProduct.congr (LinearEquiv.refl A B) _) map
  exact {
    __ := AddEquiv.refl _
    map_smul' a x := by
      ext v
      exact Algebra.smul_def a (x v) |>.symm
  }

omit [IsFractionRing B L] in
lemma tensorEquivRestrictedProduct_tmul (b : B) (x : 𝔸ᶠ[A, K])
    (v : HeightOneSpectrum A) :
    tensorEquivRestrictedProduct A K L B (b ⊗ₜ[A] x) v = b ⊗ₜ[A] (x v) := rfl

/-- The `A`-linear isomorphism `∏'_v [B ⊗[A] K_v, B ⊗[A] 𝓞_v] ≅ ∏'_v [∏_{w|v} L_w, ∏_{w|v} 𝓞_w]`
given by `adicCompletionComapIntegerLinearEquiv`. -/
def restrictedProduct_tensorProduct_equiv_restrictedProduct_prod [FiniteDimensional K L] :
    Πʳ v, [B ⊗[A] (adicCompletion K v), RestrictedProduct.rangeLTensor A
      B (adicCompletion K) (integerSubmodule K) v] ≃ₗ[A]
    Πʳ (v : HeightOneSpectrum A), [(w : Extension B v) → adicCompletion L w.val,
      Submodule.pi Set.univ fun w : Extension B v ↦ (integerSubmodule L w.val).restrictScalars A] :=
  LinearEquiv.restrictedProductCongrRight
    (integerBaseChangeLinearEquiv K L B)
    (.of_forall <| integerBaseChangeLinearEquiv_bijOn K L)

omit [Algebra 𝔸ᶠ[A, K] 𝔸ᶠ[B, L]] [ComapFiberwiseSMul A K L B] in
lemma restrictedProduct_tensorProduct_equiv_restrictedProduct_prod_apply [FiniteDimensional K L]
    (f) (v : HeightOneSpectrum A) :
    FiniteAdeleRing.restrictedProduct_tensorProduct_equiv_restrictedProduct_prod A K L B f v =
    integerBaseChangeLinearEquiv K L B v (f v) := rfl

/-- The `A`-linear isomorphism `∏'_v [∏_{w|v} L_w, ∏_{w|v} 𝓞_w] → 𝔸_L^∞` given by
`RestrictedProduct.flatten_equiv'`. -/
def restrictedProduct_prod_equiv [Algebra A 𝔸ᶠ[B, L]] [IsScalarTower A B 𝔸ᶠ[B, L]] :
    Πʳ (v : HeightOneSpectrum A), [(w : Extension B v) → adicCompletion L w.val,
    Submodule.pi .univ fun w : Extension B v ↦ (integerSubmodule L w.val).restrictScalars A] ≃ₗ[A]
      𝔸ᶠ[B, L] :=
  have : FaithfulSMul A B := FaithfulSMul.of_field_isFractionRing A B K L
  {
    __ := RestrictedProduct.flatten_equiv'
      (fun w : HeightOneSpectrum B ↦ SetLike.coe <| w.adicCompletionIntegers L)
      (tendsTo_comap_cofinite A B)
    map_add' x y := rfl
    map_smul' a x := by
      ext w
      change a • (x (comap A w) ⟨w, rfl⟩) = _
      simp only [Submodule.coe_pi, Submodule.coe_restrictScalars, Algebra.smul_def,
        RingHom.id_apply, Equiv.toFun_as_coe,
        IsScalarTower.algebraMap_apply A B (w.adicCompletion L)]
      rw [IsScalarTower.algebraMap_apply A B 𝔸ᶠ[B, L]]
      rfl
  }

omit [Algebra 𝔸ᶠ[A, K] 𝔸ᶠ[B, L]] [ComapFiberwiseSMul A K L B] in
lemma restrictedProduct_prod_equiv_apply [Algebra A 𝔸ᶠ[B, L]] [IsScalarTower A B 𝔸ᶠ[B, L]]
    (f) (w : HeightOneSpectrum B) :
    restrictedProduct_prod_equiv A K L B f w = f (comap A w) ⟨w, rfl⟩ := rfl

-- TODO : are all these needed?
variable [Algebra K 𝔸ᶠ[B, L]] [IsScalarTower K 𝔸ᶠ[A, K] 𝔸ᶠ[B, L]] [Algebra A 𝔸ᶠ[B, L]]
  [IsScalarTower A B 𝔸ᶠ[B, L]] [IsScalarTower A 𝔸ᶠ[A, K] 𝔸ᶠ[B, L]]

/-- The `K`-linear isomorphism `L ⊗ A_K^∞ ≅ A_L^∞` given by composing the previous four maps. -/
def baseChangeLinearEquiv [FiniteDimensional K L] : L ⊗[K] 𝔸ᶠ[A, K] ≃ₗ[K] 𝔸ᶠ[B, L] :=
  have : IsScalarTower A K 𝔸ᶠ[B, L] := .to₁₂₄ _ _ 𝔸ᶠ[A, K] _
  let f := (tensorEquivTensor A K L B) ≪≫ₗ
    (tensorEquivRestrictedProduct A K L B) ≪≫ₗ
    (restrictedProduct_tensorProduct_equiv_restrictedProduct_prod A K L B) ≪≫ₗ
    (restrictedProduct_prod_equiv A K L B).restrictScalars A
  LinearEquiv.extendScalarsOfIsLocalization (nonZeroDivisors A) K f

@[simp]
lemma algebraMap_apply (x : K) (v : HeightOneSpectrum A) :
    algebraMap K 𝔸ᶠ[A, K] x v = algebraMap K (v.adicCompletion K) x := rfl

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

theorem baseChange_bijective [FiniteDimensional K L] [IsScalarTower K L 𝔸ᶠ[B, L]] :
    Function.Bijective (SemialgHom.baseChange_of_algebraMap <|
      (mapSemialgHom A K L B).toSemialgHom) := by
  suffices ⇑(SemialgHom.baseChange_of_algebraMap <| FiniteAdeleRing.mapSemialgHom A K L B) =
      ⇑(FiniteAdeleRing.baseChangeLinearEquiv A K L B) by
    rw [ContinuousSemialgHom.toSemialgHom_eq_coe, this]
    exact (FiniteAdeleRing.baseChangeLinearEquiv A K L B).bijective
  rw [← AlgHom.coe_restrictScalars' (R:=K), ← AlgHom.coe_toLinearMap, ← LinearEquiv.coe_toLinearMap]
  apply congr_arg
  have := IsIntegralClosure.isLocalizedModule A K L B
  apply IsLocalization.tensorProduct_ext (nonZeroDivisors A) B
  intro b x
  ext w
  simp [SemialgHom.baseChange_of_algebraMap_tmul, mapSemialgHom_apply, BaseChange.algebraMap_apply,
    IsScalarTower.algebraMap_apply B L 𝔸ᶠ[B, L]]

/-- The `L`-algebra isomorphism `L ⊗_K 𝔸_K^∞ ≅ 𝔸_L^∞`. -/
def baseChangeAlgEquiv [FiniteDimensional K L] [IsScalarTower K L 𝔸ᶠ[B, L]] :
    L ⊗[K] 𝔸ᶠ[A, K] ≃ₐ[L] 𝔸ᶠ[B, L] :=
  .ofBijective (SemialgHom.baseChange_of_algebraMap <| FiniteAdeleRing.mapSemialgHom A K L B)
    (FiniteAdeleRing.baseChange_bijective A K L B)

/-- The `𝔸_K^∞`-algebra isomorphism `L ⊗_K 𝔸_K^∞ ≅ 𝔸_L^∞`. -/
def baseChangeAdeleAlgEquiv [FiniteDimensional K L] [IsScalarTower K L 𝔸ᶠ[B, L]] :
    L ⊗[K] 𝔸ᶠ[A, K] ≃ₐ[𝔸ᶠ[A, K]] 𝔸ᶠ[B, L] where
  __ := SemialgHom.baseChangeRightOfAlgebraMap <|
    (FiniteAdeleRing.mapSemialgHom A K L B).toSemialgHom
  __ := FiniteAdeleRing.baseChangeAlgEquiv A K L B
  commutes' x := by
    ext
    simp [BaseChange.algebraMap_apply]
    rfl

instance [FiniteDimensional K L] [IsScalarTower K L 𝔸ᶠ[B, L]] : Module.Finite 𝔸ᶠ[A, K] 𝔸ᶠ[B, L] :=
  Module.Finite.equiv (FiniteAdeleRing.baseChangeAdeleAlgEquiv A K L B).toLinearEquiv

end bijection

section moduleTopology

-- TODO : are all these needed?
variable [Algebra K 𝔸ᶠ[B, L]] [IsScalarTower K 𝔸ᶠ[A, K] 𝔸ᶠ[B, L]] [Algebra A 𝔸ᶠ[B, L]]
  [IsScalarTower A B 𝔸ᶠ[B, L]] [IsScalarTower A 𝔸ᶠ[A, K] 𝔸ᶠ[B, L]]

-- shortcut instances

variable (v : HeightOneSpectrum A) in
noncomputable instance : Module (v.adicCompletionIntegers K) (v.adicCompletion K) :=
  Algebra.toModule

variable (v : HeightOneSpectrum A) in
noncomputable instance : MulAction (v.adicCompletionIntegers K) (v.adicCompletion K) :=
  Algebra.toModule.toMulAction

variable (v : HeightOneSpectrum A) in
noncomputable instance : SMul (v.adicCompletionIntegers K) (v.adicCompletion K) :=
  Algebra.toModule.toMulAction.toSMul

/-- `𝓞_v`-module structure on `∏ L_w` from restricting the scalars of the `K_v`-module structure. -/
noncomputable local instance (v : HeightOneSpectrum A) : Module (adicCompletionIntegers K v)
    ((w : Extension B v) → adicCompletion L w.val) :=
  Module.compHom _ (algebraMap (adicCompletionIntegers K v) (adicCompletion K v))

/-- SMul instance from the module structure. -/
noncomputable local instance (v : HeightOneSpectrum A) : SMul (adicCompletionIntegers K v)
    ((w : Extension B v) → adicCompletion L w.val) :=
  Module.toDistribMulAction.toDistribSMul.toSMul

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

/-- An auxiliary 𝔸_K-module structure on restricted product over v of (product of w's dividing v
of L_w wrt 𝓞_w). Only used in this file to compare L ⊗ 𝔸_K and 𝔸_L.
-/
noncomputable local instance : Module 𝔸ᶠ[A, K]
    Πʳ (v : HeightOneSpectrum A), [(w : Extension B v) → adicCompletion L w.1,
    ↑(piAdicIntegerSubmodule A K L B v)] :=
  inferInstanceAs <| Module
      (Πʳ v : HeightOneSpectrum A, [v.adicCompletion K, v.adicCompletionIntegers K])
      Πʳ (v : HeightOneSpectrum A), [(w : Extension B v) → adicCompletion L w.1,
    ↑(piAdicIntegerSubmodule A K L B v)]

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

lemma restrictedProduct_pi_isModuleTopology [FiniteDimensional K L] [IsScalarTower K L 𝔸ᶠ[B, L]] :
    IsModuleTopology 𝔸ᶠ[A, K]
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

instance [FiniteDimensional K L] [IsScalarTower K L 𝔸ᶠ[B, L]] :
    IsModuleTopology 𝔸ᶠ[A, K] 𝔸ᶠ[B, L] :=
  have := restrictedProduct_pi_isModuleTopology A K L B
  IsModuleTopology.iso (FiniteAdeleRing.restrictedProduct_pi_equiv A K L B)

end moduleTopology

-- TODO : are all these needed?
variable [Algebra K 𝔸ᶠ[B, L]] [IsScalarTower K 𝔸ᶠ[A, K] 𝔸ᶠ[B, L]] [Algebra A 𝔸ᶠ[B, L]]
  [IsScalarTower A B 𝔸ᶠ[B, L]] [IsScalarTower A 𝔸ᶠ[A, K] 𝔸ᶠ[B, L]]

/-- The continuous `𝔸_K^∞`-algebra isomorphism `L ⊗_K 𝔸_K^∞ ≅ 𝔸_L^∞` -/
noncomputable def baseChangeAdeleContinuousAlgEquiv [FiniteDimensional K L]
    [IsScalarTower K L 𝔸ᶠ[B, L]] : L ⊗[K] 𝔸ᶠ[A, K] ≃A[𝔸ᶠ[A, K]] 𝔸ᶠ[B, L] :=
  IsModuleTopology.continuousAlgEquivOfAlgEquiv <| baseChangeAdeleAlgEquiv A K L B

/-- The continuous `L`-algebra isomorphism `L ⊗_K 𝔸_K^∞ ≅ 𝔸_L^∞` -/
noncomputable def baseChangeContinuousAlgEquiv [FiniteDimensional K L]
    [IsScalarTower K L 𝔸ᶠ[B, L]] : L ⊗[K] 𝔸ᶠ[A, K] ≃A[L] 𝔸ᶠ[B, L] where
  __ := FiniteAdeleRing.baseChangeAlgEquiv A K L B
  __ := FiniteAdeleRing.baseChangeAdeleContinuousAlgEquiv A K L B

end IsDedekindDomain.FiniteAdeleRing
