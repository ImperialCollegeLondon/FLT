/-
Copyright (c) 2025 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Matthew Jasper
-/
import FLT.DedekindDomain.Completion.BaseChange
import FLT.DedekindDomain.FiniteAdeleRing.TensorRestrictedProduct
import FLT.Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
import FLT.Mathlib.Topology.Algebra.RestrictedProduct.Module
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

* `FiniteAdeleRing.baseChangeAlgEquiv : L ⊗[K] FiniteAdeleRing A K ≃ₐ[L] FiniteAdeleRing B L`

## Main theorems

* `FiniteAdeleRing B L` has the `FiniteAdeleRing A K`-module topology, shown as an instance.

-/

variable (A K L B : Type*) [CommRing A] [CommRing B] [Algebra A B] [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K] [Algebra B L] [IsDedekindDomain A]
    [Algebra K L] [Algebra A L] [IsScalarTower A B L] [IsScalarTower A K L]
    [IsIntegralClosure B A L] [FiniteDimensional K L] [Module.Finite A B]
    [IsDedekindDomain B] [IsFractionRing B L]

namespace IsDedekindDomain

open IsDedekindDomain HeightOneSpectrum

open scoped TensorProduct -- ⊗ notation for tensor product

lemma tendsTo_comap_cofinite [FaithfulSMul A B] :
    Filter.Tendsto (comap A (B:=B)) Filter.cofinite Filter.cofinite :=
  have : FaithfulSMul A (FractionRing B) := FractionRing.instFaithfulSMul A B
  letI : Algebra (FractionRing A) (FractionRing B) :=
    FractionRing.liftAlgebra A (FractionRing B)
  (Filter.Tendsto.cofinite_of_finite_preimage_singleton <|
    Extension.finite A (FractionRing A) (FractionRing B) B)

omit [IsIntegralClosure B A L] [FiniteDimensional K L] in
lemma cofinite_mapsTo_adicCompletionComapSemialgHom :
    ∀ᶠ (w : HeightOneSpectrum B) in Filter.cofinite,
    Set.MapsTo (adicCompletionComapSemialgHom A K L B (comap A w) ⟨w, rfl⟩)
      (adicCompletionIntegers K (comap A w)) (adicCompletionIntegers L w) := by
  apply Filter.Eventually.of_forall
  intro w
  have := adicCompletionComapSemialgHom.mapadicCompletionIntegers A K L B (comap A w) ⟨w, rfl⟩
  exact Set.image_subset_iff.1 this

namespace FiniteAdeleRing

scoped notation:max "𝔸ᶠ[" A ", " K "]" => FiniteAdeleRing A K

/-- The ring homomorphism `𝔸_K^∞ → 𝔸_L^∞` for `L/K` an extension of number fields. -/
noncomputable def mapRingHom : 𝔸ᶠ[A, K] →+* 𝔸ᶠ[B, L] :=
  have : FaithfulSMul A B := FaithfulSMul.of_field_isFractionRing A B K L
  RestrictedProduct.mapAlongRingHom
    (fun (v : HeightOneSpectrum A) ↦ v.adicCompletion K)
    (fun (w : HeightOneSpectrum B) ↦ w.adicCompletion L)
    (HeightOneSpectrum.comap A)
    (tendsTo_comap_cofinite A B)
    (fun w ↦ adicCompletionComapSemialgHom A K L B (w.comap A) ⟨w, rfl⟩)
    (cofinite_mapsTo_adicCompletionComapSemialgHom A K L B)

/-- The ring homomorphism `𝔸_K^∞ → 𝔸_L^∞` for `L/K` an extension of number fields,
as a morphism lying over the canonical map `K → L`. -/
noncomputable def mapSemialgHom :
    𝔸ᶠ[A, K] →ₛₐ[algebraMap K L] 𝔸ᶠ[B, L] where
      __ := FiniteAdeleRing.mapRingHom A K L B
      map_smul' k a := by
        ext w
        simpa only [Algebra.smul_def'] using
          (adicCompletionComapSemialgHom A K L B (comap A w) ⟨w, rfl⟩).map_smul' k (a (comap A w))

omit [IsIntegralClosure B A L] [FiniteDimensional K L] in
lemma mapSemialgHom_apply (x : 𝔸ᶠ[A, K]) (w : HeightOneSpectrum B) :
    mapSemialgHom A K L B x w =
      adicCompletionComapSemialgHom A K L B (w.comap A) ⟨w, rfl⟩ (x (comap A w)) := rfl

omit [IsIntegralClosure B A L] [FiniteDimensional K L] in
lemma mapSemialgHom_continuous : Continuous (mapSemialgHom A K L B) :=
  have : FaithfulSMul A B := FaithfulSMul.of_field_isFractionRing A B K L
  RestrictedProduct.mapAlong_continuous _ _ _ (tendsTo_comap_cofinite A B) _
    (cofinite_mapsTo_adicCompletionComapSemialgHom A K L B)
    fun w ↦ adicCompletionComapSemialgHom_continuous A K L B _ ⟨w, rfl⟩

open scoped TensorProduct.RightActions

-- noncomputable
-- instance BaseChange.algebra : Algebra (FiniteAdeleRing A K) (FiniteAdeleRing B L) :=
--   RingHom.toAlgebra (FiniteAdeleRing.mapRingHom A K L B)
variable [Algebra 𝔸ᶠ[A, K] 𝔸ᶠ[B, L]]

-- attribute [local instance 9999] Algebra.toSMul in
-- noncomputable instance baseChangeAlgebra : Algebra K (FiniteAdeleRing B L) :=
--   Algebra.compHom (FiniteAdeleRing B L) (algebraMap K L)

-- instance : IsScalarTower K L (FiniteAdeleRing B L) :=
--   IsScalarTower.of_algebraMap_eq' rfl

/- this instance creates a nasty diamond for
 `IsScalarTower K (FiniteAdeleRing A K) (FiniteAdeleRing B L)` when K = L A = B, and
should probably be scoped (or even removed and statements changed so that they
don't need it).

examples of trouble this instance causes:

failure of
#synth IsScalarTower K (FiniteAdeleRing (𝓞 K) K) (FiniteAdeleRing (𝓞 K) K)

and as a consequence, failure of
#synth Module (FiniteAdeleRing (𝓞 K) K) ((FiniteAdeleRing (𝓞 K) K) ⊗[K] B)
-/
--attribute [local instance 9999] Algebra.toSMul in
instance [Algebra K 𝔸ᶠ[B, L]] [IsScalarTower K 𝔸ᶠ[A, K] 𝔸ᶠ[B, L]] :
    IsScalarTower K (FiniteAdeleRing A K) (FiniteAdeleRing B L) := by
  apply IsScalarTower.of_algebraMap_eq
  intro x
  rw [← IsScalarTower.algebraMap_apply]
  -- nth_rw 2 [RingHom.algebraMap_toAlgebra]
  -- exact SemialgHom.commutes (FiniteAdeleRing.mapSemialgHom A K L B) x |>.symm

open scoped RestrictedProduct in
class _root_.RestrictedProduct.FiberwiseSMul {α β : Type*} (f : α → β) (R : (b : β) → Type*)
    (A : (b : β) → Set (R b)) (𝓕 : Filter β) (M : (a : α) → Type*) (B : (a : α) → Set (M a))
    (𝓖 : Filter α) [(b : β) → (σ : { a // f a = b }) → SMul (R b) (M ↑σ)]
    [SMul (Πʳ b, [R b, A b]_[𝓕]) (Πʳ a, [M a, B a]_[𝓖])] : Prop where
  map_smul (f R M) (r : Πʳ b, [R b, A b]_[𝓕]) (x : Πʳ a, [M a, B a]_[𝓖]) (b : β)
    (σ : {a // f a = b}) : (r • x) σ = r b • x σ

open scoped RestrictedProduct in
instance : Algebra (Πʳ v : HeightOneSpectrum A, [v.adicCompletion K, v.adicCompletionIntegers K])
    (Πʳ w: HeightOneSpectrum B, [w.adicCompletion L, w.adicCompletionIntegers L]) :=
  inferInstanceAs (Algebra 𝔸ᶠ[A, K] 𝔸ᶠ[B, L])

abbrev ComapFiberwiseSMul : Prop :=
    RestrictedProduct.FiberwiseSMul (fun w : HeightOneSpectrum B ↦ w.comap A)
      (fun v ↦ v.adicCompletion K) (fun v ↦ adicCompletionIntegers K v) Filter.cofinite
      (fun w ↦ w.adicCompletion L) (fun w ↦ adicCompletionIntegers L w) Filter.cofinite

variable [i : ComapFiberwiseSMul A K L B]

omit [IsIntegralClosure B A L] [FiniteDimensional K L] in
lemma BaseChange.algebraMap_apply (w : HeightOneSpectrum B) (x : FiniteAdeleRing A K) :
    algebraMap _ (FiniteAdeleRing B L) x w =
      adicCompletionComapSemialgHom A K L B (w.comap A) ⟨w, rfl⟩ (x (comap A w)) := by
  rw [Algebra.algebraMap_eq_smul_one]
  have := i.map_smul x 1 (w.comap A) ⟨w, rfl⟩
  erw [this]
  rw [RestrictedProduct.one_apply]
  rw [RingHom.smul_toAlgebra]
  simp
  rfl

attribute [instance 100] RestrictedProduct.instSMulCoeOfSMulMemClass
-- otherwise
-- #synth SMul (FiniteAdeleRing A K) (FiniteAdeleRing B L)
-- spends 2 seconds failing to find `SMul (FiniteAdeleRing A K) (adicCompletion L w)

noncomputable section bijection

-- TODO : assume this?
-- instance baseChangeIntegerAlgebra : Algebra A (FiniteAdeleRing B L) :=
--   Algebra.compHom (FiniteAdeleRing B L) (algebraMap A B)

omit [Module.Finite A B] [IsDedekindDomain B] in
theorem range_adicCompletionTensorIntegerCoe_eq_lTensorRestriction (v : HeightOneSpectrum A) :
    LinearMap.range (adicCompletionTensorIntegerCoe A K B v) =
    RestrictedProduct.rangeLTensor A B (adicCompletion K) (integerSubmodule A K) v := by
  rfl

/-- The canonical linear isomorphism `L ⊗[K] 𝔸_K^∞ ≅ B ⊗[A] 𝔸_K^∞`. -/
def tensorEquivTensor :
    L ⊗[K] FiniteAdeleRing A K ≃ₗ[A] B ⊗[A] FiniteAdeleRing A K := by
  exact linearEquivTensorProductModule A K L B (FiniteAdeleRing A K)

omit [Module.Finite A B] [IsDedekindDomain B] [IsFractionRing B L] in
lemma tensorEquivTensor_tmul (b : B) (x : FiniteAdeleRing A K) :
    tensorEquivTensor A K L B ((algebraMap B L b) ⊗ₜ[K] x) = b ⊗ₜ[A] x := by
  simp [tensorEquivTensor, linearEquivTensorProductModule_tmul]

open scoped RestrictedProduct in
/-- The `A`-linear isomorphism `φ : B ⊗[K] 𝔸_K^∞ ≅ ∏'_v [B ⊗[A] K_v, B ⊗[A] 𝓞_v]`
given by `φ (b ⊗ x) v = b ⊗ (x v)`. -/
def tensorEquivRestrictedProduct :
    B ⊗[A] FiniteAdeleRing A K ≃ₗ[A]
      Πʳ v, [B ⊗[A] (adicCompletion K v), RestrictedProduct.rangeLTensor A
      B (adicCompletion K) (integerSubmodule A K) v]:= by
  have := Module.finitePresentation_of_finite A B
  have := isTorsionFree A K L B
  let map :=
    RestrictedProduct.lTensorEquiv A B (adicCompletion K) Filter.cofinite (integerSubmodule A K)
  apply LinearEquiv.trans (TensorProduct.congr (LinearEquiv.refl A B) _) map
  exact {
    __ := AddEquiv.refl _
    map_smul' a x := by
      ext v
      exact Algebra.smul_def a (x v) |>.symm
  }

omit [IsIntegralClosure B A L] [FiniteDimensional K L] [IsFractionRing B L] in
lemma tensorEquivRestrictedProduct_tmul (b : B) (x : FiniteAdeleRing A K)
    (v : HeightOneSpectrum A) :
    tensorEquivRestrictedProduct A K L B (b ⊗ₜ[A] x) v = b ⊗ₜ[A] (x v) := rfl

open scoped RestrictedProduct in
/-- The `A`-linear isomorphism `∏'_v [B ⊗[A] K_v, B ⊗[A] 𝓞_v] ≅ ∏'_v [∏_{w|v} L_w, ∏_{w|v} 𝓞_w]`
given by `adicCompletionComapIntegerLinearEquiv`. -/
def restrictedProduct_tensorProduct_equiv_restrictedProduct_prod :
    Πʳ v, [B ⊗[A] (adicCompletion K v), RestrictedProduct.rangeLTensor A
      B (adicCompletion K) (integerSubmodule A K) v] ≃ₗ[A]
    Πʳ (v : HeightOneSpectrum A), [(w : Extension B v) → adicCompletion L w.val,
      Submodule.pi Set.univ fun w : Extension B v ↦ (integerSubmodule B L w.val).restrictScalars A]
    :=
  LinearEquiv.restrictedProductCongrRight
    (adicCompletionComapIntegerLinearEquiv A K L B)
    (Filter.Eventually.of_forall <| adicCompletionComapIntegerLinearEquiv_bijOn A K L B)

lemma restrictedProduct_tensorProduct_equiv_restrictedProduct_prod_apply
    (f) (v : HeightOneSpectrum A) :
     FiniteAdeleRing.restrictedProduct_tensorProduct_equiv_restrictedProduct_prod A K L B f v =
     adicCompletionComapIntegerLinearEquiv A K L B v (f v) := rfl

open scoped RestrictedProduct in
/-- The `A`-linear isomorphism `∏'_v [∏_{w|v} L_w, ∏_{w|v} 𝓞_w] → 𝔸_L^∞` given by
`RestrictedProduct.flatten_equiv'`. -/
def restrictedProduct_prod_equiv [Algebra A 𝔸ᶠ[B, L]] [IsScalarTower A B 𝔸ᶠ[B, L]] :
    Πʳ (v : HeightOneSpectrum A), [(w : Extension B v) → adicCompletion L w.val,
    Submodule.pi Set.univ fun w : Extension B v ↦ (integerSubmodule B L w.val).restrictScalars A]
    ≃ₗ[A] FiniteAdeleRing B L :=
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

omit [IsIntegralClosure B A L] [FiniteDimensional K L] in
lemma restrictedProduct_prod_equiv_apply [Algebra A 𝔸ᶠ[B, L]] [IsScalarTower A B 𝔸ᶠ[B, L]]
    (f) (w : HeightOneSpectrum B) :
    restrictedProduct_prod_equiv A K L B f w = f (comap A w) ⟨w, rfl⟩ := rfl

-- TODO : double check whether all three `IsScalarTower` instances are needed
/-- The `K`-linear isomorphism `L ⊗ A_K^∞ ≅ A_L^∞` given by composing the previous four maps. -/
def baseChangeLinearEquiv [Algebra K 𝔸ᶠ[B, L]] [IsScalarTower K 𝔸ᶠ[A, K] 𝔸ᶠ[B, L]]
    [Algebra A 𝔸ᶠ[B, L]] [IsScalarTower A B 𝔸ᶠ[B, L]] [IsScalarTower A K 𝔸ᶠ[B, L]] :
    L ⊗[K] FiniteAdeleRing A K ≃ₗ[K] FiniteAdeleRing B L :=
  -- have : IsScalarTower A K (FiniteAdeleRing B L) := by
  --   --have : IsScalarTower A B (FiniteAdeleRing B L) := IsScalarTower.of_algebraMap_eq' rfl
  --   have : IsScalarTower A K (𝔸ᶠ[A, K]) := by exact instIsScalarTower A K
  --   apply IsScalarTower.of_algebraMap_eq
  --   intro x
  --   nth_rw 2 [RingHom.algebraMap_toAlgebra]
  --   rw [RingHom.comp_apply, IsScalarTower.algebraMap_apply A B (FiniteAdeleRing B L),
  --     ← IsScalarTower.algebraMap_apply A K L, IsScalarTower.algebraMap_apply A B L]
  --   rfl
  let f := (FiniteAdeleRing.tensorEquivTensor A K L B) ≪≫ₗ
    (FiniteAdeleRing.tensorEquivRestrictedProduct A K L B) ≪≫ₗ
    (FiniteAdeleRing.restrictedProduct_tensorProduct_equiv_restrictedProduct_prod A K L B) ≪≫ₗ
    (FiniteAdeleRing.restrictedProduct_prod_equiv A K L B).restrictScalars A
  LinearEquiv.extendScalarsOfIsLocalization (nonZeroDivisors A) K f

@[simp]
lemma algebraMap_apply (x : K) (v : HeightOneSpectrum A) :
    algebraMap K (FiniteAdeleRing A K) x v = algebraMap K (v.adicCompletion K) x := by
  rfl

@[simp]
lemma baseChangeLinearEquiv_tmul [Algebra K 𝔸ᶠ[B, L]] [IsScalarTower K 𝔸ᶠ[A, K] 𝔸ᶠ[B, L]]
    [Algebra A 𝔸ᶠ[B, L]] [IsScalarTower A B 𝔸ᶠ[B, L]] [IsScalarTower A K 𝔸ᶠ[B, L]]
    (b : B) (x : FiniteAdeleRing A K) :
    FiniteAdeleRing.baseChangeLinearEquiv A K L B ((algebraMap B L b) ⊗ₜ x) =
    (algebraMap _ (FiniteAdeleRing B L) b) * (algebraMap _ (FiniteAdeleRing B L) x) := by
  ext w
  simp [baseChangeLinearEquiv, restrictedProduct_prod_equiv_apply, tensorEquivTensor_tmul,
    restrictedProduct_tensorProduct_equiv_restrictedProduct_prod_apply,
    tensorEquivRestrictedProduct_tmul, adicCompletionComapIntegerLinearEquiv_tmul_apply,
    BaseChange.algebraMap_apply, IsScalarTower.algebraMap_apply B L (FiniteAdeleRing B L),
    IsScalarTower.algebraMap_apply B L (w.adicCompletion L), -Submodule.coe_pi]
  by_cases hb : b = 0
  · grind
  · exact .inl rfl

-- TODO : can we remove these assumptions?
open scoped RestrictedProduct in
theorem baseChange_bijective [Algebra K 𝔸ᶠ[B, L]] [IsScalarTower K 𝔸ᶠ[A, K] 𝔸ᶠ[B, L]]
    [Algebra A 𝔸ᶠ[B, L]] [IsScalarTower A B 𝔸ᶠ[B, L]] [IsScalarTower A K 𝔸ᶠ[B, L]]
    [IsScalarTower K L 𝔸ᶠ[B, L]] :
    Function.Bijective (SemialgHom.baseChange_of_algebraMap <|
      FiniteAdeleRing.mapSemialgHom A K L B) := by
  suffices ⇑(SemialgHom.baseChange_of_algebraMap <| FiniteAdeleRing.mapSemialgHom A K L B) =
      ⇑(FiniteAdeleRing.baseChangeLinearEquiv A K L B) by
      rw [this]
      exact (FiniteAdeleRing.baseChangeLinearEquiv A K L B).bijective
  -- have : IsScalarTower K L (FiniteAdeleRing B L) := by
  --   apply IsScalarTower.of_algebraMap_eq' rfl
  rw [← AlgHom.coe_restrictScalars' (R:=K), ← AlgHom.coe_toLinearMap, ← LinearEquiv.coe_toLinearMap]
  apply congr_arg
  have := IsIntegralClosure.isLocalizedModule A K L B
  apply IsLocalization.tensorProduct_ext (nonZeroDivisors A) B
  intro b x
  ext w
  simp [SemialgHom.baseChange_of_algebraMap_tmul, mapSemialgHom_apply, BaseChange.algebraMap_apply,
    IsScalarTower.algebraMap_apply B L (FiniteAdeleRing B L)]

/-- The `L`-algebra isomorphism `L ⊗_K 𝔸_K^∞ ≅ 𝔸_L^∞`. -/
def baseChangeAlgEquiv [Algebra K 𝔸ᶠ[B, L]] [IsScalarTower K 𝔸ᶠ[A, K] 𝔸ᶠ[B, L]]
    [Algebra A 𝔸ᶠ[B, L]] [IsScalarTower A B 𝔸ᶠ[B, L]] [IsScalarTower A K 𝔸ᶠ[B, L]]
    [IsScalarTower K L 𝔸ᶠ[B, L]] :
    L ⊗[K] FiniteAdeleRing A K ≃ₐ[L] FiniteAdeleRing B L :=
  AlgEquiv.ofBijective
    (SemialgHom.baseChange_of_algebraMap <| FiniteAdeleRing.mapSemialgHom A K L B)
    (FiniteAdeleRing.baseChange_bijective A K L B)

/-- The `𝔸_K^∞`-algebra isomorphism `L ⊗_K 𝔸_K^∞ ≅ 𝔸_L^∞`. -/
def baseChangeAdeleAlgEquiv [Algebra K 𝔸ᶠ[B, L]] [IsScalarTower K 𝔸ᶠ[A, K] 𝔸ᶠ[B, L]]
    [Algebra A 𝔸ᶠ[B, L]] [IsScalarTower A B 𝔸ᶠ[B, L]] [IsScalarTower A K 𝔸ᶠ[B, L]]
    [IsScalarTower K L 𝔸ᶠ[B, L]] [ComapFiberwiseSMul A K L B] :
    L ⊗[K] FiniteAdeleRing A K ≃ₐ[FiniteAdeleRing A K] FiniteAdeleRing B L where
  __ := SemialgHom.baseChangeRightOfAlgebraMap <| FiniteAdeleRing.mapSemialgHom A K L B
  __ := FiniteAdeleRing.baseChangeAlgEquiv A K L B
  commutes' x := by
    ext
    simp [BaseChange.algebraMap_apply]
    rfl

instance [Algebra K 𝔸ᶠ[B, L]] [IsScalarTower K 𝔸ᶠ[A, K] 𝔸ᶠ[B, L]]
    [Algebra A 𝔸ᶠ[B, L]] [IsScalarTower A B 𝔸ᶠ[B, L]] [IsScalarTower A K 𝔸ᶠ[B, L]]
    [IsScalarTower K L 𝔸ᶠ[B, L]] : Module.Finite (FiniteAdeleRing A K) (FiniteAdeleRing B L) :=
  Module.Finite.equiv (FiniteAdeleRing.baseChangeAdeleAlgEquiv A K L B).toLinearEquiv

end bijection

section moduleTopology

open scoped RestrictedProduct

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
  --letI (w : Extension B v) := comap_algebra A K L B w.prop
  --letI (w : Extension B v) := comap_integer_algebra A K L B w.prop
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
noncomputable local instance : Module (FiniteAdeleRing A K)
    Πʳ (v : HeightOneSpectrum A), [(w : Extension B v) → adicCompletion L w.1,
    ↑(piAdicIntegerSubmodule A K L B v)] :=
  inferInstanceAs <| Module
      (Πʳ v : HeightOneSpectrum A, [v.adicCompletion K, v.adicCompletionIntegers K])
      Πʳ (v : HeightOneSpectrum A), [(w : Extension B v) → adicCompletion L w.1,
    ↑(piAdicIntegerSubmodule A K L B v)]

open scoped RestrictedProduct in
/-- The continuous `𝔸 K`-Linear equivalence between `∏'_v ∏_{w∣v} L_w` and `𝔸 L` given by
reaindexing the elements. -/
noncomputable def restrictedProduct_pi_equiv :
    Πʳ (v : HeightOneSpectrum A), [(w : Extension B v) → adicCompletion L w.val,
      piAdicIntegerSubmodule A K L B v] ≃L[FiniteAdeleRing A K] FiniteAdeleRing B L :=
  have := FaithfulSMul.of_field_isFractionRing A B K L
  let f : _ ≃ₜ (FiniteAdeleRing B L) := RestrictedProduct.flatten_homeomorph'
    (G := adicCompletion L) (fun w ↦ adicCompletionIntegers L w) (tendsTo_comap_cofinite A B)
  {
    __ := f
    map_add' x y := rfl
    map_smul' r x := by
      ext w
      --letI (w : HeightOneSpectrum B) := comap_algebra A K L B (w := w) rfl
      rw [RingHom.id_apply, Algebra.smul_def, RestrictedProduct.mul_apply,
        BaseChange.algebraMap_apply]
      rfl
  }

omit [IsIntegralClosure B A L] in
lemma restrictedProduct_pi_isModuleTopology [Algebra K 𝔸ᶠ[B, L]] [IsScalarTower K 𝔸ᶠ[A, K] 𝔸ᶠ[B, L]]
    [Algebra A 𝔸ᶠ[B, L]] [IsScalarTower A B 𝔸ᶠ[B, L]] [IsScalarTower A K 𝔸ᶠ[B, L]]
    [IsScalarTower K L 𝔸ᶠ[B, L]] : IsModuleTopology (FiniteAdeleRing A K)
    (Πʳ (v : HeightOneSpectrum A), [(w : Extension B v) → adicCompletion L w.val,
      piAdicIntegerSubmodule A K L B v]) := by
  have :=
    Module.Finite.equiv (FiniteAdeleRing.restrictedProduct_pi_equiv A K L B).symm.toLinearEquiv
  unfold FiniteAdeleRing at this
  have := prodAdicCompletionComap_isModuleTopology A K L B
  apply RestrictedProduct.isModuleTopology
  · exact fun v ↦ Valued.isOpen_integer (adicCompletion K v)
  · intro v
    simp only [piAdicIntegerSubmodule, Submodule.coe_pi, Submodule.coe_restrictScalars]
    apply isOpen_set_pi _ (fun _ _ ↦ Valued.isOpen_integer _)
    rw [Set.finite_univ_iff]
    exact Extension.finite A K L B v

omit [IsIntegralClosure B A L] in
instance [Algebra K 𝔸ᶠ[B, L]] [IsScalarTower K 𝔸ᶠ[A, K] 𝔸ᶠ[B, L]]
    [Algebra A 𝔸ᶠ[B, L]] [IsScalarTower A B 𝔸ᶠ[B, L]] [IsScalarTower A K 𝔸ᶠ[B, L]]
    [IsScalarTower K L 𝔸ᶠ[B, L]] : IsModuleTopology (FiniteAdeleRing A K) (FiniteAdeleRing B L) :=
  have := FiniteAdeleRing.restrictedProduct_pi_isModuleTopology A K L B
  IsModuleTopology.iso (FiniteAdeleRing.restrictedProduct_pi_equiv A K L B)

end moduleTopology

/-- The continuous `𝔸_K^∞`-algebra isomorphism `L ⊗_K 𝔸_K^∞ ≅ 𝔸_L^∞` -/
noncomputable def baseChangeAdeleContinuousAlgEquiv [Algebra K 𝔸ᶠ[B, L]]
    [IsScalarTower K 𝔸ᶠ[A, K] 𝔸ᶠ[B, L]]
    [Algebra A 𝔸ᶠ[B, L]] [IsScalarTower A B 𝔸ᶠ[B, L]] [IsScalarTower A K 𝔸ᶠ[B, L]]
    [IsScalarTower K L 𝔸ᶠ[B, L]] :
    L ⊗[K] FiniteAdeleRing A K ≃A[FiniteAdeleRing A K] FiniteAdeleRing B L :=
  IsModuleTopology.continuousAlgEquivOfAlgEquiv <| baseChangeAdeleAlgEquiv A K L B

/-- The continuous `L`-algebra isomorphism `L ⊗_K 𝔸_K^∞ ≅ 𝔸_L^∞` -/
noncomputable def baseChangeContinuousAlgEquiv [Algebra K 𝔸ᶠ[B, L]]
    [IsScalarTower K 𝔸ᶠ[A, K] 𝔸ᶠ[B, L]]
    [Algebra A 𝔸ᶠ[B, L]] [IsScalarTower A B 𝔸ᶠ[B, L]] [IsScalarTower A K 𝔸ᶠ[B, L]]
    [IsScalarTower K L 𝔸ᶠ[B, L]] :
    L ⊗[K] FiniteAdeleRing A K ≃A[L] FiniteAdeleRing B L where
  __ := FiniteAdeleRing.baseChangeAlgEquiv A K L B
  __ := FiniteAdeleRing.baseChangeAdeleContinuousAlgEquiv A K L B

end IsDedekindDomain.FiniteAdeleRing
