import FLT.HaarMeasure.HaarChar.Ring
import FLT.Mathlib.MeasureTheory.Constructions.BorelSpace.AdicCompletion
import FLT.Mathlib.NumberTheory.NumberField.AdeleRing
import FLT.Mathlib.NumberTheory.Padics.HeightOneSpectrum
import FLT.NumberField.AdeleRing
import FLT.HaarMeasure.HaarChar.RealComplex
import FLT.HaarMeasure.HaarChar.Padic
import Mathlib.NumberTheory.NumberField.ProductFormula
import FLT.Mathlib.LinearAlgebra.Lattice
/-!

# Global units are in the determinant of the adelic Haar character

If `K` is a number field and `B` is a finite-dimensional `K`-algebra
then `B ⊗ 𝔸_K` is a locally compact topological ring, so it admits
a Haar character `(B ⊗ 𝔸_K)ˣ → ℝ>0`. In this file we show
that the global units `Bˣ` are in the kernel of this character.

-/

open NumberField

open scoped TensorProduct

variable (K L : Type*) [Field K] [Field L] [Algebra K L] [NumberField K] [NumberField L]

open scoped NumberField.AdeleRing -- for 𝔸 K notation

variable (V : Type*) [AddCommGroup V] [Module L V] [Module K V] [IsScalarTower K L V]
  [FiniteDimensional L V] [FiniteDimensional K V] -- the latter can be proved but
  -- can't be an instance as it uses L

variable (B : Type*) [Ring B] [Algebra K B] [FiniteDimensional K B]

open scoped TensorProduct

open NumberField MeasureTheory

open scoped TensorProduct.RightActions in
variable
  [MeasurableSpace (B ⊗[K] 𝔸 K)]
  [BorelSpace (B ⊗[K] 𝔸 K)] in
lemma NumberField.AdeleRing.isCentralSimple_addHaarScalarFactor_left_mul_eq_right_mul
    [IsSimpleRing B] [Algebra.IsCentral K B] (u : (B ⊗[K] (𝔸 K))ˣ) :
    addEquivAddHaarChar (ContinuousAddEquiv.mulLeft u) =
    addEquivAddHaarChar (ContinuousAddEquiv.mulRight u) := by
  sorry

lemma MeasureTheory.ringHaarChar_adeles_rat (x : (𝔸 ℚ)ˣ) :
  ringHaarChar x = ringHaarChar (MulEquiv.prodUnits x).1 *
    (∏ᶠ p, ringHaarChar (MulEquiv.restrictedProductUnits (MulEquiv.prodUnits x).2 p)) := by
  unfold AdeleRing
  rw [ringHaarChar_prod' x]
  congr
  have := Fact.mk <| NumberField.isOpenAdicCompletionIntegers ℚ
  have := NumberField.instCompactSpaceAdicCompletionIntegers ℚ
  convert addEquivAddHaarChar_restrictedProductCongrRight
    (C := fun p ↦ (p.adicCompletionIntegers ℚ).toAddSubgroup)
    (fun p ↦
      (ContinuousAddEquiv.mulLeft (MulEquiv.restrictedProductUnits (MulEquiv.prodUnits x).2 p))) _
  exact (MulEquiv.restrictedProductUnits (MulEquiv.prodUnits x).2).2.mono
    (fun p hp ↦ Equiv.bijOn' _
      (fun x hx ↦ Subring.mul_mem _ ((Submonoid.mem_units_iff _ _).mp hp).1 hx)
      (fun x hx ↦ Subring.mul_mem _ ((Submonoid.mem_units_iff _ _).mp hp).2 hx))

lemma MeasureTheory.ringHaarChar_adeles_units_rat_eq_one (x : ℚˣ) :
  ringHaarChar (Units.map (algebraMap ℚ (𝔸 ℚ)) x : (𝔸 ℚ)ˣ) = 1 := by
  rw [ringHaarChar_adeles_rat (Units.map (algebraMap ℚ (𝔸 ℚ)) x : (𝔸 ℚ)ˣ)]
  ext; simp only [NNReal.coe_mul, NNReal.coe_one]
  rw [← NumberField.prod_abs_eq_one (K := ℚ) (x := x) (Units.ne_zero x)]; congr
  · -- infinite place
    simp only [InfiniteAdeleRing, ringHaarChar_pi', NNReal.coe_prod, Rat.infinitePlace_apply,
      Rat.cast_abs]
    congr; ext v; rw [Subsingleton.elim v Rat.infinitePlace]
    let : Algebra ℤ Rat.infinitePlace.Completion := Ring.toIntAlgebra _
    simp [InfinitePlace.mult, Rat.isReal_infinitePlace,
      ringHaarChar_eq_ringHaarChar_of_continuousAlgEquiv {
        __ := Rat.infinitePlace_completion_continuousAlgEquiv
        commutes' := by simp},
      ringHaarChar_real, ← Rat.infinitePlace_completion_continuousAlgEquiv_apply_algebraMap,
      -eq_ratCast]
    rfl
  · -- finite places
    rw [← finprod_comp_equiv FinitePlace.equivHeightOneSpectrum.symm]
    conv_lhs =>
      apply NNReal.toRealHom.map_finprod_of_injective (injective_of_le_imp_le _ fun {x y} a ↦ a)
    apply finprod_congr; intro p
    let : Algebra ℤ (p.adicCompletion ℚ) := Ring.toIntAlgebra _
    simp [FinitePlace.equivHeightOneSpectrum,
      ringHaarChar_eq_ringHaarChar_of_continuousAlgEquiv {
        __ := (Rat.HeightOneSpectrum.adicCompletion.padicEquiv p)
        commutes' := by simp},
      Rat.HeightOneSpectrum.adicCompletion.padicEquiv_norm_eq]
    rfl

-- TODO: need TensorProduct.RightActions.LinearEquiv.baseChange
open scoped TensorProduct.RightActions in
/-- The continuous A-linear map (A a topological ring, tensor products have the module
topology) A ⊗[R] M ≃ A ⊗[R] N associated to an abstract R-linear isomorphism M ≃ N. -/
noncomputable def ContinuousLinearEquiv.baseChange (R : Type*) [CommRing R]
    (A : Type*) [CommRing A] [Algebra R A] [TopologicalSpace A]
    (M N : Type*) [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [Module.Finite R M] [Module.Finite R N]
    (φ : M ≃ₗ[R] N) : (M ⊗[R] A) ≃L[A] (N ⊗[R] A) where
  __ := TensorProduct.RightActions.LinearEquiv.baseChange _ _ _ _ φ
  continuous_toFun := IsModuleTopology.continuous_of_linearMap _
  continuous_invFun := IsModuleTopology.continuous_of_linearMap _

@[simp]
lemma ContinuousLinearEquiv.baseChange_apply (R : Type*) [CommRing R]
    (A : Type*) [CommRing A] [Algebra R A] [TopologicalSpace A]
    (M N : Type*) [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [Module.Finite R M] [Module.Finite R N]
    (φ : M ≃ₗ[R] N) (m : M) (a : A) :
    ContinuousLinearEquiv.baseChange R A M N φ (m ⊗ₜ a) = (φ m) ⊗ₜ a := rfl

section Rat

variable [Module ℚ V] [FiniteDimensional ℚ V]

open TensorProduct.RightActions RestrictedProduct

-- crazy comment bug! The more comment, the longer it takes to compile.
/-- The canonical map L ⊗[ℤ] X ≃ V ⊗[ℚ] X where L is a ℤ-lattice in ℚ-vector space V.
;sdfighsdlkgfhjsdlfkjghsdlkjghsdlfkjghsdlkjfglsdh -/
noncomputable def IntegralLattice.baseChangeEquiv :
    (IntegralLattice ℤ ℚ V) ⊗[ℤ] AdeleRing (𝓞 ℚ) ℚ ≃L[AdeleRing (𝓞 ℚ) ℚ]
    V ⊗[ℚ] AdeleRing (𝓞 ℚ) ℚ := by
  classical
  letI bar : AdeleRing (𝓞 ℚ) ℚ ⊗[ℤ] (IntegralLattice ℤ ℚ V) ≃ₗ[AdeleRing (𝓞 ℚ) ℚ]
    AdeleRing (𝓞 ℚ) ℚ ⊗[ℚ] V :=
  (Module.Basis.baseChangeEquiv' (Module.Basis.ofVectorSpaceIndex ℚ V) ℤ ℚ
    (IntegralLattice ℤ ℚ V) V (IntegralLattice.basis ℤ ℚ V) (Module.Basis.ofVectorSpace ℚ V) _)
  letI foo : (IntegralLattice ℤ ℚ V) ⊗[ℤ] AdeleRing (𝓞 ℚ) ℚ ≃ₗ[AdeleRing (𝓞 ℚ) ℚ]
    V ⊗[ℚ] AdeleRing (𝓞 ℚ) ℚ := (Module.TensorProduct.comm _ _ _).symm ≪≫ₗ bar ≪≫ₗ
      (Module.TensorProduct.comm _ _ _)
  exact {
  __ := foo
  continuous_toFun := IsModuleTopology.continuous_of_linearMap foo.toLinearMap
  continuous_invFun := IsModuleTopology.continuous_of_linearMap foo.symm.toLinearMap
    }

/-- Tensoring over the adele ring is the same as the product of tensoring over ℝ and
the restricted product of tensoring over ℚₚ. -/
noncomputable def IntegralLattice.tensorAdelesEquivRestrictedProduct :
    (IntegralLattice ℤ ℚ V) ⊗[ℤ] AdeleRing (𝓞 ℚ) ℚ ≃ₗ[ℤ]
    ((IntegralLattice ℤ ℚ V) ⊗[ℤ] ℝ) × (Πʳ v : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ),
      [(IntegralLattice ℤ ℚ V) ⊗[ℤ] v.adicCompletion ℚ,
        (LinearMap.range (LinearMap.lTensor (IntegralLattice ℤ ℚ V)
          (v.adicCompletionIntegers ℚ).subtype.toIntLinearMap))]) :=
  -- tensor product commutes with binary products and restricted products
  sorry

/-- Tensoring over the adele ring is the same as the product of tensoring over ℝ and
the restricted product of tensoring over ℚₚ. -/
noncomputable def IntegralLattice.tensorAdelesContinuousEquivRestrictedProduct :
    (IntegralLattice ℤ ℚ V) ⊗[ℤ] AdeleRing (𝓞 ℚ) ℚ ≃L[ℤ]
    ((IntegralLattice ℤ ℚ V) ⊗[ℤ] ℝ) × (Πʳ v : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ),
      [(IntegralLattice ℤ ℚ V) ⊗[ℤ] v.adicCompletion ℚ,
        (LinearMap.range (LinearMap.lTensor (IntegralLattice ℤ ℚ V)
          (v.adicCompletionIntegers ℚ).subtype.toIntLinearMap))]) :=
  -- linearity is above; continuity follows from AdeleRing^n = prod'_v Q_v^n topologically
  sorry

-- we need a ton of auxiliary definitions

namespace Aux

/-- An auxiliary canonical map. -/
def c_infty_alg : IntegralLattice ℤ ℚ V ⊗[ℤ] ℝ ≃ₗ[ℝ] V ⊗[ℚ] ℝ := sorry -- algebra; done modulo symm
  -- (Module.Basis.baseChangeEquiv' in FLT/Mathlib/LinearAlgebra/Lattice.lean)

/-- An auxiliary canonical map. -/
def c_infty : IntegralLattice ℤ ℚ V ⊗[ℤ] ℝ ≃L[ℝ] V ⊗[ℚ] ℝ := sorry
-- continuity follows from module top

/-- An auxiliary canonical map. -/
def c_v_alg (v : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ)) :
    IntegralLattice ℤ ℚ V ⊗[ℤ] v.adicCompletion ℚ ≃ₗ[v.adicCompletion ℚ]
    V ⊗[ℚ] v.adicCompletion ℚ := sorry -- algebra; done (Module.Basis.baseChangeEquiv') modulo symm
    -- see FLT/Mathlib/LinearAlgebra/Lattice.lean

/-- An auxiliary canonical map. -/
def c_v (v : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ)) :
    IntegralLattice ℤ ℚ V ⊗[ℤ] v.adicCompletion ℚ ≃L[v.adicCompletion ℚ]
    V ⊗[ℚ] v.adicCompletion ℚ := sorry -- continuity follows from module top

/-- An auxiliary canonical map. -/
def c_adele : ((IntegralLattice ℤ ℚ V) ⊗[ℤ] ℝ) ×
    (Πʳ v : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ),
      [(IntegralLattice ℤ ℚ V) ⊗[ℤ] v.adicCompletion ℚ,
        (LinearMap.range (LinearMap.lTensor (IntegralLattice ℤ ℚ V)
          (v.adicCompletionIntegers ℚ).subtype.toIntLinearMap))]) ≃L[ℤ]
    (V ⊗[ℚ] ℝ) ×
    (Πʳ v : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ),
      [V ⊗[ℚ] v.adicCompletion ℚ,
        (((c_v_alg V v).toAddMonoidHom.comp (LinearMap.lTensor (IntegralLattice ℤ ℚ V)
          (v.adicCompletionIntegers ℚ).subtype.toIntLinearMap).toAddMonoidHom).range)]) := sorry
  -- product of homeos is a homeo; restricted product of homeos is a homeo

/-- The product of the local components φᵥ of a linear map φ. -/
def prodLocalComponents (φ : V ≃ₗ[ℚ] V) : (V ⊗[ℚ] ℝ) ×
    (Πʳ v : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ),
      [V ⊗[ℚ] v.adicCompletion ℚ,
        (((c_v_alg V v).toAddMonoidHom.comp (LinearMap.lTensor (IntegralLattice ℤ ℚ V)
          (v.adicCompletionIntegers ℚ).subtype.toIntLinearMap).toAddMonoidHom).range)]) ≃ₜ+
    (V ⊗[ℚ] ℝ) ×
    (Πʳ v : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ),
      [V ⊗[ℚ] v.adicCompletion ℚ,
        (((c_v_alg V v).toAddMonoidHom.comp (LinearMap.lTensor (IntegralLattice ℤ ℚ V)
          (v.adicCompletionIntegers ℚ).subtype.toIntLinearMap).toAddMonoidHom).range)]) :=
  -- this is defined to be ∏'ᵥ φᵥ
  sorry

end Aux

-- In applications R will be ℝ or v.adicCompletion ℚ but probably don't want this in general
/-- A local instance of a Borel space structure on a tensor product. -/
local instance (V : Type*) [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V]
    (R : Type*) [CommRing R] [Algebra ℚ R] [TopologicalSpace R] :
    MeasurableSpace (V ⊗[ℚ] R) := borel _

-- In applications R will be ℝ or v.adicCompletion ℚ but probably don't want this in general
local instance (V : Type*) [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V]
    (R : Type*) [CommRing R] [Algebra ℚ R] [TopologicalSpace R] :
    BorelSpace (V ⊗[ℚ] R) := ⟨rfl⟩

-- In applications this will be an adelic thing; probably don't want this in general
open scoped RestrictedProduct in
/-- A local instance of a Borel space structure on a restricted product. -/
local instance {ι : Type*} (R : ι → Type*) (A : (i : ι) → Set (R i)) (𝓕 : Filter ι)
    [(i : ι) → TopologicalSpace (R i)] : MeasurableSpace Πʳ (i : ι), [R i, A i]_[𝓕] :=
  borel _

-- In applications this will be an adelic thing; probably don't want this in general
open scoped RestrictedProduct in
local instance {ι : Type*} (R : ι → Type*) (A : (i : ι) → Set (R i)) (𝓕 : Filter ι)
    [(i : ι) → TopologicalSpace (R i)] : BorelSpace Πʳ (i : ι), [R i, A i]_[𝓕] :=
  ⟨rfl⟩

-- try left before right ;-)
attribute [instance 101] secondCountableTopologyEither_of_left

-- Don't strictly speaking need this because of above hack
instance : BorelSpace
      Πʳ (v : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ)),
        [V ⊗[ℚ] IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v,
        ↑(((Aux.c_v_alg V v)).toAddMonoidHom.comp
              (LinearMap.lTensor (IntegralLattice ℤ ℚ V)
                  (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
                          v).subtype.toAddMonoidHom.toIntLinearMap).toAddMonoidHom).range] := by
  sorry

instance : Fact (∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ), IsOpen
  (((Aux.c_v_alg V v)).toAddMonoidHom.comp
    (LinearMap.lTensor (IntegralLattice ℤ ℚ V)
      (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
        v).subtype.toAddMonoidHom.toIntLinearMap).toAddMonoidHom).range.carrier) :=
  sorry

instance : LocallyCompactSpace
      Πʳ (v : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ)),
        [V ⊗[ℚ] IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v,
        ↑(((Aux.c_v_alg V v)).toAddMonoidHom.comp
              (LinearMap.lTensor (IntegralLattice ℤ ℚ V)
                  (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ
                          v).subtype.toAddMonoidHom.toIntLinearMap).toAddMonoidHom).range] :=
  RestrictedProduct.locallyCompactSpace_of_addGroup _ sorry

lemma MeasureTheory.addHaarScalarFactor_prodLocalComponents_eq_one (φ : V ≃ₗ[ℚ] V) :
    addEquivAddHaarChar (Aux.prodLocalComponents V φ) = 1 :=
  sorry

lemma MeasureTheory.addHaarScalarFactor_tensor_adeles_rat_eq_one (φ : V ≃ₗ[ℚ] V)
    [MeasurableSpace (V ⊗[ℚ] 𝔸 ℚ)] [BorelSpace (V ⊗[ℚ] 𝔸 ℚ)] :
    addEquivAddHaarChar
      (ContinuousLinearEquiv.baseChange ℚ (𝔸 ℚ) V V φ).toContinuousAddEquiv = 1 := by
  classical
  -- show that `(ContinuousLinearEquiv.baseChange ℚ (𝔸 ℚ) V V φ)`
  -- and `(Aux.prodLocalComponents V φ)` are intertwined by
  -- `c_adele V ∘ IntegralLattice.baseChangeEquiv
  -- and then deduce from the previous lemma
  sorry

end Rat

open scoped TensorProduct.RightActions in
lemma MeasureTheory.addHaarScalarFactor_tensor_adeles_eq_one (φ : V ≃ₗ[K] V)
    [MeasurableSpace (V ⊗[K] 𝔸 K)] [BorelSpace (V ⊗[K] 𝔸 K)] :
    addEquivAddHaarChar
      (ContinuousLinearEquiv.baseChange K (𝔸 K) V V φ).toContinuousAddEquiv = 1 := by
  -- we deduce this from the corresponding statement for `K = ℚ`.
  -- A K-module is a ℚ-module
  let : Module ℚ V := Module.compHom V (algebraMap ℚ K)
  have : Module.Finite ℚ V := FiniteDimensional.trans ℚ K V
  let : Module (AdeleRing (𝓞 ℚ) ℚ) (V ⊗[K] AdeleRing (𝓞 K) K) :=
    Module.compHom _ (algebraMap (AdeleRing (𝓞 ℚ) ℚ) (AdeleRing (𝓞 K) K))
  have : IsScalarTower (AdeleRing (𝓞 ℚ) ℚ) (AdeleRing (𝓞 K) K) (V ⊗[K] AdeleRing (𝓞 K) K) :=
    IsScalarTower.of_algebraMap_smul fun r ↦ congrFun rfl
  -- and V ⊗[K] 𝔸_K ≃ V ⊗[ℚ] 𝔸_ℚ
  let f := NumberField.AdeleRing.ModuleBaseChangeContinuousAddEquiv ℚ K V
  borelize (V ⊗[ℚ] AdeleRing (𝓞 ℚ) ℚ)
  have φℚ : V ≃ₗ[ℚ] V := by exact Function.invFun (fun a ↦ φ) φ
  -- and the obvious diagram commutes
  have := MeasureTheory.addEquivAddHaarChar_eq_addEquivAddHaarChar_of_continuousAddEquiv f
    (ContinuousLinearEquiv.baseChange ℚ (𝔸 ℚ) V V (φ.restrictScalars ℚ)).toContinuousAddEquiv
    (ContinuousLinearEquiv.baseChange K (𝔸 K) V V φ).toContinuousAddEquiv
  rw [← this]
  -- so the result follows from the case K=ℚ
  · apply MeasureTheory.addHaarScalarFactor_tensor_adeles_rat_eq_one
  · intro x
    induction x with
    | zero => simp
    | tmul x y => rfl
    | add x y hx hy => simp [hx, hy]

open scoped TensorProduct.RightActions in
/-- Left multiplication by an element of Bˣ on B ⊗ 𝔸_K does not scale additive
Haar measure. In other words, Bˣ is in the kernel of the `ringHaarChar` of `B ⊗ 𝔸_K`.
-/
lemma NumberField.AdeleRing.units_mem_ringHaarCharacter_ker
    [MeasurableSpace (B ⊗[K] AdeleRing (𝓞 K) K)] [BorelSpace (B ⊗[K] AdeleRing (𝓞 K) K)]
    (b : Bˣ) :
    (Units.map Algebra.TensorProduct.includeLeftRingHom.toMonoidHom b :
      (B ⊗[K] AdeleRing (𝓞 K) K)ˣ) ∈
    ringHaarChar_ker (B ⊗[K] AdeleRing (𝓞 K) K) := by
  rw [mem_ringHaarChar_ker, ringHaarChar_apply]
  convert MeasureTheory.addHaarScalarFactor_tensor_adeles_eq_one K B (LinearEquiv.mulLeft K b)
  ext c
  change _ = (ContinuousLinearEquiv.baseChange K _ _ _ _) c
  induction c with
  | zero => simp
  | tmul x y => simp [LinearEquiv.mulLeft]
  | add x y hx hy => simp_all [mul_add]

open scoped TensorProduct.RightActions in
/-- Right multiplication by an element of Bˣ on B ⊗ 𝔸_K does not scale additive
Haar measure.
-/
lemma NumberField.AdeleRing.addEquivAddHaarChar_mulRight_unit_eq_one
    [MeasurableSpace (B ⊗[K] AdeleRing (𝓞 K) K)] [BorelSpace (B ⊗[K] AdeleRing (𝓞 K) K)]
    (b : Bˣ) :
    addEquivAddHaarChar
      (ContinuousAddEquiv.mulRight
        (Units.map Algebra.TensorProduct.includeLeftRingHom.toMonoidHom b :
      (B ⊗[K] AdeleRing (𝓞 K) K)ˣ)) = 1 := by
  convert addHaarScalarFactor_tensor_adeles_eq_one K B (LinearEquiv.mulRight K b)
  ext c
  change _ = (ContinuousLinearEquiv.baseChange K _ _ _ _) c
  induction c with
  | zero => simp
  | tmul x y => simp [LinearEquiv.mulRight]
  | add x y hx hy => simp_all [add_mul]
