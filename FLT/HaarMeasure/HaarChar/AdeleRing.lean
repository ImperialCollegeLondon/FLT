import FLT.HaarMeasure.HaarChar.Ring
import FLT.Mathlib.MeasureTheory.Constructions.BorelSpace.AdicCompletion
import FLT.Mathlib.NumberTheory.NumberField.AdeleRing
import FLT.NumberField.AdeleRing
import FLT.HaarMeasure.HaarChar.RealComplex
import FLT.HaarMeasure.HaarChar.Padic
import FLT.HaarMeasure.HaarChar.FiniteDimensional
import Mathlib.NumberTheory.NumberField.ProductFormula
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
instance (k A B : Type*) [Field k] [CommSemiring A] [Ring B]
    [Algebra k A] [Algebra k B]
    [Algebra.IsCentral k B] [IsSimpleRing B] :
    Algebra.IsCentral A (B ⊗[k] A) := sorry

open IsDedekindDomain RestrictedProduct in
open scoped TensorProduct.RightActions in
variable
  [MeasurableSpace (B ⊗[K] (FiniteAdeleRing (𝓞 K) K))]
  [BorelSpace (B ⊗[K] (FiniteAdeleRing (𝓞 K) K))] in
lemma NumberField.AdeleRing.isCentralSimple_finite_addHaarScalarFactor_left_mul_eq_right_mul
    [IsSimpleRing B] [Algebra.IsCentral K B] (u : (B ⊗[K] (FiniteAdeleRing (𝓞 K) K))ˣ) :
    addEquivAddHaarChar (ContinuousAddEquiv.mulLeft u) =
    addEquivAddHaarChar (ContinuousAddEquiv.mulRight u) := by
  -- finite places
  have : Module.FinitePresentation K B := Module.finitePresentation_of_finite ..
  /- let e :
      B ⊗[K] (FiniteAdeleRing (𝓞 K) K) ≃ₜ+
      Πʳ v : HeightOneSpectrum (𝓞 K), [B ⊗[K] (v.adicCompletion K), sorry] := sorry -/
  let v : HeightOneSpectrum (𝓞 K) := sorry
  let u' : (B ⊗[K] (v.adicCompletion K))ˣ := sorry
  let : MeasurableSpace (B ⊗[K] v.adicCompletion K) := borel _
  have : BorelSpace (B ⊗[K] v.adicCompletion K) := ⟨rfl⟩
  have hf := IsSimpleRing.ringHaarChar_eq_addEquivAddHaarChar_mulRight (F := v.adicCompletion K) u'
  sorry

open scoped TensorProduct.RightActions in
variable
  [MeasurableSpace (B ⊗[K] (InfiniteAdeleRing K))]
  [BorelSpace (B ⊗[K] (InfiniteAdeleRing K))] in
lemma NumberField.AdeleRing.isCentralSimple_infinite_addHaarScalarFactor_left_mul_eq_right_mul
    [IsSimpleRing B] [Algebra.IsCentral K B] (u : (B ⊗[K] (InfiniteAdeleRing K))ˣ) :
    addEquivAddHaarChar (ContinuousAddEquiv.mulLeft u) =
    addEquivAddHaarChar (ContinuousAddEquiv.mulRight u) := by
  -- infinite places
  #check InfiniteAdeleRing.ringEquiv_mixedSpace
  let vi : InfinitePlace K := sorry
  let u'i : (B ⊗[K] vi.Completion)ˣ := sorry
  let : MeasurableSpace (B ⊗[K] vi.Completion) := borel _
  have : BorelSpace (B ⊗[K] vi.Completion) := ⟨rfl⟩
  have hi := IsSimpleRing.ringHaarChar_eq_addEquivAddHaarChar_mulRight (F := vi.Completion) u'i
  sorry

open scoped TensorProduct.RightActions in
variable
  [MeasurableSpace (B ⊗[K] 𝔸 K)]
  [BorelSpace (B ⊗[K] 𝔸 K)] in
lemma NumberField.AdeleRing.isCentralSimple_addHaarScalarFactor_left_mul_eq_right_mul
    [IsSimpleRing B] [Algebra.IsCentral K B] (u : (B ⊗[K] (𝔸 K))ˣ) :
    addEquivAddHaarChar (ContinuousAddEquiv.mulLeft u) =
    addEquivAddHaarChar (ContinuousAddEquiv.mulRight u) := by
  open IsDedekindDomain in

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

-- depends on `IsDedekindDomain.HeightOneSpectrum.padicEquiv`, from pending mathlib PR #30576
lemma padicEquiv_norm_eq (v : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ)) (x : v.adicCompletion ℚ) :
    ‖(Rat.HeightOneSpectrum.adicCompletion.padicEquiv v) x‖ = ‖x‖ := by
  sorry

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
      padicEquiv_norm_eq]
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

open scoped TensorProduct.RightActions

lemma MeasureTheory.addHaarScalarFactor_tensor_adeles_eq_one (φ : V ≃ₗ[K] V)
    [MeasurableSpace (V ⊗[K] 𝔸 K)] [BorelSpace (V ⊗[K] 𝔸 K)] :
    addEquivAddHaarChar
      (ContinuousLinearEquiv.baseChange K (𝔸 K) V V φ).toContinuousAddEquiv = 1 := by
  sorry

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
