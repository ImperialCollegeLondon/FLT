module

public import FLT.HaarMeasure.HaarChar.Ring
public import FLT.Mathlib.Algebra.Central.TensorProduct
public import FLT.Mathlib.MeasureTheory.Constructions.BorelSpace.AdicCompletion
public import FLT.Mathlib.NumberTheory.NumberField.AdeleRing
public import FLT.Mathlib.NumberTheory.Padics.HeightOneSpectrum
public import FLT.NumberField.AdeleRing
public import FLT.HaarMeasure.HaarChar.RealComplex
public import FLT.HaarMeasure.HaarChar.Padic
public import FLT.HaarMeasure.HaarChar.FiniteDimensional
public import Mathlib.NumberTheory.NumberField.ProductFormula
public import FLT.HaarMeasure.HaarChar.FiniteDimensional
public import FLT.HaarMeasure.HaarChar.FiniteAdeleRing

/-!

# Global units are in the determinant of the adelic Haar character

If `K` is a number field and `B` is a finite-dimensional `K`-algebra
then `B ⊗ 𝔸_K` is a locally compact topological ring, so it admits
a Haar character `(B ⊗ 𝔸_K)ˣ → ℝ>0`. In this file we show
that the global units `Bˣ` are in the kernel of this character.

-/

@[expose] public section

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

set_option backward.isDefEq.respectTransparency false in
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

set_option backward.isDefEq.respectTransparency false in
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
      apply NNReal.toRealHom.map_finprod_of_injective (.of_eq_imp_le fun {_ _} a ↦ a.le)
    apply finprod_congr; intro p
    let : Algebra ℤ (p.adicCompletion ℚ) := Ring.toIntAlgebra _
    simp only [RingHom.toMonoidHom_eq_coe,
      ringHaarChar_eq_ringHaarChar_of_continuousAlgEquiv
          { __ := (Rat.HeightOneSpectrum.adicCompletion.padicEquiv p)
            commutes' := by simp },
      AlgEquiv.toEquiv_eq_coe, MulEquiv.toMonoidHom_eq_coe, ringHaarChar_padic, Units.coe_map,
      MonoidHom.coe_coe, MulEquiv.coe_mk, EquivLike.coe_coe, ContinuousAlgEquiv.coe_toAlgEquiv,
      NNReal.coe_toRealHom, coe_nnnorm, Rat.HeightOneSpectrum.adicCompletion.padicEquiv_norm_eq,
      FinitePlace.equivHeightOneSpectrum, Equiv.coe_fn_symm_mk, FinitePlace.mk_apply,
      MulEquiv.restrictedProductUnits, RestrictedProduct.inv_apply,
      Units.val_inv_eq_inv_val, MulEquiv.prodUnits, MulEquiv.coe_mk, Equiv.coe_fn_mk,
      MonoidHom.prod_apply, Units.coe_map, MonoidHom.coe_coe, MonoidHom.coe_snd, Units.coe_map_inv,
      RestrictedProduct.mk_apply]
    rw [AdeleRing.algebraMap_snd_apply, WithVal.equiv_symm_apply]
    rw [NumberField.FinitePlace.norm_embedding']
    simp  [FinitePlace.norm_def]

open scoped TensorProduct.RightActions in
/-- The continuous A-linear map (A a topological ring, tensor products have the module
topology) A ⊗[R] M ≃ A ⊗[R] N associated to an abstract R-linear isomorphism M ≃ N. -/
noncomputable def TensorProduct.RightActions.ContinuousLinearEquiv.baseChange (R : Type*)
    [CommRing R]
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
    TensorProduct.RightActions.ContinuousLinearEquiv.baseChange R A M N φ (m ⊗ₜ a) =
    (φ m) ⊗ₜ a := rfl

-- mathlib?
lemma LinearMap.toMatrix_basis {R : Type*} (A : Type*) {M : Type*} {ι j : Type*} [Fintype ι]
    [Finite j] [DecidableEq ι] [CommSemiring R] [CommSemiring A]
    [Algebra R A] [AddCommMonoid M] [Module R M] (b : Module.Basis ι R M)
    {N : Type*} [AddCommMonoid N] [Module R N] (c : Module.Basis j R N) (φ : M →ₗ[R] N) :
    LinearMap.toMatrix (Algebra.TensorProduct.basis A b) (Algebra.TensorProduct.basis A c)
      (φ.baseChange A) = (LinearMap.toMatrix b c φ).map (algebraMap R A) := by
  ext
  simp

open TensorProduct.RightActions in
lemma MeasureTheory.addHaarScalarFactor_tensor_adeles_rat_eq_one [Module ℚ V]
    [FiniteDimensional ℚ V] (φ : V ≃ₗ[ℚ] V)
    [MeasurableSpace (V ⊗[ℚ] 𝔸 ℚ)] [BorelSpace (V ⊗[ℚ] 𝔸 ℚ)] :
    addEquivAddHaarChar
      (ContinuousLinearEquiv.baseChange ℚ (𝔸 ℚ) V V φ).toContinuousAddEquiv = 1 := by
  -- need a basis
  let b := Module.finBasis ℚ V
  let b_extend := TensorProduct.RightActions.Algebra.TensorProduct.basis (𝔸 ℚ) b
  rw [MeasureTheory.addEquivAddHaarChar_eq_ringHaarChar_det_of_existsListTransvecEtc _ _ b_extend]
  · -- det of base change is base change of det
    have det_eq : (ContinuousLinearEquiv.baseChange ℚ (𝔸 ℚ) V V φ).toLinearEquiv.det =
        (φ.det).map (algebraMap ℚ (𝔸 ℚ)) := by
      ext
      simp [ContinuousLinearEquiv.baseChange, LinearMap.det_baseChange]
    rw [det_eq]
    exact MeasureTheory.ringHaarChar_adeles_units_rat_eq_one φ.det
  · have := Matrix.Pivot.baseChange_existsListTransvecEtc (LinearMap.toMatrix b b φ)
      (Matrix.Pivot.exists_list_transvec_mul_diagonal_mul_list_transvec' _) (AdeleRing (𝓞 ℚ) ℚ)
      (algebraMap _ _)
    simp only [TensorProduct.RightActions.Algebra.TensorProduct.basis,
      TensorProduct.RightActions.Module.TensorProduct.comm, b_extend, RingHom.mapMatrix_apply,
      ← LinearMap.toMatrix_basis, LinearMap.toMatrix_map_left, LinearMap.toMatrix_map_right]
        at this ⊢
    convert this
    ext
    simp

open scoped NumberField.AdeleRing in
open TensorProduct.RightActions in
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
  let f := NumberField.AdeleRing.ModuleBaseChangeContinuousLinearEquiv ℚ K V
  borelize (V ⊗[ℚ] AdeleRing (𝓞 ℚ) ℚ)
  -- and the obvious diagram commutes
  have := MeasureTheory.addEquivAddHaarChar_eq_addEquivAddHaarChar_of_continuousAddEquiv
    f.toContinuousAddEquiv
    (ContinuousLinearEquiv.baseChange ℚ (𝔸 ℚ) V V (φ.restrictScalars ℚ)).toContinuousAddEquiv
    (ContinuousLinearEquiv.baseChange K (𝔸 K) V V φ).toContinuousAddEquiv
  rw [← this]
  -- so the result follows from the case K=ℚ
  · apply MeasureTheory.addHaarScalarFactor_tensor_adeles_rat_eq_one
  · intro x
    induction x with
    | zero => simp
    | tmul x y => rfl
    | add x y hx hy => simp at hx hy; simp [hx, hy]

open TensorProduct.RightActions in
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

open TensorProduct.RightActions in
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
