import FLT.DedekindDomain.FiniteAdeleRing.BaseChange
import FLT.DedekindDomain.FiniteAdeleRing.TensorProduct
import FLT.HaarMeasure.HaarChar.FiniteDimensional
import FLT.Mathlib.Algebra.Central.TensorProduct
import FLT.Mathlib.MeasureTheory.Constructions.BorelSpace.AdicCompletion
import FLT.Mathlib.NumberTheory.NumberField.FiniteAdeleRing
import FLT.Mathlib.MeasureTheory.Constructions.BorelSpace.FiniteAdeleRing

/-!

# A result related to the Haar character of the finite adele ring of a number field

We prove the crucial result that left and right multiplication by an element of `D ⊗[K] 𝔸_K^f`
scale Haar measure by the same factor, if D is a finite-dimensional central simple `K`-alegbra.

The proof looks simple on paper. We know the analogous result for finite-dimensional
central simple algebras over local fields, but the proof essentially uses fields.
I had thought that the adelic case would follow easily from this and from the fact
that the haar character of a restricted product of maps was the product of the haar
characters, but `D ⊗[K] 𝔸_K^f` is not a restricted product, and furthermore making it
a restricted product is not completely formal because the compact open subrings 𝓞ᵥ
used in the restricted product are not `K`-modules. One could either choose a lattice
in D and work with that, or choose a basis of D and reduce first to to (𝔸_K^f)^n
and then to `Πʳ[Kᵥ^n,𝓞ᵥ^n]`, which is what we do.
-/

open NumberField

open scoped TensorProduct

variable (K : Type*) [Field K] [NumberField K]

variable (B : Type*) [Ring B] [Algebra K B] [FiniteDimensional K B]

open MeasureTheory IsDedekindDomain HeightOneSpectrum RestrictedProduct

/-- We give 𝔸_K^f ⊗ B the 𝔸_K^f-module topology in this file (it's the only sensible topology). -/
local instance : TopologicalSpace (FiniteAdeleRing (𝓞 K) K ⊗[K] B) :=
  moduleTopology (FiniteAdeleRing (𝓞 K) K) _

local instance : IsModuleTopology (FiniteAdeleRing (𝓞 K) K) (FiniteAdeleRing (𝓞 K) K ⊗[K] B) :=
  ⟨rfl⟩

local instance : IsTopologicalRing (FiniteAdeleRing (𝓞 K) K ⊗[K] B) :=
  IsModuleTopology.isTopologicalRing (FiniteAdeleRing (𝓞 K) K) _

local instance : LocallyCompactSpace (FiniteAdeleRing (𝓞 K) K ⊗[K] B) :=
  IsModuleTopology.locallyCompactSpaceOfFinite (FiniteAdeleRing (𝓞 K) K)

/-- We put the Borel measurable space structure on 𝔸_K^f ⊗ B (because it's the only
sensible one). -/
local instance : MeasurableSpace ((FiniteAdeleRing (𝓞 K) K) ⊗[K] B) := borel _

local instance : BorelSpace ((FiniteAdeleRing (𝓞 K) K) ⊗[K] B) := ⟨rfl⟩

section moving_from_tensor_B_to_Pi

/-- If `φ : 𝔸_K^f ⊗[K] B ≃ 𝔸_K^f ⊗[K] B` is continuous and 𝔸_K^f-linear then `f φ` is the
associated continuous linear isomorphism `(𝔸_K^f)^n ≃ (𝔸_K^f)^n` coming from the "canonical"
K-basis of B. -/
noncomputable def FiniteAdeleRing.Aux.f
    (φ : ((FiniteAdeleRing (𝓞 K) K) ⊗[K] B) ≃L[FiniteAdeleRing (𝓞 K) K]
      (FiniteAdeleRing (𝓞 K) K) ⊗[K] B) :
    (Module.Free.ChooseBasisIndex K B → (FiniteAdeleRing (𝓞 K) K)) ≃L[FiniteAdeleRing (𝓞 K) K]
    (Module.Free.ChooseBasisIndex K B → (FiniteAdeleRing (𝓞 K) K)) := by
  let b₀ := Module.Free.chooseBasis K B
  let b := Module.Basis.baseChange (FiniteAdeleRing (𝓞 K) K) b₀
  refine (ContinuousLinearEquiv.chooseBasis_piScalarRight' K
    (FiniteAdeleRing (𝓞 K) K) B).symm.trans ?_
  refine φ.trans ?_
  exact (ContinuousLinearEquiv.chooseBasis_piScalarRight' K (FiniteAdeleRing (𝓞 K) K) B)

lemma FiniteAdeleRing.Aux.f_commSq
    (φ : ((FiniteAdeleRing (𝓞 K) K) ⊗[K] B) ≃L[FiniteAdeleRing (𝓞 K) K]
      (FiniteAdeleRing (𝓞 K) K) ⊗[K] B) :
    addEquivAddHaarChar (φ.toContinuousAddEquiv) =
    addEquivAddHaarChar (FiniteAdeleRing.Aux.f K B φ).toContinuousAddEquiv := by
  refine MeasureTheory.addEquivAddHaarChar_eq_addEquivAddHaarChar_of_continuousAddEquiv
    (ContinuousLinearEquiv.chooseBasis_piScalarRight' K
      (FiniteAdeleRing (𝓞 K) K) B).toContinuousAddEquiv _ _ ?_
  intro x
  let g := (ContinuousLinearEquiv.chooseBasis_piScalarRight' K (FiniteAdeleRing (𝓞 K) K) B)
  change g (φ x) = g (φ (g.symm (g x)))
  simp

end moving_from_tensor_B_to_Pi

local instance {ι : Type*} [Finite ι] :
    Fact (∀ (v : HeightOneSpectrum (𝓞 K)), IsOpen
      (↑(AddSubgroup.pi (Set.univ : Set ι)
      (fun _ ↦ (v.adicCompletionIntegers K).toAddSubgroup)) :
    Set (ι → v.adicCompletion K))) := ⟨fun _ ↦
  isOpen_set_pi Set.finite_univ (fun _ _ ↦ isOpenAdicCompletionIntegers K _)⟩

local instance :
    Fact (∀ (v : HeightOneSpectrum (𝓞 K)), IsOpen
      (↑(v.adicCompletionIntegers K).toAddSubgroup :
    Set (v.adicCompletion K))) :=
  ⟨isOpenAdicCompletionIntegers K⟩

local instance (v : HeightOneSpectrum (𝓞 K)) :
    CompactSpace (AddSubgroup.pi (Set.univ : Set (Module.Free.ChooseBasisIndex K B))
      fun _ ↦ (adicCompletionIntegers K v).toAddSubgroup) := by
  change CompactSpace (Set.pi Set.univ fun x ↦ _)
  rw [← isCompact_iff_compactSpace]
  refine isCompact_univ_pi (fun i ↦ ?_)
  change IsCompact (v.adicCompletionIntegers K : Set (v.adicCompletion K))
  exact isCompactAdicCompletionIntegers K v

variable {ι : Type*} [Finite ι] in
local instance : LocallyCompactSpace
    Πʳ (v : HeightOneSpectrum (𝓞 K)), [ι → adicCompletion K v,
      (↑(AddSubgroup.pi (Set.univ : Set ι) fun _ ↦ (adicCompletionIntegers K v).toAddSubgroup) :
      Set ((ι → adicCompletion K v)))] := by
  refine RestrictedProduct.locallyCompactSpace_of_addGroup _ ?_
  filter_upwards
  intro v
  refine isCompact_univ_pi (fun i ↦ ?_)
  change IsCompact (v.adicCompletionIntegers K : Set (v.adicCompletion K))
  exact isCompactAdicCompletionIntegers K v

local instance : LocallyCompactSpace
    Πʳ (v : HeightOneSpectrum (𝓞 K)), [adicCompletion K v,
      ((adicCompletionIntegers K v).toAddSubgroup : Set (adicCompletion K v))] := by
  refine RestrictedProduct.locallyCompactSpace_of_addGroup _ ?_
  filter_upwards
  intro v
  change IsCompact (v.adicCompletionIntegers K : Set (v.adicCompletion K))
  exact isCompactAdicCompletionIntegers K v

local instance : SecondCountableTopology Πʳ (v : HeightOneSpectrum (𝓞 K)),
    [v.adicCompletion K, v.adicCompletionIntegers K] := inferInstanceAs <|
  SecondCountableTopology (FiniteAdeleRing (𝓞 K) K)

section moving_from_pi_restrictedproduct_to_restrictedproduct_pi

/-- If `ψ : (𝔸_K^f)^n ≃ (𝔸_K^f)^n` is continuous and 𝔸_K^f-linear then `g φ` is the
associated continuous additive isomorphism `Πʳ[Kᵥ^n, 𝓞ᵥ^n] → Πʳ[Kᵥ^n,𝓞ᵥ^n]`.
-/
noncomputable def FiniteAdeleRing.Aux.g {ι : Type*} [Fintype ι]
    (ψ : (ι → (FiniteAdeleRing (𝓞 K) K)) ≃L[FiniteAdeleRing (𝓞 K) K]
      (ι → (FiniteAdeleRing (𝓞 K) K))) :
    Πʳ (v : HeightOneSpectrum (𝓞 K)), [ι → v.adicCompletion K,
      (AddSubgroup.pi (Set.univ : Set ι) (fun _ ↦ (v.adicCompletionIntegers K).toAddSubgroup))] ≃ₜ+
    Πʳ (v : HeightOneSpectrum (𝓞 K)), [ι → v.adicCompletion K,
      (AddSubgroup.pi (Set.univ : Set ι) (fun _ ↦ (v.adicCompletionIntegers K).toAddSubgroup))] :=
  letI f := ContinuousAddEquiv.restrictedProductPi
    (C := fun (_ : ι) (v : HeightOneSpectrum (𝓞 K)) ↦ (v.adicCompletionIntegers K).toAddSubgroup)
    (fun _ v ↦ isOpenAdicCompletionIntegers K v)
  f.trans (ψ.toContinuousAddEquiv.trans f.symm)

lemma FiniteAdeleRing.Aux.g_commSq {ι : Type*} [Fintype ι]
    (ψ : (ι → (FiniteAdeleRing (𝓞 K) K)) ≃L[FiniteAdeleRing (𝓞 K) K]
      (ι → (FiniteAdeleRing (𝓞 K) K))) :
    addEquivAddHaarChar (ψ.toContinuousAddEquiv) =
    addEquivAddHaarChar (FiniteAdeleRing.Aux.g K ψ) := by
  symm
  let f := (ContinuousAddEquiv.restrictedProductPi
    (C := fun (i : ι) (v : HeightOneSpectrum (𝓞 K)) ↦
      (v.adicCompletionIntegers K).toAddSubgroup) (fun _ ↦ isOpenAdicCompletionIntegers K))
  refine MeasureTheory.addEquivAddHaarChar_eq_addEquivAddHaarChar_of_continuousAddEquiv f _ _ ?_
  intro x
  change f (f.symm (ψ (f x))) = ψ (f x)
  simp at f -- why??
  simp

end moving_from_pi_restrictedproduct_to_restrictedproduct_pi

/-- The only sensible topological space structure on Kᵥ ⊗ B. -/
local instance (v : HeightOneSpectrum (𝓞 K)) : TopologicalSpace (adicCompletion K v ⊗[K] B) :=
  moduleTopology (adicCompletion K v) _

local instance (v : HeightOneSpectrum (𝓞 K)) :
    IsModuleTopology (adicCompletion K v) (adicCompletion K v ⊗[K] B) :=
  ⟨rfl⟩

local instance (v : HeightOneSpectrum (𝓞 K)) :
    IsTopologicalAddGroup (adicCompletion K v ⊗[K] B) :=
  IsModuleTopology.topologicalAddGroup (adicCompletion K v) _

local instance (v : HeightOneSpectrum (𝓞 K)) :
    IsTopologicalRing (adicCompletion K v ⊗[K] B) :=
  IsModuleTopology.isTopologicalRing (adicCompletion K v) _

/-- If `φ : Kᵥ ⊗[K] B ≃ Kᵥ ⊗[K] B` is continuous and additive then `f φ` is the
associated continuous additive isomorphism `Kᵥ^n ≃ Kᵥ^n` coming from the "canonical"
K-basis of B. -/
noncomputable def FiniteAdeleRing.Aux.e (v : HeightOneSpectrum (𝓞 K))
    (α : v.adicCompletion K ⊗[K] B ≃L[K] v.adicCompletion K ⊗[K] B) :
    (Module.Free.ChooseBasisIndex K B → (v.adicCompletion K)) ≃ₜ+
    (Module.Free.ChooseBasisIndex K B → (v.adicCompletion K)) := by
  let b₀ := Module.Free.chooseBasis K B
  let b := Module.Basis.baseChange (v.adicCompletion K) b₀
  let β := (ContinuousLinearEquiv.chooseBasis_piScalarRight' K
    (v.adicCompletion K) B).toContinuousAddEquiv
  refine β.symm.trans ?_
  refine α.toContinuousAddEquiv.trans ?_
  exact β

/-- The only sensible measurable space structure on Kᵥ ⊗ B. -/
local instance (v : HeightOneSpectrum (𝓞 K)) :
  MeasurableSpace (adicCompletion K v ⊗[K] B) := borel _

local instance (v : HeightOneSpectrum (𝓞 K)) :
  BorelSpace (adicCompletion K v ⊗[K] B) := ⟨rfl⟩

local instance (v : HeightOneSpectrum (𝓞 K)) :
    LocallyCompactSpace (adicCompletion K v ⊗[K] B) :=
  IsModuleTopology.locallyCompactSpaceOfFinite (adicCompletion K v)

lemma FiniteAdeleRing.Aux.e_commSq (v : HeightOneSpectrum (𝓞 K))
    (α : v.adicCompletion K ⊗[K] B ≃L[K] v.adicCompletion K ⊗[K] B) :
    addEquivAddHaarChar (α.toContinuousAddEquiv) =
    addEquivAddHaarChar (FiniteAdeleRing.Aux.e K B v α) := by
  refine MeasureTheory.addEquivAddHaarChar_eq_addEquivAddHaarChar_of_continuousAddEquiv
    (ContinuousLinearEquiv.chooseBasis_piScalarRight' K
      (v.adicCompletion K) B).toContinuousAddEquiv _ _ ?_
  intro x
  let g := (ContinuousLinearEquiv.chooseBasis_piScalarRight' K (v.adicCompletion K) B)
  change g (α x) = g (α (g.symm (g x)))
  simp

open FiniteAdeleRing.Aux

/-- Needed in some argument below; there will never be a constructive one in this
generality so no harm in making it classical. -/
noncomputable local instance : DecidableEq (HeightOneSpectrum (𝓞 K)) := Classical.decEq _

section auxiliary_basis_lemmas

/- API for relating `ContinuousLinearEquiv.chooseBasis_piScalarRight'` to `Module.Basis`.
TODO: Could all probably be elsewhere and in greater generality. -/

/-- `b_local` is `v.adicCompletion K`-basis for `v.adicCompletion K ⊗[K] B`. -/
noncomputable abbrev b_local (v : HeightOneSpectrum (𝓞 K)) :=
  Module.Basis.baseChange (v.adicCompletion K) (Module.Free.chooseBasis K B)

/-- `b_global` is `FiniteAdeleRing (𝓞 K) K`-basis for `FiniteAdeleRing (𝓞 K) K ⊗[K] B`. -/
noncomputable abbrev b_global :=
  Module.Basis.baseChange (FiniteAdeleRing (𝓞 K) K) (Module.Free.chooseBasis K B)

lemma basis_repr_eq (v : HeightOneSpectrum (𝓞 K)) {x : adicCompletion K v ⊗[K] B} :
    (b_local K B v).repr x
    = (ContinuousLinearEquiv.chooseBasis_piScalarRight' K (v.adicCompletion K) B) x := by
  refine TensorProduct.induction_on x (by simp) (fun _ _ ↦ ?_) (fun _ _ ↦ by simp +contextual)
  ext; simp; rfl

lemma basis_repr_eq_global {x : (FiniteAdeleRing (𝓞 K) K) ⊗[K] B} :
    (b_global K B).repr x
    = (ContinuousLinearEquiv.chooseBasis_piScalarRight' K (FiniteAdeleRing (𝓞 K) K) B) x := by
  refine TensorProduct.induction_on x (by simp) (fun _ _ ↦ ?_) (fun _ _ ↦ by simp +contextual)
  ext; simp; rfl

lemma basis_eq_single (v : HeightOneSpectrum (𝓞 K))
    {j : Module.Free.ChooseBasisIndex K B} {x : adicCompletion K v} :
    x • (b_local K B v) j
    = (ContinuousLinearEquiv.chooseBasis_piScalarRight'
      K (v.adicCompletion K) B).symm (Pi.single j x) := by
  rw [ContinuousLinearEquiv.eq_symm_apply];
  ext b;
  have : (x • (b_local K B v) j) = (x ⊗ₜ[K] (Module.Free.chooseBasis K B) j) := by
    simp [Algebra.smul_def]
  rw [this]
  conv_lhs =>
    change ((Module.Free.chooseBasis K B).repr ((Module.Free.chooseBasis K B) j)) b • x
  simp [Finsupp.single, Pi.single, Algebra.smul_def, Function.update]

lemma basis_eq (v : HeightOneSpectrum (𝓞 K))
    {w : Module.Free.ChooseBasisIndex K B → adicCompletion K v} :
    ∑ (j : Module.Free.ChooseBasisIndex K B), (w j) • (b_local K B v) j
    = (ContinuousLinearEquiv.chooseBasis_piScalarRight'
      K (v.adicCompletion K) B).toContinuousAddEquiv.symm w := by
  have hw : w = ∑ x, (Pi.single x (w x)) := by
    ext; simp
  conv_rhs => rw [hw]
  simp only [basis_eq_single K B v, map_sum]; rfl

lemma basis_eq_single_global
    {j : Module.Free.ChooseBasisIndex K B} {x : FiniteAdeleRing (𝓞 K) K} :
    x • (b_global K B) j
    = (ContinuousLinearEquiv.chooseBasis_piScalarRight'
      K (FiniteAdeleRing (𝓞 K) K) B).symm (Pi.single j x) := by
  rw [ContinuousLinearEquiv.eq_symm_apply];
  ext b v;
  have : (x • (b_global K B) j) = (x ⊗ₜ[K] (Module.Free.chooseBasis K B) j) := by
    simp [Algebra.smul_def]
  rw [this]
  conv_lhs =>
    change (((Module.Free.chooseBasis K B).repr ((Module.Free.chooseBasis K B) j)) b • x) v
  simp [Finsupp.single, Pi.single, Algebra.smul_def, Function.update]

lemma basis_eq_global
    {w : Module.Free.ChooseBasisIndex K B → (FiniteAdeleRing (𝓞 K) K)} :
    ∑ (j : Module.Free.ChooseBasisIndex K B), (w j) • b_global K B j
    = (ContinuousLinearEquiv.chooseBasis_piScalarRight'
      K (FiniteAdeleRing (𝓞 K) K) B).toContinuousAddEquiv.symm w := by
  have hw : w = ∑ x, (Pi.single x (w x)) := by
    ext; simp
  conv_rhs => rw [hw]
  simp only [basis_eq_single_global K B, map_sum]; rfl

end auxiliary_basis_lemmas

-- this should really be just after the definition of `localcomponent`
/-- `TensorProduct.localcomponent φ` as `v.adicCompletion K`-linear map -/
noncomputable def φ_local_Kv_linear (v : HeightOneSpectrum (𝓞 K))
    (φ : FiniteAdeleRing (𝓞 K) K ⊗[K] B ≃L[FiniteAdeleRing (𝓞 K) K]
    FiniteAdeleRing (𝓞 K) K ⊗[K] B) :
    v.adicCompletion K ⊗[K] B →ₗ[v.adicCompletion K] v.adicCompletion K ⊗[K] B := {
  __ := (FiniteAdeleRing.TensorProduct.localcomponentEquiv (𝓞 K) K B v φ)
  map_smul' kv x := by
    -- rewrite so topology-free
    change AlgHom.rTensor B (FiniteAdeleRing.evalAlgebraMap (𝓞 K) K v)
      (φ (LinearMap.rTensor B (FiniteAdeleRing.singleLinearMap (𝓞 K) K v) (kv • x))) =
      kv • (AlgHom.rTensor B (FiniteAdeleRing.evalAlgebraMap (𝓞 K) K v)
      (φ (LinearMap.rTensor B (FiniteAdeleRing.singleLinearMap (𝓞 K) K v) x)))
    induction x with
    | zero => simp only [AlgHom.toRingHom_eq_coe, smul_zero, map_zero]
    | tmul x y =>
      -- need to slowly move the `kv •` out on the LHS
      rw [LinearMap.rTensor_tmul, TensorProduct.smul_tmul',
        LinearMap.rTensor_tmul, smul_eq_mul]
      -- 1/3 of the way there
      -- we needed `single` to be linear, but now we need it to be a MulHom
      conv =>
        enter [1, 2, 2, 2]
        change FiniteAdeleRing.singleMulHom _ _ _ _
        rw [map_mul, ← smul_eq_mul]
      -- 2/3 of the way there
      rw [← TensorProduct.smul_tmul', map_smul, AlgHom.rTensor_map_smul]
      -- out, but now in the form (single (eval kv) •)
      congr
      -- but we know this is kv
      exact FiniteAdeleRing.evalContinuousAlgebraMap_singleContinuousLinearMap (𝓞 K) K v kv
    | add x y _ _ => simp_all only [AlgHom.toRingHom_eq_coe, smul_add, map_add]
}

lemma localcomponent_matrix (v : HeightOneSpectrum (𝓞 K))
    (φ : FiniteAdeleRing (𝓞 K) K ⊗[K] B ≃L[FiniteAdeleRing (𝓞 K) K]
      FiniteAdeleRing (𝓞 K) K ⊗[K] B)
    (i j : Module.Free.ChooseBasisIndex K B) :
    letI b₀ := Module.Free.chooseBasis K B
    letI b := Module.Basis.baseChange (FiniteAdeleRing (𝓞 K) K) b₀
    letI b_local := Module.Basis.baseChange (v.adicCompletion K) b₀
    (LinearMap.toMatrix b_local b_local) (φ_local_Kv_linear K B v φ) i j =
    (LinearMap.toMatrix b b φ.toLinearMap i j) v := by
  letI b₀ := Module.Free.chooseBasis K B
  letI b := Module.Basis.baseChange (FiniteAdeleRing (𝓞 K) K) b₀
  letI b_local := Module.Basis.baseChange (v.adicCompletion K) b₀
  change (LinearMap.toMatrix b_local b_local) (φ_local_Kv_linear K B v φ) i j =
    RingHom.mapMatrix
      (evalRingHom (fun (p : HeightOneSpectrum (𝓞 K)) ↦ p.adicCompletion K) v)
      (LinearMap.toMatrix b b φ.toLinearMap) i j
  -- get rid of i,j
  apply congr_fun
  apply congr_fun
  -- move LinearMap.toMatrix onto the other side of the equation
  rw [RingHom.mapMatrix_apply (evalRingHom (fun p ↦ adicCompletion K p) v)
      ((LinearMap.toMatrix b b) ↑φ.toLinearEquiv)]
  apply_fun (Matrix.toLin b_local b_local) using (Matrix.toLin b_local b_local).injective
  rw [Matrix.toLin_toMatrix]
  -- This is now an equality of linear maps Kᵥ ⊗[K] B → Kᵥ ⊗[K] B
  ext r -- r ∈ B
  -- now get rid of `φ_local_Kv_linear`
  change AlgHom.rTensor B (FiniteAdeleRing.evalAlgebraMap (𝓞 K) K v)
    (φ (LinearMap.rTensor B (FiniteAdeleRing.singleLinearMap (𝓞 K) K v) (1 ⊗ₜ r))) =
  ((Matrix.toLin b_local b_local)
    (((LinearMap.toMatrix b b) ↑φ.toLinearEquiv).map ⇑(evalRingHom (fun p ↦ adicCompletion K p) v)))
    (1 ⊗ₜ[K] r)
  rw [LinearMap.rTensor_tmul]
  conv =>
    enter [1, 2, 2, 2]
    rw [← mul_one ((FiniteAdeleRing.singleLinearMap (𝓞 K) K v) 1)]
  rw [← smul_eq_mul, ← TensorProduct.smul_tmul', map_smul, AlgHom.rTensor_map_smul]
  rw [FiniteAdeleRing.evalAlgebraMap_singleLinearMap, one_smul]
  conv_lhs =>
    change (AlgHom.rTensor B (FiniteAdeleRing.evalAlgebraMap (𝓞 K) K v))
      (φ.toLinearEquiv.toLinearMap (1 ⊗ₜ[K] r))
    rw [← Matrix.toLin_toMatrix b b φ.toLinearEquiv]
  have rTensor_basis (j : Module.Free.ChooseBasisIndex K B) :
      (AlgHom.rTensor B (FiniteAdeleRing.evalAlgebraMap (𝓞 K) K v)) (b j)
      = b_local j := by
    simp [AlgHom.rTensor, b, b_local]
  have eval_mulVec_eq (j : Module.Free.ChooseBasisIndex K B) :
      (FiniteAdeleRing.evalAlgebraMap (𝓞 K) K v)
          (((LinearMap.toMatrix b b) ↑φ.toLinearEquiv).mulVec (⇑(b.repr (1 ⊗ₜ[K] r))) j)
      =
      (((LinearMap.toMatrix b b) ↑φ.toLinearEquiv).map
        ⇑(evalRingHom (fun p ↦ adicCompletion K p) v)).mulVec
          (⇑(b_local.repr (1 ⊗ₜ[K] r))) j := by
    set m := ((LinearMap.toMatrix b b) ↑φ.toLinearEquiv)
    convert RingHom.map_mulVec (evalRingHom (fun p ↦ adicCompletion K p) v) m _ j
    ext i
    simp [b, b_local, evalRingHom, evalMonoidHom, Algebra.smul_def]
    rfl
  simp [-Matrix.toLin_toMatrix, Matrix.toLin_apply, rTensor_basis, eval_mulVec_eq]
  /-

  localcomponent stuff and `single` (an annoying linear map) now gone.

  goal is

  ⊢ (AlgHom.rTensor B (FiniteAdeleRing.evalAlgebraMap (𝓞 K) K v)) (φ (1 ⊗ₜ[K] r)) =
  ((Matrix.toLin b_local b_local)
      (((LinearMap.toMatrix b b) ↑φ.toLinearEquiv).map
        ⇑(evalRingHom (fun p ↦ adicCompletion K p) v)))
    (1 ⊗ₜ[K] r)

  Breakdown of goal: we have φ an 𝔸_K^f-linear endomorphism of 𝔸_K^f ⊗ B, and we have r ∈ B.

  LHS is (evalᵥ ⊗ id_B : 𝔸_K^f ⊗ B → Kᵥ ⊗ B) evaluated at φ (1_𝔸 ⊗ₜ r) (a random tensor and
    not a pure tensor in general)

  RHS is: take φ as a linear map, make its matrix wrt basis b, apply evalᵥ,
  turn it back into a linear map wrt b_local (which is (evalᵥ ⊗ id_B) b, although we don't have
  a proof of this) and then evaluate at (1ᵥ ⊗ₜ[K] r) (which is (evalᵥ ⊗ id_B) (1_𝔸 ⊗ₜ r)

  so there should be some general statement here from which this follows?

  I'm not entirely sure of the best way to say that b_local is evalᵥ ⊗ id_B of b

  Could just break everything up into sums? Tried this and got confused.
  -/

/-- The matrix reps of `φ` and `f φ` agree. -/
lemma toMatrix_f
    (φ : FiniteAdeleRing (𝓞 K) K ⊗[K] B ≃L[FiniteAdeleRing (𝓞 K) K]
      FiniteAdeleRing (𝓞 K) K ⊗[K] B) :
    LinearMap.toMatrix (b_global K B) (b_global K B) φ.toLinearEquiv
    = LinearMap.toMatrix' (f K B φ) := by
  have basis_eq_global'
      {w : Module.Free.ChooseBasisIndex K B → (FiniteAdeleRing (𝓞 K) K)} :
      ∑ (j : Module.Free.ChooseBasisIndex K B), (w j) • b_global K B j
      = (ContinuousLinearEquiv.chooseBasis_piScalarRight'
        K (FiniteAdeleRing (𝓞 K) K) B).symm w :=
    basis_eq_global K B
  ext
  simp [f, ← basis_repr_eq_global K B,
    ← basis_eq_global', LinearMap.toMatrix_apply]

-- A (continuous) 𝔸_K^f-linear automorphism of 𝔸_K^f ⊗ B is "integral" at all but
-- finitely many places
lemma FiniteAdeleRing.Aux.almost_always_mapsTo
    (φ : FiniteAdeleRing (𝓞 K) K ⊗[K] B ≃L[FiniteAdeleRing (𝓞 K) K]
    FiniteAdeleRing (𝓞 K) K ⊗[K] B) :
    letI ι := Module.Free.ChooseBasisIndex K B
    ∀ᶠ (i : HeightOneSpectrum (𝓞 K)) in Filter.cofinite,
      Set.MapsTo ⇑((fun v ↦ e K B v
        (FiniteAdeleRing.TensorProduct.localcomponentEquiv (𝓞 K) K B v φ)) i)
      ↑(AddSubgroup.pi (Set.univ : Set ι) fun _ ↦ (adicCompletionIntegers K i).toAddSubgroup)
      ↑(AddSubgroup.pi (Set.univ : Set ι) fun _ ↦ (adicCompletionIntegers K i).toAddSubgroup) := by
  let b₀ := Module.Free.chooseBasis K B
  let b := Module.Basis.baseChange (FiniteAdeleRing (𝓞 K) K) b₀
  let m := LinearMap.toMatrix b b φ.toLinearMap
  have := fun i j ↦ (m i j).2
  simp_rw [← Filter.eventually_all] at this
  filter_upwards [this]
  intro v hv w (hw : w ∈ Set.pi _ _) j _
  rw [Set.mem_univ_pi] at hw
  -- hopefully true :-)
  -- Idea: φ is represented by a matrix M, and the claim is that for a finite place v
  -- at which the matrix is v-integral, the local component of φ
  -- should preserve integrality.
  let b_local := Module.Basis.baseChange (v.adicCompletion K) b₀
  -- `b_local` is `v.adicCompletion K`-basis for `v.adicCompletion K ⊗[K] B`
  have basis_repr_eq' {x : adicCompletion K v ⊗[K] B} :
      b_local.repr x
      = (ContinuousLinearEquiv.chooseBasis_piScalarRight' K (v.adicCompletion K) B) x :=
    basis_repr_eq K B v
  have local_repr_eq (i j : Module.Free.ChooseBasisIndex K B) :
      ((b_local.repr (φ_local_Kv_linear K B v φ (b_local j))) i) = (m i j) v := by
    rw [← LinearMap.toMatrix_apply, localcomponent_matrix]
  -- simp [e, ← basis_eq K B v]
  simp only [e, ← basis_eq K B v,
    ContinuousAddEquiv.trans_apply, map_sum, Finset.sum_apply] --argh!
  change ∑ c,
    (ContinuousLinearEquiv.chooseBasis_piScalarRight' K (adicCompletion K v) B)
    (φ_local_Kv_linear K B v φ (w c • b_local c)) j
    ∈ adicCompletionIntegers K v
  simpa [← basis_repr_eq', local_repr_eq] using sum_mem fun i hi ↦ mul_mem (hw i) (hv j i)

-- A (continuous) 𝔸_K^f-linear automorphism of 𝔸_K^f ⊗ B is "integral" at all but
-- finitely many places
lemma FiniteAdeleRing.Aux.almost_always_bijOn
    (φ : FiniteAdeleRing (𝓞 K) K ⊗[K] B ≃L[FiniteAdeleRing (𝓞 K) K]
    FiniteAdeleRing (𝓞 K) K ⊗[K] B) :
    letI ι := Module.Free.ChooseBasisIndex K B
    ∀ᶠ (i : HeightOneSpectrum (𝓞 K)) in Filter.cofinite,
      Set.BijOn ⇑((fun v ↦ e K B v
        (FiniteAdeleRing.TensorProduct.localcomponentEquiv (𝓞 K) K B v φ)) i)
      ↑(AddSubgroup.pi (Set.univ : Set ι) fun _ ↦ (adicCompletionIntegers K i).toAddSubgroup)
      ↑(AddSubgroup.pi (Set.univ : Set ι) fun _ ↦ (adicCompletionIntegers K i).toAddSubgroup) := by
  have h1 := FiniteAdeleRing.Aux.almost_always_mapsTo K B φ
  have h2 := FiniteAdeleRing.Aux.almost_always_mapsTo K B φ.symm
  filter_upwards [h1, h2]
  intro v h1 h2
  exact (e K B v (FiniteAdeleRing.TensorProduct.localcomponentEquiv (𝓞 K) K B v φ)).bijOn' h1 h2

/-- A diagram which obviously commutes, commutes. -/
lemma FiniteAdeleRing.Aux.f_g_local_global
    (φ : ((FiniteAdeleRing (𝓞 K) K) ⊗[K] B) ≃L[FiniteAdeleRing (𝓞 K) K]
      (FiniteAdeleRing (𝓞 K) K) ⊗[K] B) :
    g K (f K B φ) = ContinuousAddEquiv.restrictedProductCongrRight
    (fun v ↦ e _ _ _ (FiniteAdeleRing.TensorProduct.localcomponentEquiv (𝓞 K) K B v φ))
    (FiniteAdeleRing.Aux.almost_always_bijOn _ _ _) := by
  ext r v j;
  letI b₀ := Module.Free.chooseBasis K B
  letI b := Module.Basis.baseChange (FiniteAdeleRing (𝓞 K) K) b₀
  letI b_local := Module.Basis.baseChange (v.adicCompletion K) b₀
  let m := LinearMap.toMatrix b b φ.toLinearMap
  simp only [ContinuousAddEquiv.restrictedProductCongrRight, e, ← basis_eq K B v,
    ContinuousAddEquiv.coe_trans, ContinuousAddEquiv.coe_mk, AddEquiv.coe_mk, Equiv.coe_fn_mk,
    map_apply, Function.comp_apply, map_sum, Finset.sum_apply]
  conv_rhs =>
    change ∑ c,
      (ContinuousLinearEquiv.chooseBasis_piScalarRight' K (adicCompletion K v) B)
      (φ_local_Kv_linear K B v φ (r v c • b_local c)) j
  have basis_repr_eq' {x : adicCompletion K v ⊗[K] B} :
      b_local.repr x
      = (ContinuousLinearEquiv.chooseBasis_piScalarRight' K (v.adicCompletion K) B) x :=
    basis_repr_eq K B v
  have local_repr_eq (i j : Module.Free.ChooseBasisIndex K B) :
      ((b_local.repr (φ_local_Kv_linear K B v φ (b_local j))) i) = (m i j) v := by
    rw [← LinearMap.toMatrix_apply, localcomponent_matrix]
  have hf : m = LinearMap.toMatrix' (f K B φ) := toMatrix_f K B φ
  simp only [ ← basis_repr_eq', local_repr_eq, m, hf, g,
    ContinuousAddEquiv.trans_apply, map_smul, Finsupp.coe_smul, Pi.smul_apply]
  -- Up to here, what we have done is to simplify the RHS `e (localcomponent φ)` in terms of
  -- the matrix rep of `φ`, which is the same as the matrix rep of `f φ` by `toMatrix_f` above.
  -- What remains is to simplify `g`, i.e. to simplify `ContinuousAddEquiv.restrictedProductPi`.
  set ψ := f K B φ
  conv_lhs =>
    change (ψ.toLinearEquiv.toLinearMap (fun j ↦ map (fun i t ↦ t j)
      (Filter.Eventually.of_forall (fun _ _ _ ↦ by simp_all [AddSubgroup.mem_pi])) r) j) v
    rw [← Matrix.toLin'_toMatrix' ψ.toLinearEquiv.toLinearMap]
  have {f : Module.Free.ChooseBasisIndex K B → FiniteAdeleRing (𝓞 K) K} :
      (∑ x, f x) v = ∑ x, f x v :=
    -- general lemma
    map_sum (RestrictedProduct.evalAddMonoidHom _ _) _ _
  simp [-Matrix.toLin'_toMatrix', Matrix.mulVec, dotProduct, this, FiniteAdeleRing,
    mul_comm (r v _) _]

lemma localcomponent_mulLeft (u : ((FiniteAdeleRing (𝓞 K) K) ⊗[K] B)ˣ)
    (v : HeightOneSpectrum (𝓞 K)) :
    (FiniteAdeleRing.TensorProduct.localcomponentEquiv (𝓞 K) K B v
    (ContinuousLinearEquiv.mulLeft (FiniteAdeleRing (𝓞 K) K) u)).toContinuousAddEquiv =
    (ContinuousAddEquiv.mulLeft (u.map (Algebra.TensorProduct.rTensor B
      (IsDedekindDomain.FiniteAdeleRing.evalContinuousAlgebraMap
        (𝓞 K) K v).toAlgHom).toMonoidHom)) := by
  ext u'
  have keyFin := FiniteAdeleRing.TensorProduct.localcomponent_apply (𝓞 K) K B
      (ContinuousLinearEquiv.mulLeft (FiniteAdeleRing (𝓞 K) K) u)
        (TensorProduct.map (FiniteAdeleRing.singleContinuousLinearMap (𝓞 K) K v) .id u') v
  have : (FiniteAdeleRing.evalContinuousAlgebraMap (𝓞 K) K v).toContinuousLinearMap.toLinearMap ∘ₗ
      FiniteAdeleRing.singleContinuousLinearMap (𝓞 K) K v = .id := by
    ext
    simp [FiniteAdeleRing.evalContinuousAlgebraMap_singleContinuousLinearMap]
  have : u' =
      (FiniteAdeleRing.evalContinuousAlgebraMap (𝓞 K) K v).toContinuousLinearMap.rTensor B
      ((TensorProduct.map (FiniteAdeleRing.singleContinuousLinearMap (𝓞 K) K v) .id) u') := by
    rw [ContinuousLinearMap.rTensor, ContinuousLinearMap.coe_mk', LinearMap.rTensor_map, this,
      TensorProduct.map_id, LinearMap.id_apply]
  convert keyFin.symm
  change _ = Algebra.TensorProduct.rTensor B _ _
  simp [ContinuousLinearEquiv.mulLeft, LinearEquiv.mulLeft, map_mul]
  congr

lemma localcomponent_mulRight (u : ((FiniteAdeleRing (𝓞 K) K) ⊗[K] B)ˣ)
    (v : HeightOneSpectrum (𝓞 K)) :
    (FiniteAdeleRing.TensorProduct.localcomponentEquiv (𝓞 K) K B v
    (ContinuousLinearEquiv.mulRight (FiniteAdeleRing (𝓞 K) K) u)).toContinuousAddEquiv =
    (ContinuousAddEquiv.mulRight (u.map (Algebra.TensorProduct.rTensor B
      (IsDedekindDomain.FiniteAdeleRing.evalContinuousAlgebraMap
        (𝓞 K) K v).toAlgHom).toMonoidHom)) := by
  ext u'
  have keyFin := FiniteAdeleRing.TensorProduct.localcomponent_apply (𝓞 K) K B
      (ContinuousLinearEquiv.mulRight (FiniteAdeleRing (𝓞 K) K) u)
        (TensorProduct.map (FiniteAdeleRing.singleContinuousLinearMap (𝓞 K) K v) .id u') v
  have : (FiniteAdeleRing.evalContinuousAlgebraMap (𝓞 K) K v).toContinuousLinearMap.toLinearMap ∘ₗ
      FiniteAdeleRing.singleContinuousLinearMap (𝓞 K) K v = .id := by
    ext
    simp [FiniteAdeleRing.evalContinuousAlgebraMap_singleContinuousLinearMap]
  have : u' =
      (FiniteAdeleRing.evalContinuousAlgebraMap (𝓞 K) K v).toContinuousLinearMap.rTensor B
      ((TensorProduct.map (FiniteAdeleRing.singleContinuousLinearMap (𝓞 K) K v) .id) u') := by
    rw [ContinuousLinearMap.rTensor, ContinuousLinearMap.coe_mk', LinearMap.rTensor_map, this,
      TensorProduct.map_id, LinearMap.id_apply]
  convert keyFin.symm
  change _ = Algebra.TensorProduct.rTensor B _ _
  simp [ContinuousLinearEquiv.mulRight, LinearEquiv.mulRight, map_mul]
  congr

/-- left multiplication and right multiplication by a unit have the same Haar character
on `𝔸_K^f ⊗ B`. See also
`NumberField.FiniteAdeleRing.isCentralSimple_addHaarScalarFactor_left_mul_eq_right_mul`
which proves it for `B ⊗ 𝔸_K^f`.
-/
lemma NumberField.FiniteAdeleRing.tensor_isCentralSimple_addHaarScalarFactor_left_mul_eq_right_mul
    [IsSimpleRing B] [Algebra.IsCentral K B] (u : ((FiniteAdeleRing (𝓞 K) K) ⊗[K] B)ˣ) :
    addEquivAddHaarChar (ContinuousAddEquiv.mulLeft u) =
    addEquivAddHaarChar (ContinuousAddEquiv.mulRight u) := by
  change addEquivAddHaarChar
      (ContinuousLinearEquiv.mulLeft ((FiniteAdeleRing (𝓞 K) K)) u).toContinuousAddEquiv =
    addEquivAddHaarChar
      (ContinuousLinearEquiv.mulRight ((FiniteAdeleRing (𝓞 K) K)) u).toContinuousAddEquiv
  rw [FiniteAdeleRing.Aux.f_commSq, FiniteAdeleRing.Aux.f_commSq]
  rw [FiniteAdeleRing.Aux.g_commSq, FiniteAdeleRing.Aux.g_commSq]
  rw [FiniteAdeleRing.Aux.f_g_local_global, FiniteAdeleRing.Aux.f_g_local_global]
  rw [addEquivAddHaarChar_restrictedProductCongrRight,
    addEquivAddHaarChar_restrictedProductCongrRight]
  congr
  ext v
  rw [← FiniteAdeleRing.Aux.e_commSq, ← FiniteAdeleRing.Aux.e_commSq]
  rw [localcomponent_mulLeft, localcomponent_mulRight]
  congr 1
  let w : (adicCompletion K v ⊗[K] B)ˣ := ((Units.map (Algebra.TensorProduct.rTensor B
    (FiniteAdeleRing.evalContinuousAlgebraMap (𝓞 K) K v).toAlgHom).toMonoidHom) u)
  exact IsSimpleRing.ringHaarChar_eq_addEquivAddHaarChar_mulRight (F := v.adicCompletion K) w

/-!

We've proved the result for 𝔸 ⊗ B, we now deduce it for B ⊗ 𝔸

-/
open scoped TensorProduct.RightActions in
instance (k A B : Type*) [Field k] [Field A] [Ring B]
    [Algebra k A] [Algebra k B]
    [Algebra.IsCentral k B] :
    Algebra.IsCentral A (B ⊗[k] A) :=
  Algebra.IsCentral.of_algEquiv _ _ _ {
    __ := (Algebra.TensorProduct.comm k A B)
    commutes' := by simp }

open scoped TensorProduct.RightActions in
/-- B ⊗ 𝔸_K^f ≃ 𝔸_K^f ⊗ B as 𝔸_K^f-modules. -/
noncomputable def FiniteAdeleRing.TensorProduct.commLinearMap :
    (B ⊗[K] (FiniteAdeleRing (𝓞 K) K)) ≃ₗ[FiniteAdeleRing (𝓞 K) K]
    (FiniteAdeleRing (𝓞 K) K) ⊗[K] B := {
  __ := TensorProduct.comm K B (FiniteAdeleRing (𝓞 K) K)
  map_smul' _ _ := (TensorProduct.comm K B (FiniteAdeleRing (𝓞 K) K)).apply_symm_apply _
  }

open scoped TensorProduct.RightActions in
/-- B ⊗ 𝔸_K^f ≃ 𝔸_K^f ⊗ B as topological additive groups. -/
noncomputable def FiniteAdeleRing.TensorProduct.commContinuousAddMonoidHom :
    (B ⊗[K] (FiniteAdeleRing (𝓞 K) K)) ≃ₜ+
    (FiniteAdeleRing (𝓞 K) K) ⊗[K] B := {
  __ := FiniteAdeleRing.TensorProduct.commLinearMap K B
  continuous_toFun := IsModuleTopology.continuous_of_linearMap _
  continuous_invFun := IsModuleTopology.continuous_of_linearMap
    (FiniteAdeleRing.TensorProduct.commLinearMap K B).symm.toLinearMap
  }

open IsDedekindDomain HeightOneSpectrum RestrictedProduct in
open scoped TensorProduct.RightActions in
variable
  [MeasurableSpace (B ⊗[K] (FiniteAdeleRing (𝓞 K) K))]
  [BorelSpace (B ⊗[K] (FiniteAdeleRing (𝓞 K) K))] in
/-- left multiplication and right multiplication by a unit have the same Haar character
on `B ⊗ 𝔸_K^f`. See also
`NumberField.FiniteAdeleRing.tensor_isCentralSimple_addHaarScalarFactor_left_mul_eq_right_mul`
which proves it for `𝔸_K^f ⊗ B`.
-/
lemma NumberField.FiniteAdeleRing.isCentralSimple_addHaarScalarFactor_left_mul_eq_right_mul
    [IsSimpleRing B] [Algebra.IsCentral K B] (u : (B ⊗[K] (FiniteAdeleRing (𝓞 K) K))ˣ) :
    addEquivAddHaarChar (ContinuousAddEquiv.mulLeft u) =
    addEquivAddHaarChar (ContinuousAddEquiv.mulRight u) := by
  let v : ((FiniteAdeleRing (𝓞 K) K) ⊗[K] B)ˣ:=
    u.map (Algebra.TensorProduct.comm K B (FiniteAdeleRing (𝓞 K) K))
  have := MeasureTheory.addEquivAddHaarChar_eq_addEquivAddHaarChar_of_continuousAddEquiv
      (FiniteAdeleRing.TensorProduct.commContinuousAddMonoidHom K B)
      (ContinuousAddEquiv.mulLeft u)
      (ContinuousAddEquiv.mulLeft v) <| fun _ ↦
    map_mul (Algebra.TensorProduct.comm K B (FiniteAdeleRing (𝓞 K) K)) _ _
  rw [this]
  have := MeasureTheory.addEquivAddHaarChar_eq_addEquivAddHaarChar_of_continuousAddEquiv
      (FiniteAdeleRing.TensorProduct.commContinuousAddMonoidHom K B)
      (ContinuousAddEquiv.mulRight u)
      (ContinuousAddEquiv.mulRight v) <| fun _ ↦
    map_mul (Algebra.TensorProduct.comm K B (FiniteAdeleRing (𝓞 K) K)) _ _
  rw [this]
  apply NumberField.FiniteAdeleRing.tensor_isCentralSimple_addHaarScalarFactor_left_mul_eq_right_mul
