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

-- this horrible instance causes timeouts and we don't need it because we're never
-- changing number field here.
attribute [-instance] instIsScalarTowerFiniteAdeleRing_fLT_1

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

local instance {ι : Type*} [Fintype ι] :
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
      fun x ↦ (adicCompletionIntegers K v).toAddSubgroup) := by
  change CompactSpace (Set.pi Set.univ fun x ↦ _)
  rw [← isCompact_iff_compactSpace]
  refine isCompact_univ_pi (fun i ↦ ?_)
  change IsCompact (v.adicCompletionIntegers K : Set (v.adicCompletion K))
  sorry -- "integers are compact"

variable {ι : Type*} [Fintype ι] in
local instance : LocallyCompactSpace
    Πʳ (v : HeightOneSpectrum (𝓞 K)), [ι → adicCompletion K v,
      (↑(AddSubgroup.pi (Set.univ : Set ι) fun x ↦ (adicCompletionIntegers K v).toAddSubgroup) :
      Set ((ι → adicCompletion K v)))] := by
  refine RestrictedProduct.locallyCompactSpace_of_addGroup _ ?_
  filter_upwards
  intro v
  refine isCompact_univ_pi (fun i ↦ ?_)
  change IsCompact (v.adicCompletionIntegers K : Set (v.adicCompletion K))
  sorry -- "integers are compact"

local instance : LocallyCompactSpace
    Πʳ (v : HeightOneSpectrum (𝓞 K)), [adicCompletion K v,
      ((adicCompletionIntegers K v).toAddSubgroup : Set (adicCompletion K v))] := by
  refine RestrictedProduct.locallyCompactSpace_of_addGroup _ ?_
  filter_upwards
  intro v
  change IsCompact (v.adicCompletionIntegers K : Set (v.adicCompletion K))
  sorry -- "integers are compact"

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

-- A (continuous) 𝔸_K^f-linear automorphism of 𝔸_K^f ⊗ B is "integral" at all but
-- finitely many places
lemma FiniteAdeleRing.Aux.almost_always_integral
    (φ : FiniteAdeleRing (𝓞 K) K ⊗[K] B ≃L[FiniteAdeleRing (𝓞 K) K]
    FiniteAdeleRing (𝓞 K) K ⊗[K] B) :
    let ι := Module.Free.ChooseBasisIndex K B
    ∀ᶠ (i : HeightOneSpectrum (𝓞 K)) in Filter.cofinite,
      Set.BijOn ⇑((fun v ↦ e K B v
        (FiniteAdeleRing.TensorProduct.localcomponentEquiv (𝓞 K) K B v φ)) i)
      ↑(AddSubgroup.pi (Set.univ : Set ι) fun x ↦ (adicCompletionIntegers K i).toAddSubgroup)
      ↑(AddSubgroup.pi (Set.univ : Set ι) fun x ↦ (adicCompletionIntegers K i).toAddSubgroup) :=
  sorry -- this needs some thought

/-- A diagram which obviously commutes, commutes. -/
lemma FiniteAdeleRing.Aux.f_g_local_global
    (φ : ((FiniteAdeleRing (𝓞 K) K) ⊗[K] B) ≃L[FiniteAdeleRing (𝓞 K) K]
      (FiniteAdeleRing (𝓞 K) K) ⊗[K] B) :
    g K (f K B φ) = ContinuousAddEquiv.restrictedProductCongrRight
    (fun v ↦ e _ _ _ (FiniteAdeleRing.TensorProduct.localcomponentEquiv (𝓞 K) K B v φ))
    (FiniteAdeleRing.Aux.almost_always_integral _ _ _) := by
  sorry -- this is hopefully close to being true by ext but I didn't think about it.

lemma localcomponent_mulLeft (u : ((FiniteAdeleRing (𝓞 K) K) ⊗[K] B)ˣ)
    (v : HeightOneSpectrum (𝓞 K)) :
    (FiniteAdeleRing.TensorProduct.localcomponentEquiv (𝓞 K) K B v
    (ContinuousLinearEquiv.mulLeft (FiniteAdeleRing (𝓞 K) K) u)).toContinuousAddEquiv =
    (ContinuousAddEquiv.mulLeft (u.map (Algebra.TensorProduct.rTensor B
      (IsDedekindDomain.FiniteAdeleRing.evalContinuousAlgebraMap
        (𝓞 K) K v).toAlgHom).toMonoidHom)) := by
  ext u
  -- should hopefully follow from localcomponent_eval
  sorry

lemma localcomponent_mulRight (u : ((FiniteAdeleRing (𝓞 K) K) ⊗[K] B)ˣ)
    (v : HeightOneSpectrum (𝓞 K)) :
    (FiniteAdeleRing.TensorProduct.localcomponentEquiv (𝓞 K) K B v
    (ContinuousLinearEquiv.mulRight (FiniteAdeleRing (𝓞 K) K) u)).toContinuousAddEquiv =
    (ContinuousAddEquiv.mulRight (u.map (Algebra.TensorProduct.rTensor B
      (IsDedekindDomain.FiniteAdeleRing.evalContinuousAlgebraMap
        (𝓞 K) K v).toAlgHom).toMonoidHom)) := by
  ext u
  -- should hopefully follow from localcomponent_eval
  sorry

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
  map_smul' m x := by simp
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
