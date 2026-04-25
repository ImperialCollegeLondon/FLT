/-
Copyright (c) 2025 Matthew Jasper. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Jasper
-/
module

public import FLT.DedekindDomain.FiniteAdeleRing.TensorPi
public import FLT.DedekindDomain.FiniteAdeleRing.IsDirectLimitRestricted
public import Mathlib.RingTheory.Flat.Basic

@[expose] public section

namespace RestrictedProduct

open TensorProduct

variable (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M]
  {ι : Type*} (N : ι → Type*) [∀ i, AddCommGroup (N i)]
  [∀ i, Module R (N i)]

variable (ℱ : Filter ι) (L : ∀ i, Submodule R (N i))

/-- `M ⊗_R (L i)` as an `R`-submodule of `M ⊗_R (N i)`. -/
def rangeLTensor (i : ι) : Submodule R (M ⊗[R] N i) :=
  LinearMap.range (LinearMap.lTensor M ((L i).subtype))

/-- `M ⊗_R (L i)` as an `M`-submodule of `M ⊗_R (N i)`. -/
noncomputable def rangeLTensorLeft (R M : Type*) [CommSemiring R] [CommSemiring M] [Algebra R M]
    {ι : Type*} (N : ι → Type*) [∀ i, Semiring (N i)] [∀ i, Algebra R (N i)]
    (L : ∀ i, Submodule R (N i)) (i : ι) : Submodule M (M ⊗[R] N i) :=
  (TensorProduct.AlgebraTensorModule.lTensor _ _ (L i).subtype).range

set_option backward.isDefEq.respectTransparency false in
/-- The `R`-linear map `φ : M ⊗_R ∏'_i [N i, L i]_[𝓕] → ∏'_i [M ⊗_R (N i), M ⊗_R (L i)]_[𝓕]`
given by `φ (m ⊗ n) i = m ⊗ (n i)`. -/
def lTensor :
    M ⊗[R] Πʳ i, [N i, L i]_[ℱ] →ₗ[R] Πʳ i, [M ⊗[R] N i, rangeLTensor R M N L i]_[ℱ] :=
  have hmap : ∀ (m : M), ∀ᶠ (j : ι) in ℱ, Set.MapsTo
      (TensorProduct.mk R M (N j) m) (L j) (rangeLTensor R M N L j) := by
    intro m
    filter_upwards with i n hn using ⟨m ⊗ₜ[R] ⟨n, hn⟩, rfl⟩
  TensorProduct.lift {
    toFun m := mapAlongLinearMap N (M ⊗[R] N ·) id Filter.tendsto_id
        (fun i ↦ TensorProduct.mk R M (N i) m) (hmap m)
    map_add' m n := by ext; simp
    map_smul' a m := by ext; simp
  }

/-- The `M`-linear map `φ : M ⊗_R ∏'_i [N i, L i]_[𝓕] → ∏'_i [M ⊗_R (N i), M ⊗_R (L i)]_[𝓕]`
given by `φ (m ⊗ n) i = m ⊗ (n i)`. -/
noncomputable def lTensorLeft (R M : Type*) [CommRing R] [CommRing M] [Algebra R M] {ι : Type*}
    (N : ι → Type*) [∀ i, Ring (N i)] [∀ i, Algebra R (N i)] (ℱ : Filter ι)
    (L : ∀ i, Submodule R (N i)) :
    M ⊗[R] Πʳ i, [N i, L i]_[ℱ] →ₗ[M] Πʳ i, [M ⊗[R] N i, rangeLTensorLeft R M N L i]_[ℱ] :=
  have hmap : ∀ (m : M), ∀ᶠ (j : ι) in ℱ, Set.MapsTo
      (TensorProduct.mk R M (N j) m) (L j) (rangeLTensorLeft R M N L j) := by
    intro m
    filter_upwards with i n hn using ⟨m ⊗ₜ[R] ⟨n, hn⟩, rfl⟩
  let f : (i : ι) → N i →ₗ[R] M ⊗[R] N i := fun i ↦
    { toFun n := 1 ⊗ₜ n, map_add' _ _ := by simp [tmul_add], map_smul' := by simp }
  have (i : ι) : SMulMemClass (Submodule M (M ⊗[R] N i)) R ((fun x ↦ M ⊗[R] N x) i) :=
    .ofIsScalarTower _ _ _ _
  have : IsScalarTower R M Πʳ (i : ι), [M ⊗[R] N i, ↑(rangeLTensorLeft R M N L i)]_[ℱ] := by
    apply IsScalarTower.mk fun r m x ↦ by ext; simp
  (mapAlongLinearMap N (M ⊗[R] N ·) id Filter.tendsto_id f (hmap 1)).liftBaseChange _

@[simp]
lemma lTensor_tmul (m : M) (f : Πʳ i, [N i, L i]_[ℱ]) (i : ι) :
    lTensor R M N ℱ L (m ⊗ₜ f) i = m ⊗ₜ (f i) :=
  rfl

@[simp]
lemma lTensorLeft_tmul (R M : Type*) [CommRing R] [CommRing M] [Algebra R M] {ι : Type*}
    (N : ι → Type*) [∀ i, Ring (N i)] [∀ i, Algebra R (N i)] (L : ∀ i, Submodule R (N i))
    (ℱ : Filter ι) (m : M) (f : Πʳ i, [N i, L i]_[ℱ]) (i : ι) :
    lTensorLeft R M N ℱ L (m ⊗ₜ f) i = m ⊗ₜ (f i) := by
  rw [lTensorLeft, LinearMap.liftBaseChange_tmul, smul_apply, mapAlongLinearMap_apply]
  change m • (_ ⊗ₜ[R] _) = _
  simp [id_eq, smul_tmul' m (1 : M) (f i)]

lemma coe_lTensorLeft_eq_lTensor (R M : Type*) [CommRing R] [CommRing M] [Algebra R M] {ι : Type*}
    (N : ι → Type*) [∀ i, Ring (N i)] [∀ i, Algebra R (N i)] (L : ∀ i, Submodule R (N i))
    (ℱ : Filter ι) :
    ⇑(lTensorLeft R M N ℱ L) = lTensor R M N ℱ L := by
  ext x i
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, zero_apply]; rfl -- need rfl after 4.29, unsure how to fix
  | tmul x y => simp [lTensorLeft_tmul]; rfl
  | add x y hx hy => simp_all; rfl

variable (S : Set ι) [Module.FinitePresentation R M] [Module.Flat R M]

/-- `R`-Linear isomorphism between `M ⊗_R (L i)` and `rangeLTensor R M N L i`. -/
noncomputable def tmulEquivRangeLTensor (i : ι) : M ⊗[R] (L i) ≃ₗ[R] rangeLTensor R M N L i :=
  LinearEquiv.ofInjective (LinearMap.lTensor M (Submodule.subtype <| L i))
    (Module.Flat.lTensor_preserves_injective_linearMap (L i).subtype
      (Submodule.injective_subtype (L i)))

open scoped Filter in
/-- `R`-Linear isomorphism that's propositionally equal to `lTensor`. -/
noncomputable def lTensorPrincipalEquiv :
    M ⊗[R] Πʳ i, [N i, L i]_[𝓟 S] ≃ₗ[R] Πʳ i, [M ⊗[R] N i, rangeLTensor R M N L i]_[𝓟 S] :=
  open scoped Classical in
  let N' (i : ι) := if i ∈ S then L i else (⊤ : Submodule R (N i))
  let f : Πʳ i, [N i, L i]_[𝓟 S] ≃ₗ[R] (Π i, N' i) := {
    toFun x i := ⟨x i, by
      by_cases h : i ∈ S
      · simpa [N', h] using x.property h
      · simp [N', h]⟩
    invFun x := ⟨fun i ↦ x i, by
      rw [Filter.eventually_principal]
      intro y hy
      simpa only [N', hy, ↓reduceIte] using (x y).prop⟩
    map_add' x y := by ext; simp
    map_smul' a x := by ext; simp
  }
  let g1 : M ⊗[R] Πʳ i, [N i, L i]_[𝓟 S] ≃ₗ[R] M ⊗[R] (Π i, N' i) := LinearEquiv.lTensor M f
  let g2 : M ⊗[R] (Π i, N' i) ≃ₗ[R] Π i, M ⊗[R] N' i :=
    tensorPi_equiv_piTensor' R M fun i ↦ ↥(N' i)
  let gEquiv (i : ι) (h : i ∈ S) : M ⊗[R] (N' i) ≃ₗ[R] rangeLTensor R M N L i :=
    (LinearEquiv.lTensor M (LinearEquiv.ofEq _ _ (by simp [N', h]))) ≪≫ₗ
      (tmulEquivRangeLTensor R M N L i)
  let gEquiv' (i : ι) (h : i ∉ S) : M ⊗[R] (N' i) ≃ₗ[R] M ⊗[R] N i :=
    LinearEquiv.lTensor M <| LinearEquiv.ofTop (N' i) (by simp [N', h])
  let g3 : (Π i, M ⊗[R] N' i) ≃ₗ[R] Πʳ i, [M ⊗[R] N i, rangeLTensor R M N L i]_[𝓟 S] := {
    toFun x := ⟨
      fun i ↦ if h : i ∈ S then gEquiv i h (x i) else gEquiv' i h (x i),
      by
        rw [Filter.eventually_principal]
        intro i h
        simp [h]⟩
    invFun x i := if h : i ∈ S then
        gEquiv i h |>.symm ⟨(x i), by simpa using x.property h⟩
      else
        gEquiv' i h |>.symm (x i)
    left_inv x := by
      ext i
      by_cases h : i ∈ S <;> simp [h]
    right_inv x := by
      ext i
      by_cases h : i ∈ S <;> simp [h]
    map_add' x y := by
      ext i
      by_cases h : i ∈ S <;> simp [h]
    map_smul' a x := by
      ext i
      by_cases h : i ∈ S <;> simp [h]
  }
  g1 ≪≫ₗ g2 ≪≫ₗ g3

set_option backward.isDefEq.respectTransparency false in
open scoped Filter in
lemma lTensorPrincipalEquiv_tmul (m : M) (x : Πʳ i, [N i, L i]_[𝓟 S]) (i : ι) :
    lTensorPrincipalEquiv R M N L S (m ⊗ₜ x) i = m ⊗ₜ x i := by
  simp [lTensorPrincipalEquiv, tensorPi_equiv_piTensor'_apply, tmulEquivRangeLTensor,
      rangeLTensor]

set_option backward.isDefEq.respectTransparency false in
open scoped Filter in
lemma lTensor_bijective : Function.Bijective (lTensor R M N ℱ L) := by
  classical
  let comp1 := TensorProduct.directLimitRight (ι := ℱ.setsᵒᵈ) (fun _ _ x3 ↦ (inclusionLinearMap
    _ _ L <| Filter.monotone_principal x3)) M (R:=R)
  let comp := IsDirectLimit.Module.linearEquiv
    (fun _ _ h ↦ (inclusionLinearMap _ _ L (Filter.monotone_principal h)))
    (fun S ↦ inclusionLinearMap _ _ L <| Filter.le_principal_iff.2 S.2)
    (Module.DirectLimit.of R ℱ.setsᵒᵈ (fun (S : ℱ.setsᵒᵈ) ↦ Πʳ i, [N i, L i]_[𝓟 S.1])
    (fun _ _ x3 ↦ (inclusionLinearMap _ _ L (Filter.monotone_principal x3))) · )
  let comp2 := IsDirectLimit.Module.linearEquiv (fun (_ : ℱ.setsᵒᵈ) _ x3 ↦
      (inclusionLinearMap _ _ _ (Filter.monotone_principal x3)))
    (fun S ↦ inclusionLinearMap _ _ _ <| Filter.le_principal_iff.2 S.2)
    (Module.DirectLimit.of R _
      (fun (S : ℱ.setsᵒᵈ) ↦ Πʳ i, [(M ⊗[R] N i), rangeLTensor R M N L i]_[𝓟 S.1])
      (fun _ _ x3 ↦ (inclusionLinearMap _ _ _ (Filter.monotone_principal x3))) · )
  let comp4 := (LinearEquiv.lTensor M comp) ≪≫ₗ comp1
  let comp5 : Module.DirectLimit
      (fun (S : ℱ.setsᵒᵈ) ↦ M ⊗[R] Πʳ (i : ι), [N i, L i]_[𝓟 S.1])
      (fun i j h ↦
        LinearMap.lTensor M (inclusionLinearMap _ _ _ (Filter.monotone_principal h))) ≃ₗ[R]
      Module.DirectLimit
      (fun (S : ℱ.setsᵒᵈ) ↦ Πʳ (i : ι), [M ⊗[R] N i, (rangeLTensor R M N L i)]_[𝓟 (S.1)])
      (fun _ _ x3 ↦ inclusionLinearMap _ _ _ (Filter.monotone_principal x3)) :=
    Module.DirectLimit.congr (fun (S : ℱ.setsᵒᵈ) ↦
      (RestrictedProduct.lTensorPrincipalEquiv R M N L (S.1 : Set ι))) (by
        intro i j hij
        refine TensorProduct.ext' (fun x y ↦ ?_)
        ext k
        simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
          LinearMap.lTensor_tmul, lTensorPrincipalEquiv_tmul]
        change x ⊗ₜ[R] y k = ((lTensorPrincipalEquiv R M N L i.1) (x ⊗ₜ[R] y)) k
        rw [lTensorPrincipalEquiv_tmul])
  let tensor_comm' := comp4 ≪≫ₗ comp5 ≪≫ₗ comp2.symm
  have : RestrictedProduct.lTensor R M N ℱ L = tensor_comm' := by
    ext m x i
    simp only [TensorProduct.AlgebraTensorModule.curry_apply, TensorProduct.curry_apply,
      LinearMap.coe_restrictScalars, lTensor_tmul, LinearEquiv.coe_coe, tensor_comm', comp2,
      comp4, comp5, comp, comp1, LinearEquiv.trans_apply, LinearEquiv.lTensor_tmul]
    obtain ⟨j, x', hjx'⟩ := Module.DirectLimit.exists_of (comp x)
    rw [← hjx', TensorProduct.directLimitRight_tmul_of, Module.DirectLimit.congr_apply_of]
    simp only [rangeLTensor, lTensorPrincipalEquiv, tmulEquivRangeLTensor,
      LinearEquiv.trans_apply, LinearEquiv.ofInjective_apply, LinearEquiv.trans_symm,
      LinearEquiv.lTensor_tmul, LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk,
      tensorPi_equiv_piTensor'_apply, LinearMap.lTensor_tmul, Submodule.subtype_apply,
      LinearEquiv.coe_ofEq_apply, LinearEquiv.ofTop_apply, dite_eq_ite, ite_self,
      IsDirectLimit.Module.linearEquiv_symm_apply, inclusionLinearMap]
    apply_fun comp.symm at hjx'
    simp only [comp, IsDirectLimit.Module.linearEquiv_symm_apply, inclusionLinearMap,
      LinearEquiv.symm_apply_apply, id_eq] at hjx'
    simp only [← congrFun (congrArg DFunLike.coe hjx') i, mapAlongLinearMap_apply, id_eq,
      LinearMap.id_coe]
    rfl
  rw [this]
  exact tensor_comm'.bijective

lemma lTensorLeft_bijective (R M : Type*) [CommRing R] [CommRing M] [Algebra R M] {ι : Type*}
    (N : ι → Type*) [∀ i, Ring (N i)] [∀ i, Algebra R (N i)] (L : ∀ i, Submodule R (N i))
    (ℱ : Filter ι) [Module.Flat R M] [Module.FinitePresentation R M] :
    Function.Bijective (lTensorLeft R M N ℱ L) := by
  rw [coe_lTensorLeft_eq_lTensor]
  exact lTensor_bijective R M N ℱ L

/-- The `R`-linear isomorphism given by `lTensor` when `M` is a finite flat `R`-module. -/
noncomputable def lTensorEquiv :
    M ⊗[R] Πʳ i, [N i, L i]_[ℱ] ≃ₗ[R] Πʳ i, [M ⊗[R] N i, rangeLTensor R M N L i]_[ℱ] :=
  LinearEquiv.ofBijective (lTensor R M N ℱ L) (lTensor_bijective R M N ℱ L)

/-- The `M`-linear isomorphism given by `lTensor` when `M` is a finite flat `R`-module. -/
noncomputable def lTensorEquivLeft (R M : Type*) [CommRing R] [CommRing M] [Algebra R M] {ι : Type*}
    (N : ι → Type*) [∀ i, Ring (N i)] [∀ i, Algebra R (N i)] (L : ∀ i, Submodule R (N i))
    (ℱ : Filter ι) [Module.Flat R M] [Module.FinitePresentation R M] :
    M ⊗[R] Πʳ i, [N i, L i]_[ℱ] ≃ₗ[M] Πʳ i, [M ⊗[R] N i, rangeLTensorLeft R M N L i]_[ℱ] :=
  LinearEquiv.ofBijective (lTensorLeft R M N ℱ L) (lTensorLeft_bijective R M N L ℱ)

@[simp]
lemma lTensorEquiv_tmul (m : M) (f : Πʳ i, [N i, L i]_[ℱ]) (i : ι) :
    lTensorEquiv R M N ℱ L (m ⊗ₜ f) i = m ⊗ₜ (f i) :=
  rfl

@[simp]
lemma lTensorEquivLeft_tmul (R M : Type*) [CommRing R] [CommRing M] [Algebra R M] {ι : Type*}
    (N : ι → Type*) [∀ i, Ring (N i)] [∀ i, Algebra R (N i)] (L : ∀ i, Submodule R (N i))
    (ℱ : Filter ι) [Module.Flat R M] [Module.FinitePresentation R M] (m : M)
    (f : Πʳ i, [N i, L i]_[ℱ]) (i : ι) :
    lTensorEquivLeft R M N L ℱ (m ⊗ₜ f) i = m ⊗ₜ (f i) := by
  simp [lTensorEquivLeft]

end RestrictedProduct
