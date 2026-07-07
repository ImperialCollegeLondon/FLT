/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang, Kevin Buzzard
-/
module

public import FLT.Mathlib.Algebra.Algebra.Pi
public import FLT.Mathlib.Algebra.Group.Action.Hom
public import FLT.Mathlib.GroupTheory.GroupAction.Quotient
public import FLT.Mathlib.Topology.Algebra.ContinuousSMulDiscrete
public import FLT.Mathlib.Topology.Algebra.IsUniformGroup.Basic
public import Mathlib.FieldTheory.Galois.Infinite
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.FieldTheory.KrullTopology
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Invariant.Defs
public import Mathlib.Topology.Algebra.Group.ClosedSubgroup

import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.HopkinsLevitzki

/-!
# Equivalence between continuous `G`-finite sets and `k`-etale algebras

Given a group `G`, fields `L/K` with `L` separably closed,
such that `G` acts on `L` by `K`-algebra homomorphisms.
We have a contravariant adjunction
`G`-set ↔ `K`-algebra
`X → Hom_G(X, L)`,
`Hom_K(A, L) ← A`
with unit and counits:
`AlgHom.evalMulActionHom`: `A →ₐ[K] ((A →ₐ[K] L) →[G] L)`
`MulActionHom.evalAlgHom`: `X →[G] ((X →[G] L) →ₐ[K] L)`

Suppose `L/K` is galois with galois group `G`:

* If `X` is finite discrete with continuous `G` action, then `X →[G] L` is finite etale.

* `InfiniteGalois.evalAlgHom_bijective`:
  If `X` is finite discrete with continuous `G` action, then `MulActionHom.evalAlgHom` is bijective.

* If `A/K` is finite dimensional then `A →ₐ[K] L` is finite discrete with continuous `G` action.

* `InfiniteGalois.evalMulActionHom_bijective`:
  If `A/K` is etale, and `L` contains all residue fields of `A` (in particular when
  `L` is separably closed), then `AlgHom.evalMulActionHom` is bijective.

Taking `L = Kˢᵉᵖ`, the adjunction restricts to a (contravariant) equivalence
between finite discrete `Gₖ`-sets and finite etale `k`-algebras.

Material destined for Mathlib.
-/

@[expose] public section

universe u

variable (K L : Type u) [Field K] [Field L] [Algebra K L]
variable (X : Type u) [MulAction (L ≃ₐ[K] L) X]

open TensorProduct

open IntermediateField in
/-- Given a representative for each orbit of `X` under `G := Gal(L/K)`,
and for each `x : X` a choice of `σ` that sends `x` to the representative,
we obtain a `K`-algebra isomorphism between `G`-equivariant homs from `X`
and the product of `Stab(x)`-fixed points over each orbit representative `x`. -/
def MulAction.etaleSubalgebraEquiv
    (σ : X → L ≃ₐ[K] L) (hσ : ∀ a b, orbitRel (L ≃ₐ[K] L) X a b → σ a • a = σ b • b) :
    (X →[L ≃ₐ[K] L] L) ≃ₐ[K]
      Π i : Set.range (fun i ↦ σ i • i), fixedField (stabilizer (L ≃ₐ[K] L) i.1) where
  __ := MulAction.homEquivProdFixedPoints σ hσ
  map_mul' f g := by ext i; rfl
  map_add' f g := by ext i; rfl
  commutes' k := by ext i; rfl

open MulAction IntermediateField in
/-- If `G` is a closed subgroup of the galois group `Γ := Gal(L/K)`, then
`Γ/G` is in bijection with the `K`-linear embeddings of `Lᴳ` into `L`.

Note that `G` is not necessarily normal here. -/
noncomputable
def InfiniteGalois.quotientEquivFixedFieldEmb [IsGalois K L] (G : ClosedSubgroup (L ≃ₐ[K] L)) :
    ((L ≃ₐ[K] L) ⧸ G.1) ≃ (fixedField G.1 →ₐ[K] L) where
  toFun := Quotient.lift (fun σ ↦ σ.toAlgHom.comp (IntermediateField.val _)) (by
    rintro _ σ ⟨τ, rfl⟩
    ext x
    change σ _ = σ _
    simpa using x.2 ⟨_, τ.2⟩)
  invFun f := QuotientGroup.mk (.ofBijective (f.liftNormal L) (AlgHom.normal_bijective K L L _))
  left_inv := Quotient.ind fun σ ↦ show _ = QuotientGroup.mk σ by
    simp only [Quotient.lift_mk, QuotientGroup.eq]
    conv_lhs => rw [← InfiniteGalois.fixingSubgroup_fixedField G]
    intro x
    rw [mul_smul, inv_smul_eq_iff]
    exact ((σ.toAlgHom.comp (IntermediateField.val _)).liftNormal_commutes _ _).symm
  right_inv f := by ext x; simpa using! f.liftNormal_commutes _ _

open MulAction in
lemma InfiniteGalois.evalAlgHom_bijective [IsGalois K L] [Finite X]
    [ContinuousSMulDiscrete (L ≃ₐ[K] L) X] :
    Function.Bijective (MulActionHom.evalAlgHom (L ≃ₐ[K] L) K X L) := by
  classical
  choose φ hφ using Quotient.mk_surjective (s := orbitRel (L ≃ₐ[K] L) X)
  choose σ hσ using fun x ↦ Quotient.eq''.mp (hφ ⟦x⟧)
  replace hσ : ∀ a b, orbitRel (L ≃ₐ[K] L) X a b → σ a • a = σ b • b :=
    fun a b e ↦ ((hσ a).trans (congr_arg φ (Quotient.eq''.mpr e))).trans (hσ b).symm
  let e : ((X →[L ≃ₐ[K] L] L) →ₐ[K] L) ≃ X := by
    refine (AlgEquiv.arrowCongr (MulAction.etaleSubalgebraEquiv K L X σ hσ) .refl).trans ?_
    refine Pi.algHomEquivOfIsDomain.trans ?_
    refine (Equiv.sigmaCongrRight fun _ ↦
      (InfiniteGalois.quotientEquivFixedFieldEmb K L ⟨_, ?_⟩).symm).trans ?_
    · exact Subgroup.isClosed_of_isOpen _ (ContinuousSMulDiscrete.isOpen_stabilizer _ _)
    exact MulAction.sigmaRangeQuotientStabilizer σ hσ
  convert e.symm.bijective
  ext x f
  change f x = (σ x)⁻¹ • (f (σ x • x))
  rw [map_smul, inv_smul_smul]

open MulAction IntermediateField in
instance [IsGalois K L] [Finite X] : Algebra.FormallyEtale K (X →[L ≃ₐ[K] L] L) := by
  classical
  choose φ hφ using Quotient.mk_surjective (s := orbitRel (L ≃ₐ[K] L) X)
  choose σ hσ using fun x ↦ Quotient.eq''.mp (hφ ⟦x⟧)
  replace hσ : ∀ a b, orbitRel (L ≃ₐ[K] L) X a b → σ a • a = σ b • b :=
    fun a b e ↦ ((hσ a).trans (congr_arg φ (Quotient.eq''.mpr e))).trans (hσ b).symm
  have (x : X) : Algebra.FormallyEtale K (fixedField (stabilizer (L ≃ₐ[K] L) x)) :=
    .of_isSeparable _ _
  exact .of_equiv (MulAction.etaleSubalgebraEquiv K L X σ hσ).symm

open MulAction IntermediateField in
instance [IsGalois K L] [Finite X] [ContinuousSMulDiscrete (L ≃ₐ[K] L) X] :
    Module.Finite K (X →[L ≃ₐ[K] L] L) := by
  classical
  choose φ hφ using Quotient.mk_surjective (s := orbitRel (L ≃ₐ[K] L) X)
  choose σ hσ using fun x ↦ Quotient.eq''.mp (hφ ⟦x⟧)
  replace hσ : ∀ a b, orbitRel (L ≃ₐ[K] L) X a b → σ a • a = σ b • b :=
    fun a b e ↦ ((hσ a).trans (congr_arg φ (Quotient.eq''.mpr e))).trans (hσ b).symm
  have (x : X) : Module.Finite K (fixedField (stabilizer (L ≃ₐ[K] L) x)) :=
    (InfiniteGalois.isOpen_iff_finite _).mp (by
      rw [InfiniteGalois.fixingSubgroup_fixedField
        ⟨_, Subgroup.isClosed_of_isOpen _ (ContinuousSMulDiscrete.isOpen_stabilizer _ _)⟩]
      exact ContinuousSMulDiscrete.isOpen_stabilizer _ _)
  exact .equiv (MulAction.etaleSubalgebraEquiv K L X σ hσ).toLinearEquiv.symm

instance [IsGalois K L] [Finite X] [ContinuousSMulDiscrete (L ≃ₐ[K] L) X] :
    Algebra.Etale K (X →[L ≃ₐ[K] L] L) where
  finitePresentation := by rw [← Algebra.FinitePresentation.of_finiteType]; infer_instance

variable (A : Type u) [CommRing A] [Algebra K A]

instance [Module.Finite K A] : ContinuousSMulDiscrete (L ≃ₐ[K] L) (A →ₐ[K] L) := by
  refine continuousSMulDiscrete_iff_isOpen_stabilizer.mpr fun f ↦ ?_
  have : FiniteDimensional K f.range :=
    .of_surjective f.rangeRestrict.toLinearMap f.rangeRestrict_surjective
  let E := IntermediateField.adjoin K (f.range : Set L)
  have : FiniteDimensional K E := by
    change FiniteDimensional K E.toSubalgebra
    rwa [IntermediateField.adjoin_toSubalgebra_of_isAlgebraic, Algebra.adjoin_eq]
    simp only [AlgHom.coe_range, Set.mem_range, forall_exists_index, forall_apply_eq_imp_iff]
    exact fun x ↦ ((Algebra.IsIntegral.isIntegral (R := K) x).map f).isAlgebraic
  refine Subgroup.isOpen_mono ?_ E.fixingSubgroup_isOpen
  intro σ hσ
  ext x
  exact hσ ⟨f x, IntermediateField.subset_adjoin _ _ ⟨x, rfl⟩⟩

attribute [local instance] Ideal.Quotient.field RingHom.ker_isPrime in
lemma InfiniteGalois.evalMulActionHom_bijective [Algebra.Etale K A] [IsGalois K L]
    (H : ∀ 𝔪 : Ideal A, 𝔪.IsMaximal → Nonempty (A ⧸ 𝔪 →ₐ[K] L)) :
    Function.Bijective (AlgHom.evalMulActionHom (L ≃ₐ[K] L) K A L) := by
  let emb (𝔪 : Ideal A) [𝔪.IsMaximal] := (H 𝔪 ‹_›).some
  have := Algebra.FormallyUnramified.isReduced_of_field K A
  have := Algebra.FormallyUnramified.finite_of_free K A
  have : IsArtinianRing A := isArtinian_of_tower K inferInstance
  have hemb (𝔪 : Ideal A) [𝔪.IsMaximal] (f : (A →ₐ[K] L) →[(L ≃ₐ[K] L)] L) :
      f ((emb 𝔪).comp (Ideal.Quotient.mkₐ _ _)) ∈ (emb 𝔪).fieldRange := by
    rw [← fixedField_fixingSubgroup (emb 𝔪).fieldRange]
    intro ⟨σ, hσ⟩
    rw [Subgroup.mk_smul, ← map_smul]
    congr 1
    ext x
    simpa using! hσ ⟨_, Ideal.Quotient.mk _ x, rfl⟩
  choose! F' hF' using hemb
  let F : ((A →ₐ[K] L) →[(L ≃ₐ[K] L)] L) → A :=
    fun f ↦ (IsArtinianRing.equivPi A).symm fun 𝔪 ↦ F' 𝔪.1 f
  have H₁ : Function.LeftInverse F (AlgHom.evalMulActionHom (L ≃ₐ[K] L) K A L) := by
    intros a
    apply (IsArtinianRing.equivPi A).injective
    refine ((IsArtinianRing.equivPi A).apply_symm_apply _).trans ?_
    ext ⟨𝔪, h𝔪⟩
    replace h𝔪 : 𝔪.IsMaximal := h𝔪
    exact (emb 𝔪).injective (hF' _ _)
  have H₂ : Function.Injective F := by
    intros f₁ f₂ e
    ext g
    obtain ⟨σ, hσ⟩ : ∃ σ : L ≃ₐ[K] L, σ • emb (RingHom.ker g) = Ideal.kerLiftAlg g := by
      letI := (emb (RingHom.ker g)).toAlgebra
      have : IsScalarTower K (A ⧸ RingHom.ker g) L :=
        .of_algebraMap_eq' (emb (RingHom.ker g)).comp_algebraMap.symm
      exact ⟨.ofBijective ((Ideal.kerLiftAlg g).liftNormal L) (AlgHom.normal_bijective _ _ _ _),
        AlgHom.ext ((Ideal.kerLiftAlg g).liftNormal_commutes L)⟩
    have hσ' : σ • (emb (RingHom.ker g)).comp (Ideal.Quotient.mkₐ _ _) = g :=
      AlgHom.ext fun x ↦ DFunLike.congr_fun hσ (Ideal.Quotient.mk _ x)
    rw [← hσ', map_smul, map_smul, ← hF', ← hF']
    congr 2
    exact congr_fun ((IsArtinianRing.equivPi A).symm.injective e)
      ⟨RingHom.ker g, inferInstanceAs (RingHom.ker g).IsMaximal⟩
  exact ⟨H₁.injective, fun x ↦ ⟨F x, H₂ (H₁ (F x))⟩⟩

attribute [local instance] Ideal.Quotient.field Algebra.FormallyUnramified.isSeparable in
lemma InfiniteGalois.evalMulActionHom_bijective_of_isSepClosed
    [Algebra.Etale K A] [IsGalois K L] [IsSepClosed L] :
    Function.Bijective (AlgHom.evalMulActionHom (L ≃ₐ[K] L) K A L) :=
  InfiniteGalois.evalMulActionHom_bijective _ _ _ fun _ _ ↦ ⟨IsSepClosed.lift⟩

instance finiteIndex_fixingSubgroup {K L : Type*} [Field K] [Field L] [Algebra K L]
    (E : IntermediateField K L) [FiniteDimensional K E] : E.fixingSubgroup.FiniteIndex := by
  let f : (L ≃ₐ[K] L) ⧸ E.fixingSubgroup → E →ₐ[K] L := Quotient.lift
    (fun f ↦ f.toAlgHom.comp E.val)
    (by rintro _ τ ⟨σ, rfl⟩; ext x; exact DFunLike.congr_arg τ (σ.2 x))
  have : Function.Injective f := by
    rintro ⟨σ⟩ ⟨τ⟩ (H : σ.toAlgHom.comp E.val = τ.toAlgHom.comp E.val)
    refine Quotient.sound ⟨⟨.op (τ⁻¹ * σ), fun x ↦ ?_⟩, by simp⟩
    simpa [AlgEquiv.aut_inv, AlgEquiv.symm_apply_eq] using DFunLike.congr_fun H x
  have := Finite.of_injective _ this
  exact Subgroup.finiteIndex_of_finite_quotient

open IntermediateField in
instance {K L : Type*} [Field K] [Field L] [Algebra K L] [Algebra.IsAlgebraic K L] :
    CompactSpace (L ≃ₐ[K] L) := by
  classical
  letI := IsTopologicalGroup.rightUniformSpace (L ≃ₐ[K] L)
  rw [← isCompact_univ_iff, isCompact_iff_totallyBounded_isComplete]
  refine ⟨IsTopologicalGroup.totallyBounded fun s hs ↦ ?_, ?_⟩
  · obtain ⟨E, hE, H⟩ := (krullTopology_mem_nhds_one_iff _ _ _).mp hs
    refine ⟨_, inferInstance, H⟩
  · rintro f hf -
    have := hf.1
    have (x : L) :
        ∃ σ₀ : L ≃ₐ[K] L, ∃ t ∈ f, ∀ σ ∈ t, ∀ τ : L ≃ₐ[K] L, σ (τ x) = σ₀ (τ x) := by
      have : FiniteDimensional K K⟮x⟯ :=
        adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral _)
      obtain ⟨t, htf, H⟩ := ((Filter.HasBasis.cauchy_iff
        (by exact (galGroupBasis K L).nhds_one_hasBasis.comap _)).mp hf).2 _ (by
            exact ⟨_, ⟨normalClosure K K⟮x⟯ L, inferInstanceAs (FiniteDimensional K _), rfl⟩, rfl⟩)
      obtain ⟨σ, hσ⟩ := f.nonempty_of_mem htf
      refine ⟨σ, t, htf, fun τ hτ τ₀ ↦ ?_⟩
      have : σ (τ.symm (τ (τ₀ x))) = τ (τ₀ x) := H τ hτ σ hσ ⟨τ (τ₀ x), by
        refine SetLike.le_def.mp (le_iSup _ (τ.toAlgHom.comp <| τ₀.toAlgHom.comp (val _))) ?_
        exact ⟨⟨_, subset_adjoin _ _ (by simp)⟩, rfl⟩⟩
      simpa using this.symm
    choose σ₀ t htf H using this
    have H' (s σ hσ) := H s σ hσ .refl
    dsimp at H'
    let F : L ≃ₐ[K] L :=
    { toFun x := σ₀ x x
      invFun x := (σ₀ x).symm x
      left_inv x := by
        obtain ⟨σ, hσ₁, hσ₂⟩ := f.nonempty_of_mem (f.inter_mem (htf x) (htf (σ₀ x x)))
        dsimp
        have H' := H' _ _ hσ₁
        have : σ x = (σ₀ (σ₀ x x) x) := by simpa using H _ _ hσ₂ (σ₀ x).symm
        rw [← H', AlgEquiv.symm_apply_eq, H', ← this, H']
      right_inv x := by
        obtain ⟨σ, hσ₁, hσ₂⟩ := f.nonempty_of_mem (f.inter_mem (htf x) (htf ((σ₀ x).symm x)))
        dsimp
        replace H := H _ _ hσ₁ σ.symm
        simp only [AlgEquiv.apply_symm_apply, ← AlgEquiv.symm_apply_eq, AlgEquiv.symm_symm] at H
        rw [← H' _ _ hσ₂, H]
      map_mul' x y := by
        obtain ⟨σ, hσx, hσy, hσxy⟩ :=
          f.nonempty_of_mem (f.inter_mem (htf x) (f.inter_mem (htf y) (htf (x * y))))
        rw [← H' _ _ hσxy, ← H' _ _ hσx, ← H' _ _ hσy, map_mul]
      map_add' x y := by
        obtain ⟨σ, hσx, hσy, hσxy⟩ :=
          f.nonempty_of_mem (f.inter_mem (htf x) (f.inter_mem (htf y) (htf (x + y))))
        rw [← H' _ _ hσxy, ← H' _ _ hσx, ← H' _ _ hσy, map_add]
      commutes' := by simp }
    refine ⟨F, Set.mem_univ _, ?_⟩
    rw [((galGroupBasis K L).nhds_hasBasis F).ge_iff]
    rintro _ ⟨_, ⟨E, hE, rfl⟩, rfl⟩
    simp only [Set.image_mul_left]
    have ⟨s, hs⟩ := E.toSubmodule.fg_iff_finiteDimensional.mpr hE
    refine f.mem_of_superset ((Filter.biInter_finset_mem s).mpr fun i _ ↦ htf i) ?_
    rintro σ hσ ⟨x, hx⟩
    change F.symm (σ x) = x
    induction hs.ge hx using Submodule.span_induction with
    | zero | add | smul => simp_all
    | mem x h =>
      rw [AlgEquiv.symm_apply_eq]
      simp [F, ← H' _ _ (Set.mem_iInter₂.mp hσ _ h)]

open scoped IntermediateField in
instance {K L : Type*} [Field K] [Field L] [Algebra K L] [Algebra.IsAlgebraic K L] :
    ContinuousSMulDiscrete (L ≃ₐ[K] L) L := by
  constructor
  intro x y
  rw [isOpen_iff_forall_mem_open]
  rintro σ (hσ : _ = _)
  have : FiniteDimensional K K⟮x⟯ := IntermediateField.adjoin.finiteDimensional
      (Algebra.IsAlgebraic.isAlgebraic (R := K) x).isIntegral
  refine ⟨_, ?_, K⟮x⟯.fixingSubgroup_isOpen.smul σ, 1, one_mem _, by simp⟩
  rintro _ ⟨τ, hτ, rfl⟩
  have := (mem_fixingSubgroup_iff _).mp hτ x (IntermediateField.mem_adjoin_simple_self K x)
  simp only [smul_eq_mul, Set.mem_setOf_eq, mul_smul, this, hσ]

instance {K L : Type*} [Field K] [Field L] [Algebra K L] [IsGalois K L] :
    Algebra.IsInvariant K L (L ≃ₐ[K] L) :=
  ⟨fun _ H ↦ (InfiniteGalois.fixedField_fixingSubgroup
    (⊥ : IntermediateField K L)).le fun _ ↦ H _⟩
