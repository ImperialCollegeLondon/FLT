/-
Copyright (c) 2026 Y. Samanda Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Y. Samanda Zhang
-/
module

public import Mathlib
public import FLT.Slop.PoitouTate.cupprod

/-!
# Cochain-level lemmas for the Poitou–Tate pairing

Generic infrastructure on homogeneous cochains needed by the explicit construction of
the kernel pairing `⟨f, g⟩ = ∑_{v ∈ S} inv_v(x_v)` of `PTblueprint.tex` §"Explicitly
defining the pairing" (see `FLT/Slop/PoitouTate/KerPairing.lean`). Three independent layers:

* **The cocycle-class API** (`ContRepresentation.cocycleClass`): the cohomology class of a
  homogeneous cocycle, with the characterizations the blueprint uses implicitly — every class
  has a cocycle representative (`cocycleClass_surjective`), and a cocycle represents `0` iff it
  is a coboundary (`cocycleClass_eq_zero_iff`). Built on `cohomologyIsoQuot` of `cupprod.lean`.
  `map_cocycleClass` tracks representatives through the functorial maps
  `ContinuousCohomology.map` (restriction to a decomposition group, coefficient morphisms).

* **The `ℤ`-scalar restriction bridge** (`TopRep.toInt`, `toIntCochainEquiv`): the cup
  products pairing `M` and `M* = Hom_ℤ(M, K_S^×)` into `K_S^×` are only `ℤ`-bilinear, so the
  blueprint's cochain computations happen over `ℤ`, while `kerAlpha` lives in `𝔽`-linear
  cohomology. The bridge identifies the homogeneous cochains of a `TopRep k G` with those of
  its `ℤ`-scalar restriction, compatibly with the differentials and with restriction maps.

* **Cup product vs. restriction** (`cochainsMap_cupCochain`): restriction along `φ : H →ₜ* G`
  commutes with the cochain-level cup products of `cupprod.lean` (the blueprint's silent
  identity `res_v (f ∪ g) = f_v ∪ g_v`), allowing a coefficient morphism on the third slot
  (in the application: the inclusion `K_S^× → K̄ᵥ^×`).
-/

@[expose] public section

set_option allowUnsafeReducibility true in
attribute [local reducible] CategoryTheory.Functor.mapHomologicalComplex

universe u v w

open CategoryTheory Limits

namespace ContRepresentation

variable {k : Type u} {G : Type v} [CommRing k] [TopologicalSpace k] [Group G]
  [TopologicalSpace G] [IsTopologicalGroup G]

open TopRep

section CocycleClass

/-- Applying a `TopModuleCat`-isomorphism is injective on elements. -/
lemma _root_.TopModuleCat.iso_hom_apply_injective {A B : TopModuleCat.{w} k} (e : A ≅ B) :
    Function.Injective (fun a : ↥A ↦ e.hom a) :=
  (ConcreteCategory.bijective_of_isIso e.hom).injective

/-- The homology projection agrees with the concrete cokernel projection under the
identification `homologyIsoCoker`. -/
lemma homologyπ_comp_homologyIsoCoker_hom {ι : Type w} {c : ComplexShape ι}
    (K : HomologicalComplex (TopModuleCat.{v} k) c) (i j : ι) (hij : c.prev j = i) :
    K.homologyπ j ≫ (K.homologyIsoCoker i j hij).hom =
      TopModuleCat.cokerπ (K.toCycles i j) := by
  have h2 := CokernelCofork.π_mapOfIsColimit (K.homologyIsCokernel i j hij)
    (CokernelCofork.ofπ (TopModuleCat.cokerπ (K.toCycles i j)) (TopModuleCat.comp_cokerπ _))
    (Iso.refl (Arrow.mk (K.toCycles i j))).hom
  simp only [Cofork.π_ofπ, Iso.refl_hom, Arrow.id_right, Category.id_comp] at h2
  exact h2

/-- The natural map from cocycles to continuous cohomology agrees, under `cohomologyIsoQuot`,
with the cokernel projection of the kernel model. -/
lemma π_comp_cohomologyIsoQuot_hom (X : TopRep k G) (j : ℕ) :
    ContinuousCohomology.π X j ≫ (cohomologyIsoQuot X j).hom =
      ((homogeneousCochains X).cyclesIsoKer j (j + 1) (by simp)).hom ≫
        TopModuleCat.cokerπ (bdryKer X j) := by
  unfold cohomologyIsoQuot
  rw [Iso.trans_hom, ← Category.assoc, homologyπ_comp_homologyIsoCoker_hom,
    TopModuleCat.cokerπ_cokerCongr_hom]

/-- The differential of the homogeneous cochain complex, applied to an element, is the
differential of the standard resolution (ConcreteCategory-application spelling). -/
lemma homogeneousCochains_d_apply' (X : TopRep k G) (i : ℕ)
    (σ : ↥((homogeneousCochains X).X i)) :
    ((homogeneousCochains X).d i (i + 1) σ : ↥(resolutionX X (i + 1 + 1))) =
      (TopRep.d X (i + 1)).hom σ.1 := by
  rw [TopRep.homogeneousCochains.d_eq]
  rfl

variable (X : TopRep k G) (j : ℕ)

/-- The continuous cohomology class of a kernel-model cocycle, as an additive homomorphism. -/
noncomputable def cocycleClassHom :
    ↥(TopModuleCat.ker ((homogeneousCochains X).d j (j + 1))) →+
      ↥(continuousCohomology j X) :=
  ((ContinuousCohomology.π X j).hom.toLinearMap.toAddMonoidHom).comp
    (((homogeneousCochains X).cyclesIsoKer j (j + 1) (by simp)).inv.hom.toLinearMap.toAddMonoidHom)

/-- The continuous cohomology class of a homogeneous cocycle. -/
noncomputable def cocycleClass (z : ↥((homogeneousCochains X).X j))
    (hz : (homogeneousCochains X).d j (j + 1) z = 0) :
    ↥(continuousCohomology j X) :=
  cocycleClassHom X j ⟨z, LinearMap.mem_ker.2 hz⟩

lemma cocycleClass_eq_π (z : ↥((homogeneousCochains X).X j))
    (hz : (homogeneousCochains X).d j (j + 1) z = 0) :
    cocycleClass X j z hz = ContinuousCohomology.π X j
      (((homogeneousCochains X).cyclesIsoKer j (j + 1) (by simp)).inv
        ⟨z, LinearMap.mem_ker.2 hz⟩) := rfl

lemma cohomologyIsoQuot_hom_cocycleClass (z : ↥((homogeneousCochains X).X j))
    (hz : (homogeneousCochains X).d j (j + 1) z = 0) :
    (cohomologyIsoQuot X j).hom (cocycleClass X j z hz) =
      TopModuleCat.cokerπ (bdryKer X j) ⟨z, LinearMap.mem_ker.2 hz⟩ := by
  have h := congr($(π_comp_cohomologyIsoQuot_hom X j)
    (((homogeneousCochains X).cyclesIsoKer j (j + 1) (by simp)).inv ⟨z, LinearMap.mem_ker.2 hz⟩))
  rw [CategoryTheory.comp_apply, CategoryTheory.comp_apply] at h
  have hcancel := congr($(((homogeneousCochains X).cyclesIsoKer j (j + 1) (by simp)).inv_hom_id)
    (⟨z, LinearMap.mem_ker.2 hz⟩ :
      ↥(TopModuleCat.ker ((homogeneousCochains X).d j (j + 1)))))
  rw [CategoryTheory.comp_apply, CategoryTheory.id_apply] at hcancel
  rw [hcancel] at h
  exact h

@[simp]
lemma cocycleClass_zero :
    cocycleClass X j 0 (by rw [map_zero]) = 0 :=
  map_zero (cocycleClassHom X j)

lemma cocycleClass_add (z₁ z₂ : ↥((homogeneousCochains X).X j))
    (hz₁ : (homogeneousCochains X).d j (j + 1) z₁ = 0)
    (hz₂ : (homogeneousCochains X).d j (j + 1) z₂ = 0) :
    cocycleClass X j (z₁ + z₂) (by rw [map_add, hz₁, hz₂, add_zero]) =
      cocycleClass X j z₁ hz₁ + cocycleClass X j z₂ hz₂ :=
  map_add (cocycleClassHom X j) ⟨z₁, LinearMap.mem_ker.2 hz₁⟩ ⟨z₂, LinearMap.mem_ker.2 hz₂⟩

lemma cocycleClass_neg (z : ↥((homogeneousCochains X).X j))
    (hz : (homogeneousCochains X).d j (j + 1) z = 0) :
    cocycleClass X j (-z) (by rw [map_neg, hz, neg_zero]) = -cocycleClass X j z hz :=
  map_neg (cocycleClassHom X j) ⟨z, LinearMap.mem_ker.2 hz⟩

lemma cocycleClass_sub (z₁ z₂ : ↥((homogeneousCochains X).X j))
    (hz₁ : (homogeneousCochains X).d j (j + 1) z₁ = 0)
    (hz₂ : (homogeneousCochains X).d j (j + 1) z₂ = 0) :
    cocycleClass X j (z₁ - z₂) (by rw [map_sub, hz₁, hz₂, sub_zero]) =
      cocycleClass X j z₁ hz₁ - cocycleClass X j z₂ hz₂ :=
  map_sub (cocycleClassHom X j) ⟨z₁, LinearMap.mem_ker.2 hz₁⟩ ⟨z₂, LinearMap.mem_ker.2 hz₂⟩

lemma cocycleClass_nsmul (n : ℕ) (z : ↥((homogeneousCochains X).X j))
    (hz : (homogeneousCochains X).d j (j + 1) z = 0) :
    cocycleClass X j (n • z) (by rw [map_nsmul, hz, smul_zero]) =
      n • cocycleClass X j z hz :=
  map_nsmul (cocycleClassHom X j) n ⟨z, LinearMap.mem_ker.2 hz⟩

/-- Proof-irrelevance for the cocycle-class construction. -/
lemma cocycleClass_congr {z₁ z₂ : ↥((homogeneousCochains X).X j)}
    (h : z₁ = z₂) (hz₁ : (homogeneousCochains X).d j (j + 1) z₁ = 0) :
    cocycleClass X j z₁ hz₁ = cocycleClass X j z₂ (h ▸ hz₁) := by
  subst h; rfl

/-- Every continuous cohomology class is the class of a cocycle. -/
lemma cocycleClass_surjective (x : ↥(continuousCohomology j X)) :
    ∃ (z : ↥((homogeneousCochains X).X j))
      (hz : (homogeneousCochains X).d j (j + 1) z = 0), cocycleClass X j z hz = x := by
  obtain ⟨y, hy⟩ := TopModuleCat.cokerπ_surjective' (bdryKer X j) ((cohomologyIsoQuot X j).hom x)
  refine ⟨y.1, LinearMap.mem_ker.1 y.2, ?_⟩
  refine TopModuleCat.iso_hom_apply_injective (cohomologyIsoQuot X j) ?_
  change (cohomologyIsoQuot X j).hom _ = (cohomologyIsoQuot X j).hom x
  rw [cohomologyIsoQuot_hom_cocycleClass, ← hy]

/-- A cocycle has trivial class iff it is a coboundary. -/
lemma cocycleClass_eq_zero_iff (z : ↥((homogeneousCochains X).X j))
    (hz : (homogeneousCochains X).d j (j + 1) z = 0) :
    cocycleClass X j z hz = 0 ↔
      ∃ y : ↥((homogeneousCochains X).X (j - 1)),
        (homogeneousCochains X).d (j - 1) j y = z := by
  constructor
  · intro h
    have h2 : TopModuleCat.cokerπ (bdryKer X j) ⟨z, LinearMap.mem_ker.2 hz⟩ = 0 := by
      rw [← cohomologyIsoQuot_hom_cocycleClass X j z hz, h]
      exact (cohomologyIsoQuot X j).hom.hom.map_zero
    rw [TopModuleCat.cokerπ_eq_zero_iff] at h2
    obtain ⟨y, hy⟩ := h2
    exact ⟨y, congr_arg Subtype.val hy⟩
  · rintro ⟨y, hy⟩
    refine TopModuleCat.iso_hom_apply_injective (cohomologyIsoQuot X j) ?_
    change (cohomologyIsoQuot X j).hom _ = (cohomologyIsoQuot X j).hom 0
    rw [cohomologyIsoQuot_hom_cocycleClass]
    have h0 : (cohomologyIsoQuot X j).hom 0 = 0 := (cohomologyIsoQuot X j).hom.hom.map_zero
    rw [h0, TopModuleCat.cokerπ_eq_zero_iff]
    exact ⟨y, Subtype.ext ((bdryKer_apply_coe X j y).trans hy)⟩

/-- The class of a coboundary is trivial. -/
lemma cocycleClass_d (y : ↥((homogeneousCochains X).X j)) :
    cocycleClass X (j + 1) ((homogeneousCochains X).d j (j + 1) y)
      (homogeneousCochains.d_comp_d_apply X j (j + 1) (j + 2) y) = 0 :=
  (cocycleClass_eq_zero_iff X (j + 1) _ _).2 ⟨y, rfl⟩

/-- Two cocycles differing by a coboundary have the same class. -/
lemma cocycleClass_eq_of_sub_coboundary (z₁ z₂ : ↥((homogeneousCochains X).X j))
    (hz₁ : (homogeneousCochains X).d j (j + 1) z₁ = 0)
    (hz₂ : (homogeneousCochains X).d j (j + 1) z₂ = 0)
    (w : ↥((homogeneousCochains X).X (j - 1)))
    (hw : (homogeneousCochains X).d (j - 1) j w = z₁ - z₂) :
    cocycleClass X j z₁ hz₁ = cocycleClass X j z₂ hz₂ := by
  have h := cocycleClass_sub X j z₁ z₂ hz₁ hz₂
  rw [(cocycleClass_eq_zero_iff X j (z₁ - z₂)
    (by rw [map_sub, hz₁, hz₂, sub_zero])).2 ⟨w, hw⟩] at h
  exact (sub_eq_zero.mp h.symm)

end CocycleClass

section MapCocycleClass

variable {H : Type v} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

/-- Element-level naturality of the cochain map with respect to the differentials. -/
lemma cochainsMap_f_d {X : TopRep k G} {Y : TopRep k H} (φ : H →ₜ* G)
    (f : TopRep.res (φ : H →* G) X ⟶ Y) (i : ℕ) (z : ↥((homogeneousCochains X).X i)) :
    (homogeneousCochains Y).d i (i + 1) ((ContinuousCohomology.cochainsMap φ f).f i z) =
      (ContinuousCohomology.cochainsMap φ f).f (i + 1)
        ((homogeneousCochains X).d i (i + 1) z) := by
  have h := congr($((ContinuousCohomology.cochainsMap φ f).comm i (i + 1)) z)
  simpa using h

/-- Under the kernel-model identification, `cyclesIsoKer.inv` recovers the cocycle. -/
lemma iCycles_cyclesIsoKer_inv {X : TopRep k G} (j : ℕ)
    (w : ↥(TopModuleCat.ker ((homogeneousCochains X).d j (j + 1)))) :
    (homogeneousCochains X).iCycles j
      (((homogeneousCochains X).cyclesIsoKer j (j + 1) (by simp)).inv w) = w.1 := by
  have hcancel := congr($(((homogeneousCochains X).cyclesIsoKer j (j + 1) (by simp)).inv_hom_id) w)
  rw [CategoryTheory.comp_apply, CategoryTheory.id_apply] at hcancel
  have h := HomologicalComplex.cyclesIsoKer_hom_apply_coe (homogeneousCochains X) j (j + 1)
    (by simp) (((homogeneousCochains X).cyclesIsoKer j (j + 1) (by simp)).inv w)
  rw [hcancel] at h
  exact h.symm

/-- The functorial map on continuous cohomology sends the class of a cocycle to the class of
the mapped cocycle. -/
lemma map_cocycleClass {X : TopRep k G} {Y : TopRep k H} (φ : H →ₜ* G)
    (f : TopRep.res (φ : H →* G) X ⟶ Y) (j : ℕ)
    (z : ↥((homogeneousCochains X).X j)) (hz : (homogeneousCochains X).d j (j + 1) z = 0) :
    ContinuousCohomology.map φ f j (cocycleClass X j z hz) =
      cocycleClass Y j ((ContinuousCohomology.cochainsMap φ f).f j z)
        (by rw [cochainsMap_f_d, hz, map_zero]) := by
  rw [cocycleClass_eq_π, cocycleClass_eq_π]
  have hπ := congr($(ContinuousCohomology.π_map φ f j)
    (((homogeneousCochains X).cyclesIsoKer j (j + 1) (by simp)).inv ⟨z, LinearMap.mem_ker.2 hz⟩))
  rw [CategoryTheory.comp_apply, CategoryTheory.comp_apply] at hπ
  rw [hπ]
  congr 1
  -- It remains to identify the two cocycles; compare through the kernel model.
  refine TopModuleCat.iso_hom_apply_injective
    (((homogeneousCochains Y).cyclesIsoKer j (j + 1) (by simp))) (Subtype.ext ?_)
  change (((homogeneousCochains Y).cyclesIsoKer j (j + 1) (by simp)).hom _).1 =
    (((homogeneousCochains Y).cyclesIsoKer j (j + 1) (by simp)).hom _).1
  rw [HomologicalComplex.cyclesIsoKer_hom_apply_coe, HomologicalComplex.cyclesIsoKer_hom_apply_coe]
  have hmi := congr($(HomologicalComplex.cyclesMap_i (ContinuousCohomology.cochainsMap φ f) j)
    (((homogeneousCochains X).cyclesIsoKer j (j + 1) (by simp)).inv ⟨z, LinearMap.mem_ker.2 hz⟩))
  rw [CategoryTheory.comp_apply, CategoryTheory.comp_apply] at hmi
  rw [hmi, iCycles_cyclesIsoKer_inv, iCycles_cyclesIsoKer_inv]

end MapCocycleClass

end ContRepresentation

/-- Postcomposition with a continuous additive equivalence, as a continuous additive
equivalence between spaces of continuous maps. -/
def ContinuousAddEquiv.arrowCongrRight {A B : Type w} [AddCommGroup A] [AddCommGroup B]
    [TopologicalSpace A] [TopologicalSpace B] [IsTopologicalAddGroup A]
    [IsTopologicalAddGroup B] (α : Type v) [TopologicalSpace α] (e : A ≃ₜ+ B) :
    C(α, A) ≃ₜ+ C(α, B) where
  toFun f := (ContinuousMap.mk ⇑e e.toHomeomorph.continuous).comp f
  invFun f := (ContinuousMap.mk ⇑e.symm e.symm.toHomeomorph.continuous).comp f
  left_inv f := by ext x; simp
  right_inv f := by ext x; simp
  map_add' f g := by ext x; simp
  continuous_toFun := ContinuousMap.continuous_postcomp _
  continuous_invFun := ContinuousMap.continuous_postcomp _

@[simp]
lemma ContinuousAddEquiv.arrowCongrRight_apply {A B : Type w} [AddCommGroup A] [AddCommGroup B]
    [TopologicalSpace A] [TopologicalSpace B] [IsTopologicalAddGroup A]
    [IsTopologicalAddGroup B] {α : Type v} [TopologicalSpace α] (e : A ≃ₜ+ B) (f : C(α, A))
    (x : α) : e.arrowCongrRight α f x = e (f x) := rfl

namespace TopRep

variable {k : Type u} {G : Type v} [CommRing k] [TopologicalSpace k] [Group G]

/-- The `ℤ`-scalar restriction of a topological representation: the same carrier with the same
`G`-action, viewed as a representation over `ℤ`. -/
noncomputable def toInt (X : TopRep k G) : TopRep ℤ G :=
  TopRep.of (X := ↥X)
    { toMonoidHom :=
      { toFun g :=
          { toLinearMap := (X.ρ g).toLinearMap.toAddMonoidHom.toIntLinearMap
            cont := (X.ρ g).cont }
        map_one' := by ext x; exact congr($(map_one X.ρ) x)
        map_mul' g₁ g₂ := by ext x; exact congr($(map_mul X.ρ g₁ g₂) x) } }

@[simp]
lemma toInt_ρ_apply (X : TopRep k G) (g : G) (x : ↥X) :
    (toInt X).ρ g x = X.ρ g x := rfl

instance (X : TopRep k G) [DiscreteTopology ↥X] : DiscreteTopology ↥(toInt X) :=
  inferInstanceAs (DiscreteTopology ↥X)

instance (X : TopRep k G) [Finite ↥X] : Finite ↥(toInt X) :=
  inferInstanceAs (Finite ↥X)

/-- `ℤ`-scalar restriction commutes with restriction along a group homomorphism. -/
lemma res_toInt {H : Type v} [Group H] (φ : H →* G) (X : TopRep k G) :
    res φ (toInt X) = toInt (res φ X) := rfl

variable [TopologicalSpace G] [IsTopologicalGroup G]

/-- The levels of the standard resolutions of `X` and of its `ℤ`-scalar restriction are
canonically identified. -/
noncomputable def toIntResolutionEquiv (X : TopRep k G) :
    (i : ℕ) → ↥(resolutionX (toInt X) i) ≃ₜ+ ↥(resolutionX X i)
  | 0 => ContinuousAddEquiv.refl _
  | i + 1 => (toIntResolutionEquiv X i).arrowCongrRight G

@[simp]
lemma toIntResolutionEquiv_zero_apply (X : TopRep k G) (y : ↥(resolutionX (toInt X) 0)) :
    toIntResolutionEquiv X 0 y = y := rfl

@[simp]
lemma toIntResolutionEquiv_succ_apply (X : TopRep k G) (i : ℕ)
    (y : ↥(resolutionX (toInt X) (i + 1))) (x : G) :
    toIntResolutionEquiv X (i + 1) y x = toIntResolutionEquiv X i (y x) := rfl

/-- The resolution-level identification is `G`-equivariant. -/
lemma toIntResolutionEquiv_ρ (X : TopRep k G) :
    ∀ (i : ℕ) (g : G) (y : ↥(resolutionX (toInt X) i)),
      toIntResolutionEquiv X i ((resolutionX (toInt X) i).ρ g y) =
        (resolutionX X i).ρ g (toIntResolutionEquiv X i y)
  | 0, g, y => rfl
  | i + 1, g, y => by
      ext x
      exact toIntResolutionEquiv_ρ X i g (y (g⁻¹ * x))

/-- The resolution-level identification commutes with the differentials. -/
lemma toIntResolutionEquiv_d (X : TopRep k G) :
    ∀ (i : ℕ) (y : ↥(resolutionX (toInt X) i)),
      toIntResolutionEquiv X (i + 1) ((d (toInt X) i).hom y) =
        (d X i).hom (toIntResolutionEquiv X i y)
  | 0, y => by
      ext x
      rw [ContRepresentation.d_hom_zero, ContRepresentation.d_hom_zero]
      rfl
  | i + 1, y => by
      ext x
      rw [toIntResolutionEquiv_succ_apply, ContRepresentation.d_hom_succ_apply,
        ContRepresentation.d_hom_succ_apply, map_sub, toIntResolutionEquiv_d X i (y x)]
      rfl

/-- The homogeneous cochains of `X` and of its `ℤ`-scalar restriction are canonically
identified as additive groups. -/
noncomputable def toIntCochainEquiv (X : TopRep k G) (i : ℕ) :
    ↥((homogeneousCochains (toInt X)).X i) ≃+ ↥((homogeneousCochains X).X i) where
  toFun σ := ⟨toIntResolutionEquiv X (i + 1) σ.1, fun g ↦ by
    rw [← toIntResolutionEquiv_ρ, σ.2 g]⟩
  invFun σ := ⟨(toIntResolutionEquiv X (i + 1)).symm σ.1, fun g ↦ by
    apply (toIntResolutionEquiv X (i + 1)).injective
    rw [toIntResolutionEquiv_ρ, ContinuousAddEquiv.apply_symm_apply]
    exact σ.2 g⟩
  left_inv σ := Subtype.ext ((toIntResolutionEquiv X (i + 1)).symm_apply_apply σ.1)
  right_inv σ := Subtype.ext ((toIntResolutionEquiv X (i + 1)).apply_symm_apply σ.1)
  map_add' σ τ := Subtype.ext (map_add (toIntResolutionEquiv X (i + 1)) σ.1 τ.1)

@[simp]
lemma toIntCochainEquiv_coe (X : TopRep k G) (i : ℕ)
    (σ : ↥((homogeneousCochains (toInt X)).X i)) :
    (toIntCochainEquiv X i σ : ↥(resolutionX X (i + 1))) =
      toIntResolutionEquiv X (i + 1) σ.1 := rfl

@[simp]
lemma toIntCochainEquiv_symm_coe (X : TopRep k G) (i : ℕ)
    (σ : ↥((homogeneousCochains X).X i)) :
    ((toIntCochainEquiv X i).symm σ : ↥(resolutionX (toInt X) (i + 1))) =
      (toIntResolutionEquiv X (i + 1)).symm σ.1 := rfl

/-- The cochain-level identification commutes with the differentials. -/
lemma toIntCochainEquiv_d (X : TopRep k G) (i : ℕ)
    (σ : ↥((homogeneousCochains (toInt X)).X i)) :
    (homogeneousCochains X).d i (i + 1) (toIntCochainEquiv X i σ) =
      toIntCochainEquiv X (i + 1) ((homogeneousCochains (toInt X)).d i (i + 1) σ) := by
  refine Subtype.ext ?_
  rw [ContRepresentation.homogeneousCochains_d_apply', toIntCochainEquiv_coe,
    toIntCochainEquiv_coe, ContRepresentation.homogeneousCochains_d_apply']
  exact (toIntResolutionEquiv_d X (i + 1) σ.1).symm

/-- The cochain-level identification commutes with the differentials, `symm` version. -/
lemma toIntCochainEquiv_symm_d (X : TopRep k G) (i : ℕ)
    (σ : ↥((homogeneousCochains X).X i)) :
    (homogeneousCochains (toInt X)).d i (i + 1) ((toIntCochainEquiv X i).symm σ) =
      (toIntCochainEquiv X (i + 1)).symm ((homogeneousCochains X).d i (i + 1) σ) := by
  apply (toIntCochainEquiv X (i + 1)).injective
  rw [← toIntCochainEquiv_d, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]

/-- The cochain-level identification commutes with the restriction maps. -/
lemma toIntResolutionEquiv_resolutionMap {H : Type v} [Group H] [TopologicalSpace H]
    [IsTopologicalGroup H] (φ : H →ₜ* G) (X : TopRep k G) :
    ∀ (i : ℕ) (y : ↥(resolutionX (toInt X) i)),
      toIntResolutionEquiv (res (φ : H →* G) X) i
          ((ContinuousCohomology.resolutionMap φ (𝟙 (res (φ : H →* G) (toInt X))) i).hom y) =
        (ContinuousCohomology.resolutionMap φ (𝟙 (res (φ : H →* G) X)) i).hom
          (toIntResolutionEquiv X i y)
  | 0, y => rfl
  | i + 1, y => by
      ext x
      exact toIntResolutionEquiv_resolutionMap φ X i (y (φ x))

/-- The cochain-level identification commutes with `cochainsMap` along a continuous group
homomorphism (with identity coefficients). -/
lemma toIntCochainEquiv_cochainsMap {H : Type v} [Group H] [TopologicalSpace H]
    [IsTopologicalGroup H] (φ : H →ₜ* G) (X : TopRep k G) (i : ℕ)
    (σ : ↥((homogeneousCochains (toInt X)).X i)) :
    toIntCochainEquiv (res (φ : H →* G) X) i
        ((ContinuousCohomology.cochainsMap φ (𝟙 (res (φ : H →* G) (toInt X)))).f i σ) =
      (ContinuousCohomology.cochainsMap φ (𝟙 (res (φ : H →* G) X))).f i
        (toIntCochainEquiv X i σ) := by
  refine Subtype.ext ?_
  exact toIntResolutionEquiv_resolutionMap φ X (i + 1) σ.1

/-- The cochain-level identification commutes with `cochainsMap`, `symm` version. -/
lemma toIntCochainEquiv_symm_cochainsMap {H : Type v} [Group H] [TopologicalSpace H]
    [IsTopologicalGroup H] (φ : H →ₜ* G) (X : TopRep k G) (i : ℕ)
    (σ : ↥((homogeneousCochains X).X i)) :
    (ContinuousCohomology.cochainsMap φ (𝟙 (res (φ : H →* G) (toInt X)))).f i
        ((toIntCochainEquiv X i).symm σ) =
      (toIntCochainEquiv (res (φ : H →* G) X) i).symm
        ((ContinuousCohomology.cochainsMap φ (𝟙 (res (φ : H →* G) X))).f i σ) := by
  apply (toIntCochainEquiv (res (φ : H →* G) X) i).injective
  rw [toIntCochainEquiv_cochainsMap, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]

/-- Cochains valued in an `n`-torsion module are `n`-torsion. -/
lemma nsmul_resolutionX_eq_zero (X : TopRep ℤ G) (n : ℕ) (hX : ∀ x : ↥X, n • x = 0) :
    ∀ (i : ℕ) (y : ↥(resolutionX X i)), n • y = 0
  | 0, y => hX y
  | i + 1, y => by
      ext x
      have h := nsmul_resolutionX_eq_zero X n hX i (y x)
      simpa using h

/-- Homogeneous cochains valued in an `n`-torsion module are `n`-torsion. -/
lemma nsmul_homogeneousCochains_eq_zero (X : TopRep ℤ G) (n : ℕ)
    (hX : ∀ x : ↥X, n • x = 0) (i : ℕ) (σ : ↥((homogeneousCochains X).X i)) :
    n • σ = 0 := by
  refine Subtype.ext ?_
  simpa using nsmul_resolutionX_eq_zero X n hX (i + 1) σ.1

end TopRep

namespace ContRepresentation

section CupRes

open TopRep TopCup

variable {k : Type u} {G H : Type v} [CommRing k] [TopologicalSpace k] [Group G] [Group H]
  [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace H] [IsTopologicalGroup H]

variable {M1 M2 M3 M3' : Type v}
  [AddCommGroup M1] [Module k M1] [TopologicalSpace M1] [IsTopologicalAddGroup M1]
  [ContinuousSMul k M1]
  [AddCommGroup M2] [Module k M2] [TopologicalSpace M2] [IsTopologicalAddGroup M2]
  [ContinuousSMul k M2]
  [AddCommGroup M3] [Module k M3] [TopologicalSpace M3] [IsTopologicalAddGroup M3]
  [ContinuousSMul k M3]
  [AddCommGroup M3'] [Module k M3'] [TopologicalSpace M3'] [IsTopologicalAddGroup M3']
  [ContinuousSMul k M3']
  {ρ1 : ContRepresentation k G M1} {ρ2 : ContRepresentation k G M2}
  {ρ3 : ContRepresentation k G M3} {ρ3' : ContRepresentation k H M3'}
  (φ : H →ₜ* G)
  (c3 : TopRep.res (φ : H →* G) (.of ρ3) ⟶ .of ρ3')

/-- Restriction maps commute with index transport along the standard resolutions. -/
lemma resolutionMap_hom_resolutionXCast {X : TopRep k G} {Y : TopRep k H}
    (c : TopRep.res (φ : H →* G) X ⟶ Y) {i j : ℕ} (h : i = j) (y : ↥(resolutionX X i)) :
    (ContinuousCohomology.resolutionMap φ c j).hom (resolutionXCast X h y) =
      resolutionXCast Y h ((ContinuousCohomology.resolutionMap φ c i).hom y) := by
  subst h; rfl

/-- Restriction commutes with the functorial extension `resolutionCLM` of a continuous linear
map, given a pointwise compatibility of the coefficient morphisms. -/
lemma resolutionMap_resolutionCLM (u : M2 →L[k] M3) (u' : M2 →L[k] M3')
    (hu : ∀ w : M2, c3.hom (u w) = u' w) :
    ∀ (i : ℕ) (y : ↥(resolutionX (.of ρ2) i)),
      (ContinuousCohomology.resolutionMap φ c3 i).hom (resolutionCLM ρ2 ρ3 u i y) =
        resolutionCLM (ρ2.restrict (φ : H →* G)) ρ3' u' i
          ((ContinuousCohomology.resolutionMap φ
            (𝟙 (TopRep.res (φ : H →* G) (.of ρ2))) i).hom y)
  | 0, y => hu y
  | i + 1, y => by
      ext x
      exact resolutionMap_resolutionCLM u u' hu i (y (φ x))

variable [DiscreteTopology M1]
variable (f : ρ1 →ⁱL linHom ρ2 ρ3)
  (f' : ρ1.restrict (φ : H →* G) →ⁱL linHom (ρ2.restrict (φ : H →* G)) ρ3')
  (hc : ∀ (v : M1) (w : M2), c3.hom (f v w) = f' v w)

include hc in
/-- Restriction commutes with the cup-product pairing on the levels of the standard
resolutions. -/
lemma resolutionMap_cupPair :
    ∀ (m n : ℕ) (σ : ↥(resolutionX (.of ρ1) (m + 1)))
      (τ : ↥(resolutionX (.of ρ2) (n + 1))),
      (ContinuousCohomology.resolutionMap φ c3 (n + 1 + m)).hom ((cupPair f n m).1 σ τ) =
        (cupPair f' n m).1
          ((ContinuousCohomology.resolutionMap φ
            (𝟙 (TopRep.res (φ : H →* G) (.of ρ1))) (m + 1)).hom σ)
          ((ContinuousCohomology.resolutionMap φ
            (𝟙 (TopRep.res (φ : H →* G) (.of ρ2))) (n + 1)).hom τ)
  | 0, n, σ, τ => by
      ext x
      exact resolutionMap_resolutionCLM φ c3 (f (σ (φ x))) (f' (σ (φ x))) (hc (σ (φ x))) n
        (τ (φ x))
  | m + 1, n, σ, τ => by
      ext x
      exact resolutionMap_cupPair m n (σ (φ x)) τ

/-- The cochain-level cup product is additive in the first slot (subtraction form). -/
lemma cupCochain_sub_left' {ρ1 : ContRepresentation k G M1} {ρ2 : ContRepresentation k G M2}
    {ρ3 : ContRepresentation k G M3} (e : ρ1 →ⁱL linHom ρ2 ρ3) (m n r : ℕ) (hr : r = m + n)
    (σ₁ σ₂ : ↥((homogeneousCochains (.of ρ1)).X m))
    (τ : ↥((homogeneousCochains (.of ρ2)).X n)) :
    cupCochain e m n r hr (σ₁ - σ₂) τ =
      cupCochain e m n r hr σ₁ τ - cupCochain e m n r hr σ₂ τ :=
  congr($((cupCochain e m n r hr).hom.map_sub σ₁ σ₂) τ)

/-- The cochain-level cup product is additive in the first slot. -/
lemma cupCochain_add_left' {ρ1 : ContRepresentation k G M1} {ρ2 : ContRepresentation k G M2}
    {ρ3 : ContRepresentation k G M3} (e : ρ1 →ⁱL linHom ρ2 ρ3) (m n r : ℕ) (hr : r = m + n)
    (σ₁ σ₂ : ↥((homogeneousCochains (.of ρ1)).X m))
    (τ : ↥((homogeneousCochains (.of ρ2)).X n)) :
    cupCochain e m n r hr (σ₁ + σ₂) τ =
      cupCochain e m n r hr σ₁ τ + cupCochain e m n r hr σ₂ τ :=
  congr($((cupCochain e m n r hr).hom.map_add σ₁ σ₂) τ)

/-- The cochain-level cup product is additive in the second slot (subtraction form). -/
lemma cupCochain_sub_right' {ρ1 : ContRepresentation k G M1} {ρ2 : ContRepresentation k G M2}
    {ρ3 : ContRepresentation k G M3} (e : ρ1 →ⁱL linHom ρ2 ρ3) (m n r : ℕ) (hr : r = m + n)
    (σ : ↥((homogeneousCochains (.of ρ1)).X m))
    (τ₁ τ₂ : ↥((homogeneousCochains (.of ρ2)).X n)) :
    cupCochain e m n r hr σ (τ₁ - τ₂) =
      cupCochain e m n r hr σ τ₁ - cupCochain e m n r hr σ τ₂ :=
  map_sub (cupCochain e m n r hr σ : ↥((homogeneousCochains (.of ρ2)).X n) →L[k]
    ↥((homogeneousCochains (.of ρ3)).X r)) τ₁ τ₂

/-- The cochain-level cup product is additive in the second slot. -/
lemma cupCochain_add_right' {ρ1 : ContRepresentation k G M1} {ρ2 : ContRepresentation k G M2}
    {ρ3 : ContRepresentation k G M3} (e : ρ1 →ⁱL linHom ρ2 ρ3) (m n r : ℕ) (hr : r = m + n)
    (σ : ↥((homogeneousCochains (.of ρ1)).X m))
    (τ₁ τ₂ : ↥((homogeneousCochains (.of ρ2)).X n)) :
    cupCochain e m n r hr σ (τ₁ + τ₂) =
      cupCochain e m n r hr σ τ₁ + cupCochain e m n r hr σ τ₂ :=
  map_add (cupCochain e m n r hr σ : ↥((homogeneousCochains (.of ρ2)).X n) →L[k]
    ↥((homogeneousCochains (.of ρ3)).X r)) τ₁ τ₂

include hc in
/-- Restriction along `φ : H →ₜ* G` (with a coefficient morphism `c3` on the target slot)
commutes with the cochain-level cup product `cupCochain`. -/
lemma cochainsMap_cupCochain (m n r : ℕ) (hr : r = m + n)
    (σ : ↥((homogeneousCochains (.of ρ1)).X m)) (τ : ↥((homogeneousCochains (.of ρ2)).X n)) :
    (ContinuousCohomology.cochainsMap φ c3).f r (cupCochain f m n r hr σ τ) =
      cupCochain f' m n r hr
        ((ContinuousCohomology.cochainsMap φ (𝟙 (TopRep.res (φ : H →* G) (.of ρ1)))).f m σ)
        ((ContinuousCohomology.cochainsMap φ (𝟙 (TopRep.res (φ : H →* G) (.of ρ2)))).f n τ) := by
  refine Subtype.ext ?_
  have hl : (((ContinuousCohomology.cochainsMap φ c3).f r (cupCochain f m n r hr σ τ)) :
      ↥(resolutionX (.of ρ3') (r + 1))) =
      (ContinuousCohomology.resolutionMap φ c3 (r + 1)).hom
        ((cupCochain f m n r hr σ τ) : ↥(resolutionX (.of ρ3) (r + 1))) := rfl
  rw [hl, cupCochain_coe, cupCochain_coe, resolutionMap_hom_resolutionXCast,
    resolutionMap_cupPair φ c3 f f' hc]
  rfl

end CupRes

end ContRepresentation
