/-
Copyright (c) 2026 Y. Samanda Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Y. Samanda Zhang
-/
module

public import Mathlib

/-!
# Conjugation acts trivially on continuous cohomology

For a topological group `G`, an element `g : G` and a topological representation `X` of `G`,
conjugation by `g` (with coefficients twisted by `ρ g⁻¹`) induces the identity on continuous
cohomology `Hⁿ(G, X)`. More generally, for a continuous homomorphism `φ : H →ₜ* G`, the map on
continuous cohomology induced by `conj g ∘ φ` (with the coefficient twist) agrees with the map
induced by `φ`; this is proved in `LocalGlobalMaps.lean` from the core result here.

## Strategy

Mathlib computes continuous cohomology from homogeneous cochains: `G`-invariant elements of the
iterated function spaces `C(G, C(G, ⋯, C(G, M)))`. On an invariant cochain, the conjugation map
`σ ↦ ρ(g⁻¹) ∘ σ ∘ conj g` simplifies (using invariance under the action of `g`) to *right
translation of every argument by `g⁻¹`*, the chain map `resolutionRightTrans` below. Right
translation is chain-homotopic to the identity via the classical prism homotopy
`(hσ)(x₁, …, xₙ) = Σᵢ (−1)^(i−1) σ(x₁, …, xᵢ, xᵢg⁻¹, x₍ᵢ₊₁₎g⁻¹, …, xₙg⁻¹)`
(`prismQ` below, in curried inductive form), and homotopic chain maps induce equal maps on
homology.

The prism formula duplicates a variable, which in curried form is the diagonal evaluation
`τ ↦ (x ↦ τ x (x * g⁻¹))`; evaluation on `C(G, V)` is only continuous for locally compact `G`,
whence the `[LocallyCompactSpace G]` hypothesis on the main results. In the intended application
`G` is a profinite Galois group, hence locally compact.

## Main declarations

* `NumberField.PoitouTate.conjCMHom g` — conjugation by `g` as a continuous monoid homomorphism.
* `NumberField.PoitouTate.conjResHom X φ g` — the coefficient intertwiner `ρ g⁻¹` from the
  restriction of `X` along `conj g ∘ φ` to its restriction along `φ`.
* `NumberField.PoitouTate.continuousCohomology_map_conj_id` — the core result: the map on
  continuous cohomology induced by `(conjCMHom g, conjResHomId X g)` is the identity.
-/

@[expose] public section

universe u v

open CategoryTheory ContRepresentation TopRep

namespace NumberField.PoitouTate

variable {k : Type u} [Ring k] [TopologicalSpace k]
variable {G H : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

set_option allowUnsafeReducibility true in
attribute [local reducible] CategoryTheory.Functor.mapHomologicalComplex

/-- Conjugation by `g` as a continuous monoid homomorphism. -/
def conjCMHom (g : G) : G →ₜ* G where
  __ := (MulAut.conj g).toMonoidHom
  continuous_toFun := (continuous_const.mul continuous_id).mul continuous_const

/-- The coefficient intertwiner for conjugation invariance: `ρ g⁻¹` intertwines the
restriction of `X` along `conj g ∘ φ` with its restriction along `φ`. -/
def conjResHom (X : TopRep k G) (φ : H →ₜ* G) (g : G) :
    TopRep.res (((conjCMHom g).comp φ : H →ₜ* G) : H →* G) X ⟶
      TopRep.res (φ : H →* G) X :=
  TopRep.ofHom
    { toContinuousLinearMap := X.ρ g⁻¹
      isIntertwining' := fun h => by
        ext x
        change (X.ρ g⁻¹ * X.ρ (g * φ h * g⁻¹)) x = (X.ρ (φ h) * X.ρ g⁻¹) x
        rw [← map_mul, ← map_mul]
        congr 2
        group }

/-- The `φ = id` special case of `conjResHom`: `ρ g⁻¹` intertwines the restriction of `X`
along `conj g` with `X` itself. -/
def conjResHomId (X : TopRep k G) (g : G) :
    TopRep.res ((conjCMHom g : G →ₜ* G) : G →* G) X ⟶ X :=
  TopRep.ofHom
    { toContinuousLinearMap := X.ρ g⁻¹
      isIntertwining' := fun s => by
        ext x
        change (X.ρ g⁻¹ * X.ρ (g * s * g⁻¹)) x = (X.ρ s * X.ρ g⁻¹) x
        rw [← map_mul, ← map_mul]
        congr 2
        group }

omit [IsTopologicalGroup H] in
lemma conjResHom_eq (X : TopRep k G) (φ : H →ₜ* G) (g : G) :
    conjResHom X φ g =
      (TopRep.resFunctor (φ : H →* G)).map (conjResHomId X g) ≫
        𝟙 (TopRep.res (φ : H →* G) X) :=
  rfl

section RightTranslation

variable {V : Type*} [AddCommGroup V] [Module k V] [TopologicalSpace V]
  [IsTopologicalAddGroup V] [ContinuousSMul k V]

/-- Right translation of the argument by `g⁻¹`, applying a given self-intertwiner `f` of `π` to
the values, as a self-intertwiner of the coinduced representation on `C(G, V)`. Decurried over
the standard resolution, this translates every argument of a homogeneous cochain on the right by
`g⁻¹`. -/
def coind₁RightTrans (g : G) {π : ContRepresentation k G V} (f : π →ⁱL π) :
    π.coind₁ →ⁱL π.coind₁ where
  toFun F := (f : ContinuousMap _ _).comp (F.comp (ContinuousMap.mulRight g⁻¹))
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp
  cont := (ContinuousMap.continuous_postcomp _).comp (ContinuousMap.continuous_precomp _)
  isIntertwining' s := by
    ext F x
    change f (π.coind₁ s F (x * g⁻¹)) = π.coind₁ s ((f : ContinuousMap _ _).comp
      (F.comp (ContinuousMap.mulRight g⁻¹))) x
    rw [coind₁_apply_apply, coind₁_apply_apply, f.isIntertwining]
    simp [mul_assoc]

@[simp]
lemma coind₁RightTrans_apply (g : G) {π : ContRepresentation k G V} (f : π →ⁱL π)
    (F : C(G, V)) (x : G) : coind₁RightTrans g f F x = f (F (x * g⁻¹)) := rfl

end RightTranslation

variable (X : TopRep k G) (g : G)

/-- Right translation by `g⁻¹` in every argument, levelwise on the standard resolution. -/
def resolutionRightTrans : (n : ℕ) → (resolutionX X n ⟶ resolutionX X n)
  | 0 => 𝟙 X
  | n + 1 => TopRep.ofHom (coind₁RightTrans g (resolutionRightTrans n).hom)

@[simp]
lemma resolutionRightTrans_zero : resolutionRightTrans X g 0 = 𝟙 X := rfl

lemma resolutionRightTrans_succ_apply (n : ℕ) (F : C(G, (resolutionX X n).V)) (x : G) :
    (resolutionRightTrans X g (n + 1)).hom F x =
      (resolutionRightTrans X g n).hom (F (x * g⁻¹)) := rfl

/-- Pointwise form of the differential in positive degrees. -/
lemma d_succ_apply (m : ℕ) (F : C(G, (resolutionX X m).V)) (x : G) :
    (TopRep.d X (m + 1)).hom F x = F - (TopRep.d X m).hom (F x) := rfl

lemma resolutionRightTrans_zero_apply (v : X) : (resolutionRightTrans X g 0).hom v = v := rfl

lemma d_zero_apply (v : X) (y : G) : (TopRep.d X 0).hom v y = v := rfl

/-- Right translation commutes with the differential of the standard resolution. -/
lemma d_comp_resolutionRightTrans (n : ℕ) :
    TopRep.d X n ≫ resolutionRightTrans X g (n + 1) =
      resolutionRightTrans X g n ≫ TopRep.d X n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    refine TopRep.hom_ext (ContIntertwiningMap.ext (ContinuousLinearMap.ext fun F =>
      ContinuousMap.ext fun x => ?_))
    change (resolutionRightTrans X g (n + 2)).hom ((TopRep.d X (n + 1)).hom F) x =
      (TopRep.d X (n + 1)).hom ((resolutionRightTrans X g (n + 1)).hom F) x
    have ih' : (resolutionRightTrans X g (n + 1)).hom ((TopRep.d X n).hom (F (x * g⁻¹))) =
        (TopRep.d X n).hom ((resolutionRightTrans X g n).hom (F (x * g⁻¹))) :=
      congr($(ih).hom (F (x * g⁻¹)))
    rw [resolutionRightTrans_succ_apply, d_succ_apply, d_succ_apply, map_sub, ih',
      resolutionRightTrans_succ_apply]

/-- Right translation as an endomorphism of the (shifted) standard resolution. -/
def resolution'RightTrans : resolution' X ⟶ resolution' X where
  f n := resolutionRightTrans X g (n + 1)
  comm' i j hij := by
    obtain rfl : j = i + 1 := hij.symm
    have hd : (resolution' X).d i (i + 1) = TopRep.d X (i + 1) :=
      (CochainComplex.of_d _ _ i).trans (resolution'd_eq X i)
    rw [hd]
    exact (d_comp_resolutionRightTrans X g (i + 1)).symm

/-- On the resolution, the map induced by conjugation (with the `ρ g⁻¹` coefficient twist)
is the action of `g⁻¹` followed by right translation. -/
lemma resolutionMap_conj (n : ℕ) :
    ContinuousCohomology.resolutionMap (conjCMHom g) (conjResHomId X g) n =
      conjResHomId (resolutionX X n) g ≫ resolutionRightTrans X g n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    ext F x
    change (ContinuousCohomology.resolutionMap (conjCMHom g) (conjResHomId X g) n).hom
        (F (conjCMHom g x)) =
      (resolutionRightTrans X g (n + 1)).hom ((resolutionX X (n + 1)).ρ g⁻¹ F) x
    rw [congr($(ih).hom (F (conjCMHom g x))), resolutionRightTrans_succ_apply]
    change (resolutionRightTrans X g n).hom ((resolutionX X n).ρ g⁻¹ (F (g * x * g⁻¹))) =
      (resolutionRightTrans X g n).hom (((resolutionX X n).ρ.coind₁ g⁻¹ F) (x * g⁻¹))
    rw [coind₁_apply_apply, inv_inv, mul_assoc]

/-- On invariants, the `ρ g⁻¹` twist is trivial. -/
lemma invariantsResMap_conjResHomId (A : TopRep k G) :
    TopRep.invariantsResMap ((conjCMHom g : G →ₜ* G) : G →* G) (conjResHomId A g) =
      𝟙 A.invariants := by
  ext σ
  change A.ρ g⁻¹ σ.1 = σ.1
  exact σ.2 g⁻¹

/-- On homogeneous cochains, the conjugation map is right translation. -/
lemma cochainsMap_conj_eq :
    ContinuousCohomology.cochainsMap (conjCMHom g) (conjResHomId X g) =
      ((TopRep.invariantsFunctor k G).mapHomologicalComplex _).map (resolution'RightTrans X g) := by
  ext i : 1
  have hf : (((TopRep.invariantsFunctor k G).mapHomologicalComplex _).map
        (resolution'RightTrans X g)).f i =
      (TopRep.invariantsFunctor k G).map (resolutionRightTrans X g (i + 1)) := rfl
  rw [hf, ContinuousCohomology.cochainsMap_f, resolutionMap_conj, TopRep.invariantsResMap_comp,
    invariantsResMap_conjResHomId, Category.id_comp]

section Prism

variable [LocallyCompactSpace G]

/-- Diagonal evaluation `τ ↦ (x ↦ τ x (x * g⁻¹))` as a continuous linear map; this is where
local compactness of `G` is needed. -/
def diagEvalCLM (g : G) {V : Type*} [AddCommGroup V] [Module k V] [TopologicalSpace V]
    [IsTopologicalAddGroup V] [ContinuousSMul k V] :
    C(G, C(G, V)) →L[k] C(G, V) where
  toFun τ := τ.uncurry.comp ⟨fun x => (x, x * g⁻¹), by fun_prop⟩
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp
  cont := (ContinuousMap.continuous_precomp _).comp ContinuousMap.continuous_uncurry

@[simp]
lemma diagEvalCLM_apply (g : G) {V : Type*} [AddCommGroup V] [Module k V] [TopologicalSpace V]
    [IsTopologicalAddGroup V] [ContinuousSMul k V] (τ : C(G, C(G, V))) (x : G) :
    diagEvalCLM (k := k) g τ x = τ x (x * g⁻¹) := rfl

/-- The prism homotopy, in curried inductive form: decurried,
`(prismQ (n+1) σ)(x₁, …, x₍ₙ₊₁₎) = Σᵢ (−1)^(i−1) σ(x₁, …, xᵢ, xᵢg⁻¹, …, x₍ₙ₊₁₎g⁻¹)`. -/
def prismQ : (n : ℕ) → (resolutionX X (n + 1) ⟶ resolutionX X n)
  | 0 => 0
  | n + 1 => TopRep.ofHom
      { toContinuousLinearMap :=
          (ContinuousLinearMap.compLeftContinuous k G
              (resolutionRightTrans X g n).hom.toContinuousLinearMap).comp (diagEvalCLM g)
            - ContinuousLinearMap.compLeftContinuous k G
                (prismQ n).hom.toContinuousLinearMap
        isIntertwining' := fun s => by
          refine ContinuousLinearMap.ext fun τ => ContinuousMap.ext fun x => ?_
          change (resolutionRightTrans X g n).hom
                (((resolutionX X (n + 1)).ρ.coind₁ s τ) x (x * g⁻¹)) -
              (prismQ n).hom (((resolutionX X (n + 1)).ρ.coind₁ s τ) x) =
            (resolutionX X n).ρ s
              ((resolutionRightTrans X g n).hom (τ (s⁻¹ * x) (s⁻¹ * x * g⁻¹)) -
                (prismQ n).hom (τ (s⁻¹ * x)))
          rw [coind₁_apply_apply]
          change (resolutionRightTrans X g n).hom
                (((resolutionX X n).ρ.coind₁ s (τ (s⁻¹ * x))) (x * g⁻¹)) -
              (prismQ n).hom ((resolutionX X (n + 1)).ρ s (τ (s⁻¹ * x))) = _
          rw [coind₁_apply_apply, TopRep.hom_comm_apply (resolutionRightTrans X g n) s,
            TopRep.hom_comm_apply (prismQ n) s, ← map_sub, mul_assoc] }

@[simp]
lemma prismQ_zero : prismQ X g 0 = 0 := rfl

lemma prismQ_succ_apply (n : ℕ) (τ : C(G, (resolutionX X (n + 1)).V)) (x : G) :
    (prismQ X g (n + 1)).hom τ x =
      (resolutionRightTrans X g n).hom (τ x (x * g⁻¹)) - (prismQ X g n).hom (τ x) := rfl

lemma prismQ_zero_apply (v : C(G, X.V)) : (prismQ X g 0).hom v = 0 := rfl

/-- The homotopy identity for the prism homotopy, pointwise. -/
lemma prismQ_comm_apply :
    ∀ (n : ℕ) (τ : C(G, (resolutionX X n).V)) (x : G),
      (resolutionRightTrans X g (n + 1)).hom τ x - τ x =
        (prismQ X g (n + 1)).hom ((TopRep.d X (n + 1)).hom τ) x +
          (TopRep.d X n).hom ((prismQ X g n).hom τ) x := by
  intro n
  induction n with
  | zero =>
    intro σ x
    rw [prismQ_succ_apply, resolutionRightTrans_succ_apply, d_succ_apply]
    simp only [ContinuousMap.sub_apply]
    rw [d_zero_apply, prismQ_zero_apply, sub_zero, prismQ_zero_apply, map_zero,
      resolutionRightTrans_zero_apply, resolutionRightTrans_zero_apply,
      ContinuousMap.zero_apply, add_zero]
  | succ n ih =>
    intro τ x
    have hchain : ∀ w, (resolutionRightTrans X g (n + 1)).hom ((TopRep.d X n).hom w) =
        (TopRep.d X n).hom ((resolutionRightTrans X g n).hom w) := fun w =>
      congr($(d_comp_resolutionRightTrans X g n).hom w)
    have ih' : (prismQ X g (n + 1)).hom ((TopRep.d X (n + 1)).hom (τ x)) =
        (resolutionRightTrans X g (n + 1)).hom (τ x) - τ x -
          (TopRep.d X n).hom ((prismQ X g n).hom (τ x)) := by
      ext y
      rw [ContinuousMap.sub_apply, ContinuousMap.sub_apply, ih (τ x) y, add_sub_cancel_right]
    rw [resolutionRightTrans_succ_apply, prismQ_succ_apply, d_succ_apply, d_succ_apply,
      prismQ_succ_apply]
    simp only [ContinuousMap.sub_apply]
    rw [d_succ_apply, map_sub, map_sub, map_sub, map_sub, hchain, ih']
    abel

/-- The homotopy identity for the prism homotopy. -/
lemma prismQ_comm (n : ℕ) :
    resolutionRightTrans X g (n + 1) - 𝟙 (resolutionX X (n + 1)) =
      TopRep.d X (n + 1) ≫ prismQ X g (n + 1) + prismQ X g n ≫ TopRep.d X n := by
  refine TopRep.hom_ext (ContIntertwiningMap.ext (ContinuousLinearMap.ext fun τ =>
    ContinuousMap.ext fun x => ?_))
  change (resolutionRightTrans X g (n + 1)).hom τ x - τ x =
    (prismQ X g (n + 1)).hom ((TopRep.d X (n + 1)).hom τ) x +
      (TopRep.d X n).hom ((prismQ X g n).hom τ) x
  exact prismQ_comm_apply X g n τ x

/-- Right translation is chain-homotopic to the identity, via the prism homotopy. -/
noncomputable def rightTransHomotopy :
    Homotopy (resolution'RightTrans X g) (𝟙 (resolution' X)) := by
  refine Homotopy.equivSubZero.symm ((Homotopy.ofEq ?_).trans (Homotopy.nullHomotopy'
    (fun i j hij => eqToHom (congrArg (resolution' X).X (Eq.symm hij)) ≫ prismQ X g (j + 1))))
  ext n : 1
  have hsub : (resolution'RightTrans X g - 𝟙 (resolution' X)).f n =
      resolutionRightTrans X g (n + 1) - 𝟙 (resolutionX X (n + 1)) := rfl
  rcases n with _ | n
  · rw [hsub, Homotopy.nullHomotopicMap'_f_of_not_rel_right (k₀ := 0 + 1) rfl
      (fun l hl => Nat.succ_ne_zero l hl)]
    simp only [eqToHom_refl, Category.id_comp]
    rw [CochainComplex.of_d, resolution'd_eq]
    have h := prismQ_comm X g 0
    rw [prismQ_zero, Limits.zero_comp, add_zero] at h
    exact h
  · rw [hsub, Homotopy.nullHomotopicMap'_f (k₂ := n) (k₀ := n + 1 + 1) rfl rfl]
    simp only [eqToHom_refl, Category.id_comp]
    rw [CochainComplex.of_d, CochainComplex.of_d, resolution'd_eq, resolution'd_eq]
    exact prismQ_comm X g (n + 1)

/-- **Conjugation acts trivially on continuous cohomology**: the map on `Hⁿ(G, X)` induced by
conjugation by `g` (with the `ρ g⁻¹` coefficient twist) is the identity. -/
lemma continuousCohomology_map_conj_id (n : ℕ) :
    ContinuousCohomology.map (conjCMHom g) (conjResHomId X g) n =
      𝟙 (continuousCohomology n X) := by
  have h : Homotopy (ContinuousCohomology.cochainsMap (conjCMHom g) (conjResHomId X g))
      (𝟙 (homogeneousCochains X)) :=
    (Homotopy.ofEq (cochainsMap_conj_eq X g)).trans
      ((Functor.mapHomotopy _ (rightTransHomotopy X g)).trans
        (Homotopy.ofEq (CategoryTheory.Functor.map_id _ _)))
  exact (h.homologyMap_eq n).trans (HomologicalComplex.homologyMap_id _ _)

end Prism

end NumberField.PoitouTate
