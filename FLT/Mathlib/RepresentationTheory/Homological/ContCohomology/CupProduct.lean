/-
Copyright (c) 2026 Yunzhou Xie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Edison Xie
-/
module

public import Mathlib
public import FLT.Mathlib.Algebra.Category.ModuleCat.Topology.Basic
public import FLT.Mathlib.Algebra.Category.ModuleCat.Topology.Homology
public import FLT.Mathlib.RepresentationTheory.Continuous.Basic
public import FLT.Mathlib.RepresentationTheory.Continuous.TopRep
public import FLT.Mathlib.RepresentationTheory.Homological.ContCohomology.Basic
public import FLT.Mathlib.Topology.CompactOpen

/-!
# Cup products in continuous group cohomology

This file constructs the cup product on continuous group cohomology, via a cup product pairing
on the coinduced resolutions.

## Main definitions

* `ContRepresentation.cupZeroSucc f hp n`: the degree-`(0, n)` cup product pairing on the coinduced
  resolutions induced by an intertwining map `f : ρ1 →ⁱL linHom ρ2 ρ3`.
* `ContRepresentation.cupSucc F hF`: the inductive step of the cup product, turning an
  intertwining map `π₁ →ⁱL linHom π₂ π₃` with jointly continuous underlying pairing into an
  intertwining map `π₁.coind₁ →ⁱL linHom π₂ π₃.coind₁`.
* `ContRepresentation.cupComplex`: the degree-`(m, n)` cup product pairing on the coinduced
  resolutions, as a morphism `(resolution' (of ρ1)).X m ⟶ iHom ((resolution' (of ρ2)).X n)
  ((resolution' (of ρ3)).X (m + n))`.
* `ContinuousCohomology.cupCochain`: the cup product pairing on homogeneous cochains.
* `ContinuousCohomology.cup`: the cup product on continuous group cohomology, descending
  `cupCochain` to the quotients of the cocycles by the coboundaries via
  `ContinuousCohomology.cohomologyIsoQuot`.

Throughout, the intertwining map `f` is only assumed to have jointly continuous uncurried
pairing (`hp`); this holds automatically when `M1` is discrete
(`ContRepresentation.continuous_pair_of_discrete`).

## Main results

* `ContRepresentation.cupPair_d_comm` and `ContinuousCohomology.cup_d_comm`: the Leibniz rule
  `d (σ ∪ τ) = (d σ) ∪ τ + (-1) ^ m • (σ ∪ d τ)` for the cup product, on the resolutions and on
  homogeneous cochains respectively.

## TODO

* Minimise the imports once the constructions are complete.
-/

@[expose] public section

set_option allowUnsafeReducibility true in
attribute [local reducible] CategoryTheory.Functor.mapHomologicalComplex

universe u v

open CategoryTheory ContinuousLinearMap.CompactOpen

namespace ContRepresentation

variable {k : Type u} {G : Type v} [CommRing k] [TopologicalSpace k] [Group G]

section Cup

variable {M1 M2 M3 : Type v}
  [AddCommGroup M1] [Module k M1] [TopologicalSpace M1] [IsTopologicalAddGroup M1]
  [ContinuousSMul k M1]
  [AddCommGroup M2] [Module k M2] [TopologicalSpace M2] [IsTopologicalAddGroup M2]
  [ContinuousSMul k M2]
  [AddCommGroup M3] [Module k M3] [TopologicalSpace M3] [IsTopologicalAddGroup M3]
  [ContinuousSMul k M3]
  [TopologicalSpace G] [IsTopologicalGroup G]
  (ρ1 : ContRepresentation k G M1) (ρ2 : ContRepresentation k G M2)
  (ρ3 : ContRepresentation k G M3) (f : ρ1 →ⁱL linHom ρ2 ρ3)

open TopRep

section CupSucc

variable {V W2 W3 : Type v}
  [AddCommGroup V] [Module k V] [TopologicalSpace V] [IsTopologicalAddGroup V]
  [ContinuousSMul k V]
  [AddCommGroup W2] [Module k W2] [TopologicalSpace W2] [IsTopologicalAddGroup W2]
  [AddCommGroup W3] [Module k W3] [TopologicalSpace W3] [IsTopologicalAddGroup W3]
  [ContinuousSMul k W3]
  {π₁ : ContRepresentation k G V} {π₂ : ContRepresentation k G W2}
  {π₃ : ContRepresentation k G W3}

/-- The inductive step of the cup product: an intertwining map `F : π₁ →ⁱL linHom π₂ π₃` whose
underlying pairing `(v, w) ↦ F v w` is jointly continuous induces an intertwining map
`π₁.coind₁ →ⁱL linHom π₂ π₃.coind₁` sending `σ` and `τ` to `x ↦ F (σ x) τ`.

The joint continuity hypothesis `hF` cannot be dropped: for a general `F` the continuity of
`τ ↦ (x ↦ F (σ x) τ)` would require an equicontinuity property of `F` on compact subsets of
`C(G, V)`. It is preserved by this construction (`continuous_cupSucc_uncurry`), which allows the
construction to be iterated. -/
def cupSucc (F : π₁ →ⁱL linHom π₂ π₃)
    (hF : Continuous fun p : V × W2 ↦ F p.1 p.2) :
    π₁.coind₁ →ⁱL linHom π₂ π₃.coind₁ where
  toFun σ := {
    toFun τ := ⟨fun x ↦ F (σ x) τ, hF.comp (σ.continuous.prodMk continuous_const)⟩
    map_add' τ₁ τ₂ := by ext x; exact map_add (F (σ x)) τ₁ τ₂
    map_smul' c τ := by ext x; exact map_smul (F (σ x)) c τ
    cont := ((⟨fun p ↦ F p.1 p.2, hF⟩ : C(V × W2, W3)).continuous_postcomp).comp <|
      (ContinuousMap.prodSwap.continuous_postcomp).comp <|
        ContinuousMap.continuous_prodMk_const.comp (continuous_id.prodMk continuous_const) }
  map_add' σ₁ σ₂ := by ext τ x; exact congr($(map_add F (σ₁ x) (σ₂ x)) τ)
  map_smul' c σ := by ext τ x; exact congr($(map_smul F c (σ x)) τ)
  cont := by
    refine continuous_induced_rng.2 (ContinuousMap.continuous_of_continuous_uncurry _ ?_)
    exact ((⟨fun p ↦ F p.1 p.2, hF⟩ : C(V × W2, W3)).continuous_postcomp).comp
      ((ContinuousMap.prodSwap.continuous_postcomp).comp
        (ContinuousMap.continuous_prodMk_const.comp (continuous_snd.prodMk continuous_fst)))
  isIntertwining' h := by ext σ τ x; simp [F.isIntertwining]

@[simp]
lemma cupSucc_apply_apply (F : π₁ →ⁱL linHom π₂ π₃)
    (hF : Continuous fun p : V × W2 ↦ F p.1 p.2) (σ : C(G, V)) (τ : W2) (x : G) :
    cupSucc F hF σ τ x = F (σ x) τ := rfl

/-- The uncurried pairing of `cupSucc F hF` is again jointly continuous, so `cupSucc` can be
iterated. -/
lemma continuous_cupSucc_uncurry (F : π₁ →ⁱL linHom π₂ π₃)
    (hF : Continuous fun p : V × W2 ↦ F p.1 p.2) :
    Continuous fun p : C(G, V) × W2 ↦ cupSucc F hF p.1 p.2 :=
  ((⟨fun p ↦ F p.1 p.2, hF⟩ : C(V × W2, W3)).continuous_postcomp).comp
    ((ContinuousMap.prodSwap.continuous_postcomp).comp
      (ContinuousMap.continuous_prodMk_const.comp (continuous_snd.prodMk continuous_fst)))

end CupSucc

variable (hp : Continuous fun p : M1 × M2 ↦ f p.1 p.2)

section

variable {ρ1 ρ2 ρ3}

/-- The pairing `resolutionX (of ρ2) n × M1 → resolutionX (of ρ3) n` underlying the cup product,
sending `(y, v)` to `resolutionCLM (f v) n y`, as a continuous map. The joint continuity of the
uncurried pairing of `f` propagates through the levels of the resolution. -/
def cupZeroSuccAux (n : ℕ) : C(resolutionX (of ρ2) n × M1, resolutionX (of ρ3) n) :=
  ⟨fun p ↦ resolutionCLM ρ2 ρ3 (f p.2) n p.1, by
    induction n with
    | zero => exact hp.comp continuous_swap
    | succ i ih =>
      have h : (fun p : ↥(resolutionX (of ρ2) (i + 1)) × M1 ↦
          resolutionCLM ρ2 ρ3 (f p.2) (i + 1) p.1) = fun p ↦
          (⟨_, ih⟩ : C(↥(resolutionX (of ρ2) i) × M1, ↥(resolutionX (of ρ3) i))).comp
            (p.1.prodMk (ContinuousMap.const G p.2)) := by
        funext p
        ext g
        rfl
      rw [h]
      exact (ContinuousMap.continuous_postcomp _).comp
        (ContinuousMap.continuous_prodMk.comp
          (continuous_fst.prodMk (ContinuousMap.continuous_const'.comp continuous_snd)))⟩

/-- The degree-`(0, n)` cup product pairing: an intertwining map `f : ρ1 →ⁱL linHom ρ2 ρ3` pairs
a degree-`0` cochain `σ` with a degree-`n` cochain `τ` by
`(σ ∪ τ) g = resolutionCLM (f (σ g)) n (τ g)`, intertwining the coinduced representations. -/
def cupZeroSucc (n : ℕ) :
    ρ1.coind₁ →ⁱL linHom (resolutionX (of ρ2) (n + 1)).ρ (resolutionX (of ρ3) (n + 1)).ρ where
  toFun σ := {
    toFun τ := ⟨fun g ↦ resolutionCLM ρ2 ρ3 (f (σ g)) n (τ g),
      (cupZeroSuccAux f hp n).continuous.comp (τ.continuous.prodMk σ.continuous)⟩
    map_add' τ₁ τ₂ := by ext g; exact map_add (resolutionCLM ρ2 ρ3 (f (σ g)) n) _ _
    map_smul' c τ := by ext g; exact map_smul (resolutionCLM ρ2 ρ3 (f (σ g)) n) c _
    cont := ((cupZeroSuccAux f hp n).continuous_postcomp).comp <|
      ContinuousMap.continuous_prodMk.comp <|
        continuous_id.prodMk continuous_const }
  map_add' σ₁ σ₂ := by ext τ g; simp [resolutionCLM_add]
  map_smul' c σ := by ext τ g; simp [resolutionCLM_smul]
  cont := by
    refine continuous_induced_rng.2 (ContinuousMap.continuous_of_continuous_uncurry _ ?_)
    exact ((cupZeroSuccAux f hp n).continuous_postcomp).comp
      (ContinuousMap.continuous_prodMk.comp (continuous_snd.prodMk continuous_fst))
  isIntertwining' h := by ext σ τ g; simp [f.isIntertwining, resolutionCLM_conj]

@[simp]
lemma cupZeroSucc_apply_apply (n : ℕ) (σ : C(G, M1)) (τ : C(G, resolutionX (of ρ2) n))
    (g : G) : cupZeroSucc f hp n σ τ g = resolutionCLM ρ2 ρ3 (f (σ g)) n (τ g) := rfl

/-- The uncurried pairing of `cupZeroSucc f hp n` is jointly continuous, so `cupSucc` applies
to it. -/
lemma continuous_cupZeroSucc_uncurry (n : ℕ) :
    Continuous fun p : C(G, M1) × C(G, resolutionX (of ρ2) n) ↦ cupZeroSucc f hp n p.1 p.2 :=
  ((cupZeroSuccAux f hp n).continuous_postcomp).comp
    (ContinuousMap.continuous_prodMk.comp (continuous_snd.prodMk continuous_fst))

/-- The degree-`(m, n)` cup product pairing on the coinduced resolutions, defined by iterating
`cupSucc` starting from `cupZeroSucc`, bundled with the joint continuity of its underlying
pairing (which is needed to keep iterating). -/
def cupPair (n : ℕ) : (m : ℕ) →
    { F : (resolutionX (of ρ1) (m + 1)).ρ →ⁱL
        linHom (resolutionX (of ρ2) (n + 1)).ρ (resolutionX (of ρ3) (n + 1 + m)).ρ //
      Continuous fun p : ↥(resolutionX (of ρ1) (m + 1)) × ↥(resolutionX (of ρ2) (n + 1)) ↦
        F p.1 p.2 }
  | 0 => ⟨cupZeroSucc f hp n, continuous_cupZeroSucc_uncurry f hp n⟩
  | m + 1 =>
    ⟨cupSucc (cupPair n m).1 (cupPair n m).2,
      continuous_cupSucc_uncurry (cupPair n m).1 (cupPair n m).2⟩

end

/-- The degree-`(m, n)` cup product pairing on the coinduced resolutions, as a morphism from the
`m`-th level to the internal hom of the `n`-th and `r`-th levels, obtained from `cupPair` by
reindexing along `r = m + n`. -/
def cupComplex (m n r : ℕ) (hr : r = m + n) :
    (TopRep.resolution' (.of ρ1)).X m ⟶
      iHom ((TopRep.resolution' (.of ρ2)).X n) ((TopRep.resolution' (.of ρ3)).X r) :=
  (TopRep.ofHom (cupPair f hp n m).1 :
      _ ⟶ ((TopRep.of ρ2).resolution'.X n).iHom (TopRep.resolutionX (.of ρ3) (n + 1 + m))) ≫
    eqToHom (by subst hr; rw [show n + 1 + m = m + n + 1 from by omega])

section

variable {ρ1 ρ2 ρ3}

@[simp]
lemma cupPair_zero (n : ℕ) : (cupPair f hp n 0).1 = cupZeroSucc f hp n := rfl

lemma cupPair_succ_apply (n m : ℕ) (σ : ↥(resolutionX (of ρ1) (m + 1 + 1)))
    (τ : ↥(resolutionX (of ρ2) (n + 1))) (x : G) :
    (cupPair f hp n (m + 1)).1 σ τ x = (cupPair f hp n m).1 (σ x) τ := rfl

/-- Cupping with a constant `0`-cochain acts through the functorial extension of `f v`. -/
lemma cupZeroSucc_const_apply (n : ℕ) (v : M1) (τ : ↥(resolutionX (of ρ2) (n + 1))) :
    cupZeroSucc f hp n (ContinuousMap.const G v) τ = resolutionCLM ρ2 ρ3 (f v) (n + 1) τ := rfl

/-- The Leibniz rule for the cup product pairing on the levels of the standard resolutions:
`d (σ ∪ τ) = (d σ) ∪ τ + (-1) ^ m • (σ ∪ d τ)`. -/
lemma cupPair_d_comm (n m : ℕ) (σ : ↥(resolutionX (of ρ1) (m + 1)))
    (τ : ↥(resolutionX (of ρ2) (n + 1))) :
    (d (of ρ3) (n + 1 + m)).hom ((cupPair f hp n m).1 σ τ) =
      (cupPair f hp n (m + 1)).1 ((d (of ρ1) (m + 1)).hom σ) τ +
        (-1 : ℤ) ^ m • resolutionXCast (.of ρ3) (by omega : n + 1 + 1 + m = n + 1 + m + 1)
          ((cupPair f hp (n + 1) m).1 σ ((d (of ρ2) (n + 1)).hom τ)) := by
  induction m with
  | zero =>
    ext x : 1
    change (cupPair f hp n 0).1 σ τ -
        (d (of ρ3) n).hom (resolutionCLM ρ2 ρ3 (f (σ x)) n (τ x)) =
      (cupPair f hp n 0).1 ((d (of ρ1) 1).hom σ x) τ +
        (-1 : ℤ) ^ 0 • (resolutionXCast (.of ρ3) (by omega : n + 1 + 1 + 0 = n + 1 + 0 + 1)
          ((cupPair f hp (n + 1) 0).1 σ ((d (of ρ2) (n + 1)).hom τ))) x
    have h1 : (d (of ρ1) 1).hom σ x = σ - ContinuousMap.const G (σ x) := by
      rw [d_hom_succ_apply, d_hom_zero]
    -- The reindexing cast on the left is along a definitional equality, so it evaluates away.
    have h2 : (resolutionXCast (.of ρ3) (by omega : n + 1 + 1 + 0 = n + 1 + 0 + 1)
        ((cupPair f hp (n + 1) 0).1 σ ((d (of ρ2) (n + 1)).hom τ))) x =
        resolutionCLM ρ2 ρ3 (f (σ x)) (n + 1) ((d (of ρ2) (n + 1)).hom τ x) := rfl
    have h3 : (cupPair f hp n 0).1 (ContinuousMap.const G (σ x)) τ =
        resolutionCLM ρ2 ρ3 (f (σ x)) (n + 1) τ := by
      rw [cupPair_zero, cupZeroSucc_const_apply]
    rw [h1, h2, resolutionCLM_comp_d, map_sub ((cupPair f hp n 0).1),
      sub_apply, h3, d_hom_succ_apply, map_sub, pow_zero, one_smul]
    abel
  | succ m ih =>
    ext x : 1
    change (cupPair f hp n (m + 1)).1 σ τ -
        (d (of ρ3) (n + 1 + m)).hom ((cupPair f hp n m).1 (σ x) τ) =
      (cupPair f hp n (m + 1)).1 ((d (of ρ1) (m + 1 + 1)).hom σ x) τ +
        (-1 : ℤ) ^ (m + 1) • (resolutionXCast (.of ρ3)
          (by omega : n + 1 + 1 + (m + 1) = n + 1 + (m + 1) + 1)
          ((cupPair f hp (n + 1) (m + 1)).1 σ ((d (of ρ2) (n + 1)).hom τ))) x
    have h1 : (d (of ρ1) (m + 1 + 1)).hom σ x = σ - (d (of ρ1) (m + 1)).hom (σ x) :=
      d_hom_succ_apply _ _ σ x
    have h2 : (resolutionXCast (.of ρ3)
        (by omega : n + 1 + 1 + (m + 1) = n + 1 + (m + 1) + 1)
        ((cupPair f hp (n + 1) (m + 1)).1 σ ((d (of ρ2) (n + 1)).hom τ))) x =
        resolutionXCast (.of ρ3) (by omega : n + 1 + 1 + m = n + 1 + m + 1)
          ((cupPair f hp (n + 1) m).1 (σ x) ((d (of ρ2) (n + 1)).hom τ)) :=
      resolutionXCast_apply _ _ _ x
    rw [ih, h1, h2, map_sub ((cupPair f hp n (m + 1)).1), sub_apply,
      pow_succ, mul_comm, mul_smul, neg_one_smul]
    abel

end

end Cup

end ContRepresentation

namespace ContinuousCohomology

open ContRepresentation TopRep

section Cup

variable {k : Type u} {G : Type v} [CommRing k] [TopologicalSpace k] [Group G]

variable {M1 M2 M3 : Type v}
  [AddCommGroup M1] [Module k M1] [TopologicalSpace M1] [IsTopologicalAddGroup M1]
  [ContinuousSMul k M1]
  [AddCommGroup M2] [Module k M2] [TopologicalSpace M2] [IsTopologicalAddGroup M2]
  [ContinuousSMul k M2]
  [AddCommGroup M3] [Module k M3] [TopologicalSpace M3] [IsTopologicalAddGroup M3]
  [ContinuousSMul k M3]
  [TopologicalSpace G] [IsTopologicalGroup G]
  (ρ1 : ContRepresentation k G M1) (ρ2 : ContRepresentation k G M2)
  (ρ3 : ContRepresentation k G M3) (f : ρ1 →ⁱL linHom ρ2 ρ3)
  (hp : Continuous fun p : M1 × M2 ↦ f p.1 p.2)

variable {ρ1 ρ2 ρ3} in
/-- The cup product pairing on homogeneous cochains, obtained from the cup product pairing
`cupComplex` on the coinduced resolutions by taking invariants. -/
abbrev cupCochain (m n r : ℕ) (hr : r = m + n) :
    (homogeneousCochains (.of ρ1)).X m ⟶ TopModuleCat.linHom ((homogeneousCochains (.of ρ2)).X n)
      ((homogeneousCochains (.of ρ3)).X r) :=
  (invariantsFunctor k G).map (cupComplex ρ1 ρ2 ρ3 f hp m n r hr) ≫
    invariantsObjIHom ρ2 ρ3 n r


variable {ρ1 ρ2 ρ3} in
/-- The value of the cup product of two homogeneous cochains, as an element of the resolution. -/
lemma cupCochain_coe (m n r : ℕ) (hr : r = m + n) (σ : (homogeneousCochains (.of ρ1)).X m)
    (τ : (homogeneousCochains (.of ρ2)).X n) :
    (cupCochain f hp m n r hr σ τ : ↥((of ρ3).resolution'.X r)) =
      resolutionXCast (.of ρ3) (by omega : n + 1 + m = r + 1)
        ((cupPair f hp n m).1 σ.1 τ.1) := by
  subst hr
  exact eqToHom_iHom_apply ρ3 ((TopRep.of ρ2).resolution'.X n)
    (show n + 1 + m = m + n + 1 by omega)
    (by rw [show n + 1 + m = m + n + 1 from by omega]) ((cupPair f hp n m).1 σ.1) τ.1

variable {ρ1 ρ2 ρ3} in
lemma cupCochain_apply_zero (m n r : ℕ) (hr : r = m + n)
    (σ : (homogeneousCochains (.of ρ1)).X m) :
    cupCochain f hp m n r hr σ 0 = 0 :=
  map_zero (cupCochain f hp m n r hr σ : ↥((homogeneousCochains (.of ρ2)).X n) →L[k]
    ↥((homogeneousCochains (.of ρ3)).X r))

lemma cup_d_comm (m n r : ℕ) (hr : r = m + n) (σ : (homogeneousCochains (.of ρ1)).X m)
    (τ : (homogeneousCochains (.of ρ2)).X n) :
    (homogeneousCochains (.of ρ3)).d r (r + 1) (cupCochain f hp m n r hr σ τ) =
    cupCochain f hp (m + 1) n (r + 1) (by omega) ((homogeneousCochains (.of ρ1)).d m (m + 1) σ) τ +
    (-1) ^ m • cupCochain f hp m (n + 1) (r + 1) (by omega) σ
    ((homogeneousCochains (.of ρ2)).d n (n + 1) τ) := by
  subst hr
  refine Subtype.ext ?_
  rw [homogeneousCochains.d_apply, cupCochain_coe, d_hom_resolutionXCast, cupPair_d_comm,
    map_add, map_zsmul, resolutionXCast_trans, Submodule.coe_add, Submodule.coe_smul_of_tower,
    cupCochain_coe, cupCochain_coe, homogeneousCochains.d_apply, homogeneousCochains.d_apply]

variable {ρ1 ρ2 ρ3} in
/-- `cupCochain` vanishes when its first argument is zero. -/
lemma cupCochain_zero_apply (m n r : ℕ) (hr : r = m + n)
    (τ : (homogeneousCochains (.of ρ2)).X n) :
    cupCochain f hp m n r hr 0 τ = 0 :=
  congr($(map_zero (cupCochain f hp m n r hr).hom) τ)

variable {ρ1 ρ2 ρ3} in
/-- The cup product of two cocycles is a cocycle. -/
lemma d_cupCochain_eq_zero (m n r : ℕ) (hr : r = m + n)
    {σ : (homogeneousCochains (.of ρ1)).X m} {τ : (homogeneousCochains (.of ρ2)).X n}
    (hσ : (homogeneousCochains (.of ρ1)).d m (m + 1) σ = 0)
    (hτ : (homogeneousCochains (.of ρ2)).d n (n + 1) τ = 0) :
    (homogeneousCochains (.of ρ3)).d r (r + 1) (cupCochain f hp m n r hr σ τ) = 0 := by
  have h := cup_d_comm ρ1 ρ2 ρ3 f hp m n r hr σ τ
  rw [hσ, hτ, cupCochain_zero_apply, cupCochain_apply_zero] at h
  refine h.trans ?_
  have h0 : (0 : ↥((homogeneousCochains (.of ρ3)).X (r + 1))) +
      (-1 : ℤ) ^ m • (0 : ↥((homogeneousCochains (.of ρ3)).X (r + 1))) = 0 := by simp
  exact h0

variable {ρ1 ρ2 ρ3} in
/-- For a fixed cocycle `σ`, cupping with `σ` restricts to a continuous linear map between the
kernels of the differentials on homogeneous cochains. -/
noncomputable def cupKerCLM (m n r : ℕ) (hr : r = m + n)
    (σ : ↥(TopModuleCat.ker ((homogeneousCochains (.of ρ1)).d m (m + 1)))) :
    ↥(TopModuleCat.ker ((homogeneousCochains (.of ρ2)).d n (n + 1))) →L[k]
      ↥(TopModuleCat.ker ((homogeneousCochains (.of ρ3)).d r (r + 1))) :=
  (cupCochain f hp m n r hr σ.1 : ↥((homogeneousCochains (.of ρ2)).X n) →L[k]
      ↥((homogeneousCochains (.of ρ3)).X r)).restrict
    fun _ hτ ↦ LinearMap.mem_ker.2 (d_cupCochain_eq_zero f hp m n r hr
      (LinearMap.mem_ker.mp σ.2) (LinearMap.mem_ker.mp hτ))

variable {ρ1 ρ2 ρ3} in
lemma cupKerCLM_apply_coe (m n r : ℕ) (hr : r = m + n)
    (σ : ↥(TopModuleCat.ker ((homogeneousCochains (.of ρ1)).d m (m + 1))))
    (τ : ↥(TopModuleCat.ker ((homogeneousCochains (.of ρ2)).d n (n + 1)))) :
    (cupKerCLM f hp m n r hr σ τ).1 = cupCochain f hp m n r hr σ.1 τ.1 := rfl

variable {ρ1 ρ2 ρ3} in
/-- The cup product with a doubly-applied differential vanishes. -/
lemma cupCochain_d_comp_d (m i j l r : ℕ) (hr : r = m + l)
    (σ : (homogeneousCochains (.of ρ1)).X m) (τ : (homogeneousCochains (.of ρ2)).X i) :
    cupCochain f hp m l r hr σ
      ((homogeneousCochains (.of ρ2)).d j l ((homogeneousCochains (.of ρ2)).d i j τ)) = 0 := by
  rw [homogeneousCochains.d_comp_d_apply]
  exact map_zero (cupCochain f hp m l r hr σ : ↥((homogeneousCochains (.of ρ2)).X l) →L[k]
    ↥((homogeneousCochains (.of ρ3)).X r))

/-- The cup product of two coboundaries is a coboundary: `(d σ) ∪ (d τ) = d (σ ∪ d τ)`. This is
the special case of the Leibniz rule `cup_d_comm` where the second argument is a coboundary.

Note that `(d σ) ∪ (d τ)` is *not* zero in general: by the Leibniz rule it is the coboundary of
`σ ∪ d τ`. -/
lemma d_cup_d (m n r : ℕ) (hr : r = m + n) (σ : (homogeneousCochains (.of ρ1)).X m)
    (τ : (homogeneousCochains (.of ρ2)).X n) :
    cupCochain f hp (m + 1) (n + 1) (r + 2) (by omega)
      ((homogeneousCochains (.of ρ1)).d m (m + 1) σ)
      ((homogeneousCochains (.of ρ2)).d n (n + 1) τ) =
    (homogeneousCochains (.of ρ3)).d (r + 1) (r + 2) (cupCochain f hp m (n + 1) (r + 1) (by omega) σ
      ((homogeneousCochains (.of ρ2)).d n (n + 1) τ)) := by
  subst hr
  have h := cup_d_comm ρ1 ρ2 ρ3 f hp m (n + 1) (m + n + 1) rfl σ
    ((homogeneousCochains (.of ρ2)).d n (n + 1) τ)
  rw [cupCochain_d_comp_d] at h
  simpa only [smul_zero, add_zero] using h.symm

variable {ρ1 ρ2 ρ3} in
/-- Cupping a coboundary with a cocycle gives a coboundary. -/
lemma d_cupCochain_of_d_eq_zero (m n r : ℕ) (hr : r = m + n)
    (σ : (homogeneousCochains (.of ρ1)).X m) {τ : (homogeneousCochains (.of ρ2)).X n}
    (hτ : (homogeneousCochains (.of ρ2)).d n (n + 1) τ = 0) :
    cupCochain f hp (m + 1) n (r + 1) (by omega) ((homogeneousCochains (.of ρ1)).d m (m + 1) σ) τ =
      (homogeneousCochains (.of ρ3)).d r (r + 1) (cupCochain f hp m n r hr σ τ) := by
  have h := cup_d_comm ρ1 ρ2 ρ3 f hp m n r hr σ τ
  rw [hτ, cupCochain_apply_zero] at h
  have h0 : ∀ x : ↥((homogeneousCochains (.of ρ3)).X (r + 1)),
      x = x + (-1 : ℤ) ^ m • (0 : ↥((homogeneousCochains (.of ρ3)).X (r + 1))) := by simp
  exact (h0 _).trans h.symm

variable {ρ1 ρ2 ρ3} in
/-- Cupping a cocycle with a coboundary gives a coboundary, up to the sign `(-1) ^ m`. -/
lemma cupCochain_d_of_d_eq_zero (m n r : ℕ) (hr : r = m + n)
    {σ : (homogeneousCochains (.of ρ1)).X m} (τ : (homogeneousCochains (.of ρ2)).X n)
    (hσ : (homogeneousCochains (.of ρ1)).d m (m + 1) σ = 0) :
    cupCochain f hp m (n + 1) (r + 1) (by omega) σ ((homogeneousCochains (.of ρ2)).d n (n + 1) τ) =
      (-1 : ℤ) ^ m • (homogeneousCochains (.of ρ3)).d r (r + 1) (cupCochain f hp m n r hr σ τ) := by
  have h := cup_d_comm ρ1 ρ2 ρ3 f hp m n r hr σ τ
  rw [hσ, cupCochain_zero_apply] at h
  rw [h]
  have h0 : ∀ x : ↥((homogeneousCochains (.of ρ3)).X (r + 1)),
      (-1 : ℤ) ^ m • ((0 : ↥((homogeneousCochains (.of ρ3)).X (r + 1))) + (-1 : ℤ) ^ m • x) =
        x := by
    intro x
    rw [zero_add, smul_smul, ← pow_add, Even.neg_one_pow ⟨m, rfl⟩, one_smul]
  exact (h0 _).symm

variable {ρ1 ρ2 ρ3} in
/-- The cup product pairing on the kernels of the differentials is jointly continuous. -/
lemma continuous_cupKerCLM_uncurry (m n r : ℕ) (hr : r = m + n) :
    Continuous fun p : ↥(TopModuleCat.ker ((homogeneousCochains (.of ρ1)).d m (m + 1))) ×
        ↥(TopModuleCat.ker ((homogeneousCochains (.of ρ2)).d n (n + 1))) ↦
      cupKerCLM f hp m n r hr p.1 p.2 := by
  refine continuous_induced_rng.2 (continuous_induced_rng.2 ?_)
  change Continuous fun p : ↥(TopModuleCat.ker ((homogeneousCochains (.of ρ1)).d m (m + 1))) ×
      ↥(TopModuleCat.ker ((homogeneousCochains (.of ρ2)).d n (n + 1))) ↦
    (cupCochain f hp m n r hr p.1.1 p.2.1 : ↥((TopRep.of ρ3).resolution'.X r))
  have h2 : (fun p : ↥(TopModuleCat.ker ((homogeneousCochains (.of ρ1)).d m (m + 1))) ×
      ↥(TopModuleCat.ker ((homogeneousCochains (.of ρ2)).d n (n + 1))) ↦
      (cupCochain f hp m n r hr p.1.1 p.2.1 : ↥((TopRep.of ρ3).resolution'.X r))) =
      fun p ↦ resolutionXCast (.of ρ3) (by omega : n + 1 + m = r + 1)
        ((cupPair f hp n m).1 p.1.1.1 p.2.1.1) := by
    funext p
    exact cupCochain_coe f hp m n r hr p.1.1 p.2.1
  rw [h2]
  exact (resolutionXCast (.of ρ3) (by omega : n + 1 + m = r + 1)).continuous.comp
    ((cupPair f hp n m).2.comp
      (((continuous_subtype_val.comp continuous_subtype_val).comp continuous_fst).prodMk
        ((continuous_subtype_val.comp continuous_subtype_val).comp continuous_snd)))

variable {ρ1 ρ2 ρ3} in
/-- The cup product bundled as a morphism from the kernel of the differential into the
internal hom of the kernel models. -/
noncomputable def cupKerHom (f : ρ1 →ⁱL ρ2.linHom ρ3) (hp : Continuous fun p : M1 × M2 ↦ f p.1 p.2)
    (m n r : ℕ) (hr : r = m + n) :
    TopModuleCat.ker ((homogeneousCochains (.of ρ1)).d m (m + 1)) ⟶
      TopModuleCat.linHom (TopModuleCat.ker ((homogeneousCochains (.of ρ2)).d n (n + 1)))
        (TopModuleCat.ker ((homogeneousCochains (.of ρ3)).d r (r + 1))) :=
  TopModuleCat.homOfBilinear (cupKerCLM f hp m n r hr)
    (fun σ1 σ2 τ ↦ Subtype.ext (congr($(map_add (cupCochain f hp m n r hr).hom σ1.1 σ2.1) τ.1)))
    (fun c σ τ ↦ Subtype.ext (congr($(map_smul (cupCochain f hp m n r hr).hom c σ.1) τ.1)))
    (continuous_cupKerCLM_uncurry f hp m n r hr)

/-- The cup product of two cocycles, as a cocycle: by the Leibniz rule `cup_d_comm`, the
differential of `σ ∪ τ` vanishes when `d σ = 0` and `d τ = 0`. -/
noncomputable abbrev cupCocyclesAux (f : ρ1 →ⁱL ρ2.linHom ρ3)
    (hp : Continuous fun p : M1 × M2 ↦ f p.1 p.2) (m n r : ℕ) (hr : r = m + n)
    (σ : (homogeneousCochains (.of ρ1)).cycles m)
    (τ : (homogeneousCochains (.of ρ2)).cycles n) :
    (homogeneousCochains (.of ρ3)).cycles r :=
  letI σ' := ((homogeneousCochains (.of ρ1)).cyclesIsoKer m (m + 1) (by simp)).hom.hom σ
  letI τ' := ((homogeneousCochains (.of ρ2)).cyclesIsoKer n (n + 1) (by simp)).hom.hom τ
  ((homogeneousCochains (.of ρ3)).cyclesIsoKer r (r + 1) (by simp)).inv.hom
    ⟨cupCochain f hp m n r hr σ' τ',
      LinearMap.mem_ker.2 (d_cupCochain_eq_zero f hp m n r hr
        (LinearMap.mem_ker.mp σ'.2) (LinearMap.mem_ker.mp τ'.2))⟩

/-- The cup product pairing on the cycles of the homogeneous cochain complexes, transporting
`cupKerHom` along the identification `cyclesIsoKer` of the cycles with the kernel models. -/
noncomputable def cupCocycles (f : ρ1 →ⁱL ρ2.linHom ρ3)
    (hp : Continuous fun p : M1 × M2 ↦ f p.1 p.2) (m n r : ℕ) (hr : r = m + n) :
    (homogeneousCochains (.of ρ1)).cycles m ⟶
      TopModuleCat.linHom ((homogeneousCochains (.of ρ2)).cycles n)
        ((homogeneousCochains (.of ρ3)).cycles r) :=
  ((homogeneousCochains (.of ρ1)).cyclesIsoKer m (m + 1) (by simp)).hom ≫
    cupKerHom f hp m n r hr ≫
      TopModuleCat.linHomMap
        ((homogeneousCochains (.of ρ2)).cyclesIsoKer n (n + 1) (by simp)).hom
        ((homogeneousCochains (.of ρ3)).cyclesIsoKer r (r + 1) (by simp)).inv

variable {ρ1 ρ2 ρ3} in
@[simp]
lemma cupCocycles_apply (f : ρ1 →ⁱL ρ2.linHom ρ3) (hp : Continuous fun p : M1 × M2 ↦ f p.1 p.2)
    (m n r : ℕ) (hr : r = m + n)
    (σ : (homogeneousCochains (.of ρ1)).cycles m)
    (τ : (homogeneousCochains (.of ρ2)).cycles n) :
    cupCocycles ρ1 ρ2 ρ3 f hp m n r hr σ τ = cupCocyclesAux ρ1 ρ2 ρ3 f hp m n r hr σ τ := rfl

variable {ρ1 ρ2 ρ3} in
/-- Cupping a coboundary with a cocycle dies in the quotient by the coboundaries. -/
lemma cokerπ_cupKerCLM_bdryKer_left (m n r : ℕ) (hr : r = m + n)
    (y : ↥((homogeneousCochains (.of ρ1)).X (m - 1)))
    (τ : ↥(TopModuleCat.ker ((homogeneousCochains (.of ρ2)).d n (n + 1)))) :
    TopModuleCat.cokerπ (bdryKer (.of ρ3) r)
      (cupKerCLM f hp m n r hr (bdryKer (.of ρ1) m y) τ) = 0 := by
  cases m with
  | zero =>
    have h0 : bdryKer (TopRep.of ρ1) 0 y = 0 := Subtype.ext (by
      rw [bdryKer_apply_coe, (homogeneousCochains (TopRep.of ρ1)).shape _ _ (by simp)]
      rfl)
    have h1 : cupKerCLM f hp 0 n r hr (bdryKer (TopRep.of ρ1) 0 y) τ = 0 := by
      rw [h0]
      exact Subtype.ext (by
        rw [cupKerCLM_apply_coe]
        simpa using cupCochain_zero_apply f hp 0 n r hr τ.1)
    rw [h1]
    exact (TopModuleCat.cokerπ (bdryKer (TopRep.of ρ3) r)).hom.map_zero
  | succ i =>
    obtain rfl : r = i + n + 1 := by omega
    rw [TopModuleCat.cokerπ_eq_zero_iff]
    exact ⟨cupCochain f hp i n (i + n) rfl y τ.1, Subtype.ext
      (d_cupCochain_of_d_eq_zero f hp i n (i + n) rfl y (LinearMap.mem_ker.mp τ.2)).symm⟩

variable {ρ1 ρ2 ρ3} in
/-- Cupping a cocycle with a coboundary dies in the quotient by the coboundaries. -/
lemma cokerπ_cupKerCLM_bdryKer_right (m n r : ℕ) (hr : r = m + n)
    (σ : ↥(TopModuleCat.ker ((homogeneousCochains (.of ρ1)).d m (m + 1))))
    (y : ↥((homogeneousCochains (.of ρ2)).X (n - 1))) :
    TopModuleCat.cokerπ (bdryKer (.of ρ3) r)
      (cupKerCLM f hp m n r hr σ (bdryKer (.of ρ2) n y)) = 0 := by
  cases n with
  | zero =>
    have h0 : bdryKer (TopRep.of ρ2) 0 y = 0 := Subtype.ext (by
      rw [bdryKer_apply_coe, (homogeneousCochains (TopRep.of ρ2)).shape _ _ (by simp)]
      rfl)
    rw [h0, (cupKerCLM f hp m 0 r hr σ).map_zero]
    exact (TopModuleCat.cokerπ (bdryKer (TopRep.of ρ3) r)).hom.map_zero
  | succ i =>
    obtain rfl : r = m + i + 1 := by omega
    rw [TopModuleCat.cokerπ_eq_zero_iff]
    refine ⟨(-1 : ℤ) ^ m • cupCochain f hp m i (m + i) rfl σ.1 y, Subtype.ext ?_⟩
    change (homogeneousCochains (TopRep.of ρ3)).d (m + i) (m + i + 1)
        ((-1 : ℤ) ^ m • cupCochain f hp m i (m + i) rfl σ.1 y) =
      cupCochain f hp m (i + 1) (m + i + 1) (by omega) σ.1
        ((homogeneousCochains (TopRep.of ρ2)).d i (i + 1) y)
    rw [map_zsmul]
    exact (cupCochain_d_of_d_eq_zero f hp m i (m + i) rfl y (LinearMap.mem_ker.mp σ.2)).symm

/-- The cup product on continuous group cohomology induced by an intertwining map
`f : ρ1 →ⁱL linHom ρ2 ρ3`: descend the kernel-model cup product `cupKerHom` to the quotients
by the coboundaries on all three slots, and transport along `cohomologyIsoQuot`. -/
noncomputable def cup (f : ρ1 →ⁱL ρ2.linHom ρ3) (hp : Continuous fun p : M1 × M2 ↦ f p.1 p.2)
    (m n r : ℕ) (hr : r = m + n) :
    (continuousCohomology m (of ρ1)) ⟶
      TopModuleCat.linHom ((continuousCohomology n (of ρ2)))
        ((continuousCohomology r (of ρ3))) :=
  (cohomologyIsoQuot (of ρ1) m).hom ≫
    TopModuleCat.cokerDescBilinear (bdryKer (of ρ1) m) (bdryKer (of ρ2) n) (bdryKer (of ρ3) r)
      (cupKerHom f hp m n r hr) (continuous_cupKerCLM_uncurry f hp m n r hr)
      (fun y τ ↦ cokerπ_cupKerCLM_bdryKer_left f hp m n r hr y τ)
      (fun σ y ↦ cokerπ_cupKerCLM_bdryKer_right f hp m n r hr σ y) ≫
    TopModuleCat.linHomMap (cohomologyIsoQuot (of ρ2) n).hom (cohomologyIsoQuot (of ρ3) r).inv

end Cup

end ContinuousCohomology
