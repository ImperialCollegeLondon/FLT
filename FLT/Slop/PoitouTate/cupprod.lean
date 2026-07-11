/-
Copyright (c) 2026 Yunzhou Xie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Edison Xie
-/
module

public import Mathlib
public import FLT.Mathlib.RepresentationTheory.Homological.ContCohomology.CupProduct

/-!
# Cup products in continuous group cohomology, discrete-coefficient wrappers

The machinery constructing the cup product pairing on the coinduced resolutions computing
continuous group cohomology has been upstreamed to
`FLT.Mathlib.RepresentationTheory.Homological.ContCohomology.CupProduct` and its imports, in the
namespaces `TopModuleCat`, `HomologicalComplex`, `ContRepresentation` and `ContinuousCohomology`.
There, the intertwining map `f : ρ1 →ⁱL linHom ρ2 ρ3` carries an explicit hypothesis `hp` that
its uncurried pairing is jointly continuous, instead of a `[DiscreteTopology M1]` assumption on
the first coefficient module.

This file retains the discrete-coefficient wrappers used by the Poitou–Tate development, stated
in the `ContRepresentation` namespace with the joint continuity discharged by
`ContRepresentation.continuous_pair_of_discrete`:

* `ContRepresentation.cupCochain`: the cup product pairing on homogeneous cochains, pairing a
  degree-`m` cochain with a degree-`n` cochain to give a degree-`r = m + n` cochain.
* `ContRepresentation.cup_d_comm`: the Leibniz rule
  `d (σ ∪ τ) = (d σ) ∪ τ + (-1) ^ m • (σ ∪ d τ)` on homogeneous cochains, with the corollaries
  `d_cupCochain_eq_zero`, `d_cup_d`, `d_cupCochain_of_d_eq_zero` and `cupCochain_d_of_d_eq_zero`.
* `ContRepresentation.cupKerCLM`, `ContRepresentation.cupKerHom` and
  `ContRepresentation.cupCocycles`: the cup product on the kernel models of the cocycles and on
  the cycles of the homogeneous cochain complexes.
* `ContRepresentation.bdryKer` and `ContRepresentation.cohomologyIsoQuot`: the coboundary map
  into the kernel model, and continuous cohomology identified with the quotient of the kernel
  model of the cocycles by the coboundaries.
* `ContRepresentation.cup`: the cup product on continuous group cohomology.
-/

@[expose] public section

set_option allowUnsafeReducibility true in
attribute [local reducible] CategoryTheory.Functor.mapHomologicalComplex

universe u v

open ContinuousMap Set Topology in
/-- The pairing map `C(α, β) × C(α, δ) → C(α, β × δ)` is continuous in the compact-open
topologies when `δ` is discrete, without any local compactness assumption on `α`: a continuous
map into a discrete space takes finitely many values on a compact set, so on each compact set the
maps close to `g` in `C(α, δ)` agree with `g`. See `ContinuousMap.continuous_prodMk` for the
version assuming instead that `α` is an R₁ space. -/
lemma ContinuousMap.continuous_prodMk_of_discrete {α β δ : Type*} [TopologicalSpace α]
    [TopologicalSpace β] [TopologicalSpace δ] [DiscreteTopology δ] :
    Continuous fun p : C(α, β) × C(α, δ) ↦ p.1.prodMk p.2 := by
  simp_rw [continuous_iff_continuousAt, ContinuousAt, tendsto_nhds_compactOpen]
  rintro ⟨f, g⟩ K hK U hU hfg
  have key : ∀ c ∈ g '' K, ∀ᶠ p : C(α, β) × C(α, δ) in 𝓝 (f, g),
      MapsTo p.1 (K ∩ g ⁻¹' {c}) {y | (y, c) ∈ U} ∧ MapsTo p.2 (K ∩ g ⁻¹' {c}) {c} := by
    intro c _
    have hKc : IsCompact (K ∩ g ⁻¹' {c}) :=
      hK.inter_right ((isClosed_discrete _).preimage g.continuous)
    have h1 : ∀ᶠ f' : C(α, β) in 𝓝 f, MapsTo f' (K ∩ g ⁻¹' {c}) {y | (y, c) ∈ U} :=
      eventually_mapsTo hKc (hU.preimage (continuous_id.prodMk continuous_const))
        fun x hx ↦ by simpa [show g x = c from hx.2] using hfg hx.1
    have h2 : ∀ᶠ g' : C(α, δ) in 𝓝 g, MapsTo g' (K ∩ g ⁻¹' {c}) {c} :=
      eventually_mapsTo hKc (isOpen_discrete _) fun x hx ↦ hx.2
    rw [nhds_prod_eq]
    exact (Filter.tendsto_fst.eventually h1).and (Filter.tendsto_snd.eventually h2)
  have hfin : (g '' K).Finite := (hK.image g.continuous).finite_of_discrete
  filter_upwards [(Filter.eventually_all_finite hfin).2 key] with p hp x hxK
  obtain ⟨h1, h2⟩ := hp (g x) (mem_image_of_mem g hxK)
  have hx : x ∈ K ∩ g ⁻¹' {g x} := ⟨hxK, rfl⟩
  simpa [show p.2 x = g x from h2 hx] using h1 hx

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

variable [DiscreteTopology M1]

variable {ρ1 ρ2 ρ3} in
/-- The cup product pairing on homogeneous cochains: apply the `G`-invariants functor to the
resolution-level pairing `cupComplex` and restrict via `invariantsObjIHom`, pairing a degree-`m`
cochain with a degree-`n` cochain to give a degree-`r = m + n` cochain. -/
abbrev cupCochain (m n r : ℕ) (hr : r = m + n) :
    (homogeneousCochains (.of ρ1)).X m ⟶ TopModuleCat.linHom ((homogeneousCochains (.of ρ2)).X n)
      ((homogeneousCochains (.of ρ3)).X r) :=
  (invariantsFunctor k G).map
      (cupComplex ρ1 ρ2 ρ3 f (continuous_pair_of_discrete f) m n r hr) ≫
    invariantsObjIHom ρ2 ρ3 n r


variable {ρ1 ρ2 ρ3} in
/-- The value of the cup product of two homogeneous cochains, as an element of the resolution. -/
lemma cupCochain_coe (m n r : ℕ) (hr : r = m + n) (σ : (homogeneousCochains (.of ρ1)).X m)
    (τ : (homogeneousCochains (.of ρ2)).X n) :
    (cupCochain f m n r hr σ τ : ↥((of ρ3).resolution'.X r)) =
      resolutionXCast (.of ρ3) (by omega : n + 1 + m = r + 1)
        ((cupPair f (continuous_pair_of_discrete f) n m).1 σ.1 τ.1) := by
  subst hr
  exact eqToHom_iHom_apply ρ3 ((TopRep.of ρ2).resolution'.X n)
    (show n + 1 + m = m + n + 1 by omega)
    (by rw [show n + 1 + m = m + n + 1 from by omega])
    ((cupPair f (continuous_pair_of_discrete f) n m).1 σ.1) τ.1

variable {ρ1 ρ2 ρ3} in
@[simp, nolint simpNF] -- keeps the one-step rewrite; the linter's derivation needs 7 lemmas
lemma cupCochain_apply_zero (m n r : ℕ) (hr : r = m + n)
    (σ : (homogeneousCochains (.of ρ1)).X m) :
    cupCochain f m n r hr σ 0 = 0 :=
  map_zero (cupCochain f m n r hr σ : ↥((homogeneousCochains (.of ρ2)).X n) →L[k]
    ↥((homogeneousCochains (.of ρ3)).X r))

lemma cup_d_comm (m n r : ℕ) (hr : r = m + n) (σ : (homogeneousCochains (.of ρ1)).X m)
    (τ : (homogeneousCochains (.of ρ2)).X n) :
    (homogeneousCochains (.of ρ3)).d r (r + 1) (cupCochain f m n r hr σ τ) =
    cupCochain f (m + 1) n (r + 1) (by omega) ((homogeneousCochains (.of ρ1)).d m (m + 1) σ) τ +
    (-1) ^ m • cupCochain f m (n + 1) (r + 1) (by omega) σ
    ((homogeneousCochains (.of ρ2)).d n (n + 1) τ) := by
  subst hr
  refine Subtype.ext ?_
  rw [homogeneousCochains.d_apply, cupCochain_coe, d_hom_resolutionXCast, cupPair_d_comm,
    map_add, map_zsmul, resolutionXCast_trans, Submodule.coe_add, Submodule.coe_smul_of_tower,
    cupCochain_coe, cupCochain_coe, homogeneousCochains.d_apply, homogeneousCochains.d_apply]

variable {ρ1 ρ2 ρ3} in
/-- `cupCochain` vanishes when its first argument is zero. -/
@[simp, nolint simpNF] -- stated LHS is the form arising in practice, before hom-coe unfolding
lemma cupCochain_zero_apply (m n r : ℕ) (hr : r = m + n)
    (τ : (homogeneousCochains (.of ρ2)).X n) :
    cupCochain f m n r hr 0 τ = 0 :=
  congr($(map_zero (cupCochain f m n r hr).hom) τ)

variable {ρ1 ρ2 ρ3} in
/-- The cup product of two cocycles is a cocycle. -/
lemma d_cupCochain_eq_zero (m n r : ℕ) (hr : r = m + n)
    {σ : (homogeneousCochains (.of ρ1)).X m} {τ : (homogeneousCochains (.of ρ2)).X n}
    (hσ : (homogeneousCochains (.of ρ1)).d m (m + 1) σ = 0)
    (hτ : (homogeneousCochains (.of ρ2)).d n (n + 1) τ = 0) :
    (homogeneousCochains (.of ρ3)).d r (r + 1) (cupCochain f m n r hr σ τ) = 0 := by
  have h := cup_d_comm ρ1 ρ2 ρ3 f m n r hr σ τ
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
  (cupCochain f m n r hr σ.1 : ↥((homogeneousCochains (.of ρ2)).X n) →L[k]
      ↥((homogeneousCochains (.of ρ3)).X r)).restrict
    fun _ hτ ↦ LinearMap.mem_ker.2 (d_cupCochain_eq_zero f m n r hr
      (LinearMap.mem_ker.mp σ.2) (LinearMap.mem_ker.mp hτ))

variable {ρ1 ρ2 ρ3} in
@[simp]
lemma cupKerCLM_apply_coe (m n r : ℕ) (hr : r = m + n)
    (σ : ↥(TopModuleCat.ker ((homogeneousCochains (.of ρ1)).d m (m + 1))))
    (τ : ↥(TopModuleCat.ker ((homogeneousCochains (.of ρ2)).d n (n + 1)))) :
    (cupKerCLM f m n r hr σ τ).1 = cupCochain f m n r hr σ.1 τ.1 := rfl

/-- The coboundary map into the kernel model: the differential corestricted to the cocycles of
the next degree. In degree `0` the junk value `d 0 0 = 0` makes its range `⊥`, matching the
convention of `HomologicalComplex.homologyIsCokernel`. -/
noncomputable def bdryKer (X : TopRep k G) (j : ℕ) :
    (homogeneousCochains X).X (j - 1) ⟶
      TopModuleCat.ker ((homogeneousCochains X).d j (j + 1)) :=
  TopModuleCat.ofHom
    (((homogeneousCochains X).d (j - 1) j).hom.codRestrict _
      fun y ↦ LinearMap.mem_ker.2 (homogeneousCochains.d_comp_d_apply X (j - 1) j (j + 1) y))

@[simp]
lemma bdryKer_apply_coe (X : TopRep k G) (j : ℕ) (y : ↥((homogeneousCochains X).X (j - 1))) :
    (bdryKer X j y).1 = (homogeneousCochains X).d (j - 1) j y := rfl

variable {ρ1 ρ2 ρ3} in
/-- The cup product with a doubly-applied differential vanishes. -/
lemma cupCochain_d_comp_d (m i j l r : ℕ) (hr : r = m + l)
    (σ : (homogeneousCochains (.of ρ1)).X m) (τ : (homogeneousCochains (.of ρ2)).X i) :
    cupCochain f m l r hr σ
      ((homogeneousCochains (.of ρ2)).d j l ((homogeneousCochains (.of ρ2)).d i j τ)) = 0 := by
  rw [homogeneousCochains.d_comp_d_apply]
  exact map_zero (cupCochain f m l r hr σ : ↥((homogeneousCochains (.of ρ2)).X l) →L[k]
    ↥((homogeneousCochains (.of ρ3)).X r))

/-- The cup product of two coboundaries is a coboundary: `(d σ) ∪ (d τ) = d (σ ∪ d τ)`. This is
the special case of the Leibniz rule `cup_d_comm` where the second argument is a coboundary.

Note that `(d σ) ∪ (d τ)` is *not* zero in general: by the Leibniz rule it is the coboundary of
`σ ∪ d τ`. -/
lemma d_cup_d (m n r : ℕ) (hr : r = m + n) (σ : (homogeneousCochains (.of ρ1)).X m)
    (τ : (homogeneousCochains (.of ρ2)).X n) :
    cupCochain f (m + 1) (n + 1) (r + 2) (by omega) ((homogeneousCochains (.of ρ1)).d m (m + 1) σ)
      ((homogeneousCochains (.of ρ2)).d n (n + 1) τ) =
    (homogeneousCochains (.of ρ3)).d (r + 1) (r + 2) (cupCochain f m (n + 1) (r + 1) (by omega) σ
      ((homogeneousCochains (.of ρ2)).d n (n + 1) τ)) := by
  subst hr
  have h := cup_d_comm ρ1 ρ2 ρ3 f m (n + 1) (m + n + 1) rfl σ
    ((homogeneousCochains (.of ρ2)).d n (n + 1) τ)
  rw [cupCochain_d_comp_d] at h
  simpa only [smul_zero, add_zero] using h.symm

variable {ρ1 ρ2 ρ3} in
/-- Cupping a coboundary with a cocycle gives a coboundary. -/
lemma d_cupCochain_of_d_eq_zero (m n r : ℕ) (hr : r = m + n)
    (σ : (homogeneousCochains (.of ρ1)).X m) {τ : (homogeneousCochains (.of ρ2)).X n}
    (hτ : (homogeneousCochains (.of ρ2)).d n (n + 1) τ = 0) :
    cupCochain f (m + 1) n (r + 1) (by omega) ((homogeneousCochains (.of ρ1)).d m (m + 1) σ) τ =
      (homogeneousCochains (.of ρ3)).d r (r + 1) (cupCochain f m n r hr σ τ) := by
  have h := cup_d_comm ρ1 ρ2 ρ3 f m n r hr σ τ
  rw [hτ, cupCochain_apply_zero] at h
  have h0 : ∀ x : ↥((homogeneousCochains (.of ρ3)).X (r + 1)),
      x = x + (-1 : ℤ) ^ m • (0 : ↥((homogeneousCochains (.of ρ3)).X (r + 1))) := by simp
  exact (h0 _).trans h.symm

variable {ρ1 ρ2 ρ3} in
/-- Cupping a cocycle with a coboundary gives a coboundary, up to the sign `(-1) ^ m`. -/
lemma cupCochain_d_of_d_eq_zero (m n r : ℕ) (hr : r = m + n)
    {σ : (homogeneousCochains (.of ρ1)).X m} (τ : (homogeneousCochains (.of ρ2)).X n)
    (hσ : (homogeneousCochains (.of ρ1)).d m (m + 1) σ = 0) :
    cupCochain f m (n + 1) (r + 1) (by omega) σ ((homogeneousCochains (.of ρ2)).d n (n + 1) τ) =
      (-1 : ℤ) ^ m • (homogeneousCochains (.of ρ3)).d r (r + 1) (cupCochain f m n r hr σ τ) := by
  have h := cup_d_comm ρ1 ρ2 ρ3 f m n r hr σ τ
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
      cupKerCLM f m n r hr p.1 p.2 := by
  refine continuous_induced_rng.2 (continuous_induced_rng.2 ?_)
  change Continuous fun p : ↥(TopModuleCat.ker ((homogeneousCochains (.of ρ1)).d m (m + 1))) ×
      ↥(TopModuleCat.ker ((homogeneousCochains (.of ρ2)).d n (n + 1))) ↦
    (cupCochain f m n r hr p.1.1 p.2.1 : ↥((TopRep.of ρ3).resolution'.X r))
  have h2 : (fun p : ↥(TopModuleCat.ker ((homogeneousCochains (.of ρ1)).d m (m + 1))) ×
      ↥(TopModuleCat.ker ((homogeneousCochains (.of ρ2)).d n (n + 1))) ↦
      (cupCochain f m n r hr p.1.1 p.2.1 : ↥((TopRep.of ρ3).resolution'.X r))) =
      fun p ↦ resolutionXCast (.of ρ3) (by omega : n + 1 + m = r + 1)
        ((cupPair f (continuous_pair_of_discrete f) n m).1 p.1.1.1 p.2.1.1) := by
    funext p
    exact cupCochain_coe f m n r hr p.1.1 p.2.1
  rw [h2]
  exact (resolutionXCast (.of ρ3) (by omega : n + 1 + m = r + 1)).continuous.comp
    ((cupPair f (continuous_pair_of_discrete f) n m).2.comp
      (((continuous_subtype_val.comp continuous_subtype_val).comp continuous_fst).prodMk
        ((continuous_subtype_val.comp continuous_subtype_val).comp continuous_snd)))

variable {ρ1 ρ2 ρ3} in
/-- The cup product bundled as a morphism from the kernel of the differential into the
internal hom of the kernel models. -/
noncomputable def cupKerHom (f : ρ1 →ⁱL ρ2.linHom ρ3) (m n r : ℕ) (hr : r = m + n) :
    TopModuleCat.ker ((homogeneousCochains (.of ρ1)).d m (m + 1)) ⟶
      TopModuleCat.linHom (TopModuleCat.ker ((homogeneousCochains (.of ρ2)).d n (n + 1)))
        (TopModuleCat.ker ((homogeneousCochains (.of ρ3)).d r (r + 1))) :=
  TopModuleCat.homOfBilinear (cupKerCLM f m n r hr)
    (fun σ1 σ2 τ ↦ Subtype.ext (congr($(map_add (cupCochain f m n r hr).hom σ1.1 σ2.1) τ.1)))
    (fun c σ τ ↦ Subtype.ext (congr($(map_smul (cupCochain f m n r hr).hom c σ.1) τ.1)))
    (continuous_cupKerCLM_uncurry f m n r hr)

/-- The cup product of two cocycles, as a cocycle: by the Leibniz rule `cup_d_comm`, the
differential of `σ ∪ τ` vanishes when `d σ = 0` and `d τ = 0`. -/
noncomputable abbrev cupCocyclesAux (f : ρ1 →ⁱL ρ2.linHom ρ3) (m n r : ℕ) (hr : r = m + n)
    (σ : (homogeneousCochains (.of ρ1)).cycles m)
    (τ : (homogeneousCochains (.of ρ2)).cycles n) :
    (homogeneousCochains (.of ρ3)).cycles r :=
  letI σ' := ((homogeneousCochains (.of ρ1)).cyclesIsoKer m (m + 1) (by simp)).hom.hom σ
  letI τ' := ((homogeneousCochains (.of ρ2)).cyclesIsoKer n (n + 1) (by simp)).hom.hom τ
  ((homogeneousCochains (.of ρ3)).cyclesIsoKer r (r + 1) (by simp)).inv.hom
    ⟨cupCochain f m n r hr σ' τ',
      LinearMap.mem_ker.2 (d_cupCochain_eq_zero f m n r hr
        (LinearMap.mem_ker.mp σ'.2) (LinearMap.mem_ker.mp τ'.2))⟩

/-- The cup product on cocycles: the kernel-model pairing `cupKerHom` transported along the
identifications `cyclesIsoKer` of the cycles of the homogeneous cochain complexes with the
kernels of the differentials, pairing a degree-`m` cocycle with a degree-`n` cocycle to give a
degree-`r = m + n` cocycle. -/
noncomputable def cupCocycles (f : ρ1 →ⁱL ρ2.linHom ρ3) (m n r : ℕ) (hr : r = m + n) :
    (homogeneousCochains (.of ρ1)).cycles m ⟶
      TopModuleCat.linHom ((homogeneousCochains (.of ρ2)).cycles n)
        ((homogeneousCochains (.of ρ3)).cycles r) :=
  ((homogeneousCochains (.of ρ1)).cyclesIsoKer m (m + 1) (by simp)).hom ≫
    cupKerHom f m n r hr ≫
      TopModuleCat.linHomMap
        ((homogeneousCochains (.of ρ2)).cyclesIsoKer n (n + 1) (by simp)).hom
        ((homogeneousCochains (.of ρ3)).cyclesIsoKer r (r + 1) (by simp)).inv

variable {ρ1 ρ2 ρ3} in
@[simp]
lemma cupCocycles_apply (f : ρ1 →ⁱL ρ2.linHom ρ3) (m n r : ℕ) (hr : r = m + n)
    (σ : (homogeneousCochains (.of ρ1)).cycles m)
    (τ : (homogeneousCochains (.of ρ2)).cycles n) :
    cupCocycles ρ1 ρ2 ρ3 f m n r hr σ τ = cupCocyclesAux ρ1 ρ2 ρ3 f m n r hr σ τ := rfl

lemma up_nat_prev (j : ℕ) : (ComplexShape.up ℕ).prev j = j - 1 := by
  cases j with
  | zero => simp
  | succ i => simp

/-- Under the identification of the cycles with the kernel model, `toCycles` becomes the
corestricted differential `bdryKer`. -/
lemma toCycles_comp_cyclesIsoKer_hom (X : TopRep k G) (j : ℕ) :
    (homogeneousCochains X).toCycles (j - 1) j ≫
      ((homogeneousCochains X).cyclesIsoKer j (j + 1) (by simp)).hom = bdryKer X j := by
  refine ConcreteCategory.hom_ext _ _ fun y ↦ Subtype.ext ?_
  rw [ConcreteCategory.comp_apply, (homogeneousCochains X).cyclesIsoKer_hom_apply_coe,
    bdryKer_apply_coe]
  exact congr($((homogeneousCochains X).toCycles_i (i := j - 1) (j := j)) y)

/-- Continuous cohomology identified with the quotient of the kernel model of the cocycles by
the coboundaries, carrying the quotient topology. -/
noncomputable def cohomologyIsoQuot (X : TopRep k G) (j : ℕ) :
    continuousCohomology j X ≅ TopModuleCat.coker (bdryKer X j) :=
  (homogeneousCochains X).homologyIsoCoker (j - 1) j (up_nat_prev j) ≪≫
    TopModuleCat.cokerCongr ((homogeneousCochains X).cyclesIsoKer j (j + 1) (by simp))
      (toCycles_comp_cyclesIsoKer_hom X j)

variable {ρ1 ρ2 ρ3} in
/-- Cupping a coboundary with a cocycle dies in the quotient by the coboundaries. -/
lemma cokerπ_cupKerCLM_bdryKer_left (m n r : ℕ) (hr : r = m + n)
    (y : ↥((homogeneousCochains (.of ρ1)).X (m - 1)))
    (τ : ↥(TopModuleCat.ker ((homogeneousCochains (.of ρ2)).d n (n + 1)))) :
    TopModuleCat.cokerπ (bdryKer (.of ρ3) r)
      (cupKerCLM f m n r hr (bdryKer (.of ρ1) m y) τ) = 0 := by
  cases m with
  | zero =>
    have h0 : bdryKer (TopRep.of ρ1) 0 y = 0 := Subtype.ext (by
      rw [bdryKer_apply_coe, (homogeneousCochains (TopRep.of ρ1)).shape _ _ (by simp)]
      rfl)
    have h1 : cupKerCLM f 0 n r hr (bdryKer (TopRep.of ρ1) 0 y) τ = 0 := by
      rw [h0]
      exact Subtype.ext (by
        rw [cupKerCLM_apply_coe]
        simpa using cupCochain_zero_apply f 0 n r hr τ.1)
    rw [h1]
    exact (TopModuleCat.cokerπ (bdryKer (TopRep.of ρ3) r)).hom.map_zero
  | succ i =>
    obtain rfl : r = i + n + 1 := by omega
    rw [TopModuleCat.cokerπ_eq_zero_iff]
    exact ⟨cupCochain f i n (i + n) rfl y τ.1, Subtype.ext
      (d_cupCochain_of_d_eq_zero f i n (i + n) rfl y (LinearMap.mem_ker.mp τ.2)).symm⟩

variable {ρ1 ρ2 ρ3} in
/-- Cupping a cocycle with a coboundary dies in the quotient by the coboundaries. -/
lemma cokerπ_cupKerCLM_bdryKer_right (m n r : ℕ) (hr : r = m + n)
    (σ : ↥(TopModuleCat.ker ((homogeneousCochains (.of ρ1)).d m (m + 1))))
    (y : ↥((homogeneousCochains (.of ρ2)).X (n - 1))) :
    TopModuleCat.cokerπ (bdryKer (.of ρ3) r)
      (cupKerCLM f m n r hr σ (bdryKer (.of ρ2) n y)) = 0 := by
  cases n with
  | zero =>
    have h0 : bdryKer (TopRep.of ρ2) 0 y = 0 := Subtype.ext (by
      rw [bdryKer_apply_coe, (homogeneousCochains (TopRep.of ρ2)).shape _ _ (by simp)]
      rfl)
    rw [h0, (cupKerCLM f m 0 r hr σ).map_zero]
    exact (TopModuleCat.cokerπ (bdryKer (TopRep.of ρ3) r)).hom.map_zero
  | succ i =>
    obtain rfl : r = m + i + 1 := by omega
    rw [TopModuleCat.cokerπ_eq_zero_iff]
    refine ⟨(-1 : ℤ) ^ m • cupCochain f m i (m + i) rfl σ.1 y, Subtype.ext ?_⟩
    change (homogeneousCochains (TopRep.of ρ3)).d (m + i) (m + i + 1)
        ((-1 : ℤ) ^ m • cupCochain f m i (m + i) rfl σ.1 y) =
      cupCochain f m (i + 1) (m + i + 1) (by omega) σ.1
        ((homogeneousCochains (TopRep.of ρ2)).d i (i + 1) y)
    rw [map_zsmul]
    exact (cupCochain_d_of_d_eq_zero f m i (m + i) rfl y (LinearMap.mem_ker.mp σ.2)).symm

/-- The cup product on continuous group cohomology induced by an intertwining map
`f : ρ1 →ⁱL linHom ρ2 ρ3`: descend the kernel-model cup product `cupKerHom` to the quotients
by the coboundaries on all three slots, and transport along `cohomologyIsoQuot`. -/
noncomputable def cup (f : ρ1 →ⁱL ρ2.linHom ρ3) (m n r : ℕ) (hr : r = m + n) :
    (continuousCohomology m (of ρ1)) ⟶
      TopModuleCat.linHom ((continuousCohomology n (of ρ2)))
        ((continuousCohomology r (of ρ3))) :=
  (cohomologyIsoQuot (of ρ1) m).hom ≫
    TopModuleCat.cokerDescBilinear (bdryKer (of ρ1) m) (bdryKer (of ρ2) n) (bdryKer (of ρ3) r)
      (cupKerHom f m n r hr) (continuous_cupKerCLM_uncurry f m n r hr)
      (fun y τ ↦ cokerπ_cupKerCLM_bdryKer_left f m n r hr y τ)
      (fun σ y ↦ cokerπ_cupKerCLM_bdryKer_right f m n r hr σ y) ≫
    TopModuleCat.linHomMap (cohomologyIsoQuot (of ρ2) n).hom (cohomologyIsoQuot (of ρ3) r).inv

end Cup

end ContRepresentation
