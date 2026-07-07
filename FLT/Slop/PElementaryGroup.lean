/-
Copyright (c) 2025 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McCarthy
-/
module

public import Mathlib.GroupTheory.Nilpotent
public import FLT.Slop.Background.Group.PDecomposition
public import FLT.Slop.Background.Group.Basic
public import FLT.Slop.Background.Group.InternalDirectProduct
public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
public import Mathlib.GroupTheory.Index

@[expose] public section

/-!
# `p`-Elementary groups

This file defines `p`-elementary groups and develops their basic structure.

A `p`-elementary group is represented by explicit data: a cyclic prime-to-`p`
part `C`, a `p`-group part `P`, elementwise commutation between `C` and `P`,
and a decomposition of every element as a product `c * q`.

The file also constructs the `p`-elementary group associated to a `p`-regular
element `x`, namely the subgroup `Subgroup.zpowers x ⊔ P_of_Z p x`, where
`P_of_Z p x` is a chosen Sylow `p`-subgroup of the centralizer of `x`.
-/

universe u v

namespace BrauerInduction

/--
A group `G` is `p`-elementary if it is the product of a cyclic `p`-regular
subgroup `C` and a `p`-group `P`, with `C` centralizing `P`.

The structure is data-bearing: it records chosen subgroups `C` and `P`. The
corresponding proposition is expressed as `Nonempty (PElementary p G)`, or
equivalently `IsPElementary p G`.
-/
structure PElementary (p : ℕ) (G : Type u) [Group G] where
  protected C : Subgroup G
  protected P : Subgroup G
  protected C_isCyclic : IsCyclic C
  protected P_isPGroup : IsPGroup p P
  protected C_isPRegular : ∀ {c : G}, c ∈ C → IsPRegular p c
  protected comm : ∀ {c q : G}, c ∈ C → q ∈ P → Commute c q
  protected decompose : ∀ h : G, ∃ c ∈ C, ∃ q ∈ P, c * q = h

/-- A group is `p`-elementary if it admits a `PElementary p` structure. -/
def IsPElementary (p : ℕ) (G : Type u) [Group G] : Prop :=
  Nonempty (PElementary p G)

namespace PElementary

variable {p : ℕ} {G : Type u} [Group G] {g : G}

lemma isPSingular_of_mem_P [Fact p.Prime]
    (e : PElementary p G) {g : G} (hg : g ∈ e.P) :
    IsPSingular p g := by
  rcases (IsPGroup.iff_orderOf).1 e.P_isPGroup ⟨g, hg⟩ with ⟨k, hk⟩
  exact ⟨k, by simpa [Subgroup.orderOf_coe] using hk⟩

/--
In a `p`-elementary group `G = C * P`, an element of `G` is `p`-singular
iff it lies in the `p`-subgroup part `P`.
-/
lemma mem_P_iff_pSingular [Fact p.Prime]
    (e : PElementary p G) {g : G} :
    g ∈ e.P ↔ IsPSingular p g := by
  constructor
  · intro hg
    exact e.isPSingular_of_mem_P hg
  · intro hgu
    rcases e.decompose g with ⟨c, cC, q, qP, hg_eq⟩
    have hcr : IsPRegular p c := e.C_isPRegular cC
    have hqs  : IsPSingular p q := e.isPSingular_of_mem_P qP
    have hf : IsOfFinOrder (c * q) := by
      rw [hg_eq]
      exact hgu.isOfFinOrder
    have hcomm : q * c = c * q := by
      rw [e.comm cC qP]
    obtain ⟨hq_eq, hc_eq⟩ :=
      Group.pSingular_pRegular_unique p hf hcomm rfl hqs  hcr
    have hc1 : c = 1 := by
      rw [hc_eq]
      exact Group.isPSingular_pRegular_eq_one p hf (by simpa [hg_eq] using hgu)
    rw [← hg_eq, hc1, one_mul]
    exact qP

/--
In a `p`-elementary group `G = C * P`, an element of `G` is `p`-regular
iff it lies in the cyclic subgroup part `C`.
-/
lemma mem_C_iff_pRegular [Fact p.Prime]
    (e : PElementary p G) {g : G} :
    g ∈ e.C ↔ IsPRegular p g := by
  constructor
  · intro hg
    exact e.C_isPRegular hg
  · intro hgr
    rcases e.decompose g with ⟨c, cC, q, qP, hg_eq⟩
    have hps  : IsPSingular p q := e.isPSingular_of_mem_P qP
    have hpr : IsPRegular p c := e.C_isPRegular cC
    have hf : IsOfFinOrder (c * q) := by
      rw [hg_eq]
      exact hgr.isOfFinOrder
    have hcomm : q * c = c * q := by
      rw [e.comm cC qP]
    obtain ⟨hq_eq, hc_eq⟩ :=
      Group.pSingular_pRegular_unique p hf hcomm rfl hps  hpr
    have hq1 : q = 1 := by
      rw [hq_eq]
      exact Group.isPRegular_pSingular_eq_one p hf (by simpa [hg_eq] using hgr)
    rw [← hg_eq, hq1, mul_one]
    exact cC

/--
In a `p`-elementary group, the cyclic prime-to-`p` part is finite.
-/
lemma finite_C [Fact p.Prime]
    (e : PElementary p G) :
    Finite e.C := by
  obtain ⟨g, hg⟩ := isCyclic_iff_exists_zpowers_eq_top.mp e.C_isCyclic
  have hp_reg : IsPRegular p (g : G) := e.C_isPRegular g.property
  have hfin : IsOfFinOrder (g : G) := IsPRegular.isOfFinOrder p hp_reg
  have h_ord : 0 < orderOf g := by
    have h_ordG : 0 < orderOf (g : G) := orderOf_pos_iff.mpr hfin
    simp only [Subgroup.orderOf_coe] at h_ordG ⊢
    exact h_ordG
  let φ : Subgroup.zpowers g ≃ e.C :=
    (MulEquiv.subgroupCongr hg).toEquiv.trans Subgroup.topEquiv.toEquiv
  have h_card : Nat.card e.C = Nat.card (Subgroup.zpowers g) :=
    Nat.card_congr φ.symm
  have h_pos : 0 < Nat.card e.C := by
    rw [h_card, Nat.card_zpowers]
    exact h_ord
  exact (Nat.card_pos_iff.mp h_pos).2

/--
Every element of a `p`-elementary group has finite order.
-/
lemma isOfFinOrder [Fact p.Prime]
    (e : PElementary p G) (g : G) :
    IsOfFinOrder g := by
  rcases e.decompose g with ⟨c, hc, q, hq, rfl⟩
  exact Commute.isOfFinOrder_mul
    (e.comm hc hq)
    (IsPRegular.isOfFinOrder p (e.C_isPRegular hc))
    (IsPSingular.isOfFinOrder p (e.isPSingular_of_mem_P hq))

/--
The order of the cyclic factor of a `p`-elementary group is coprime to `p`.
-/
lemma card_C_coprime_p [Fact p.Prime]
    (e : PElementary p G) :
    Nat.Coprime (Nat.card e.C) p := by
  haveI : IsCyclic e.C := e.C_isCyclic
  letI : CommGroup e.C := IsCyclic.commGroup
  haveI : Finite e.C := e.finite_C
  obtain ⟨g, hg⟩ : ∃ g : e.C, orderOf g = Monoid.exponent e.C := by
    apply Monoid.exists_orderOf_eq_exponent
    exact Monoid.ExponentExists.of_finite
  have hg_regG : IsPRegular p (g : G) := e.C_isPRegular g.property
  have hg_coprimeG : Nat.Coprime (orderOf (g : G)) p :=
    IsPRegular.order_coprime p hg_regG
  have hg_coprimeC : Nat.Coprime (orderOf g) p := by
    simpa [Subgroup.orderOf_coe] using hg_coprimeG
  have : Nat.Coprime (Monoid.exponent e.C) p := by
    simpa [hg] using hg_coprimeC
  rw [← IsCyclic.exponent_eq_card]
  exact this

lemma inf_C_P_eq_bot [Fact p.Prime]
    (e : PElementary p G) : e.C ⊓ e.P = ⊥ := by
  ext x
  simp only [Subgroup.mem_inf, Subgroup.mem_bot]
  constructor
  · rintro ⟨hx_C, hx_P⟩
    have hs  : IsPSingular p x := (e.mem_P_iff_pSingular).mp hx_P
    have hr : IsPRegular p x := (e.mem_C_iff_pRegular).mp hx_C
    exact IsPSingular.isPRegular_eq_one p x hs  hr
  · rintro rfl
    exact ⟨Subgroup.one_mem _, Subgroup.one_mem _⟩

/--
The product map `C × P → G` is an isomorphism for a `p`-elementary group.
-/
noncomputable def mulEquivProd [Fact p.Prime]
    (e : PElementary p G) : e.C × e.P ≃* G :=
  (Subgroup.mulEquivProdOfInternalDirect e.C e.P (⊤ : Subgroup G)
    le_top le_top e.comm (e.inf_C_P_eq_bot)
    (by
      intro g _
      exact e.decompose g)).trans Subgroup.topEquiv

/--
The `P`-part of a `p`-elementary group is finite if the whole group is finite.
-/
private lemma finite_P_of_finite
    (e : PElementary p G) [Finite G] :
    Finite e.P := inferInstance

lemma isNilpotent_of_finite_P [Fact p.Prime]
    (e : PElementary p G) [Finite e.P] :
    Group.IsNilpotent G := by
  haveI : Group.IsNilpotent e.C :=
    @CommGroup.isNilpotent e.C (e.C_isCyclic.commGroup)
  haveI : Group.IsNilpotent e.P :=
    IsPGroup.isNilpotent e.P_isPGroup
  exact Group.nilpotent_of_mulEquiv e.mulEquivProd

lemma isNilpotent
    [Fact p.Prime] [Finite G]
    (e : PElementary p G) :
    Group.IsNilpotent G := by
  haveI : Finite e.P := finite_P_of_finite e
  exact e.isNilpotent_of_finite_P

/-- The centralizer of `x`. -/
abbrev Z (x : G) : Subgroup G := Subgroup.centralizer ({x})

/-- The cyclic subgroup generated by `x`. -/
abbrev Cyc (x : G) : Subgroup G := Subgroup.zpowers x

@[simp]
lemma cyc_isCyclic (x : G) : IsCyclic (Cyc x) := by
  simp only [Subgroup.isCyclic_iff_exists_zpowers_eq_top]
  use x

lemma commute_of_mem_Z_of_mem_Cyc {x z c : G} (hz : z ∈ Z x)
    (hc : c ∈ Cyc x) : Commute c z := by
  rcases Subgroup.mem_zpowers_iff.mp hc with ⟨n, rfl⟩
  exact Commute.zpow_left (hz x rfl) n

/--
A chosen Sylow `p`-subgroup of the centralizer `Z x`.
-/
noncomputable def P_in_Z (p : ℕ) (x : G) : Sylow p (Z x) :=
  Classical.choice (Sylow.nonempty : Nonempty (Sylow p (Z x)))

/-- Inclusion of `Z(x)` into `G`. -/
def inclZ (x : G) : Z x →* G := Subgroup.subtype (Z x)

/--
The chosen Sylow `p`-subgroup of `Z x`, viewed as a subgroup of the ambient
group `G`.
-/
noncomputable def P_of_Z (p : ℕ) (x : G) : Subgroup G :=
  Subgroup.map (inclZ x) (P_in_Z p x)

lemma P_of_Z_isPGroup (x : G) :
    IsPGroup p (P_of_Z p x) := IsPGroup.map (P_in_Z p x).isPGroup' (inclZ x)

/--
The chosen Sylow `p`-subgroup of `Z x`, viewed inside `G`, is contained in
`Z x`.
-/
lemma P_of_Z_le_Z (x : G) : P_of_Z p x ≤ Z x := by
  rw [P_of_Z]
  apply Subgroup.map_le_iff_le_comap.mpr
  intro g _
  exact g.property

lemma card_P_of_Z_eq_card_P_in_Z [Fact p.Prime] (x : G) :
    Nat.card ↥(P_of_Z p x)
      =
    Nat.card ↥((P_in_Z p x : Subgroup (Z x))) := by
  simpa [P_of_Z, PElementary.inclZ] using
    (Subgroup.card_map_of_injective (f := inclZ x) Subtype.coe_injective)

/--
The index of the chosen Sylow `p`-subgroup in the centralizer of `x` is not
divisible by `p`.
-/
lemma p_not_dvd_cardCentralizer_div_cardP
    [Fact p.Prime] (x : G) [Finite (Z x)] :
    ¬ p ∣ (Nat.card (Z x : Set G) / Nat.card (P_of_Z p x)) := by
  rw [PElementary.card_P_of_Z_eq_card_P_in_Z x]
  haveI : Finite (P_in_Z p x : Subgroup (Z x)) := inferInstance
  haveI : (P_in_Z p x : Subgroup (Z x)).FiniteIndex := inferInstance
  have h_div :
      Nat.card ↥(Z x : Set G) /
          Nat.card ↥(P_in_Z p x : Subgroup (Z x))
        =
      (P_in_Z p x : Subgroup (Z x)).index := by
    exact Nat.div_eq_of_eq_mul_left
      Nat.card_pos
      (Subgroup.index_mul_card (P_in_Z p x : Subgroup (Z x))).symm
  rw [h_div]
  exact Sylow.not_dvd_index (PElementary.P_in_Z p x)

/--
If every element of `C` commutes with every element of `P`, then every element
of `C ⊔ P` can be written as `c * p`.
-/
lemma sup_decompose_of_commute
    {C P : Subgroup G}
    (hcomm : ∀ ⦃c p : G⦄, c ∈ C → p ∈ P → Commute c p) :
    ∀ {h : G}, h ∈ C ⊔ P → ∃ c ∈ C, ∃ p ∈ P, c * p = h := by
  intro h hh
  have eq_closure : C ⊔ P = Subgroup.closure ((C : Set G) ∪ P) := by
    symm
    simp [Subgroup.closure_union]
  rw [eq_closure] at hh
  refine Subgroup.closure_induction
    (p := fun x _ => ∃ c ∈ C, ∃ p ∈ P, c * p = x)
    ?mem ?one ?mul ?inv hh
  · rintro x (hx | hx)
    · exact ⟨x, hx, 1, P.one_mem, by simp⟩
    · exact ⟨1, C.one_mem, x, hx, by simp⟩
  · exact ⟨1, C.one_mem, 1, P.one_mem, by simp⟩
  · rintro a b - - ⟨c1, hc1, p1, hp1, rfl⟩ ⟨c2, hc2, p2, hp2, rfl⟩
    refine ⟨c1 * c2, C.mul_mem hc1 hc2, p1 * p2, P.mul_mem hp1 hp2, ?_⟩
    calc (c1 * c2) * (p1 * p2)
      _ = c1 * (c2 * p1) * p2 := by simp [mul_assoc]
      _ = c1 * (p1 * c2) * p2 := by rw [(hcomm hc2 hp1).eq]
      _ = (c1 * p1) * (c2 * p2) := by simp [mul_assoc]
  · rintro a - ⟨c, hc, p, hp, rfl⟩
    exact ⟨c⁻¹, C.inv_mem hc, p⁻¹, P.inv_mem hp,
      by simp [mul_inv_rev, (hcomm hc hp).inv_left.inv_right.eq]⟩

/--
The `p`-elementary structure on the subgroup associated to a `p`-regular element
`x`.

The underlying group is `Cyc x ⊔ P_of_Z p x`.
-/
noncomputable def associatedSubgroup {x : G} (hx : IsPRegular p x) :
    PElementary p ((Cyc x ⊔ P_of_Z p x : Subgroup G)) := by
  let H : Subgroup G := Cyc x ⊔ P_of_Z p x
  let C_H : Subgroup H :=
    Subgroup.comap (Subgroup.subtype H) (Cyc x)
  let P_H : Subgroup H :=
    Subgroup.comap (Subgroup.subtype H) (P_of_Z p x)
  exact
  { C := C_H
    P := P_H

    C_isCyclic := by
      have hle : Cyc x ≤ H := le_sup_left
      let φ := Subgroup.subgroupOfEquivOfLe hle
      exact (MulEquiv.isCyclic φ.symm).mp (cyc_isCyclic (G := G) x)

    P_isPGroup := by
      have hle : P_of_Z p x ≤ H := le_sup_right
      exact IsPGroup.of_equiv
        (P_of_Z_isPGroup (p := p) x)
        (Subgroup.subgroupOfEquivOfLe hle).symm

    C_isPRegular := by
      intro c hc
      have hcG : ((c : H) : G) ∈ Cyc x := hc
      have hc_regG : IsPRegular p ((c : H) : G) :=
        IsPRegular.of_mem_zpowers p hcG hx
      simpa [IsPRegular, Subgroup.orderOf_coe] using hc_regG

    comm := by
      intro c q hc hq
      have hcG : ((c : H) : G) ∈ Cyc x := hc
      have hqG : ((q : H) : G) ∈ P_of_Z p x := hq
      have hqZ : ((q : H) : G) ∈ Z x :=
        P_of_Z_le_Z (p := p) x hqG
      have hcommG : Commute ((c : H) : G) ((q : H) : G) :=
        commute_of_mem_Z_of_mem_Cyc (x := x) hqZ hcG
      apply Subtype.ext
      exact hcommG.eq

    decompose := by
      intro h
      have hh : ((h : H) : G) ∈ H := h.property
      rcases sup_decompose_of_commute
          (G := G)
          (C := Cyc x)
          (P := P_of_Z p x)
          (by
            intro c q hc hq
            have hqZ : q ∈ Z x := P_of_Z_le_Z (p := p) x hq
            exact commute_of_mem_Z_of_mem_Cyc (x := x) hqZ hc)
          hh with ⟨c, hc, q, hq, h_eq⟩
      refine ⟨⟨c, Subgroup.mem_sup_left hc⟩, hc,
              ⟨q, Subgroup.mem_sup_right hq⟩, hq, ?_⟩
      ext
      exact h_eq
}

/--
A subgroup of a `p`-elementary group is `p`-elementary.

The cyclic and `p`-group parts are obtained by intersecting the original parts
with the subgroup.
-/
def ofSubgroup [Fact p.Prime]
    (e : PElementary p G) (K : Subgroup G) :
    PElementary p K where
  C := Subgroup.comap (Subgroup.subtype K) e.C
  P := Subgroup.comap (Subgroup.subtype K) e.P

  C_isCyclic := by
    let C_K : Subgroup K := Subgroup.comap (Subgroup.subtype K) e.C
    let K_C : Subgroup e.C := Subgroup.comap (Subgroup.subtype e.C) K
    have hKC : IsCyclic K_C := by
      haveI : IsCyclic e.C := e.C_isCyclic
      exact Subgroup.isCyclic_of_le (show K_C ≤ ⊤ by
        intro x hx
        trivial)
    exact
      (MulEquiv.isCyclic
        (Subgroup.comapSubtypeCommEquiv (G := G) K e.C).symm).mp hKC
  P_isPGroup := by
    let P_K : Subgroup K := Subgroup.comap (Subgroup.subtype K) e.P
    let f : P_K →* e.P :=
      { toFun := fun x => ⟨((x : K) : G), x.property⟩
        map_one' := rfl
        map_mul' := by
          intro x y
          rfl }
    have hf : Function.Injective f := by
      intro x y hxy
      have hG : ((x : K) : G) = ((y : K) : G) := by
        simpa [f] using congrArg (fun z : e.P => (z : G)) hxy
      apply Subtype.ext
      apply Subtype.ext
      exact hG
    exact IsPGroup.of_injective e.P_isPGroup f hf
  C_isPRegular := by
    intro c hc
    exact (IsPRegular.subtype_iff (p := p) c).1 (e.C_isPRegular hc)
  comm := by
    intro c q hc hq
    exact (Subgroup.commute_subtype_iff c q).1 (e.comm hc hq)
  decompose := by
    intro k
    rcases e.decompose (k : G) with ⟨c, hc, q, hq, hk_eq⟩
    have hk_fin : IsOfFinOrder (k : G) := e.isOfFinOrder (k : G)
    obtain ⟨hq_eq, hc_eq⟩ :=
      Group.pSingular_pRegular_unique p hk_fin
        (by rw [← hk_eq, (e.comm hc hq).eq])
        hk_eq
        (e.isPSingular_of_mem_P hq)
        (e.C_isPRegular hc)
    refine
      ⟨⟨c, hc_eq ▸ Subgroup.zpow_mem K k.property _⟩, hc,
       ⟨q, hq_eq ▸ Subgroup.zpow_mem K k.property _⟩, hq, ?_⟩
    ext
    exact hk_eq

/--
Transport a `p`-elementary structure across a group isomorphism.
-/
def ofMulEquiv {G : Type u} {G' : Type v} [Group G] [Group G']
    (eG : PElementary p G) (φ : G ≃* G') : PElementary p G' where
  C := eG.C.map φ.toMonoidHom
  P := eG.P.map φ.toMonoidHom
  C_isCyclic := by
    have hf_inj : Function.Injective φ.toMonoidHom := φ.injective
    let ψ := eG.C.equivMapOfInjective φ.toMonoidHom hf_inj
    exact (MulEquiv.isCyclic ψ).mp eG.C_isCyclic
  P_isPGroup := IsPGroup.map eG.P_isPGroup φ.toMonoidHom
  C_isPRegular := by
    rintro _ ⟨y, hy, rfl⟩
    have horder : orderOf (φ.toMonoidHom y) = orderOf y := by
      simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, MulEquiv.orderOf_eq]
    have hy_reg : (orderOf y).Coprime p := by
      rw [← horder]
      simpa [IsPRegular] using eG.C_isPRegular hy
    simpa [IsPRegular, horder] using hy_reg
  comm := by
    rintro _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
    exact (eG.comm hx hy).map φ.toMonoidHom
  decompose := by
    intro g'
    obtain ⟨c, hc, q, hq, h_eq⟩ := eG.decompose (φ.symm g')
    refine ⟨φ c, ⟨c, hc, rfl⟩, φ q, ⟨q, hq, rfl⟩, ?_⟩
    rw [← map_mul, h_eq, φ.apply_symm_apply]

/--
Transport a `p`-elementary structure across a multiplicative equivalence.
-/
abbrev mapEquiv {G : Type u} {G' : Type v} [Group G] [Group G']
    (eG : PElementary p G) (φ : G ≃* G') :
    PElementary p G' := PElementary.ofMulEquiv eG φ

/--
In the `p`-elementary subgroup associated to a `p`-regular element `r`, the
elements whose `p`-regular part is `r` are exactly the elements of the coset
`r * P_of_Z p r`.
-/
lemma mem_associatedSubgroup_fiber [Fact p.Prime]
    {r : G} (hr : IsPRegular p r)
    (h : ↥(Subgroup.zpowers r ⊔ P_of_Z p r)) :
    Group.pRegular p (h : G) = r ↔ ∃ s ∈ P_of_Z p r, (h : G) = r * s := by
  let H := Subgroup.zpowers r ⊔ P_of_Z p r
  let eH := associatedSubgroup (p := p) hr
  have hf : IsOfFinOrder (h : G) := by
    have hfH : IsOfFinOrder h := eH.isOfFinOrder h
    exact (Submonoid.isOfFinOrder_coe (x := h)).2 hfH
  constructor
  · intro h_reg_is_s
    let s := Group.pSingular p (h : G)
    have h_decomp : (h : G) = r * s := by
      simp only [← h_reg_is_s]
      rw [Group.pDecomp' p hf]
    use s
    constructor
    · have s_in_H : s ∈ H := by
        rw [eq_inv_mul_iff_mul_eq.mpr h_decomp.symm]
        apply Subgroup.mul_mem
        · apply Subgroup.inv_mem
          apply Subgroup.mem_sup_left
          simp only [Subgroup.mem_zpowers]
        · exact h.property
      have hsH : (⟨s, s_in_H⟩ : H) ∈ eH.P := by
        rw [eH.mem_P_iff_pSingular]
        exact
          (IsPSingular.subtype_iff p (x := ⟨s, s_in_H⟩)).1
              (Group.isPSingular_pSingular p (h : G))
      exact hsH
    · exact h_decomp
  · rintro ⟨s, hs, h_eq⟩
    rw [h_eq]
    have hsr_fin : IsOfFinOrder (r * s) := by
      simpa [← h_eq] using hf
    apply Group.pRegular_mul_eq_self_of_pSingular_commute p hsr_fin
    · exact hr
    · have s_in_H : s ∈ H := Subgroup.mem_sup_right hs
      have huH : (⟨s, s_in_H⟩ : H) ∈ eH.P := hs
      have : IsPSingular p (⟨s, s_in_H⟩ : H) := (eH.mem_P_iff_pSingular).mp huH
      exact (IsPSingular.subtype_iff p (x := ⟨s, s_in_H⟩)).2 this
    · have h_comm := P_of_Z_le_Z (p := p) r hs
      simp only [Subgroup.mem_centralizer_iff, Set.mem_singleton_iff] at h_comm
      exact (commute_iff_eq r s).mpr (h_comm r rfl)

/--
If a `p`-singular element acts on `G ⧸ H`, then the number of fixed cosets
is congruent modulo `p` to the total number of cosets.
-/
lemma card_fixedPoints_pSingular_modEq
    [hp : Fact p.Prime]
    (H : Subgroup G) [H.FiniteIndex] (s : G) (hs : IsPSingular p s) :
    Nat.card { c : G ⧸ H // s • c = c } ≡ Nat.card (G ⧸ H) [MOD p] := by
  let zs := Subgroup.zpowers s
  have hU_pgroup : IsPGroup p zs := by
    intro ⟨g, hg⟩
    rcases hs with ⟨k, hk⟩
    use k
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    ext
    simp only [Subgroup.coe_pow, Subgroup.coe_one]
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast]
    have hs_one : s ^ (p ^ k) = 1 := by rw [← hk, pow_orderOf_eq_one]
    rw [hs_one, one_zpow]
  have h_fix_eq : Nat.card { c : G ⧸ H // s • c = c } =
                  Nat.card (MulAction.fixedPoints zs (G ⧸ H)) := by
    apply Nat.card_congr
    refine { toFun := fun ⟨c, hc⟩ => ⟨c, ?_⟩,
             invFun := fun ⟨c, hc⟩ => ⟨c, ?_⟩,
             left_inv := fun _ => by ext; rfl,
             right_inv := fun _ => by ext; rfl }
    · intro ⟨g, hg⟩
      let cStab : Subgroup G := MulAction.stabilizer G c
      have hs_cStab : s ∈ cStab := by change s • c = c;  simpa using hc
      rcases (Subgroup.mem_zpowers_iff.mp hg) with ⟨n, rfl⟩
      have : (s ^ n) ∈ cStab := by exact cStab.zpow_mem hs_cStab n
      exact MulAction.mem_stabilizer_iff.mp this
    · exact hc ⟨s, Subgroup.mem_zpowers s⟩
  rw [h_fix_eq]
  exact (hU_pgroup.card_modEq_card_fixedPoints (G ⧸ H)).symm

end PElementary

namespace IsPElementary

open BrauerInduction

variable {p : ℕ} {G : Type u} [Group G]

/--
Transport `p`-elementarity across a multiplicative equivalence.
-/
lemma ofMulEquiv
    (p : ℕ)
    {G : Type u} {G' : Type v} [Group G] [Group G']
    (hG : IsPElementary p G) (e : G ≃* G') :
    IsPElementary p G' := by
  obtain ⟨eG⟩ := hG
  exact ⟨PElementary.ofMulEquiv eG e⟩

/--
Unpack the definition of `IsPElementary` into explicit cyclic, `p`-group,
commutativity, and decomposition data.
-/
lemma iff :
    IsPElementary p G ↔ ∃ (C P : Subgroup G),
      IsCyclic C ∧ IsPGroup p P ∧
      (∀ {c : G}, c ∈ C → IsPRegular p c) ∧
      (∀ {c q : G}, c ∈ C → q ∈ P → Commute c q) ∧
      (∀ h : G, ∃ c ∈ C, ∃ q ∈ P, c * q = h) := by
  constructor
  · intro hG
    obtain ⟨e⟩ := hG
    exact ⟨e.C, e.P, e.C_isCyclic, e.P_isPGroup,
           e.C_isPRegular, e.comm, e.decompose⟩
  · intro h
    obtain ⟨C, P, C_cyc, P_pg, C_reg, comm, decomp⟩ := h
    exact ⟨{
      C := C,
      P := P,
      C_isCyclic := C_cyc,
      P_isPGroup := P_pg,
      C_isPRegular := C_reg,
      comm := comm,
      decompose := decomp
    }⟩

/--
A `p`-group is `p`-elementary, with trivial cyclic prime-to-`p` part.
-/
lemma ofIsPGroup
    (hG : IsPGroup p G) : IsPElementary p G := by
  rw [IsPElementary.iff]
  refine ⟨⊥, ⊤, isCyclic_of_subsingleton, ?_, ?_, ?_, ?_⟩
  · exact IsPGroup.of_equiv hG Subgroup.topEquiv.symm
  · intro c hc
    rw [Subgroup.mem_bot] at hc
    rw [hc]
    exact IsPRegular.one p
  · intro c q hc _
    rw [Subgroup.mem_bot] at hc
    rw [hc]
    exact Commute.one_left q
  · intro g
    use 1, Subgroup.one_mem ⊥, g, Subgroup.mem_top g
    rw [one_mul]

/--
A finite cyclic group is `p`-elementary.

The cyclic generator decomposes into its `p`-regular and `p`-singular parts.
-/
lemma of_isCyclic [Finite G] [h_cyc : IsCyclic G]
    [Fact p.Prime] : IsPElementary p G := by
  refine ⟨?_⟩
  let x := Classical.choose (IsCyclic.exists_generator (α := G))
  have hx_gen := Classical.choose_spec (IsCyclic.exists_generator (α := G))
  have hfx : IsOfFinOrder x := isOfFinOrder_of_finite x
  let x_reg  := Group.pRegular p x
  let x_sing := Group.pSingular p x
  exact {
    C := Subgroup.zpowers x_reg
    P := Subgroup.zpowers x_sing
    C_isCyclic := Subgroup.isCyclic_zpowers x_reg
    P_isPGroup := by
      rw [← IsPSingular.iff_zpowers_isPGroup]
      exact Group.isPSingular_pSingular p x
    C_isPRegular := by
      intro c hc
      have h_dvd : orderOf c ∣ orderOf x_reg := orderOf_dvd_of_mem_zpowers hc
      have h_reg_gen : IsPRegular p x_reg := Group.isPRegular_pRegular p hfx
      exact Nat.Coprime.coprime_dvd_left h_dvd h_reg_gen
    comm := by
      intro c s hc hs
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hs
      apply Commute.zpow_zpow
      exact Group.pRegular_pSingular_commute p rfl
    decompose := by
      intro h
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hx_gen h)
      use x_reg ^ k, Subgroup.zpow_mem _ (Subgroup.mem_zpowers x_reg) k
      use x_sing ^ k, Subgroup.zpow_mem _ (Subgroup.mem_zpowers x_sing) k
      rw [← Commute.mul_zpow (Group.pDecomp_commute p x).symm]
      rw [Group.pDecomp' p hfx]
      exact hk
  }

/--
The bottom subgroup, regarded as a group, is `p`-elementary.
-/
lemma bot [Fact p.Prime] :
      IsPElementary (G := (⊥ : Subgroup G)) p := by
  exact ofIsPGroup (p := p) (G := (⊥ : Subgroup G)) IsPGroup.of_bot

/--
The cyclic subgroup generated by a finite-order element is `p`-elementary.
-/
lemma zpowers_of_isOfFinOrder [Fact p.Prime]
    (x : G) (hx : IsOfFinOrder x) :
    IsPElementary p (Subgroup.zpowers x) := by
  haveI : Finite (Subgroup.zpowers x) := Finite.of_equiv _ (finEquivZPowers hx)
  exact of_isCyclic (p := p) (G := Subgroup.zpowers x)

end IsPElementary

end BrauerInduction
