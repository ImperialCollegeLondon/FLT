/-
Copyright (c) 2025 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McCarthy
-/
module

public import FLT.KnownIn1980s.BrauerInduction.Slop.Background.ClassFun.Maps
public import FLT.KnownIn1980s.BrauerInduction.Slop.Background.Group.Coset

@[expose] public section

universe u v w

/-!
# Induction of class functions

This file defines induction of class functions from a subgroup `H ≤ G` to `G`.

The definition is given by summing the usual conjugation summand over coset
representatives. The file proves the basic algebraic properties of induction:
additivity, compatibility with scalar multiplication, transitivity, the
projection formula, compatibility with coefficient maps, and the standard
averaging formula over the whole group.
-/

namespace ClassFun

section Summand

variable {k : Type u} [Zero k]
variable {G : Type v} [Group G]

open Classical in
/--
The summand appearing in the induced class function.
-/
noncomputable def indSummand
    (H : Subgroup G) (φ : ClassFun k H) (g x : G) : k :=
  if hx : x⁻¹ * g * x ∈ H then
    φ ⟨x⁻¹ * g * x, hx⟩
  else
    0

private lemma indSummand_mul_right
    (H : Subgroup G) (φ : ClassFun k H)
    (g x : G) (h : H) :
    indSummand H φ g (x * (h : G)) =
      indSummand H φ g x := by
  unfold indSummand
  have halg :
      (x * (h : G))⁻¹ * g * (x * (h : G)) =
        (h⁻¹ : H).val * (x⁻¹ * g * x) * (h : H).val := by
    simp only [mul_inv_rev, InvMemClass.coe_inv]
    group
  by_cases hx : x⁻¹ * g * x ∈ H
  · have hxh :
        (x * (h : G))⁻¹ * g * (x * (h : G)) ∈ H :=
      halg.symm ▸
        H.mul_mem
          (H.mul_mem (H.inv_mem h.property) hx)
          h.property
    simp only [dif_pos hx, dif_pos hxh]
    have hconj :
        IsConj
          (⟨(x * (h : G))⁻¹ * g * (x * (h : G)), hxh⟩ : H)
          (⟨x⁻¹ * g * x, hx⟩ : H) := by
      rw [isConj_iff]
      use h
      ext
      push_cast
      rw [halg]
      simp only [InvMemClass.coe_inv]
      group
    exact φ.map_conj _ _ hconj
  · have hxh :
        (x * (h : G))⁻¹ * g * (x * (h : G)) ∉ H := by
      intro hmem
      apply hx
      have halg_inv :
          x⁻¹ * g * x =
            (h : H).val *
              ((x * (h : G))⁻¹ * g * (x * (h : G))) *
              (h⁻¹ : H).val := by
        simp only [mul_inv_rev, InvMemClass.coe_inv]
        group
      exact halg_inv.symm ▸
        H.mul_mem
          (H.mul_mem h.property hmem)
          (H.inv_mem h.property)
    simp only [dif_neg hx, dif_neg hxh]

open Classical in
private lemma indSummand_conj_mul_left
    (H : Subgroup G) (φ : ClassFun k H)
    {x y : G} (a z : G)
    (ha : a * x * a⁻¹ = y) :
    indSummand H φ y (a * z) =
      indSummand H φ x z := by
  unfold indSummand
  have harg :
      (a * z)⁻¹ * y * (a * z) =
        z⁻¹ * x * z := by
    rw [← ha]
    group
  rw [harg]

open Classical in
private lemma indSummand_smul_quotient
    (H : Subgroup G) (φ : ClassFun k H)
    {x y : G} (a : G)
    (ha : a * x * a⁻¹ = y)
    (q : G ⧸ H) :
    indSummand H φ y (a • q).out =
      indSummand H φ x q.out := by
  have hq :
      (a • q : G ⧸ H) =
        (↑(a * q.out) : G ⧸ H) := by
    rw [← QuotientGroup.out_eq' q]
    simpa using
      (MulAction.Quotient.smul_mk H a q.out)
  obtain ⟨h, hout⟩ :=
    QuotientGroup.mk_out_eq_mul H (a * q.out)
  have hout' :
      (a • q).out =
        a * q.out * (h : G) := by
    rw [hq]
    exact hout
  calc
    indSummand H φ y (a • q).out
        =
      indSummand H φ y
        ((a * q.out) * (h : G)) := by
          rw [hout']
    _ =
      indSummand H φ y (a * q.out) :=
        indSummand_mul_right H φ y (a * q.out) h
    _ =
      indSummand H φ x q.out :=
        indSummand_conj_mul_left H φ a q.out ha

end Summand

section Induction

variable {k : Type u} [AddCommMonoid k]
variable {G : Type v} [Group G] [Fintype G]

open Classical in
/--
Induced class function, defined by summing the usual conjugation summand over
the quotient `G ⧸ H`.
-/
noncomputable def ind
    (H : Subgroup G) (φ : ClassFun k H) :
    ClassFun k G where
  toFun g :=
    ∑ q : G ⧸ H, indSummand H φ g q.out
  map_conj := by
    intro x y hxy
    rw [isConj_iff] at hxy
    rcases hxy with ⟨a, ha⟩
    let e : G ⧸ H ≃ G ⧸ H := {
      toFun q := a • q
      invFun q := a⁻¹ • q
      left_inv q := by
        simp [smul_smul]
      right_inv q := by
        simp [smul_smul]
    }
    nth_rewrite 2 [← Equiv.sum_comp e]
    apply Finset.sum_congr rfl
    intro q _
    dsimp [e]
    exact (indSummand_smul_quotient H φ a ha q).symm

open Classical in
/--
The defining formula for the induced class function.
-/
@[simp]
lemma ind_apply
    (H : Subgroup G) (φ : ClassFun k H) (g : G) :
    ind H φ g =
      ∑ q : G ⧸ H,
        if hx : q.out⁻¹ * g * q.out ∈ H then
          φ ⟨q.out⁻¹ * g * q.out, hx⟩
        else
          0 :=
  rfl

open Classical in
/--
Alternative formula for induction as a sum over the explicit right-coset
quotient.

The equivalence with the defining quotient is induced by inversion, so the
conjugate `x⁻¹ * g * x` becomes `x * g * x⁻¹`.
-/
lemma ind_apply_rightCosets
    (H : Subgroup G) (φ : ClassFun k H) (g : G) :
    ind H φ g =
      ∑ q : Quotient (QuotientGroup.rightRel H),
        if hx : q.out * g * q.out⁻¹ ∈ H then
          φ ⟨q.out * g * q.out⁻¹, hx⟩
        else
          0 := by
  rw [ind_apply]
  let e :
      Quotient (QuotientGroup.rightRel H) ≃ G ⧸ H :=
    QuotientGroup.quotientRightRelEquivQuotientLeftRel H
  change
    (∑ p : G ⧸ H, indSummand H φ g p.out) =
      ∑ q : Quotient (QuotientGroup.rightRel H),
        if hx : q.out * g * q.out⁻¹ ∈ H then
          φ ⟨q.out * g * q.out⁻¹, hx⟩
        else
          0
  rw [← Equiv.sum_comp e]
  apply Finset.sum_congr rfl
  intro q _
  have heq :
      e q = (↑(q.out⁻¹) : G ⧸ H) := by
    calc
      e q = e (Quotient.mk (QuotientGroup.rightRel H) q.out) := by
        exact congrArg e (Quotient.out_eq q).symm
      _ = (↑(q.out⁻¹) : G ⧸ H) := by
        rfl
  obtain ⟨h, hout⟩ := QuotientGroup.mk_out_eq_mul H q.out⁻¹
  have hout' : (e q).out = q.out⁻¹ * (h : G) := by
    rw [heq]
    exact hout
  calc
    indSummand H φ g (e q).out
        =
      indSummand H φ g (q.out⁻¹ * (h : G)) := by
        rw [hout']
    _ =
      indSummand H φ g q.out⁻¹ :=
        indSummand_mul_right H φ g q.out⁻¹ h
    _ =
      if hx : q.out * g * q.out⁻¹ ∈ H then
        φ ⟨q.out * g * q.out⁻¹, hx⟩
      else
        0 := by
      unfold indSummand
      simp only [inv_inv]

/--
Induction is additive.
-/
@[simp]
theorem ind_add {H : Subgroup G} (φ ψ : ClassFun k H) :
    ind H (φ + ψ) = ind H φ + ind H ψ := by
  ext g
  simp only [ind_apply, add_apply]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _
  split_ifs <;> simp

/--
Induction commutes with finite sums.
-/
lemma ind_sum (H : Subgroup G) {ι : Type*} [Fintype ι] (f : ι → ClassFun k H) :
    ind H (∑ i, f i) = ∑ i, ind H (f i) := by
  ext g
  simp [ind_apply, Finset.sum_comm]

/--
Induction sends the zero class function to zero.
-/
@[simp]
theorem ind_zero {H : Subgroup G} :
    ind H (0 : ClassFun k H) = 0 := by
  ext g
  simp [ind_apply, zero_apply, Finset.sum_const_zero]

end Induction

section ScalarAction

variable {R : Type w} [Semiring R]
variable {k : Type u} [AddCommMonoid k] [Module R k]
variable {G : Type v} [Group G] [Fintype G]

/--
Induction commutes with scalar multiplication.
-/
@[simp]
theorem ind_smul
    {H : Subgroup G} (r : R) (φ : ClassFun k H) :
    ind H (r • φ) = r • ind H φ := by
  ext g
  simp only [ind_apply, smul_apply]
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro q _
  by_cases hq : q.out⁻¹ * g * q.out ∈ H
  · simp only [hq, ↓reduceDIte]
  · simp only [hq, ↓reduceDIte, smul_zero]

/--
Induction of class functions from `H` to `G`, regarded as a linear map.
-/
noncomputable def indLinearMap
    (H : Subgroup G) :
    ClassFun k H →ₗ[R] ClassFun k G where
  toFun := ind H
  map_add' φ ψ := by
    simp only [ind_add (H := H) φ ψ]
  map_smul' r φ := by
    simp only [ind_smul (R := R) (H := H) r φ, RingHom.id_apply]

/--
Evaluation of `indLinearMap`.
-/
@[simp]
lemma indLinearMap_apply
    (H : Subgroup G) (φ : ClassFun k H) :
    indLinearMap (R := R) H φ = ind H φ :=
  rfl

end ScalarAction

section AdditiveGroup

variable {k : Type u} [AddCommGroup k]
variable {G : Type v} [Group G] [Fintype G]

/--
Induction commutes with integer scalar multiplication.
-/
@[simp]
theorem ind_zsmul
    {H : Subgroup G} (n : ℤ) (φ : ClassFun k H) :
    ind H (n • φ) = n • ind H φ :=
  ind_smul n φ

end AdditiveGroup

section AveragingFormula

variable {k : Type u} [Field k] [CharZero k]
variable {G : Type v} [Group G] [Fintype G]

open Classical in
/--
The standard averaging formula for induction, written as a sum over all
elements of `G`.
-/
lemma ind_apply_eq_inv_mul_sum
    (H : Subgroup G) (φ : ClassFun k H) (g : G) :
    ind H φ g =
      (Nat.card H : k)⁻¹ *
        ∑ x : G,
          if hx : x⁻¹ * g * x ∈ H then
            φ ⟨x⁻¹ * g * x, hx⟩
          else
            0 := by
  rw [ind_apply]
  let f : G → k := indSummand H φ g
  change
    (∑ q : G ⧸ H, f q.out) =
      (Nat.card H : k)⁻¹ * ∑ x : G, f x
  have hsum :
      (∑ x : G, f x) =
        (Nat.card H : k) * ∑ q : G ⧸ H, f q.out := by
    simpa using
      Subgroup.sum_of_left_coset_constant
        H f (indSummand_mul_right H φ g)
  rw [hsum]
  have hcard : (Nat.card H : k) ≠ 0 := by
    have hcardNat : Nat.card H ≠ 0 := by
      exact (Nat.card_ne_zero).mpr ⟨⟨1⟩, inferInstance⟩
    exact_mod_cast hcardNat
  rw [← mul_assoc, inv_mul_cancel₀ hcard, one_mul]

open Classical in
/--
The standard averaging formula for induction, with conjugation written as
`x * g * x⁻¹`.
-/
lemma ind_apply_eq_inv_mul_sum_mul_inv
    (H : Subgroup G) (φ : ClassFun k H) (g : G) :
    ind H φ g =
      (Nat.card H : k)⁻¹ *
        ∑ x : G,
          if hx : x * g * x⁻¹ ∈ H
          then φ ⟨x * g * x⁻¹, hx⟩
          else 0 := by
  rw [ind_apply_eq_inv_mul_sum]
  congr 1
  refine Finset.sum_bij
    (fun x (_ : x ∈ (Finset.univ : Finset G)) => (x : G)⁻¹)
    ?map_mem ?map_eq ?inj ?surj
  · intro x hx
    simp
  · intro x hx
    simp only [Finset.mem_univ, inv_inj, imp_self, implies_true]
  · intro y hy
    refine ⟨y⁻¹, by simp, ?_⟩
    simp only [inv_inv]
  · intro x₁ hx₁
    simp only [inv_inv]

end AveragingFormula

section Transitivity

variable {k : Type u} [AddCommMonoid k]
variable {G : Type v} [Group G] [Fintype G]

open Classical in
private noncomputable def iteratedIndSummand
    {k : Type u} [Zero k]
    {G : Type v} [Group G]
    (K : Subgroup G) (H : Subgroup K)
    (φ : ClassFun k H) (g : G)
    (p : Σ (_ : G ⧸ K), K ⧸ H) : k :=
  if hK : p.1.out⁻¹ * g * p.1.out ∈ K then
    indSummand H φ
      ⟨p.1.out⁻¹ * g * p.1.out, hK⟩
      p.2.out
  else
    0

open Classical in
private lemma sum_indSummand_ind_eq_sigma
    {k : Type u} [AddCommMonoid k]
    {G : Type v} [Group G] [Fintype G]
    (K : Subgroup G) (H : Subgroup K)
    (φ : ClassFun k H) (g : G) :
    (∑ qK : G ⧸ K,
        indSummand K (ind H φ) g qK.out)
      =
    ∑ p : Σ (_ : G ⧸ K), K ⧸ H,
      iteratedIndSummand K H φ g p := by
  rw [Fintype.sum_sigma]
  apply Fintype.sum_congr
  intro qK
  unfold iteratedIndSummand indSummand
  by_cases hK : qK.out⁻¹ * g * qK.out ∈ K
  · simp only [dif_pos hK, ind_apply]
  · simp only [dif_neg hK, Finset.sum_const_zero]

open Classical in
private lemma iteratedIndSummand_eq_product
    {k : Type u} [Zero k]
    {G : Type v} [Group G]
    (K : Subgroup G) (H : Subgroup K)
    (φ : ClassFun k H) (g : G)
    (qK : G ⧸ K) (qH : K ⧸ H) :
    let eH := H.equivMapOfInjective K.subtype Subtype.coe_injective
    let ψ := (ClassFun.equivOfMulEquiv (k := k) eH).symm φ
    iteratedIndSummand K H φ g ⟨qK, qH⟩
      =
    indSummand (H.map K.subtype) ψ g (qK.out * (qH.out : G)) := by
  dsimp only
  let eH := H.equivMapOfInjective K.subtype Subtype.coe_injective
  let ψ := (ClassFun.equivOfMulEquiv (k := k) eH).symm φ
  let gK : G := qK.out⁻¹ * g * qK.out
  let xGH : G := qK.out * (qH.out : G)
  change
    (if hK : gK ∈ K then indSummand H φ ⟨gK, hK⟩ qH.out else 0)
      =
    indSummand (H.map K.subtype) ψ g xGH
  by_cases hK : gK ∈ K
  · rw [dif_pos hK]
    let gH : K := qH.out⁻¹ * ⟨gK, hK⟩ * qH.out
    have harg : xGH⁻¹ * g * xGH = (gH : G) := by dsimp [xGH, gH, gK]; group
    have hmem_iff :
        xGH⁻¹ * g * xGH ∈ H.map K.subtype ↔ gH ∈ H := by
      constructor
      · rintro ⟨z, hz, hz_eq⟩
        have hzg : z = gH := by
          apply Subtype.ext
          exact hz_eq.trans harg
        simpa [hzg] using hz
      · intro hgH
        exact ⟨gH, hgH, harg.symm⟩
    unfold indSummand
    change
      (if hH : gH ∈ H then φ ⟨gH, hH⟩ else 0)
        =
      if hmap : xGH⁻¹ * g * xGH ∈ H.map K.subtype then
        ψ ⟨xGH⁻¹ * g * xGH, hmap⟩ else 0
    by_cases hH : gH ∈ H
    · have hmap : xGH⁻¹ * g * xGH ∈ H.map K.subtype := hmem_iff.mpr hH
      rw [dif_pos hH, dif_pos hmap]
      have hpreimage :
          eH.symm ⟨xGH⁻¹ * g * xGH, hmap⟩ =⟨gH, hH⟩ := by
        apply eH.injective
        rw [eH.apply_symm_apply]
        apply Subtype.ext
        change xGH⁻¹ * g * xGH = (gH : G)
        exact harg
      rw [ClassFun.equivOfMulEquiv_symm_apply]
      exact congrArg (fun z : H => φ z) hpreimage.symm
    · have hmap : xGH⁻¹ * g * xGH ∉ H.map K.subtype := fun h => hH (hmem_iff.mp h)
      rw [dif_neg hH, dif_neg hmap]
  · rw [dif_neg hK]
    have hmap : xGH⁻¹ * g * xGH ∉ H.map K.subtype := by
      intro hm
      apply hK
      rcases hm with ⟨z, hz, hz_eq⟩
      have hambient_mem_K : xGH⁻¹ * g * xGH ∈ K := by
        rw [← hz_eq]; exact z.property
      have hgK : gK = (qH.out : G) * (xGH⁻¹ * g * xGH) * (qH.out : G)⁻¹ := by
        dsimp [gK, xGH]
        group
      rw [hgK]
      exact K.mul_mem
        (K.mul_mem qH.out.property hambient_mem_K)
        (K.inv_mem qH.out.property)
    unfold indSummand
    rw [dif_neg hmap]

open Classical in
private lemma iteratedIndSummand_eq_sigmaEquiv
    {k : Type u} [Zero k]
    {G : Type v} [Group G]
    (K : Subgroup G) (H : Subgroup K)
    (φ : ClassFun k H) (g : G)
    (p : Σ (_ : G ⧸ K), K ⧸ H) :
    let e := (QuotientGroup.equivSigmaQuotient (G := G) (K := K) H).symm
    let eH := H.equivMapOfInjective K.subtype Subtype.coe_injective
    let ψ := (ClassFun.equivOfMulEquiv (k := k) eH).symm φ
    iteratedIndSummand K H φ g p =
      indSummand (H.map K.subtype) ψ g (e p).out := by
  dsimp only
  rcases p with ⟨qK, qH⟩
  let e := (QuotientGroup.equivSigmaQuotient (G := G) (K := K) H).symm
  let eH := H.equivMapOfInjective K.subtype Subtype.coe_injective
  let ψ := (ClassFun.equivOfMulEquiv (k := k) eH).symm φ
  let xGH : G := qK.out * (qH.out : G)
  let s : G ⧸ H.map K.subtype := e ⟨qK, qH⟩
  have hproduct := iteratedIndSummand_eq_product K H φ g qK qH
  dsimp only at hproduct
  change
    iteratedIndSummand K H φ g ⟨qK, qH⟩ =
      indSummand (H.map K.subtype) ψ g s.out
  rw [hproduct]
  have h_s_rel :
      s.out⁻¹ * xGH ∈ H.map K.subtype := by
    have h_qH_out :
        ((Subgroup.quotientEquivOfEq
            (Subgroup.subgroupOf_map_subtype_eq_self H)).symm qH)
          =
        (⟦qH.out⟧ :
          K ⧸ (H.map K.subtype).subgroupOf K) := by
      let hEq := Subgroup.subgroupOf_map_subtype_eq_self H
      exact calc
        ((Subgroup.quotientEquivOfEq hEq).symm qH)
            =
          ((Subgroup.quotientEquivOfEq hEq).symm
            (⟦qH.out⟧ : K ⧸ H)) := by
              exact congrArg
                (fun q : K ⧸ H =>
                  (Subgroup.quotientEquivOfEq hEq).symm q)
                (Quotient.out_eq qH).symm
        _ =
          (Subgroup.quotientEquivOfEq hEq.symm)
            (⟦qH.out⟧ : K ⧸ H) := by
              rfl
        _ =
          (⟦qH.out⟧ :
            K ⧸ (H.map K.subtype).subgroupOf K) := by
              exact
                Subgroup.quotientEquivOfEq_mk
                  hEq.symm qH.out
    rw [← QuotientGroup.eq]
    dsimp [s, e, QuotientGroup.equivSigmaQuotient, xGH]
    simp only [
      Equiv.sigmaEquivProd_apply,
      Equiv.prodCongr_apply,
      Equiv.coe_refl,
      Prod.map_apply,
      id_eq,
      Subgroup.quotientEquivProdOfLE_symm_apply,
      Quotient.out_eq,
      h_qH_out,
      Quotient.map'_mk
    ]
  let h : H.map K.subtype := ⟨s.out⁻¹ * xGH, h_s_rel⟩
  have hx : s.out * (h : G) = xGH := by dsimp [h]; group
  calc
    indSummand (H.map K.subtype) ψ g xGH
        =
      indSummand (H.map K.subtype) ψ g
        (s.out * (h : G)) := by
          rw [hx]
    _ =
      indSummand (H.map K.subtype) ψ g s.out :=
        indSummand_mul_right
          (H.map K.subtype) ψ g s.out h

open Classical in
/--
Transitivity of induction for class functions.

Inducing from `H` to `K` and then from `K` to `G` agrees with inducing
directly from the image of `H` as a subgroup of `G`, after transporting the
class function along the natural subgroup equivalence.
-/
lemma ind_trans
    {k : Type u} [AddCommMonoid k]
    {G : Type v} [Group G] [Fintype G]
    {K : Subgroup G} {H : Subgroup K}
    (φ : ClassFun k H) :
    ind K (ind H φ) =
      ind (H.map K.subtype)
        ((ClassFun.equivOfMulEquiv
          (k := k)
          (H.equivMapOfInjective
            K.subtype Subtype.coe_injective)).symm φ) := by
  ext g
  rw [ind_apply, ind_apply]
  change
    (∑ qK : G ⧸ K,
        indSummand K (ind H φ) g qK.out)
      =
    ∑ q : G ⧸ H.map K.subtype,
      indSummand
        (H.map K.subtype)
        ((ClassFun.equivOfMulEquiv
          (k := k)
          (H.equivMapOfInjective
            K.subtype Subtype.coe_injective)).symm φ)
        g q.out
  rw [sum_indSummand_ind_eq_sigma K H φ g]
  let e := (QuotientGroup.equivSigmaQuotient (G := G) (K := K) H).symm
  rw [← Equiv.sum_comp e]
  apply Finset.sum_congr rfl
  intro p _
  exact iteratedIndSummand_eq_sigmaEquiv K H φ g p

end Transitivity

section ProjectionFormula

variable {k : Type u} [Semiring k]
variable {G : Type v} [Group G] [Fintype G]

open Classical in
/--
The projection formula for class-function induction.

Multiplication by a class function on `G` commutes with induction after
restricting that class function to the subgroup.
-/
lemma projection_formula
    (H : Subgroup G)
    (ψ : ClassFun k G)
    (χ : ClassFun k H) :
    ψ * ind H χ = ind H (res H ψ * χ) := by
  ext g
  simp only [mul_apply, ind_apply]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q _
  by_cases hq : q.out⁻¹ * g * q.out ∈ H
  · simp only [dif_pos hq, res_apply]
    rw [map_conj_eq]
  · simp only [dif_neg hq, mul_zero]

end ProjectionFormula

section CoefficientMaps

variable {R : Type u} {S : Type w}
variable [AddCommMonoid R] [AddCommMonoid S]
variable {G : Type v} [Group G] [Fintype G]

open Classical in
/--
Induction commutes with postcomposition by an additive homomorphism of
coefficient types.
-/
@[simp]
lemma ind_postcomp
    (F : R →+ S)
    (H : Subgroup G)
    (φ : ClassFun R H) :
    ind H (φ.postcomp F) =
      (ind H φ).postcomp F := by
  ext g
  simp only [ind_apply, postcomp_apply]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro q _
  by_cases hq : q.out⁻¹ * g * q.out ∈ H
  · simp only [hq, ↓reduceDIte]
  · simp only [hq, ↓reduceDIte, map_zero]

end CoefficientMaps

end ClassFun
