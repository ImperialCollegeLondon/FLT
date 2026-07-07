/-
Copyright (c) 2025 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McCarthy
-/
module

public import FLT.Slop.Background.FDRep.CoindBasic

@[expose] public section

/-!
# A basis for coinduced representations

This file constructs an explicit basis for the coinduced representation
`FDRep.coind H σ`.

If `bV : Module.Basis ι k σ` is a basis of the representation of the
subgroup `H`, then `FDRep.coindBasis H σ bV` is a basis of the coinduced
representation indexed by
w
`Quotient (QuotientGroup.rightRel H) × ι`.

The basis vector indexed by `(q, i)` is supported on the right coset `q`; at an
element `x` of that coset it is obtained by transporting the basis vector
`bV i` using the element `x * q.out⁻¹ ∈ H`.
-/

universe u v

variable {k : Type u} {G : Type u}

namespace FDRep

variable [CommRing k] [IsNoetherianRing k] [Group G] [Finite G]

/--
The coefficient functional of a coinduced representation at coset `q` and basis
index `i`.
-/
noncomputable def coindCoeff
    (I : Subgroup G) (σ : FDRep k I)
    {ι : Type*}
    (bV : Module.Basis ι k σ)
    (q : Quotient (QuotientGroup.rightRel I)) (i : ι) :
    (FDRep.coind I σ) →ₗ[k] k :=
  (Finsupp.lapply i).comp
    (bV.repr.toLinearMap.comp (coindEval I σ q.out))

@[simp]
lemma coindCoeff_apply
    (I : Subgroup G) (σ : FDRep k I)
    {ι : Type*}
    (bV : Module.Basis ι k σ)
    (q : Quotient (QuotientGroup.rightRel I)) (i : ι)
    (v : (FDRep.coind I σ)) :
    coindCoeff I σ bV q i v = bV.repr (v.val q.out) i :=
  rfl

open Classical in
/--
The basis vector of the coinduced representation indexed by a
`QuotientGroup.rightRel H`-class `q` and a basis index `i`.

It is supported on the class `q`. If `x` lies in this class, its value at `x`
is `σ (x * q.out⁻¹) (bV i)`, where `x * q.out⁻¹` is viewed as an element of the
subgroup.
-/
noncomputable def coindBasisVector {ι : Type*}
    (H : Subgroup G)
    (σ : FDRep k H) (bV : Module.Basis ι k σ)
    (q : Quotient (QuotientGroup.rightRel H)) (i : ι) :
    (FDRep.coind H σ) :=
{
  val := fun x =>
    if h_eq : Quotient.mk (QuotientGroup.rightRel H) x = q then
      -- Construct h ∈ I such that x = h * q.out
      let h_elt : H := ⟨x * (q.out)⁻¹, by
        have h_rel := Quotient.exact (h_eq.trans (Quotient.out_eq q).symm)
        change QuotientGroup.rightRel H x q.out at h_rel
        rw [QuotientGroup.rightRel_apply] at h_rel
        rw [← H.inv_mem_iff]
        simp only [mul_inv_rev, inv_inv]
        exact h_rel ⟩
      σ.ρ h_elt (bV i)
    else
      0,
  property := by
    rintro ⟨h, hh⟩ x
    dsimp
    have h_coset : Quotient.mk (QuotientGroup.rightRel H) (h * x) =
                   Quotient.mk (QuotientGroup.rightRel H) x := by
      apply Quotient.sound
      change QuotientGroup.rightRel H (h * x) x
      rw [QuotientGroup.rightRel_apply]
      simp only [mul_inv_rev, ← mul_assoc, mul_inv_cancel, one_mul]
      exact H.inv_mem hh
    simp only [h_coset]
    split_ifs with h_eq
    · change σ.ρ _ (bV i) = (σ.ρ ⟨h, hh⟩ * σ.ρ _) (bV i)
      rw [← map_mul]
      congr 2
      ext
      dsimp
      group
    · exact (map_zero _).symm
}

@[simp]
lemma coindBasisVector_val_out
    (I : Subgroup G) (σ : FDRep k I)
    {ι : Type*}
    (bV : Module.Basis ι k σ)
    (q : Quotient (QuotientGroup.rightRel I)) (i : ι) :
    (FDRep.coindBasisVector I σ bV q i).val q.out = bV i := by
  dsimp [FDRep.coindBasisVector]
  rw [dif_pos (Quotient.out_eq q)]
  have hsub :
      (⟨q.out * q.out⁻¹, by
        simp only [mul_inv_cancel, I.one_mem]⟩ : I) = 1 := by ext; simp
  rw [hsub]
  simp only [map_one, Module.End.one_apply]

@[simp]
lemma coindBasisVector_val_eq_zero_of_ne
    (I : Subgroup G) (σ : FDRep k I)
    {ι : Type*}
    (bV : Module.Basis ι k σ)
    (q : Quotient (QuotientGroup.rightRel I)) (i : ι)
    {x : G}
    (hx : Quotient.mk (QuotientGroup.rightRel I) x ≠ q) :
    (FDRep.coindBasisVector I σ bV q i).val x = 0 := by
  dsimp [FDRep.coindBasisVector]
  rw [dif_neg hx]

open Classical in
/--
The canonical basis of a coinduced representation.

Given a basis `bV` of `σ`, this basis of `FDRep.coind I σ` is indexed by pairs
`(q, i)`, where `q` is a right coset of `I` in `G` and `i` indexes the basis
`bV`.
-/
noncomputable def coindBasis
    {ι : Type*} [Fintype ι]
    (I : Subgroup G) (σ : FDRep k I)
    (bV : Module.Basis ι k σ) :
    Module.Basis (Quotient (QuotientGroup.rightRel I) × ι) k (FDRep.coind I σ) := by
  letI : Fintype G := Fintype.ofFinite G
  exact
  Module.Basis.ofEquivFun {
    toFun := fun v (q, i) => coindCoeff I σ bV q i v,
    invFun := fun f => ∑ p : (Quotient (QuotientGroup.rightRel I) × ι),
                       f p • FDRep.coindBasisVector I σ bV p.1 p.2,
    left_inv := by
      intro v
      apply coind_ext I σ
      intro x
      rw [map_sum]
      simp only [coindEval_apply, map_smul]
      rw [← Finset.univ_product_univ, Finset.sum_product]
      let qx := Quotient.mk (QuotientGroup.rightRel I) x
      rw [Finset.sum_eq_single qx]
      · dsimp [FDRep.coindBasisVector]
        simp_rw [dif_pos (show ⟦x⟧ = qx from rfl)]
        let h_val : I := ⟨x * qx.out⁻¹, by
          have h_rel := Quotient.exact (Quotient.out_eq qx).symm
          change QuotientGroup.rightRel I x qx.out at h_rel
          rw [QuotientGroup.rightRel_apply] at h_rel
          rw [← I.inv_mem_iff]
          simpa using h_rel ⟩
        let L := σ.ρ h_val
        change (∑ y, (bV.repr (v.val qx.out) y) • L (bV y)) = v.val x
        simp_rw [← L.map_smul]
        rw [← map_sum L]
        rw [bV.sum_repr]
        have h_sec := v.property h_val qx.out
        change v.val (h_val * qx.out) = σ.ρ h_val (v.val qx.out) at h_sec
        rw [← h_sec]
        apply congr_arg v.val
        rw [Subtype.coe_mk]
        group
      · intro q _ hne
        apply Finset.sum_eq_zero
        intro i _
        rw [coindBasisVector_val_eq_zero_of_ne
          (I := I) (σ := σ) (bV := bV) (q := q) (i := i)
          (x := x) (hx := hne.symm)]
        exact MulActionWithZero.smul_zero ((coindCoeff I σ bV q i) v)
      · intro hqx
        exact False.elim (hqx (Finset.mem_univ qx))
    right_inv := by
      intro f
      funext p
      rcases p with ⟨q, i⟩
      change
        coindCoeff I σ bV q i
          (∑ p : Quotient (QuotientGroup.rightRel I) × ι,
            f p • FDRep.coindBasisVector I σ bV p.1 p.2)
          =
        f (q, i)
      rw [map_sum]
      simp only [map_smul, coindCoeff_apply]
      rw [← Finset.univ_product_univ, Finset.sum_product]
      rw [Finset.sum_eq_single q]
      · rw [Finset.sum_eq_single i]
        · simp only [coindBasisVector_val_out, Module.Basis.repr_self, Finsupp.single_eq_same,
            smul_eq_mul, mul_one]
        · intro c _ hne
          simp only [coindBasisVector_val_out]
          simp only [Module.Basis.repr_self, smul_eq_mul, smul_eq_mul,
            Finsupp.single_eq_of_ne hne.symm, mul_zero]
        · intro h
          simp at h
      · intro q' _ hne
        apply Finset.sum_eq_zero
        intro i' _
        have hx : Quotient.mk (QuotientGroup.rightRel I) q.out ≠ q' := by
          rw [Quotient.out_eq q]
          exact hne.symm
        rw [coindBasisVector_val_eq_zero_of_ne
          (I := I) (σ := σ) (bV := bV) (q := q') (i := i')
          (x := q.out) (hx := hx)]
        simp only [smul_eq_mul]
        have hcoord : (bV.repr (0 : σ.V)) i = 0 := by
          simp only [map_zero, Finsupp.coe_zero, Pi.zero_apply]
        exact mul_eq_zero_of_right (f (q', i')) hcoord
      · intro h
        simp at h
    map_add' := by
      intros v w
      ext ⟨q, i⟩
      simp only [map_add (coindCoeff I σ bV q i) v w, coindCoeff_apply, Pi.add_apply]
    map_smul' := by
      intros c v
      ext ⟨q, i⟩
      simp only [map_smul (coindCoeff I σ bV q i) c v, coindCoeff_apply, smul_eq_mul,
        RingHom.id_apply, Pi.smul_apply]
  }

open Classical in
/--
The basis vector of `coindBasis` indexed by `(q, i)` is the explicit vector
`coindBasisVector I σ bV q i`.
-/
@[simp]
lemma coindBasis_apply
    (I : Subgroup G) (σ : FDRep k I)
    {ι : Type*} [Fintype ι]
    (bV : Module.Basis ι k σ)
    (q : Quotient (QuotientGroup.rightRel I)) (i : ι) :
    (FDRep.coindBasis I σ bV) (q, i) =
      FDRep.coindBasisVector I σ bV q i := by
  letI : Fintype G := Fintype.ofFinite G
  dsimp [FDRep.coindBasis]
  rw [Module.Basis.coe_ofEquivFun]
  change
    (∑ p : Quotient (QuotientGroup.rightRel I) × ι,
      ((Pi.single (q, i) (1 : k) :
        Quotient (QuotientGroup.rightRel I) × ι → k) p) •
        FDRep.coindBasisVector I σ bV p.1 p.2) =
    FDRep.coindBasisVector I σ bV q i
  rw [Finset.sum_eq_single (q, i)]
  · simp only [Pi.single_eq_same, one_smul]
  · intro p _ hp
    rw [Pi.single_eq_of_ne hp]
    simp only [zero_smul]
  · intro h
    simp only [Finset.mem_univ, not_true_eq_false] at h

/-! ### Finrank of coinduced representations -/

section Finrank

variable {k : Type u} [Field k]

/--
The dimension of a coinduced representation, computed from the explicit
coinduced basis.

This version keeps a chosen basis of `σ` as an argument; it is the direct
finrank statement attached to `coindBasis`.
-/
theorem finrank_coind_of_basis
    (I : Subgroup G)
    (σ : FDRep k I)
    {ι : Type*} [Finite ι]
    (bV : Module.Basis ι k σ) :
    finrank (FDRep.coind I σ) =
      Nat.card (Quotient (QuotientGroup.rightRel I)) * finrank σ := by
  classical
  letI: Fintype ι := Fintype.ofFinite ι
  letI : Fintype G := Fintype.ofFinite G
  simp only [Module.finrank_eq_card_basis (FDRep.coindBasis I σ bV)]
  simp only [Module.finrank_eq_card_basis bV]
  simp only [Fintype.card_prod, Nat.card_eq_fintype_card]

end Finrank

end FDRep
