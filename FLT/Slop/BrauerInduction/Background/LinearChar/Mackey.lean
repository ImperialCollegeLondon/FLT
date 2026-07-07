/-
Copyright (c) 2025 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McCarthy
-/
module

public import FLT.Slop.BrauerInduction.Background.FDRep.Mackey.Character
public import FLT.Slop.BrauerInduction.Background.LinearChar.Eigenspace

@[expose] public section


/-!
# Mackey theory for induced linear characters

This file specializes the Mackey character computation to representations
induced from inertia groups of linear characters.

Let `A` be an abelian normal subgroup of `G`, let `ψ : A →* kˣ`, and let
`I` be the inertia subgroup of `ψ`. If a representation `σ` of `I` embeds into
the `ψ`-eigenspace of a representation `ρ`, then all Mackey terms outside the
identity double coset vanish. Consequently the endomorphism ring of
`Ind_I^G σ` has dimension one when `σ` is simple.
-/

open CategoryTheory BigOperators

universe u v

namespace FDRep

variable {k : Type u} [Field k]
variable {G : Type v} [Group G]

/--
A Mackey Hom term vanishes outside the inertia subgroup.

If `σ` embeds into the `ψ`-eigenspace and `g⁻¹` is not in the inertia subgroup
of `ψ`, then the Mackey Hom term attached to `g` is zero.
-/
lemma mackeyHomTerm_eq_zero_of_inv_not_mem_inertia
    (ρ : FDRep k G)
    (A : Subgroup G) [A.Normal] [IsMulCommutative A]
    (ψ : A →* kˣ)
    (σ : FDRep k (LinearChar.inertia ψ))
    (ι : σ ⟶ LinearChar.psiEigenspaceFDRep ρ A ψ)
    [Mono ι]
    (g : G)
    (hg : g⁻¹ ∉ LinearChar.inertia ψ)
    (f : mackeyHomTerm (k := k) (I := LinearChar.inertia ψ) σ g) :
    f = 0 := by
  let I : Subgroup G := LinearChar.inertia ψ
  let Ig : Subgroup G := mackeyConjSubgroup I g
  let H : Subgroup G := mackeyIntersection I g
  let σH : FDRep k H := mackeyLeftRes (k := k) I σ g
  let σgH : FDRep k H := mackeyConjRes (k := k) I σ g
  ext v
  -- choose a separating a ∈ A
  obtain ⟨a, ha_neq⟩ :=
    LinearChar.exists_conj_coe_apply_ne_of_not_mem_inertia ψ hg
  have hAI : A ≤ I :=
    LinearChar.le_inertia_of_isMulCommutative (A := A) ψ
  have hAIg : A ≤ Ig :=
    FDRep.le_conjMap_of_normal A I hAI g
  have hAH : A ≤ H := by
    intro x hx
    exact ⟨hAI hx, hAIg hx⟩
  let aH : H := ⟨(a : G), hAH a.2⟩
  have hcomm :
      f.hom (σH.ρ aH v)
        =
      σgH.ρ aH (f.hom v) := FDRep.homToLinearMap_rho_apply f aH v
  have hsrc :
      σH.ρ aH v = (ψ a : k) • v := by
    change σ.ρ ⟨(a : G), hAI a.2⟩ v = (ψ a : k) • v
    have hlin :=
      LinearChar.sigma_rho_eq_smul_id_of_mono_into_psiEigenspace ρ A ψ σ ι a
    have happ :=
      congrArg
        (fun F : σ →ₗ[k] σ => F v)
        hlin
    simpa [LinearMap.smul_apply, LinearMap.id_apply] using happ
  have htgt :
      σgH.ρ aH (f.hom v)
        =
      ((LinearChar.conj ψ g⁻¹) a : k) • f.hom v := by
    have h1 :
        σgH.ρ aH (f.hom v)
          =
        (FDRep.conjMap (k := k) I g σ).ρ
          ⟨(a : G), hAIg a.2⟩ (f.hom v) := rfl
    rw [h1]
    have h2 :=
      FDRep.conjMap_rho_apply_of_mem_normal (k := k) A I hAI g σ a (v := f.hom v)
    rw [h2]
    let a_conj_val : G := g⁻¹ * (a : G) * g
    have h_mem_A : a_conj_val ∈ A := by
      simpa [a_conj_val] using
        (Subgroup.Normal.conj_mem'
          (inferInstance : A.Normal) (a : G) a.2 g)
    let a_conj_A : A := ⟨a_conj_val, h_mem_A⟩
    have hlin :=
      LinearChar.sigma_rho_eq_smul_id_of_mono_into_psiEigenspace ρ A ψ σ ι a_conj_A
    have happ :=
      congrArg
        (fun F : σ →ₗ[k] σ => F (f.hom v))
        hlin
    have hscalar :
        σ.ρ ⟨a_conj_val, hAI h_mem_A⟩ (f.hom v)
          =
        (ψ a_conj_A : k) • f.hom v := by
      exact cancel_hom_of_mono ι (congrArg (⇑(ConcreteCategory.hom ι.hom)) happ)
    rw [hscalar]
    congr 1
    rw [LinearChar.conj_apply]
    congr
    apply Subtype.ext
    simp [a_conj_A, a_conj_val]
  -- The source and target actions give distinct scalars, so the image of `v`
  -- under `f` must be zero.
  rw [hsrc, htgt] at hcomm
  rw [map_smul] at hcomm
  have hscalar_eq :
      (ψ a : k) • f.hom v =
        ((LinearChar.conj ψ g⁻¹) a : k) • f.hom v := hcomm
  have hscalar_ne :
      (ψ a : k) ≠ ((LinearChar.conj ψ g⁻¹) a : k) := Ne.symm ha_neq
  have hz :
      (((ψ a : k) - ((LinearChar.conj ψ g⁻¹) a : k)) • f.hom v) = 0 := by
    rw [sub_smul, sub_eq_zero]
    exact hscalar_eq
  exact (smul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hscalar_ne)

/--
The Mackey Hom term has dimension zero away from the identity double coset.

For representatives of non-identity double cosets in `I \ G / I`, where
`I` is the inertia subgroup of `ψ`, the corresponding Mackey Hom term
vanishes.
-/
lemma finrank_mackeyHomTerm_eq_zero_of_ne_oneDC
    (ρ : FDRep k G)
    (A : Subgroup G) [A.Normal] [IsMulCommutative A]
    (ψ : A →* kˣ)
    (σ : FDRep k (LinearChar.inertia ψ))
    (ι : σ ⟶ LinearChar.psiEigenspaceFDRep
      (ρ := ρ) (A := A) (ψ := ψ))
    [Mono ι]
    (d : DoubleCoset.Quotient
      (G := G) (LinearChar.inertia ψ) (LinearChar.inertia ψ))
    (hd : d ≠ DoubleCoset.oneDC (G := G) (LinearChar.inertia ψ)) :
    Module.finrank k
      (mackeyHomTerm
        (k := k)
        (I := LinearChar.inertia ψ)
        σ
        (Quotient.out d)) = 0 := by
  let I : Subgroup G := LinearChar.inertia ψ
  have hg : Quotient.out d ∉ I := by
    exact DoubleCoset.out_not_mem_of_ne_one
      (G := G) I d hd
  have hg_inv : (Quotient.out d)⁻¹ ∉ I := by
    intro hinv
    apply hg
    simpa using I.inv_mem hinv
  apply finrank_zero_iff_forall_zero.mpr
  intro f
  exact mackeyHomTerm_eq_zero_of_inv_not_mem_inertia ρ A ψ σ ι (Quotient.out d) hg_inv f

/--
The sum of Mackey Hom-term dimensions reduces to the identity double-coset
term.

All non-identity double-coset terms vanish by the inertia argument.
-/
lemma sum_mackeyHomTerm_eq_identity_term
    [Finite G]
    (ρ : FDRep k G)
    (A : Subgroup G) [A.Normal] [IsMulCommutative A]
    (ψ : A →* kˣ)
    (σ : FDRep k (LinearChar.inertia ψ))
    (ι : σ ⟶ LinearChar.psiEigenspaceFDRep
      (ρ := ρ) (A := A) (ψ := ψ))
    [Mono ι] :
    letI : Fintype (DoubleCoset.Quotient
      (G := G) (LinearChar.inertia ψ) (LinearChar.inertia ψ)) :=
      DoubleCoset.quotientFintype
        (LinearChar.inertia ψ) (LinearChar.inertia ψ)
    (∑ d : DoubleCoset.Quotient
        (G := G) (LinearChar.inertia ψ) (LinearChar.inertia ψ),
      Module.finrank k
        (mackeyHomTerm
          (k := k)
          (I := LinearChar.inertia ψ)
          σ
          (Quotient.out d)))
      =
    Module.finrank k
      (mackeyHomTerm
        (k := k)
        (I := LinearChar.inertia ψ)
        σ
        (Quotient.out
          (DoubleCoset.oneDC
            (G := G) (LinearChar.inertia ψ)))) := by
  letI : Fintype (DoubleCoset.Quotient
      (G := G) (LinearChar.inertia ψ) (LinearChar.inertia ψ)) :=
    DoubleCoset.quotientFintype
      (LinearChar.inertia ψ) (LinearChar.inertia ψ)
  apply Fintype.sum_eq_single
  · intro d hd
    exact finrank_mackeyHomTerm_eq_zero_of_ne_oneDC ρ A ψ σ ι d hd

open Classical in
/--
Mackey decomposition for the endomorphism dimension of an induced
representation.

The dimension of `End(Ind_I^G σ)` is the sum over double cosets `I \ G / I`
of the dimensions of the corresponding Mackey Hom terms.
-/
lemma finrank_end_ind_eq_sum_mackeyHomTerm
    {G : Type u} [Group G] [Finite G] [CharZero k]
    (I : Subgroup G)
    (σ : FDRep k I) :
    Module.finrank k (FDRep.ind I σ ⟶ FDRep.ind I σ)
      =
    letI : Fintype (DoubleCoset.Quotient (G := G) I I) :=
      DoubleCoset.quotientFintype I I
    ∑ d : DoubleCoset.Quotient (G := G) I I,
      Module.finrank k
        (mackeyHomTerm (k := k) I σ (Quotient.out d)) := by
  calc
    Module.finrank k (FDRep.ind I σ ⟶ FDRep.ind I σ)
        =
      Module.finrank k
        (σ ⟶ FDRep.res (FDRep.ind I σ) I) :=
      FDRep.finrank_end_ind_eq_hom_res_ind (k := k) I σ
    _ =
      letI : Fintype (DoubleCoset.Quotient (G := G) I I) :=
        DoubleCoset.quotientFintype I I
      ∑ d : DoubleCoset.Quotient (G := G) I I,
        Module.finrank k
          (mackeyHomTerm (k := k) I σ (Quotient.out d)) :=
      FDRep.finrank_hom_res_ind_eq_sum_mackeyHomTerm
        (k := k) I σ

/--
If `σ` embeds into the `ψ`-eigenspace and has inertia subgroup `I`, then
`End(Ind_I^G σ)` has dimension one.

The proof uses the Mackey decomposition: all non-identity double-coset terms
vanish by the inertia argument, while the identity term is `End(σ)`, which has
dimension one because `σ` is simple.
-/
theorem finrank_end_ind_from_inertia_eq_one
    {G : Type u} [Group G] [Finite G] [CharZero k] [IsAlgClosed k]
    (ρ : FDRep k G)
    (A : Subgroup G) [A.Normal] [IsMulCommutative A]
    (ψ : A →* kˣ)
    (σ : FDRep k (LinearChar.inertia ψ))
    (ι : σ ⟶ LinearChar.psiEigenspaceFDRep
      (ρ := ρ) (A := A) (ψ := ψ))
    [Mono ι] [Simple σ] :
    Module.finrank k (FDRep.ind (LinearChar.inertia ψ) σ ⟶
      FDRep.ind (LinearChar.inertia ψ) σ) = 1 := by
  let I : Subgroup G := LinearChar.inertia ψ
  letI : Fintype (DoubleCoset.Quotient (G := G) I I) :=
    DoubleCoset.quotientFintype I I
  calc
    Module.finrank k (FDRep.ind I σ ⟶ FDRep.ind I σ)
        =
      ∑ d : DoubleCoset.Quotient (G := G) I I,
        Module.finrank k
          (mackeyHomTerm (k := k) I σ (Quotient.out d)) := by
        exact FDRep.finrank_end_ind_eq_sum_mackeyHomTerm
          (k := k) (G := G) I σ
    _ =
      Module.finrank k
        (mackeyHomTerm
          (k := k) I σ
          (Quotient.out (DoubleCoset.oneDC (G := G) I))) := by
        exact FDRep.sum_mackeyHomTerm_eq_identity_term
          (ρ := ρ) (A := A) (ψ := ψ) (σ := σ) (ι := ι)
    _ =
      Module.finrank k (σ ⟶ σ) := finrank_mackeyHomTerm_oneDC_eq_end I σ
    _ = 1 := CategoryTheory.finrank_endomorphism_simple_eq_one k σ

end FDRep
