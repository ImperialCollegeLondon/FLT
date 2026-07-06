/-
Copyright (c) 2025 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McCarthy
-/
module

public import FLT.KnownIn1980s.BrauerInduction.Slop.Background.FDRep.Character.Induced
public import FLT.KnownIn1980s.BrauerInduction.Slop.Background.ClassFun.Character.Basis
public import FLT.KnownIn1980s.BrauerInduction.Slop.Background.LinearChar.Clifford
public import FLT.KnownIn1980s.BrauerInduction.Slop.Background.LinearChar.InducedCharacter
public import FLT.KnownIn1980s.BrauerInduction.Slop.BrauerElementaryGroup

@[expose] public section

/-!
# Brauer spans

This file defines the two Brauer spans used at the end of Bernstein's proof.

* `BrauerSpanChar` is the `ℤ`-span of characters induced from arbitrary
  representations of Brauer-elementary subgroups.

* `BrauerSpanLin` is the `ℤ`-span of characters induced from linear characters
  of Brauer-elementary subgroups.

The main result is

`BrauerSpanChar_le_BrauerSpanLin`,

which uses the nilpotence of Brauer-elementary groups to replace induced
characters by induced linear characters.  This converts the character-span
conclusion obtained from the projection step into the usual linear-character
form of Brauer induction.

The file also proves that `BrauerSpanChar` is closed under multiplication and
stable under induction from subgroups.
-/

universe u v

open BigOperators CategoryTheory

namespace BrauerInduction

section BrauerSpanLin

/--
A generator for the linear-character Brauer span: a Brauer-elementary subgroup
together with a linear character of it.
-/
structure BrauerLinGen (k : Type u) [CommRing k] (G : Type v) [Group G] where
  protected H : Subgroup G
  protected hElem : IsBrauerElementary H
  protected ψ : H →* kˣ

variable {k : Type u} [Field k]
variable {G : Type u} [Group G] [Fintype G]

namespace BrauerLinGen

/--
The finite-dimensional representation induced from the linear character attached
to a generator of `BrauerSpanLin`.
-/
noncomputable def inducedFDRep
    (i : BrauerLinGen k G) : FDRep k G :=
  FDRep.indLin i.H i.ψ

/--
The induced linear character attached to a generator of `BrauerSpanLin`.
-/
noncomputable def inducedCharacter
    (i : BrauerLinGen k G) : ClassFun k G :=
  ClassFun.character i.inducedFDRep

@[simp] lemma inducedCharacter_apply
    (i : BrauerLinGen k G) (g : G) :
    BrauerLinGen.inducedCharacter i g =
      i.inducedFDRep.character g := rfl

lemma inducedFDRep_character
    (i : BrauerLinGen k G) :
    ClassFun.character i.inducedFDRep =
      BrauerLinGen.inducedCharacter i := rfl

end BrauerLinGen

/--
The `ℤ`-span of characters induced from linear characters of Brauer-elementary
subgroups.
-/
def BrauerSpanLin : Submodule ℤ (ClassFun k G) :=
  Submodule.span ℤ (Set.range (BrauerLinGen.inducedCharacter))

/--
Membership in `BrauerSpanLin` gives an explicit finite `ℤ`-linear combination
of induced linear characters.
-/
theorem exists_decomposition_of_mem_BrauerSpanLin
    (χ : ClassFun k G)
    (hχ : χ ∈ BrauerSpanLin) :
    ∃ (ι : Type) (_ : Fintype ι)
      (ns : ι → ℤ) (Hs : ι → Subgroup G)
      (ψs : ∀ i, Hs i →* kˣ),
      (∀ i, IsBrauerElementary (Hs i)) ∧
      χ = ∑ i, (ns i) • (ClassFun.character (FDRep.indLin (Hs i) (ψs i))) := by
  let P : ClassFun k G → Prop :=
    fun φ =>
      ∃ (ι : Type) (_ : Fintype ι)
        (ns : ι → ℤ) (Hs : ι → Subgroup G)
        (ψs : ∀ i, Hs i →* kˣ),
        (∀ i,  IsBrauerElementary (Hs i)) ∧
        φ = ∑ i, (ns i) • ClassFun.character (FDRep.indLin (Hs i) (ψs i))
  have hP : P χ := by
    refine Submodule.span_induction (p := fun φ _ => P φ) ?gen ?zero ?add ?smul hχ
    · intro φ hφ
      rcases hφ with ⟨i, rfl⟩
      refine ⟨PUnit, inferInstance,
        (fun _ => (1 : ℤ)), (fun _ => i.H), (fun _ => i.ψ), (fun _ => i.hElem), ?_⟩
      ext g
      simp [BrauerLinGen.inducedCharacter, BrauerLinGen.inducedFDRep]
    · refine ⟨Empty, inferInstance, isEmptyElim, isEmptyElim, isEmptyElim, isEmptyElim, ?_⟩
      simp only [Finset.univ_eq_empty, zsmul_eq_mul, Finset.sum_empty]
    · intro x y _ _ hx hy
      rcases hx with ⟨ιx, _, nsx, Hsx, ψsx, hHx, rfl⟩
      rcases hy with ⟨ιy, _, nsy, Hsy, ψsy, hHy, rfl⟩
      refine ⟨Sum ιx ιy, inferInstance,
              Sum.elim nsx nsy,
              Sum.elim Hsx Hsy,
              (fun i => match i with | Sum.inl j => ψsx j | Sum.inr j => ψsy j),
              (fun i => match i with | Sum.inl j => hHx j | Sum.inr j => hHy j),
              ?_⟩
      simp only [zsmul_eq_mul, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]
    · intro n x _ hx
      rcases hx with ⟨ιx, _, nsx, Hsx, ψsx, hHx, rfl⟩
      refine ⟨ιx, inferInstance, (fun i => n * nsx i), Hsx, ψsx, hHx, ?_⟩
      rw [Finset.smul_sum]
      simp_rw [mul_smul]
  exact hP

end BrauerSpanLin

section BrauerSpanChar

variable {k : Type u} [Field k] {G : Type u} [Group G] [Fintype G]

/--
The `ℤ`-span of characters induced from representations of Brauer-elementary
subgroups.
-/
def BrauerSpanChar : Submodule ℤ (ClassFun k G) :=
  Submodule.span ℤ
    { φ | ∃ (H : Subgroup G) (_ : IsBrauerElementary H)
          (W :  FDRep k H),
        φ = ClassFun.ind H (ClassFun.character W) }


namespace BrauerSpanChar

/--
The character span is contained in the linear-character span.

The proof uses the fact that Brauer-elementary groups are nilpotent: every
simple representation of such a group is induced from a linear character of a
subgroup.  After decomposing an arbitrary character into irreducibles, induction
transitivity transports the resulting linear-character induction back to `G`.
-/
theorem le_BrauerSpanLin [IsAlgClosed k] [CharZero k] :
    BrauerSpanChar (k := k) (G := G) ≤ BrauerSpanLin := by
  rw [BrauerSpanChar, Submodule.span_le]
  rintro φ ⟨H, hH_elem, V, rfl⟩
  haveI : Group.IsNilpotent H := hH_elem.isNilpotent
  haveI:  NeZero ↑(Nat.card ↥H) := ⟨One.natCard_ne_zero_of_finite H⟩
  have h_decomp : ClassFun.character V ∈ Submodule.span ℤ { ψ | ∃ (S : FDRep k H)
    (_ : CategoryTheory.Simple S), ψ = ClassFun.character S } := by
    apply ClassFun.character_mem_span_irreducibles
  let P := fun (χ : ClassFun k H) => ClassFun.ind H χ ∈ BrauerSpanLin (k := k) (G := G)
  refine Submodule.span_induction (p := fun χ _ => P χ) ?gen ?zero ?add ?smul h_decomp
  · rintro σ ⟨S, hS_simple, rfl⟩
    obtain ⟨K, ψ_lin, ⟨h_iso⟩⟩ := FDRep.exists_indLin_of_nilpotent_simple (ρ := S)
    have h_char_eq :
        ClassFun.character S =
          ClassFun.character (FDRep.indLin K ψ_lin) :=
      ClassFun.char_eq_of_iso h_iso
    rw [h_char_eq]
    letI : DecidablePred fun x : G => x ∈ H := Classical.decPred _
    letI : Fintype H := H.instFintypeSubtypeMemOfDecidablePred
    rw [ClassFun.character_indLin (G := H) (k := k) K ψ_lin]
    unfold P
    let K_G : Subgroup G := K.map H.subtype
    let eK : K ≃* K_G :=
      K.equivMapOfInjective H.subtype Subtype.coe_injective
    let ψ_lin_G : K_G →* kˣ :=
      ψ_lin.comp eK.symm.toMonoidHom
    have hK_elem : IsBrauerElementary K := by
      exact IsBrauerElementary.ofSubgroup hH_elem K
    have hK_G_elem : IsBrauerElementary K_G := by
      exact IsBrauerElementary.ofMulEquiv hK_elem eK
    have h_trans_direct :
    ClassFun.ind H
      (ClassFun.ind K
        (ClassFun.character (FDRep.ofLinearChar ψ_lin)))
      =
    ClassFun.ind K_G
      ((ClassFun.equivOfMulEquiv (k := k) eK).symm
        (ClassFun.character (FDRep.ofLinearChar ψ_lin))) := by
      simpa [K_G, eK] using
        (ClassFun.ind_trans (K := H) (H := K)
          (ClassFun.character (FDRep.ofLinearChar ψ_lin)))
    rw [h_trans_direct]
    have h_char_lin_G :
        (ClassFun.equivOfMulEquiv eK).symm
            (ClassFun.character (FDRep.ofLinearChar ψ_lin))
          =
        ClassFun.character (FDRep.ofLinearChar ψ_lin_G) := by
      ext x
      rfl
    have h_indLin_G :
        ClassFun.character (FDRep.indLin K_G ψ_lin_G)
          =
        ClassFun.ind K_G
          ((ClassFun.equivOfMulEquiv (k := k) eK).symm
            (ClassFun.character (FDRep.ofLinearChar ψ_lin))) := by
      calc
        ClassFun.character (FDRep.indLin K_G ψ_lin_G)
            =
          ClassFun.ind K_G
            (ClassFun.character (FDRep.ofLinearChar ψ_lin_G)) := by
              change
                ClassFun.character
                  (FDRep.ind K_G
                    (FDRep.ofLinearChar ψ_lin_G))
                  =
                ClassFun.ind K_G
                  (ClassFun.character (FDRep.ofLinearChar ψ_lin_G))
              exact
                ClassFun.char_ind K_G (FDRep.ofLinearChar ψ_lin_G)
        _ =
          ClassFun.ind K_G
            ((ClassFun.equivOfMulEquiv eK).symm
              (ClassFun.character (FDRep.ofLinearChar ψ_lin))) := by
                rw [h_char_lin_G]
    rw [← h_indLin_G]
    exact Submodule.subset_span
      ⟨{ H := K_G, hElem := hK_G_elem, ψ := ψ_lin_G }, rfl⟩
  · dsimp [P]
    rw [ClassFun.ind_zero]
    exact Submodule.zero_mem _
  · intro x y _ _ hx hy
    dsimp [P]
    rw [ClassFun.ind_add]
    exact Submodule.add_mem _ hx hy
  · intro n x _ hx
    dsimp [P]
    rw [ClassFun.ind_zsmul n]
    exact Submodule.smul_mem _ n hx

/--
Multiplication on the left by the character of a representation preserves
membership in `BrauerSpanChar`.
-/
lemma character_mul_mem
    (V : FDRep k G) {φ : ClassFun k G}
    (hφ : φ ∈ BrauerSpanChar) :
    (ClassFun.character V) * φ ∈ BrauerSpanChar := by
  refine Submodule.span_induction
      (p := fun θ hθ => (ClassFun.character V) * θ ∈ BrauerSpanChar)
      (x := φ) (hx := hφ)
      ?gen ?zero ?add ?smul
  · intro θ hθ
    rcases hθ with ⟨H, hH_elem, W, rfl⟩
    rw [ClassFun.projection_formula H (ClassFun.character V)
          (ClassFun.character W)]
    rw [ClassFun.res_ofChar (H := H) V]
    have hmul :
      ClassFun.character (FDRep.res V H) *
        ClassFun.character W
        =
      ClassFun.character
        (FDRep.tensor
          (FDRep.res V H)
          W) := by
      exact (ClassFun.char_tensor
        (FDRep.res V H) W).symm
    rw [hmul]
    refine Submodule.subset_span ?_
    refine ⟨H, hH_elem, FDRep.tensor (FDRep.res V H) W, rfl⟩
  · simp [mul_zero]
  · intro x y _ _ hx hy
    rw [mul_add]
    exact Submodule.add_mem BrauerSpanChar hx hy
  · intro n x hx_in_span ihx
    have hcomm : (ClassFun.character V) * (n • x) = n • ((ClassFun.character V) * x) := by
      ext g
      simp only [ClassFun.mul_apply, ClassFun.zsmul_apply]
      rw [mul_smul_comm n]
    rw [hcomm]
    exact Submodule.smul_mem BrauerSpanChar n ihx

/--
The Brauer-character span is closed under pointwise multiplication.
-/
lemma mul_mem
    (f g : ClassFun k G)
    (hf : f ∈ BrauerSpanChar)
    (hg : g ∈ BrauerSpanChar) :
    f * g ∈ BrauerSpanChar := by
  refine Submodule.span_induction  ?_ ?_ ?_ ?_ hf
  · intro x hx
    obtain ⟨H, hH, V, rfl⟩ := hx
    let W : FDRep k G := FDRep.ind H V
    have hW : ClassFun.character W = ClassFun.ind H (ClassFun.character V) :=
       ClassFun.char_ind H V
    rw [← hW]
    exact character_mul_mem W hg
  · rw [zero_mul]
    exact Submodule.zero_mem _
  · intro x y _ _ hx_mem hy_mem
    rw [add_mul]
    exact Submodule.add_mem _ hx_mem hy_mem
  · intro z x _ hx_mem
    rw [smul_mul_assoc]
    exact Submodule.smul_mem _ z hx_mem

open Classical in
/--
Induction from a subgroup preserves membership in `BrauerSpanChar`.
-/
lemma induction_mem
    {H : Subgroup G}
    {ψ : ClassFun k H} (hψ : ψ ∈ BrauerSpanChar (G := H) (k := k)) :
    ClassFun.ind H ψ ∈ BrauerSpanChar := by
  let P := fun (f : ClassFun k H) => ClassFun.ind H f ∈ BrauerSpanChar
  refine Submodule.span_induction ?gen ?zero ?add ?smul hψ
  · rintro f ⟨K, hK_elem, W, rfl⟩
    let K_G : Subgroup G := K.map H.subtype
    let eK : K ≃* K_G := K.equivMapOfInjective H.subtype Subtype.coe_injective
    let W_G : FDRep k K_G := FDRep.transport eK W
    have h_transport_char :
        ClassFun.character W_G =
          (ClassFun.equivOfMulEquiv (k := k) eK).symm (ClassFun.character W) := by
      ext x
      rfl
    rw [ClassFun.ind_trans (K := H) (H := K) (ClassFun.character W)]
    rw [← h_transport_char]
    refine Submodule.subset_span ?_
    refine ⟨K_G, ?hK_G_elem, W_G, rfl⟩
    exact IsBrauerElementary.ofMulEquiv hK_elem eK
  · simp only [ClassFun.ind_zero, zero_mem]
  · intro x y hx hy hPx hPy
    rw [ClassFun.ind_add]
    exact Submodule.add_mem _ hPx hPy
  · intro n x hx hPx
    rw [ClassFun.ind_zsmul]
    exact Submodule.smul_mem _ n hPx

end BrauerSpanChar

end BrauerSpanChar

end BrauerInduction
