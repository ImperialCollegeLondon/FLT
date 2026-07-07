/-
Copyright (c) 2025 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McCarthy
-/
module

public import FLT.Slop.Background.ClassFun.Character.Induced
public import FLT.Slop.Background.ClassFun.Maps
public import FLT.Slop.Lambda
public import FLT.Slop.Background.FDRep.Character.Induced

@[expose] public section

/-!
# Bernstein character systems

This file defines the character-system pieces used in Bernstein's proof of
Brauer induction.

For a fixed ambient finite group `G`, the submodule `R_Lambda k G H` is the
`Λ`-span of characters of finite-dimensional representations of the subgroup
`H`. The set `Q_sys k G H` is the intersection of `R_Lambda k G H` with the
integer-valued class functions `C_Z k H`.

The main closure properties proved here are:

* `ClassFun.R_Lambda.ind_mem`: induction preserves `R_Λ`;
* `ClassFun.R_Lambda.comp_inclusion_mem`: restriction along subgroup inclusion
  preserves `R_Λ`;
* `ClassFun.R_Lambda.mul_mem`: `R_Λ` is closed under pointwise multiplication;
* `ClassFun.Q_sys.ind_mem`: induction preserves `Q = R_Λ ∩ C_Z`.
-/

universe u v

open scoped BigOperators

variable {k : Type u} [Field k]
variable {G : Type u} [Group G] [Finite G]

namespace ClassFun

section R_Λ

/--
Bernstein's character system `R_Λ`.

For a subgroup `H ≤ G`, `R_Lambda k G H` is the `Λ`-span of characters of
finite-dimensional representations of `H`, where `Λ = ClassFun.Lambda k G` is
formed using the fixed ambient group `G`.
-/
def R_Lambda
    (k : Type u) [Field k]
    (G : Type u) [Group G] [Finite G]
    (H : Subgroup G) :
    Submodule (Lambda k G) (ClassFun k H) :=
  Submodule.span (Lambda k G)
    { χ : ClassFun k H |
        ∃ V : FDRep k H, χ = ClassFun.character V }

namespace R_Lambda
/-- Characters of finite-dimensional representations lie in `R_Λ(H)`. -/
lemma char_mem
    (H : Subgroup G) (V : FDRep k H) :
    ClassFun.character V ∈ R_Lambda k G H := by
  exact Submodule.subset_span ⟨V, rfl⟩

/--
Induction preserves `R_Λ`.

The result is stated after restricting the induced class function to `⊤`, so
that the target is the subgroup-indexed module `R_Lambda k G ⊤`.
-/
lemma ind_mem
    [Fintype G]
    (H : Subgroup G)
    {q : ClassFun k H}
    (hq : q ∈ R_Lambda k G H) :
    ClassFun.res (G := G) (k := k) (⊤ : Subgroup G)
      (ClassFun.ind (G := G) (k := k) H q)
      ∈ R_Lambda k G (⊤ : Subgroup G) := by
  refine Submodule.span_induction
    (p := fun q _ =>
      ClassFun.res (G := G) (k := k) (⊤ : Subgroup G)
        (ClassFun.ind (G := G) (k := k) H q)
        ∈ R_Lambda k G (⊤ : Subgroup G))
    ?gen ?zero ?add ?smul hq
  · rintro χ ⟨V, rfl⟩
    rw [← ClassFun.char_ind]
    rw [ClassFun.res_ofChar]
    exact Submodule.subset_span
      ⟨FDRep.res (k := k) (G := G)
          (FDRep.ind (k := k) (G := G) H V)
          (⊤ : Subgroup G),
        rfl⟩
  · simp only [ClassFun.ind_zero, ClassFun.res_zero, zero_mem]
  · intro x y hx hy ihx ihy
    rw [ClassFun.ind_add, ClassFun.res_add]
    exact Submodule.add_mem _ ihx ihy
  · intro a x hx ihx
    change
      ClassFun.res (G := G) (k := k) (⊤ : Subgroup G)
        (ClassFun.ind (G := G) (k := k) H
          (((a : Lambda k G) : k) • x))
        ∈ R_Lambda k G (⊤ : Subgroup G)
    rw [ClassFun.ind_smul (H := H) ((a : Lambda k G) : k) x]
    rw [ClassFun.res_smul
      (K := (⊤ : Subgroup G))
      ((a : Lambda k G) : k)
      (ClassFun.ind (G := G) (k := k) H x)]
    exact Submodule.smul_mem _ a ihx

open Classical in
/--
Restriction along a subgroup inclusion preserves `R_Λ`.

If `H ≤ K` and a class function on `K` lies in the `Λ`-span of characters of
finite-dimensional representations of `K`, then its composition with the
inclusion `H → K` lies in the corresponding `Λ`-span for `H`.
-/
lemma comp_inclusion_mem
    {H K : Subgroup G} (hHK : H ≤ K)
    (φ : ClassFun k K)
    (hφ : φ ∈ R_Lambda k G K) :
    φ.comp (Subgroup.inclusion hHK)
      ∈ R_Lambda k G H := by
  dsimp [R_Lambda] at hφ ⊢
  refine Submodule.span_induction
    (s := {χ : ClassFun k K |
      ∃ V : FDRep k K, χ = ClassFun.character V})
    (p := fun x _ =>
      x.comp (Subgroup.inclusion hHK)
        ∈ Submodule.span (Lambda k G)
          {χ : ClassFun k H |
            ∃ W : FDRep k H, χ = ClassFun.character W})
    ?mem ?zero ?add ?smul hφ
  · intro ψ hψ
    rcases hψ with ⟨V, rfl⟩
    apply Submodule.subset_span
    let HK : Subgroup K := H.subgroupOf K
    let W₀ : FDRep k HK :=
      FDRep.res (k := k) (G := K) V HK
    let e : HK ≃* H :=
      Subgroup.subgroupOfEquiv (H := H) (K := K) hHK
    let W : FDRep k H :=
      FDRep.transport e W₀
    refine ⟨W, ?_⟩
    ext h
    simp only [ClassFun.comp_apply, ClassFun.char_apply]
    rw [FDRep.char_transport]
    simp only [Function.comp_apply]
    rfl
  · simp
  · intro x y hx hy hx' hy'
    simpa using Submodule.add_mem _ hx' hy'
  · intro a x hx hx'
    have h_smul :
        (a • x).comp (Subgroup.inclusion hHK)
          =
        a • x.comp (Subgroup.inclusion hHK) := by
      ext h
      rfl
    rw [h_smul]
    simpa using Submodule.smul_mem _ a hx'

/--
Restricting from `⊤` to a subgroup preserves membership in `R_Λ`.

This is the special case of `R_Lambda.comp_inclusion_mem` used in the localized
ideal multiplication proof.
-/
lemma res_top_to_subgroup
     {E : Subgroup G} {g : ClassFun k G}
    (hg :
      ClassFun.res (G := G) (k := k) (⊤ : Subgroup G) g
        ∈ R_Lambda k G (⊤ : Subgroup G)) :
    ClassFun.res (G := G) (k := k) E g
      ∈ R_Lambda k G E := by
  have h_le : E ≤ (⊤ : Subgroup G) := by
    intro x hx
    exact Subgroup.mem_top x
  have h_comp :=
    comp_inclusion_mem
      (G := G) (k := k)
      h_le
      (ClassFun.res (G := G) (k := k) (⊤ : Subgroup G) g)
      hg
  exact (Submodule.mem_toAddSubgroup (R_Lambda k G E)).mp h_comp

/--
The character system `R_Λ` is closed under pointwise multiplication.
-/
lemma mul_mem
    {k : Type u} [Field k] {H : Subgroup G} {f g : ClassFun k H}
    (hf : f ∈ R_Lambda k G H)
    (hg : g ∈ R_Lambda k G H) :
    f * g ∈ R_Lambda k G H := by
  refine Submodule.span_induction
    (p := fun f _ => f * g ∈ R_Lambda k G H)
    ?gen_f ?zero_f ?add_f ?smul_f hf
  · rintro _ ⟨V, rfl⟩
    refine Submodule.span_induction
      (p := fun g _ => ClassFun.character V * g ∈ R_Lambda k G H)
      ?gen_g ?zero_g ?add_g ?smul_g hg
    · rintro _ ⟨W, rfl⟩
      rw [(ClassFun.char_tensor V W).symm]
      exact Submodule.subset_span
        ⟨FDRep.tensor V W, rfl⟩
    · simp
    · intro y₁ y₂ _ _ hy₁ hy₂
      rw [mul_add]
      exact Submodule.add_mem _ hy₁ hy₂
    · intro c y _ hy
      have h_comm :
          ClassFun.character V * (c • y)
            =
          c • (ClassFun.character V * y) := by
        ext z
        change
          ClassFun.character V z * ((c : k) * y z)
            =
          (c : k) * (ClassFun.character V z * y z)
        ring
      rw [h_comm]
      exact Submodule.smul_mem _ c hy
  · simp
  · intro x₁ x₂ _ _ hx₁ hx₂
    rw [add_mul]
    exact Submodule.add_mem _ hx₁ hx₂
  · intro c x _ hx
    have h_assoc :
        (c • x) * g = c • (x * g) := by
      ext z
      change
        ((c : k) * x z) * g z
          =
        (c : k) * (x z * g z)
      ring
    rw [h_assoc]
    exact Submodule.smul_mem _ c hx


/--
The global `Λ`-span of characters of finite-dimensional representations of `G`.

This is the version of `R_Lambda k G ⊤` living directly on `G`, rather than on
the top subgroup `⊤ : Subgroup G`.
-/
def top
    (k : Type u) [Field k]
    (G : Type u) [Group G] [Finite G] :
    Submodule (Lambda k G) (ClassFun k G) :=
  Submodule.span (Lambda k G)
    { χ : ClassFun k G |
      ∃ V : FDRep k G,
        χ = ClassFun.character V }

/--
Restricting an element of the global `R_Λ` to a subgroup gives an element of
the subgroup-indexed `R_Λ`.
-/
lemma top_res_to_subgroup
    (H : Subgroup G)
    {f : ClassFun k G}
    (hf : f ∈ R_Lambda.top k G) :
    ClassFun.res (G := G) (k := k) H f ∈ R_Lambda k G H := by
  unfold R_Lambda.top at hf
  unfold R_Lambda
  refine Submodule.span_induction
    (p := fun f _ =>
      ClassFun.res (G := G) (k := k) H f ∈
        Submodule.span (Lambda k G)
          {χ : ClassFun k H |
            ∃ V : FDRep k H, χ = ClassFun.character V})
    ?gen ?zero ?add ?smul hf
  · rintro χ ⟨V, rfl⟩
    rw [ClassFun.res_ofChar]
    exact Submodule.subset_span
      ⟨FDRep.res (k := k) (G := G) V H, rfl⟩
  · rw [ClassFun.res_zero]
    exact Submodule.zero_mem _
  · intro x y _ _ hx hy
    rw [ClassFun.res_add]
    exact Submodule.add_mem _ hx hy
  · intro a x _ hx
    change
      ClassFun.res (G := G) (k := k) H ((a : k) • x) ∈
        Submodule.span (Lambda k G)
          {χ : ClassFun k H |
            ∃ V : FDRep k H, χ = ClassFun.character V}
    rw [ClassFun.res_smul]
    exact Submodule.smul_mem _ a hx

end R_Lambda
end R_Λ

section QSys
/--
Bernstein's character system `Q`.

For a subgroup `H ≤ G`, `Q_sys k G H` consists of class functions lying both in
`R_Λ(H)` and in the integer-valued class functions `C_Z(H)`.
-/
def Q_sys (k : Type u) [Field k]
    (G : Type u) [Group G] [Finite G]
    (H : Subgroup G) : Set (ClassFun k H) :=
  { χ | χ ∈ R_Lambda k G H ∧ χ ∈ C_Z k H }

/--
The character system `Q` on the top subgroup of the fixed ambient group.
-/
abbrev Q_top (k : Type u) [Field k]
    (G : Type u) [Group G] [Finite G] :
    Set (ClassFun k (⊤ : Subgroup G)) :=
  Q_sys k G (⊤ : Subgroup G)

/--
Induction preserves Bernstein's character system `Q = R_Λ ∩ C_Z`.
-/
lemma Q_sys.ind_mem
    {k : Type u} [Field k]
    {G : Type u} [Group G] [Fintype G]
    {H : Subgroup G} {q : ClassFun k H}
    (hq : q ∈ Q_sys k G H) :
    ClassFun.res (G := G) (k := k) (⊤ : Subgroup G)
      (ClassFun.ind (G := G) (k := k) H q)
      ∈ Q_sys k G (⊤ : Subgroup G) := by
  exact ⟨
    R_Lambda.ind_mem (k := k) (G := G) H hq.1,
    C_Z.ind_mem_C_Z (k := k) (G := G) hq.2
  ⟩

end QSys

end ClassFun
