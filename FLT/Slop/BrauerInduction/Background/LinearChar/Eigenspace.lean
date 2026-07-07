/-
Copyright (c) 2025 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McCarthy
-/
module

public import FLT.Slop.BrauerInduction.Background.LinearChar.Inertia
public import FLT.Slop.BrauerInduction.Background.FDRep.Res
public import Mathlib.CategoryTheory.Simple

/-!
# Eigenspaces attached to linear characters

This file constructs the `ψ`-eigenspace of a representation restricted to a
normal subgroup `A`, shows that it is stable under the inertia subgroup of `ψ`,
and packages it as an `FDRep`.

The final lemmas record the two Clifford-theoretic facts needed later: elements
of `A` act by the scalar `ψ`, and if the inertia subgroup is all of `G`, then a
nonzero eigenspace is the whole simple representation.
-/

@[expose] public section

namespace Slop
open Slop

universe u v w

namespace LinearChar

open CategoryTheory

variable {k : Type u} [Field k]
variable {G : Type v} [Group G]

/--
The `ψ`-eigenspace of the restriction of `ρ` to a normal subgroup `A`.
A vector `v` belongs to this subspace iff every `a : A` acts by the scalar `ψ a`.
-/
noncomputable def psiEigenspace
    (ρ : FDRep k G) (A : Subgroup G) (ψ : A →* kˣ) :
    Submodule k ρ :=
  ⨅ a : A, LinearMap.ker (ρ.ρ (a : G) - (ψ a : k) • LinearMap.id)

/--
Membership criterion for the `ψ`-eigenspace.
-/
lemma mem_psiEigenspace_iff
    (ρ : FDRep k G) (A : Subgroup G) (ψ : A →* kˣ) (v : ρ) :
    v ∈ psiEigenspace ρ A ψ
      ↔ ∀ a : A, ρ.ρ (a : G) v = (ψ a : k) • v := by
  simp only [psiEigenspace, Submodule.mem_iInf, LinearMap.mem_ker,
    LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
    sub_eq_zero]

/--
The `ψ`-eigenspace is stable under the inertia subgroup of `ψ`.
-/
lemma psiEigenspace_invariant
    (ρ : FDRep k G) (A : Subgroup G) [hA : A.Normal]
    (ψ : A →* kˣ)
    (g : LinearChar.inertia (H := A) ψ)
    (v : ρ)
    (hv : v ∈ psiEigenspace ρ A ψ) :
    ρ.ρ (g : G) v ∈ psiEigenspace ρ A ψ := by
  rw [mem_psiEigenspace_iff] at hv ⊢
  intro a
  have hmem : g.1⁻¹ * (a : G) * g.1 ∈ A := by
    simpa using Subgroup.Normal.conj_mem hA (a : G) a.2 (g.1⁻¹)
  let a' : A := ⟨g.1⁻¹ * (a : G) * g.1, hmem⟩
  have hag : (a : G) * (g : G) = (g : G) * (a' : G) := by
    dsimp [a']
    group
  calc
    ρ.ρ (a : G) (ρ.ρ (g : G) v)
        = ρ.ρ ((a : G) * (g : G)) v := by
          simp only [map_mul, Module.End.mul_apply]
    _ = ρ.ρ ((g : G) * (a' : G)) v := by
          rw [hag]
    _ = ρ.ρ (g : G) (ρ.ρ (a' : G) v) := by
          simp only [map_mul, Module.End.mul_apply]
    _ = ρ.ρ (g : G) ((ψ a' : k) • v) := by
          rw [hv a']
    _ = ρ.ρ (g : G) ((ψ a : k) • v) := by
          have hψ_units : ψ a' = ψ a := by
            have hg_inv : LinearChar.conj (H := A) ψ ((g : G)⁻¹) = ψ := by
              exact (LinearChar.mem_inertia_iff (H := A) ψ ((g : G)⁻¹)).mp
                (Subgroup.inv_mem (LinearChar.inertia (H := A) ψ) g.2)
            calc
              ψ a' = LinearChar.conj (H := A) ψ ((g : G)⁻¹) a := by
                rw [LinearChar.conj_apply]
                congr
                ext
                simp [a']
              _ = ψ a := by
                rw [hg_inv]
          have hψ : ((ψ a' : kˣ) : k) = ((ψ a : kˣ) : k) :=
            congrArg (fun z : kˣ => (z : k)) hψ_units
          rw [hψ]
    _ = (ψ a : k) • ρ.ρ (g : G) v := by
          exact (ρ.ρ (g : G)).map_smul (ψ a : k) v

/--
The `ψ`-eigenspace of `ρ` as a representation of the inertia subgroup of `ψ`.
-/
noncomputable def psiEigenspaceFDRep
    (ρ : FDRep k G)
    (A : Subgroup G) [A.Normal]
    (ψ : A →* kˣ) :
    FDRep k (LinearChar.inertia (H := A) ψ) :=
  FDRep.ofSubmodule
    (ρ.res (LinearChar.inertia (H := A) ψ))
    (psiEigenspace ρ A ψ)
    (by
      intro g v hv
      exact psiEigenspace_invariant
        ρ A ψ g v hv)

@[simp] lemma psiEigenspaceFDRep_rho_apply
    (ρ : FDRep k G)
    (A : Subgroup G) [A.Normal]
    (ψ : A →* kˣ)
    (g : inertia ψ)
    (v : psiEigenspace ρ A ψ) :
    (psiEigenspaceFDRep ρ A ψ).ρ g v
      =
    (⟨ρ.ρ (g : G) v.1,
      psiEigenspace_invariant ρ A ψ g v.1 v.2⟩ : psiEigenspace ρ A ψ) := by
  rfl

/--
The canonical inclusion of the `ψ`-eigenspace representation into the
restriction of `ρ` to the inertia subgroup of `ψ`.
-/
noncomputable def psiEigenspaceIncl
    (ρ : FDRep k G)
    (A : Subgroup G) [A.Normal]
    (ψ : A →* kˣ) :
    psiEigenspaceFDRep ρ A ψ
      ⟶
    ρ.res (LinearChar.inertia (H := A) ψ) :=
  FDRep.ofSubmoduleIncl
    (ρ.res (LinearChar.inertia (H := A) ψ))
    (psiEigenspace ρ A ψ)
    (by
      intro g v hv
      exact psiEigenspace_invariant
        ρ A ψ g v hv)

instance psiEigenspaceIncl_mono
    (ρ : FDRep k G)
    (A : Subgroup G) [A.Normal]
    (ψ : A →* kˣ) :
    Mono (psiEigenspaceIncl ρ A ψ) := by
  apply ConcreteCategory.mono_of_injective
     (C := FDRep k (LinearChar.inertia (H := A) ψ))
  exact
    (Set.injective_codRestrict Subtype.property).mp fun ⦃a₁ a₂⦄ a ↦ a

/--
Every element of `A` acts on the `ψ`-eigenspace by the scalar `ψ(a)`.
-/
lemma psiEigenspaceFDRep_rho_eq_smul_id
    (ρ : FDRep k G)
    (A : Subgroup G) [A.Normal] [IsMulCommutative A]
    (ψ : A →* kˣ)
    (a : A) :
    let I : Subgroup G := LinearChar.inertia (H := A) ψ
    let aI : I :=
      ⟨(a : G), LinearChar.le_inertia_of_isMulCommutative
        (A := A) ψ a.2⟩
    (psiEigenspaceFDRep ρ A ψ).ρ aI
      =
    (ψ a : k) • LinearMap.id := by
  ext v
  rw [psiEigenspaceFDRep_rho_apply]
  apply Subtype.ext
  exact (mem_psiEigenspace_iff
    ρ A ψ v.1).mp v.2 a

/--
If a representation embeds into the `ψ`-eigenspace, then every element of
`A` acts on it by the scalar `ψ(a)`.
-/
lemma sigma_rho_eq_smul_id_of_mono_into_psiEigenspace
    (ρ : FDRep k G)
    (A : Subgroup G) [A.Normal] [IsMulCommutative A]
    (ψ : A →* kˣ)
    (σ : FDRep k (LinearChar.inertia ψ))
    (ι : σ ⟶ psiEigenspaceFDRep ρ A ψ)
    [Mono ι]
    (a : A) :
    let I : Subgroup G := LinearChar.inertia ψ
    let aI : I := ⟨(a : G), LinearChar.le_inertia_of_isMulCommutative ψ a.2⟩
    σ.ρ aI = (ψ a : k) • LinearMap.id := by
  intro I aI
  ext x
  have hιinj : Function.Injective (FDRep.homToLinearMap ι) := by
      apply (FDRep.mono_iff_injective ι).mp
      exact MorphismProperty.monomorphisms.infer_property ι
  have h_val :
      FDRep.homToLinearMap ι (σ.ρ aI x)
        =
      (psiEigenspaceFDRep ρ A ψ).ρ aI (FDRep.homToLinearMap ι x) := by
    exact FDRep.homToLinearMap_rho_apply ι aI x
  rw [psiEigenspaceFDRep_rho_eq_smul_id
    ρ A ψ (a := a)] at h_val
  apply hιinj
  calc
    FDRep.homToLinearMap ι (σ.ρ aI x)
        = (ψ a : k) • FDRep.homToLinearMap ι x := h_val
    _ = FDRep.homToLinearMap ι ((ψ a : k) • x) := by
        simp only [map_smul]

private lemma psiEigenspace_ne_bot_of_hom_aux
    (ρ : FDRep k G)
    (A : Subgroup G)
    (ψ : A →* kˣ)
    {σ : FDRep k A}
    (hσ : ∀ (a : A) (x : σ), σ.ρ a x = (ψ a : k) • x)
    (f : σ ⟶ ρ.res A)
    (hf : f ≠ 0) :
    psiEigenspace ρ A ψ ≠ ⊥ := by
  intro hW
  apply hf
  ext x
  have hxW :
      (((FDRep.homToLinearMap f x : ρ.res A) : ρ) ∈
        psiEigenspace ρ A ψ) := by
    refine
      (mem_psiEigenspace_iff ρ A ψ
        (((FDRep.homToLinearMap f x : ρ.res A) : ρ))).2 ?_
    intro a
    calc
      ρ.ρ (a : G)
          (((FDRep.homToLinearMap f x : ρ.res A) : ρ))
          =
        ((ρ.res A).ρ a) (FDRep.homToLinearMap f x) := by
          rfl
      _ =
        FDRep.homToLinearMap f (σ.ρ a x) := by
          exact (FDRep.homToLinearMap_rho_apply f a x).symm
      _ =
        FDRep.homToLinearMap f ((ψ a : k) • x) := by
          rw [hσ a x]
      _ =
        (ψ a : k) • FDRep.homToLinearMap f x := by
          simp
  have hxBot :
      (((FDRep.homToLinearMap f x : ρ.res A) : ρ) ∈
        (⊥ : Submodule k ρ)) := by
    simpa [hW] using hxW
  have hxZero :
      (((FDRep.homToLinearMap f x : ρ.res A) : ρ) = 0) := by
    exact LinearMap.mem_ker.mp hxBot
  -- The goal after `ext x` is the pointwise zero statement for `f`.
  exact LinearMap.mem_eqLocus.mp hxBot

/--
A nonzero morphism from the one-dimensional representation associated to `ψ`
produces a nonzero `ψ`-eigenspace.
-/
lemma psiEigenspace_ne_bot_of_hom
    (ρ : FDRep k G)
    (A : Subgroup G)
    (ψ : A →* kˣ)
    (f : FDRep.ofLinearChar ψ ⟶ ρ.res A)
    (hf : f ≠ 0) :
    psiEigenspace ρ A ψ ≠ ⊥ := by
  have hσ :
      ∀ (a : A) (x : (FDRep.ofLinearChar ψ)),
        (FDRep.ofLinearChar ψ).ρ a x =
          (ψ a : k) • x := by
    intro a x
    exact FDRep.ofLinearChar_rho_apply
      (k := k) ψ a x
  exact psiEigenspace_ne_bot_of_hom_aux ρ A ψ hσ f hf

lemma psiEigenspace_invariant_of_inertia_eq_top
    (ρ : FDRep k G)
    (A : Subgroup G) [A.Normal]
    (ψ : A →* kˣ)
    (hI : LinearChar.inertia ψ = ⊤)
    (g : G)
    (v : ρ)
    (hv : v ∈ psiEigenspace ρ A ψ) :
    ρ.ρ g v ∈ psiEigenspace ρ A ψ := by
  have hg : g ∈ LinearChar.inertia ψ := by
    simp only [hI, Subgroup.mem_top]
  exact psiEigenspace_invariant
    ρ A ψ
    ⟨g, hg⟩ v hv

/--
If the inertia subgroup is all of `G`, then the `ψ`-eigenspace is a
`G`-subrepresentation of `ρ`.
-/
noncomputable def psiEigenspaceFDRepOfInertiaEqTop
    (ρ : FDRep k G)
    (A : Subgroup G) [A.Normal]
    (ψ : A →* kˣ)
    (hI : LinearChar.inertia ψ = ⊤) :
    FDRep k G := by
  let W : Submodule k ρ := psiEigenspace ρ A ψ
  exact FDRep.ofSubmodule ρ W (by
    intro g x hx
    exact psiEigenspace_invariant_of_inertia_eq_top
      ρ A ψ hI g x hx)

/--
The whole-group eigenspace representation embeds into `ρ`.
-/
noncomputable def psiEigenspaceInclOfInertiaEqTop
    (ρ : FDRep k G)
    (A : Subgroup G) [A.Normal]
    (ψ : A →* kˣ)
    (hI : LinearChar.inertia ψ = ⊤) :
    psiEigenspaceFDRepOfInertiaEqTop
      ρ A ψ hI ⟶ ρ := by
  let W : Submodule k ρ := psiEigenspace ρ A ψ
  exact FDRep.ofSubmoduleIncl ρ W (by
    intro g x hx
    exact psiEigenspace_invariant_of_inertia_eq_top
      ρ A ψ hI g x hx)

@[simp] lemma psiEigenspaceInclOfInertiaEqTop_apply
    (ρ : FDRep k G)
    (A : Subgroup G) [A.Normal]
    (ψ : A →* kˣ)
    (hI : LinearChar.inertia ψ = ⊤)
    (x : psiEigenspace ρ A ψ) :
    (psiEigenspaceInclOfInertiaEqTop
      ρ A ψ hI).hom x
      =
    (x : ρ) := by
  rfl

lemma psiEigenspaceInclOfInertiaEqTop_ne_zero
    (ρ : FDRep k G)
    (A : Subgroup G) [A.Normal]
    (ψ : A →* kˣ)
    (hI : LinearChar.inertia ψ = ⊤)
    (hW : psiEigenspace ρ A ψ ≠ ⊥) :
    psiEigenspaceInclOfInertiaEqTop
      ρ A ψ hI ≠ 0 := by
  intro hi
  apply hW
  apply le_antisymm
  · intro x hx
    let xW : psiEigenspace ρ A ψ := ⟨x, hx⟩
    have h_app :
        (psiEigenspaceInclOfInertiaEqTop ρ A ψ hI).hom xW
          =
        (0 : psiEigenspaceFDRepOfInertiaEqTop ρ A ψ hI ⟶ ρ).hom xW := by
      exact congrArg
        (fun f :
          psiEigenspaceFDRepOfInertiaEqTop ρ A ψ hI ⟶ ρ => f.hom xW) hi
    have h_app :=
      congrArg
        (fun f : psiEigenspaceFDRepOfInertiaEqTop ρ A  ψ hI ⟶ ρ => f.hom xW) hi
    have hx0 : x = 0 := by
      change x = 0 at h_app
      exact h_app
    simpa [Submodule.mem_bot] using hx0
  · exact bot_le

lemma psiEigenspace_eq_top_of_inertia_eq_top
    (ρ : FDRep k G)
    (A : Subgroup G) [A.Normal]
    (ψ : A →* kˣ)
    (hI : LinearChar.inertia ψ = ⊤)
    (hW : psiEigenspace ρ A ψ ≠ ⊥)
    [Simple ρ] :
    psiEigenspace ρ A ψ = ⊤ := by
  let W : Submodule k ρ := psiEigenspace ρ A ψ
  let σ : FDRep k G := psiEigenspaceFDRepOfInertiaEqTop ρ A ψ hI
  let i : σ ⟶ ρ := psiEigenspaceInclOfInertiaEqTop ρ A ψ hI
  have hi_ne : i ≠ 0 := psiEigenspaceInclOfInertiaEqTop_ne_zero ρ A ψ hI hW
  haveI : Mono i := by
    apply ConcreteCategory.mono_of_injective
      (C := FDRep k G)
    exact
      (Set.injective_codRestrict Subtype.property).mp
        fun ⦃a₁ a₂⦄ h ↦ h
  haveI : IsIso i := by
    exact isIso_of_mono_of_nonzero (f:=i) hi_ne
  apply eq_top_iff.mpr
  intro x hx
  let y : W := (inv i).hom x
  have hy : i.hom y = x := by
    change ((inv i ≫ i).hom) x = ((𝟙 ρ : ρ ⟶ ρ).hom) x
    rw [IsIso.inv_hom_id i]
  have hyW : (y : ρ) ∈ W := y.2
  simpa [W, i, FDRep.ofSubmoduleIncl_apply] using hy ▸ hyW

/--
If the inertia subgroup of `ψ` is all of `G`, then `ρ(g)` acts by the scalar
`ψ(g)` on the whole `ψ`-eigenspace.
-/
lemma rho_eq_smul_of_inertia_eq_top
    (ρ : FDRep k G) [Simple ρ]
    (A : Subgroup G) [A.Normal] [IsMulCommutative A]
    (ψ : A →* kˣ)
    (hI : LinearChar.inertia ψ = ⊤)
    (hW : LinearChar.psiEigenspace ρ A ψ ≠ ⊥) :
    ∀ a : A, ρ.ρ (a : G) = (ψ a : k) • LinearMap.id := by
  intro a
  have hW_top :
    LinearChar.psiEigenspace ρ A ψ = ⊤ :=
      psiEigenspace_eq_top_of_inertia_eq_top ρ A ψ hI hW
  apply LinearMap.ext
  intro v
  have hv : v ∈ LinearChar.psiEigenspace ρ A ψ := by
    simp only [hW_top, Submodule.mem_top]
  exact
    (LinearChar.mem_psiEigenspace_iff ρ A ψ v).1 hv a

end LinearChar

end Slop
