/-
Copyright (c) 2025 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McCarthy
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import FLT.KnownIn1980s.BrauerInduction.Slop.Background.FDRep.Simple

@[expose] public section

universe u v

/-!
# Simple representations of abelian groups

This file contains elementary consequences of Schur's lemma for simple
finite-dimensional representations of abelian groups. In particular, over an
algebraically closed field, every simple finite-dimensional representation of
a commutative group is one-dimensional.
-/

open CategoryTheory

namespace FDRep

variable {k : Type u} [Field k]
variable {G : Type v} [Group G]

/--
The action of an element of a commutative group as an endomorphism of a
representation.
-/
noncomputable def endoOfAction
    [IsMulCommutative G]
    (ρ : FDRep k G) (g : G) : ρ ⟶ ρ :=
  FDRep.forget₂HomLinearEquiv ρ ρ
    (Rep.ofHom
      { toLinearMap := ρ.ρ g
        isIntertwining' := by
          intro h
          ext v
          change ρ.ρ g (ρ.ρ h v) = ρ.ρ h (ρ.ρ g v)
          calc
            ρ.ρ g (ρ.ρ h v)
                = (ρ.ρ g * ρ.ρ h) v := rfl
            _ = ρ.ρ (g * h) v := by rw [← map_mul]
            _ = ρ.ρ (h * g) v := by rw [mul_comm' g h]
            _ = (ρ.ρ h * ρ.ρ g) v := by rw [map_mul]
            _ = ρ.ρ h (ρ.ρ g v) := rfl })

/--
The underlying linear map of the endomorphism induced by the action of a group
element.
-/
@[simp]
lemma endoOfAction_homToLinearMap
    [IsMulCommutative G]
    (ρ : FDRep k G) (g : G) :
    FDRep.homToLinearMap (FDRep.endoOfAction ρ g) = ρ.ρ g := by
  rfl

/--
Evaluation of the endomorphism induced by the action of a group element.
-/
@[simp]
lemma endoOfAction_hom_apply
    [IsMulCommutative G]
    (ρ : FDRep k G) (g : G) (v : ρ) :
    FDRep.homToLinearMap (FDRep.endoOfAction ρ g) v = ρ.ρ g v := by
  rfl

/--
In a simple representation of a commutative group over an algebraically closed
field, every group element acts by a scalar.
-/
lemma exists_scalar_action_of_simple_abelian
    [IsMulCommutative G] [IsAlgClosed k]
    (ρ : FDRep k G) [Simple ρ] (g : G) :
    ∃ c : k, ρ.ρ g = c • LinearMap.id := by
  obtain ⟨c, hc⟩ :=
    CategoryTheory.endomorphism_simple_eq_smul_id
      (𝕜 := k) (f := FDRep.endoOfAction ρ g)
  refine ⟨c, ?_⟩
  ext v
  have h :=
    congrArg
      (fun f : ρ ⟶ ρ => FDRep.homToLinearMap f v)
      hc
  change ρ.ρ g v = c • v
  calc
    ρ.ρ g v
        = FDRep.homToLinearMap (FDRep.endoOfAction ρ g) v := by
            rw [FDRep.endoOfAction_hom_apply]
    _ = FDRep.homToLinearMap (c • 𝟙 ρ : ρ ⟶ ρ) v := by
            exact h.symm
    _ = c • v := by
            rfl

/--
Every simple finite-dimensional representation of a commutative group over an
algebraically closed field is one-dimensional.
-/
lemma abelian_simple_is_linear
    [IsMulCommutative G] [IsAlgClosed k]
    (ρ : FDRep k G) [Simple ρ] :
    Module.finrank k ρ = 1 := by
  have hρnz : Nontrivial ρ := FDRep.nontrivial_of_simple ρ
  obtain ⟨v, hv⟩ : ∃ v : ρ, v ≠ 0 := by
    exact exists_ne (0 : ρ)
  let W : Submodule k ρ := Submodule.span k ({v} : Set ρ)
  have hstable : ∀ g : G, W ≤ W.comap (ρ.ρ g) := by
    intro g x hx
    obtain ⟨c, hc⟩ :=
      FDRep.exists_scalar_action_of_simple_abelian (ρ := ρ) g
    change ρ.ρ g x ∈ W
    rw [hc]
    exact W.smul_mem c hx
  let σ : FDRep k G := FDRep.ofSubmodule ρ W hstable
  let i : σ ⟶ ρ := FDRep.ofSubmoduleIncl ρ W hstable
  haveI : Mono i := by
    apply ConcreteCategory.mono_of_injective
      (C := FDRep k G)
    exact
      (Set.injective_codRestrict Subtype.property).mp
        fun ⦃a₁ a₂⦄ h ↦ h
  have hi_ne : i ≠ 0 := by
    intro hi
    have h_app :
        FDRep.homToLinearMap i
            (⟨v, Submodule.subset_span (by simp)⟩ : W)
          =
        FDRep.homToLinearMap (0 : σ ⟶ ρ)
            (⟨v, Submodule.subset_span (by simp)⟩ : W) := by
      exact congrArg
        (fun f : σ ⟶ ρ =>
          FDRep.homToLinearMap f
            (⟨v, Submodule.subset_span (by simp)⟩ : W))
        hi
    have hv0 : v = 0 := not_neZero.mp fun a ↦ hv h_app
    exact hv hv0
  haveI : IsIso i := isIso_of_mono_of_nonzero (f := i) hi_ne
  have hWtop : W = ⊤ := by
    apply eq_top_iff.mpr
    intro x hx
    let y : W := (inv i).hom x
    have hy : i.hom y = x := by
      change ((inv i ≫ i).hom) x = ((𝟙 ρ : ρ ⟶ ρ).hom) x
      rw [IsIso.inv_hom_id i]
    have hyW : (y : ρ) ∈ W := y.2
    simpa [i, FDRep.ofSubmoduleIncl_apply] using hy ▸ hyW
  have hspan_top :
      k ∙ v = (⊤ : Submodule k ρ) := by
    simpa [W] using hWtop
  exact (finrank_eq_one_iff_of_nonzero v hv).2 hspan_top

end FDRep
