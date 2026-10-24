/-
Copyright (c) 2025 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McCarthy
-/
module

public import FLT.Slop.BrauerInduction.Background.ClassFun.Basic
public import FLT.Slop.BrauerInduction.Background.FDRep.Character.Basic
public import FLT.Slop.BrauerInduction.Background.FDRep.Simple

/-!

# The action of class functions on representations

A class function `f : ClassFun k G` determines a linear operator on every
finite-dimensional representation `V` of `G` by

`∑ g : G, f g • V(g⁻¹)`.

Conjugacy invariance of `f` implies that this operator commutes with the
`G`-action, so it defines an endomorphism of `V`. This file develops the
basic properties of this construction: naturality with respect to
intertwining maps, its trace formula, scalarity on simple representations,
compatibility with isomorphisms and finite biproducts, and faithfulness on
the left regular representation.
-/

@[expose] public section

namespace Slop
open Slop

universe u v

variable {k : Type u} [Field k] {G : Type v} [Group G]


open CategoryTheory CategoryTheory.Limits
open scoped BigOperators

namespace ClassFun

section LinearAction

/--
The linear operator on `V` associated to the class function `f`, defined by
`∑ g : G, f g • V(g⁻¹)`.
-/
noncomputable def action [Fintype G]
  (f : ClassFun k G) (V : FDRep k G) : V →ₗ[k] V :=
  ∑ g, f g • V.ρ g⁻¹

/--
The operator associated to a class function commutes with the action of every
group element.
-/
lemma action_comm [Fintype G] (f : ClassFun k G) (V : FDRep k G) (h : G) :
    action f V ∘ₗ V.ρ h = V.ρ h ∘ₗ action f V := by
  ext v
  simp only [action, LinearMap.comp_apply, LinearMap.sum_apply,
    LinearMap.smul_apply, map_sum, map_smul]
  let e : G ≃ G := MulAut.conj h
  have h_reindex := Equiv.sum_comp e (fun x => f x • V.ρ x⁻¹ (V.ρ h v))
  rw [← h_reindex]
  apply Finset.sum_congr rfl
  intro g _
  change
    f (h * g * h⁻¹) •
        (V.ρ (h * g * h⁻¹)⁻¹) ((V.ρ h) v)
      =
    f g • (V.ρ h) ((V.ρ g⁻¹) v)
  have hf_conj : f (h * g * h⁻¹) = f g := by
    let u : Gˣ := ⟨h⁻¹, h, by simp, by simp⟩
    exact f.map_conj (h * g * h⁻¹) g ⟨u, by
      change h⁻¹ * (h * g * h⁻¹) = g * h⁻¹
      group⟩
  have hρ :
      (V.ρ (h * g * h⁻¹)⁻¹) ((V.ρ h) v)
        =
      (V.ρ h) ((V.ρ g⁻¹) v) := by
    simp [map_mul, mul_assoc]
  rw [hf_conj, hρ]

/--
The trace of the action of a class function `f` on `V` is
`∑ g : G, f g * V.character g⁻¹`.
-/
lemma trace_action [Fintype G] (f : ClassFun k G) (V : FDRep k G) :
    LinearMap.trace k V (action f V) = ∑ g : G, f g * V.character g⁻¹ := by
  dsimp [action]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro g _
  have h_char : V.character g⁻¹ = LinearMap.trace k V (V.ρ g⁻¹) := rfl
  simp only [h_char, map_smul, smul_eq_mul]

end LinearAction

section EquivariantEndomorphism

/--
Package the class-function action as an equivariant endomorphism of `V`.
-/
noncomputable def actionHom [Fintype G]
    (f : ClassFun k G) (V : FDRep k G) : V ⟶ V :=
  FDRep.homOfLinearMap (ClassFun.action f V) (ClassFun.action_comm f V)

/--
The class-function action is natural with respect to intertwining maps.
-/
lemma action_naturality
    [Fintype G]
    (f : ClassFun k G)
    {V W : FDRep k G}
    (α : V ⟶ W) :
    FDRep.homToLinearMap α ∘ₗ ClassFun.action f V =
      ClassFun.action f W ∘ₗ FDRep.homToLinearMap α := by
  ext v
  simp only [action]
  rw [LinearMap.comp_apply, LinearMap.sum_apply]
  rw [LinearMap.comp_apply, LinearMap.sum_apply]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro g _
  simp only [LinearMap.smul_apply, map_smul]
  congr 1
  exact FDRep.homToLinearMap_rho_apply α g⁻¹ v

/--
The endomorphisms obtained from the class-function action form a natural
family with respect to morphisms of representations.
-/
lemma actionHom_naturality [Fintype G]
    (f : ClassFun k G) {A B : FDRep k G} (α : A ⟶ B) :
    actionHom f A ≫ α = α ≫ actionHom f B := by
  ext v
  exact LinearMap.congr_fun (action_naturality f α) v

/--
The bundled equivariant endomorphism associated to a class function is zero
if and only if its underlying linear action is zero.
-/
lemma actionHom_eq_zero_iff [Fintype G]
    (f : ClassFun k G) (V : FDRep k G) :
    actionHom f V = 0 ↔ ClassFun.action f V = 0 := by
  constructor
  · intro h
    ext v
    have hv :=
      congrArg (fun m : V ⟶ V => FDRep.homToLinearMap m v) h
    exact LinearMap.mem_eqLocus.mp hv
  · intro h
    ext v
    exact LinearMap.congr_fun h v


end EquivariantEndomorphism

section SimpleRepresentations

/--
If the equivariant endomorphism associated to `f` is multiplication by
`lambda`, then its trace is `lambda` times the dimension of the representation.
-/
lemma trace_action_eq_scalar_mul_finrank
    [Fintype G] (f : ClassFun k G) (V : FDRep k G)
    (lambda : k) (h : actionHom f V = lambda • 𝟙 V) :
    LinearMap.trace k V (action f V) =
      lambda * (Module.finrank k V : k) := by
  let F : (V ⟶ V) → (V →ₗ[k] V) :=
    fun m => FDRep.homToLinearMap m
  have h_map :
      F (actionHom f V) = F (lambda • 𝟙 V) :=
    congrArg F h
  have h_LHS :
      F (actionHom f V) = action f V := by
    rfl
  have h_RHS :
      F (lambda • 𝟙 V) =
        lambda • (LinearMap.id : V →ₗ[k] V) := by
    ext v
    rfl
  have h_lin :
      action f V =
        lambda • (LinearMap.id : V →ₗ[k] V) := by
    simpa [h_LHS, h_RHS] using h_map
  rw [h_lin]
  simp only [map_smul, LinearMap.trace_id, smul_eq_mul]


/--
On a simple representation over an algebraically closed field, the
endomorphism associated to a class function is scalar.
-/
lemma actionHom_is_scalar [Fintype G] [IsAlgClosed k]
  (f : ClassFun k G) (V : FDRep k G) [Simple V] :
    ∃ lambda : k, actionHom f V = lambda • 𝟙 V := by
  exact FDRep.end_eq_smul_id_of_simple V (actionHom f V)

end SimpleRepresentations

section IsomorphismsAndBiproducts

open Classical in
/--
Vanishing of the action of a class function is preserved when a
representation is replaced by an isomorphic representation.
-/
lemma action_zero_of_iso
    [Fintype G]
    (f : ClassFun k G)
    {A B : FDRep k G}
    (e : A ≅ B)
    (hB : ClassFun.action f B = 0) :
    ClassFun.action f A = 0 := by
  apply (actionHom_eq_zero_iff f A).mp
  have hBhom : actionHom f B = 0 :=
    (actionHom_eq_zero_iff f B).mpr hB
  rw [← cancel_mono e.hom]
  simpa [hBhom] using
    actionHom_naturality f e.hom

/--
A class function acts trivially on one representation if and only if it acts
trivially on any isomorphic representation.
-/
lemma action_eq_zero_iff_of_iso [Fintype G]
    {V W : FDRep k G}
    (f : ClassFun k G) (e : V ≅ W) :
    action f V = 0 ↔ action f W = 0 := by
  constructor
  · exact action_zero_of_iso f e.symm
  · exact action_zero_of_iso f e

/--
If a class function acts trivially on every representation in a finite family,
then the endomorphisms obtained from the class-function of their biproduct is
trivial.
-/
lemma actionHom_eq_zero_of_biproduct
    [Fintype G] {ι : Type*} [Finite ι]
    (f : ClassFun k G) (S : ι → FDRep k G)
    (hS : ∀ i, ClassFun.action f (S i) = 0) :
    actionHom f (biproduct S) = 0 := by
  apply biproduct.hom_ext
  intro i
  have hnat :
      actionHom f (biproduct S) ≫ biproduct.π S i =
        biproduct.π S i ≫ actionHom f (S i) :=
    actionHom_naturality f (biproduct.π S i)
  have hz : actionHom f (S i) = 0 :=
    (actionHom_eq_zero_iff f (S i)).mpr (hS i)
  rw [hz] at hnat
  simpa using hnat

/--
If a class function acts trivially on every representation in a finite
family, then it acts trivially on their biproduct.
-/
lemma action_zero_of_biproduct
    [Fintype G] {ι : Type*} [Finite ι]
    (f : ClassFun k G) (S : ι → FDRep k G)
    (hS : ∀ i, ClassFun.action f (S i) = 0) :
    ClassFun.action f (biproduct S) = 0 := by
  exact
    (actionHom_eq_zero_iff f (biproduct S)).mp
      (actionHom_eq_zero_of_biproduct f S hS)

end IsomorphismsAndBiproducts

section LeftRegular

/--
The action of class functions on the left regular representation is faithful:
if a class function acts as the zero endomorphism, then it is zero.
-/
lemma eq_zero_of_action_leftRegular_eq_zero
    {G : Type u} [Group G] [Fintype G] (f : ClassFun k G)
    (h_zero : ClassFun.action f (FDRep.leftRegular k G) = 0) :
    f = 0 := by
  classical
  ext g
  let R : FDRep k G := FDRep.leftRegular k G
  let v : R := by
    change MonoidAlgebra k G
    exact MonoidAlgebra.single (1 : G) (1 : k)
  let coeff : R →ₗ[k] k :=
    Finsupp.lapply g⁻¹ ∘ₗ (MonoidAlgebra.coeffLinearEquiv k).toLinearMap
  have h_apply :
      ClassFun.action f R v = 0 := by
    change ClassFun.action f (FDRep.leftRegular k G) v = 0
    rw [h_zero]
    rfl
  have h_coeff_zero :
      coeff (ClassFun.action f R v) = 0 := by
    simpa using congrArg coeff h_apply
  have h_coeff_action :
      coeff (ClassFun.action f R v) = f g := by
    dsimp [ClassFun.action]
    rw [LinearMap.sum_apply]
    rw [map_sum]
    have h_term :
        ∀ x : G,
          coeff (f x • R.ρ x⁻¹ v)
            =
          if x = g then f g else 0 := by
      intro x
      rw [map_smul]
      have h_rho :
          R.ρ x⁻¹ v =
            (MonoidAlgebra.single x⁻¹ (1 : k) : R) := by
        dsimp [R, v]
        simp only [
          FDRep.leftRegular_rho_single
            (a := x⁻¹) (b := 1) (r := (1 : k)),
          mul_one
        ]
      rw [h_rho]
      by_cases hx : x = g
      · subst x
        have h_eval :
            coeff ((MonoidAlgebra.single g⁻¹ (1 : k) : R)) = 1 := by
          change (Finsupp.lapply g⁻¹ ∘ₗ (MonoidAlgebra.coeffLinearEquiv k).toLinearMap)
            (MonoidAlgebra.single g⁻¹ (1 : k)) = 1
          rw [LinearMap.comp_apply, Finsupp.lapply_apply, LinearEquiv.coe_coe,
            MonoidAlgebra.coeffLinearEquiv_apply, MonoidAlgebra.coeff_single,
            Finsupp.single_apply, if_pos rfl]
        rw [h_eval]
        simp
      · have hne : x⁻¹ ≠ g⁻¹ := by
          intro h
          exact hx (inv_injective h)
        have h_eval :
            coeff ((MonoidAlgebra.single x⁻¹ (1 : k) : R)) = 0 := by
          change (Finsupp.lapply g⁻¹ ∘ₗ (MonoidAlgebra.coeffLinearEquiv k).toLinearMap)
            (MonoidAlgebra.single x⁻¹ (1 : k)) = 0
          rw [LinearMap.comp_apply, Finsupp.lapply_apply, LinearEquiv.coe_coe,
            MonoidAlgebra.coeffLinearEquiv_apply, MonoidAlgebra.coeff_single,
            Finsupp.single_apply, if_neg hne]
        rw [h_eval]
        simp only [smul_eq_mul, mul_zero, right_eq_ite_iff]
        intro h
        exact False.elim (hx h)
    calc
      (∑ x : G,
          coeff (((f x) • R.ρ x⁻¹ : R →ₗ[k] R) v))
          =
        ∑ x : G, if x = g then f g else 0 := by
          apply Finset.sum_congr rfl
          intro x _
          exact h_term x
      _ = f g := by
          simp
  rw [h_coeff_action] at h_coeff_zero
  exact h_coeff_zero

end LeftRegular

end ClassFun

end Slop
