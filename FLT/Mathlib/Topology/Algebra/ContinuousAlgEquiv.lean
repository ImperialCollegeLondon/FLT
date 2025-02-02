/-
Copyright (c) 2024 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
import Mathlib.Topology.Algebra.Algebra
import Mathlib.Topology.Algebra.Algebra.Equiv
import FLT.Mathlib.Algebra.Algebra.Pi

/-!
# Topological (sub)algebras

more API for `ContinuousAlgEquiv`.
-/

open scoped Topology

namespace ContinuousAlgEquiv

variable {ι α β : Type*}

@[simps!]
def piCurry (S : Type*) [CommSemiring S] {Y : ι → Type*}
    (α : (i : ι) → Y i → Type*) [(i : ι) → (y : Y i) → Semiring (α i y)]
    [(i : ι) → (y : Y i) → Algebra S (α i y)] [(i : ι) → (y : Y i) → TopologicalSpace (α i y)] :
    ((i : Sigma Y) → α i.1 i.2) ≃A[S] ((i : ι) → (y : Y i) → α i y) where
  toAlgEquiv := AlgEquiv.piCurry S α
  continuous_toFun := continuous_pi (fun _ => continuous_pi <| fun _ => continuous_apply _)
  continuous_invFun := by
    refine continuous_pi (fun ⟨x, y⟩ => ?_)
    simp only [AlgEquiv.toEquiv_eq_coe, Equiv.invFun_as_coe, AlgEquiv.symm_toEquiv_eq_symm,
      EquivLike.coe_coe, AlgEquiv.piCurry_symm_apply, Sigma.uncurry]
    exact Continuous.comp' (continuous_apply _) (continuous_apply _)

@[simps!]
def piCongrLeft (S : Type*) [CommSemiring S] (B : β → Type*) (e : α ≃ β)
    [∀ b, Semiring (B b)] [∀ b, Algebra S (B b)] [∀ b, TopologicalSpace (B b)]  :
    ((a : α) → B (e a)) ≃A[S] ((b : β) → B b) where
  toAlgEquiv := AlgEquiv.piCongrLeft S B e
  continuous_toFun := continuous_pi <| e.forall_congr_right.mp fun i ↦ by
    simp only [AlgEquiv.toEquiv_eq_coe, AlgEquiv.piCongrLeft, Equiv.toFun_as_coe, EquivLike.coe_coe]
    have := AlgEquiv.piCongrLeft'_symm_apply_apply S B e.symm
    simp only [Equiv.symm_symm_apply] at this
    simp only [this]
    exact continuous_apply _
  continuous_invFun := Pi.continuous_precomp' e

def piCongrRight {R ι : Type*} {A₁ A₂ : ι → Type*} [CommSemiring R]
    [(i : ι) → Semiring (A₁ i)] [(i : ι) → Semiring (A₂ i)] [(i : ι) → TopologicalSpace (A₁ i)]
    [(i : ι) → TopologicalSpace (A₂ i)] [(i : ι) → Algebra R (A₁ i)] [(i : ι) → Algebra R (A₂ i)]
    (e : (i : ι) → A₁ i ≃A[R] A₂ i) :
    ((i : ι) → A₁ i) ≃A[R] (i : ι) → A₂ i where
  __ := AlgEquiv.piCongrRight <| fun _ => (e _).toAlgEquiv
  continuous_toFun := Pi.continuous_postcomp' fun i ↦ (e i).continuous
  continuous_invFun := Pi.continuous_postcomp' fun i ↦ (e i).symm.continuous

@[simp]
theorem piCongrRight_apply {R ι : Type*} {A₁ A₂ : ι → Type*} [CommSemiring R]
    [(i : ι) → Semiring (A₁ i)] [(i : ι) → Semiring (A₂ i)] [(i : ι) → TopologicalSpace (A₁ i)]
    [(i : ι) → TopologicalSpace (A₂ i)] [(i : ι) → Algebra R (A₁ i)] [(i : ι) → Algebra R (A₂ i)]
    (e : (i : ι) → A₁ i ≃A[R] A₂ i) (x : (i : ι) → A₁ i) (j : ι) :
    piCongrRight e x j = e j (x j) := rfl

end ContinuousAlgEquiv


namespace Pi


variable {I : Type*}
variable {R : Type*}
variable {f : I → Type*} {a : I → Type*}
variable (R f a)

def mapContinuousAlgHom [CommSemiring R] [(i : I) → Semiring (f i)]
    [(i : I) → Algebra R (f i)] [(i : I) → Semiring (a i)] [(i : I) → Algebra R (a i)]
    [(i : I) → TopologicalSpace (a i)] [(i : I) → TopologicalSpace (f i)]
    (g : (i : I) → a i →A[R] f i) :
    ((i : I) → a i) →A[R] (i : I) → f i where
  __ := Pi.mapAlgHom _ _ _ (fun _ => (g _).toAlgHom)
  cont := continuous_pi fun i => Continuous.comp (g i).cont (continuous_apply _)

end Pi
