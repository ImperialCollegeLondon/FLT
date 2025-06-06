/-
Copyright (c) 2025 Matthew Jasper. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Jasper
-/
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.TensorProduct.Pi
import FLT.Mathlib.Algebra.Algebra.Tower
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.RingTheory.FiniteType
/-!

# API for base change of free modules

We (presumably) have all this in mathlib for base change on the other side; this
is all about: if `A` is a free `R`-algebra then `A ⊗[R] B` is a free `B`-algebra.

Note: when we have `open scoped TensorProduct.RightActions` merged, all of this
can be downgraded to `A` being a free `R`-module.

-/

section Basis

open scoped TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra

variable {R : Type*} (A : Type*) {B : Type*} {ι : Type*} [CommSemiring R]
variable [CommSemiring A] [Algebra R A] [Fintype ι]
variable [CommSemiring B] [Algebra R B]

/-- The lift of an `R`-basis of `A` to a `B`-basis of the base change `A ⊗[R] B`. -/

noncomputable
def Basis.rightBaseChange [DecidableEq ι] (b : Basis ι R A) : Basis ι B (A ⊗[R] B) where
  repr :=
    let comm := (Algebra.TensorProduct.comm R B A).extendScalars B |>.toLinearEquiv
    let π : B ⊗[R] A ≃ₗ[B] (ι → B) :=
      (TensorProduct.AlgebraTensorModule.congr
        (LinearEquiv.refl B B)
        b.equivFun).trans
      (TensorProduct.piScalarRight _ _ _ _)
    let finite : (ι →₀ B) ≃ₗ[B] (ι → B) := Finsupp.linearEquivFunOnFinite B B ι
    comm.symm.trans π |>.trans finite.symm

@[simp]
lemma Basis.rightBaseChange_repr [DecidableEq ι] (b : Basis ι R A) (i) (x : B) :
    (b.rightBaseChange A).repr (b i ⊗ₜ x) = Finsupp.single i x := by
  have : ∑ (j : ι), (Pi.single i (1 : R) : ι → R) j • (b j) = b i := by
    conv =>
      lhs
      arg 2
      intro j
      rw [Pi.single_comm, Pi.single_apply_smul]
    simp
  rw [← LinearEquiv.eq_symm_apply]
  simp [rightBaseChange, this]

@[simp]
lemma Basis.rightBaseChange_apply [DecidableEq ι] (b : Basis ι R A) (i) :
    b.rightBaseChange A i = b i ⊗ₜ (1 : B) := by
  rw [apply_eq_iff]
  exact rightBaseChange_repr A b i 1

end Basis

section Finrank

namespace TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra

variable {R : Type*} (A : Type*) {B : Type*} [CommRing R]
  [CommSemiring A] [Algebra R A] [CommRing B] [Algebra R B] [Nontrivial B]

lemma finrank_rightAlgebra [Module.Finite R A] [Module.Free R A] :
    Module.finrank B (A ⊗[R] B) = Module.finrank R A := by
  have : Nontrivial R := RingHom.domain_nontrivial (algebraMap R B)
  let b := Module.Free.chooseBasis R A
  let b' : Basis _ _ (A ⊗[R] B) := Basis.rightBaseChange A b
  rw [Module.finrank_eq_card_basis b, Module.finrank_eq_card_basis b']

end TensorProduct

end Finrank
