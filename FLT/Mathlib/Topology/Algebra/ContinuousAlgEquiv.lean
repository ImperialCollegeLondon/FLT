/-
Copyright (c) 2024 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
import Mathlib.Topology.Algebra.Algebra.Equiv
import Mathlib.Topology.Algebra.Algebra
import Mathlib.Topology.Algebra.Module.Equiv

/-!
# Topological (sub)algebras

This file contains an API for `ContinuousAlgEquiv`.
-/

open scoped Topology


namespace ContinuousAlgEquiv

variable {R A B C : Type*}
  [CommSemiring R] [Semiring A] [TopologicalSpace A] [Semiring B]
  [TopologicalSpace B] [Semiring C] [TopologicalSpace C] [Algebra R A] [Algebra R B]
  [Algebra R C]

@[coe]
def toContinuousLinearEquiv (e : A ≃A[R] B) : A ≃L[R] B where
  __ := e.toLinearEquiv
  continuous_toFun := e.continuous_toFun
  continuous_invFun := e.continuous_invFun

theorem toContinuousLinearEquiv_apply (e : A ≃A[R] B) (a : A) :
  e.toContinuousLinearEquiv a = e a := rfl

end ContinuousAlgEquiv
