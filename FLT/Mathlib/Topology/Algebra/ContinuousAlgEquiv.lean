/-
Copyright (c) 2024 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
module

public import Mathlib.Topology.Algebra.Algebra.Equiv
public import Mathlib.Topology.Algebra.Algebra
public import Mathlib.Topology.Algebra.Module.Equiv
public import FLT.Mathlib.Algebra.Algebra.Tower

/-!
# Topological (sub)algebras

This file contains an API for `ContinuousAlgEquiv`.
-/

@[expose] public section

open scoped Topology


namespace ContinuousAlgEquiv

variable {R A B C : Type*}
  [CommSemiring R] [Semiring A] [TopologicalSpace A] [Semiring B]
  [TopologicalSpace B] [Semiring C] [TopologicalSpace C] [Algebra R A] [Algebra R B]
  [Algebra R C]

/--
Produces an `S'`-linear continuous algebra isomorphism from a continuous algebra
isomorphism `f : A ≃A[S] B` which also has scalars `S'`.
-/
def changeScalars {A B : Type*} (S' : Type*) {S : Type*}
    [CommSemiring A] [CommSemiring B] [CommSemiring S'] [CommSemiring S] [Algebra S A]
    [Algebra S B] [Algebra S' A] [Algebra S' B] [TopologicalSpace A] [TopologicalSpace B]
    (f : A ≃A[S] B) [IsBiscalar S S' f.toAlgHom] :
    A ≃A[S'] B where
  __ := f.toAlgEquiv.changeScalars S'
  continuous_toFun := f.continuous
  continuous_invFun := f.continuous_invFun

end ContinuousAlgEquiv
