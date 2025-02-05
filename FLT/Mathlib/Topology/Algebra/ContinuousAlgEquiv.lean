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

@[simps!]
def restrictScalars (A : Type*) {B : Type*} {C D : Type*}
    [CommSemiring A] [CommSemiring C] [CommSemiring D] [TopologicalSpace C]
    [TopologicalSpace D] [CommSemiring B]  [Algebra B C] [Algebra B D] [Algebra A B]
    [Algebra A C] [Algebra A D] [IsScalarTower A B C] [IsScalarTower A B D] (f : C ≃A[B] D) :
    C ≃A[A] D where
  __ := f.toAlgEquiv.restrictScalars A
  continuous_toFun := f.continuous_toFun
  continuous_invFun := f.continuous_invFun

@[simp]
theorem restrictScalars_apply (A : Type*) {B : Type*} {C D : Type*}
    [CommSemiring A] [CommSemiring C] [CommSemiring D] [TopologicalSpace C]
    [TopologicalSpace D] [CommSemiring B]  [Algebra B C] [Algebra B D] [Algebra A B]
    [Algebra A C] [Algebra A D] [IsScalarTower A B C] [IsScalarTower A B D] (f : C ≃A[B] D)
    (x : C) :
    f.restrictScalars A x = f x :=
  rfl

@[simp]
theorem coe_restrictScalars_apply (A : Type*) {B : Type*} {C D : Type*}
    [CommSemiring A] [CommSemiring C] [CommSemiring D] [TopologicalSpace C]
    [TopologicalSpace D] [CommSemiring B]  [Algebra B C] [Algebra B D] [Algebra A B]
    [Algebra A C] [Algebra A D] [IsScalarTower A B C] [IsScalarTower A B D] (f : C ≃A[B] D) (c : C) :
    (f.restrictScalars A).toContinuousLinearEquiv c = f.toContinuousLinearEquiv.restrictScalars A c :=
  rfl

@[simp]
theorem coe_restrictScalars (A : Type*) {B : Type*} {C D : Type*}
    [CommSemiring A] [CommSemiring C] [CommSemiring D] [TopologicalSpace C]
    [TopologicalSpace D] [CommSemiring B]  [Algebra B C] [Algebra B D] [Algebra A B]
    [Algebra A C] [Algebra A D] [IsScalarTower A B C] [IsScalarTower A B D] (f : C ≃A[B] D) :
    (f.restrictScalars A).toContinuousLinearEquiv = f.toContinuousLinearEquiv.restrictScalars A :=
  rfl

end ContinuousAlgEquiv
