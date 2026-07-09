/-
Copyright (c) 2026 Y. Samanda Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Y. Samanda Zhang
-/
module

public import Mathlib

/-!
# Topological modules with a group action as `Action (TopModuleCat R) G`

`TopModuleCat.actionOf` packages a topological `R`-module `M` equipped with an `R`-linear
`G`-action that is continuous in the module variable as an object of
`Action (TopModuleCat R) G`, with `g` acting by `m ↦ g • m`.
-/

@[expose] public section

open CategoryTheory

namespace TopModuleCat

variable (G : Type*) (R : Type*) (M : Type*)
  [Monoid G] [CommRing R] [TopologicalSpace R]
  [AddCommGroup M] [Module R M] [TopologicalSpace M]
  [IsTopologicalAddGroup M] [ContinuousSMul R M]
  [DistribMulAction G M] [SMulCommClass G R M] [ContinuousConstSMul G M]

/-- A topological `R`-module `M` with a continuous (in the module variable) linear `G`-action,
as an object of `Action (TopModuleCat R) G`. The action of `g` is `m ↦ g • m`. -/
abbrev actionOf : Action (TopModuleCat R) G where
  V := .of R M
  ρ :=
  { toFun g := TopModuleCat.ofHom ⟨DistribSMul.toLinearMap R M g, continuous_const_smul g⟩
    map_one' := ConcreteCategory.ext (by ext m; exact one_smul G m)
    map_mul' g₁ g₂ := ConcreteCategory.ext (by ext m; exact mul_smul g₁ g₂ m) }

end TopModuleCat
