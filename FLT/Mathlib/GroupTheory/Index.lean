/-
Copyright (c) 2024 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Kevin Buzzard
-/
module

public meta import Mathlib.Tactic.ToDual
public import Mathlib.GroupTheory.Index

import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.ScopedNS
import Mathlib.Tactic.SetLike

/-!
# TODO

* Rename `relindex` to `relIndex`
* Rename `FiniteIndex.finiteIndex` to `FiniteIndex.index_ne_zero`
-/

@[expose] public section

open Function
open scoped Pointwise

-- This is cool notation. Should mathlib have it? And what should the `relindex` version be?
/-- Notation `[G : H]` for the (additive) index of a subgroup `H ≤ G`. -/
scoped[GroupTheory] notation "[" G ":" H "]" => @AddSubgroup.index G _ H

theorem Subgroup.index_op {G : Type*} [Group G] (H : Subgroup G) :
    H.op.index = H.index := by
  trans (H.comap (MulEquiv.inv' G).symm.toMonoidHom).index
  · congr 1
    ext; simp
  · exact Subgroup.index_comap_of_surjective _ (MulEquiv.inv' G).symm.surjective

instance {G : Type*} [Group G] (H : Subgroup G) [H.FiniteIndex] :
    H.op.FiniteIndex := ⟨by rw [Subgroup.index_op]; exact Subgroup.FiniteIndex.index_ne_zero⟩
