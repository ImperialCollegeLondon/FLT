/-
Copyright (c) 2025 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McCarthy
-/
module

public import FLT.Slop.BrauerInduction.Background.FDRep.Induced

@[expose] public section

universe u v

variable {k : Type u} {G : Type u}

namespace FDRep

variable [CommRing k] [IsNoetherianRing k] [Group G]

/--
Evaluation of a coinduced representation at a group element, as a linear map.
-/
noncomputable def coindEval
    [Finite G]
    (I : Subgroup G) (σ : FDRep k I) (x : G) :
    (FDRep.coind I σ) →ₗ[k] σ where
  toFun v := v.val x
  map_add' := by
    intro v w
    rfl
  map_smul' := by
    intro c v
    rfl

@[simp]
lemma coindEval_apply
    [Finite G]
    (I : Subgroup G) (σ : FDRep k I) (x : G)
    (v : (FDRep.coind I σ)) :
    coindEval I σ x v = v.val x :=
  rfl

/--
Two vectors in a coinduced representation are equal if their values agree at every
group element.
-/
@[ext]
lemma coind_ext_val
    [Finite G]
    (I : Subgroup G) (σ : FDRep k I)
    {v w : (FDRep.coind I σ)}
    (h : ∀ x : G, v.val x = w.val x) :
    v = w := by
  apply Subtype.ext
  ext x
  exact h x

/--
Two vectors in a coinduced representation are equal if they agree at every
group element.
-/
lemma coind_ext
    [Finite G]
    (I : Subgroup G) (σ : FDRep k I)
    {v w : (FDRep.coind I σ)}
    (h : ∀ x : G, coindEval I σ x v = coindEval I σ x w) :
    v = w := by
  apply coind_ext_val I σ
  intro x
  exact h x

end FDRep
