/-
Copyright (c) 2026 Mathias Stout. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mathias Stout
-/
module

public import Mathlib.GroupTheory.Index
public import Mathlib.RepresentationTheory.Induced
public import Mathlib.RepresentationTheory.Intertwining
import FLT.Slop.RepresentationTheory.Mackey

/-!
# Restriction of an induced representation to an index-two subgroup

This file contains the non-slop statement of the index-two case of Mackey's
restriction–induction formula, together with the definitions needed to state it: for
subgroups `K J : Subgroup G` with `K.index = 2` and `J ≰ K`, and a representation
`τ : Representation k K V`,

`Res_J Ind_K^G τ ≅ Ind_{K ⊓ J}^J (Res_{K ⊓ J} τ)`

as `J`-representations. The proof lives in the AI-generated development
`FLT.Slop.RepresentationTheory.MackeyClean`, which is imported non-publicly.
-/

@[expose] public section

open Representation

namespace MackeyFormula

variable {k G : Type*} [CommRing k] [Group G]
    {V : Type*} [AddCommGroup V] [Module k V]

/-- The restriction to `J` of the induced representation: `Res_J (Ind_K^G τ)`, the
`J`-action on mathlib's induced module `IndV K.subtype τ`. -/
noncomputable def resInd (K J : Subgroup G) (τ : Representation k K V) :
    Representation k J (IndV K.subtype τ) :=
  (ind K.subtype τ).comp J.subtype

/-- **Mackey's formula for an index-two subgroup**: if `K` has index `2` and `J ≰ K`,
then the restriction to `J` of the representation of `G` induced from
`τ : Representation k K V` decomposes with a single summand:
`Res_J Ind_K^G τ ≅ Ind_{K ⊓ J}^J (Res_{K ⊓ J} τ)` as `J`-representations. -/
theorem index_two {K J : Subgroup G} (hK : K.index = 2) (hJ : ¬ J ≤ K)
    (τ : Representation k K V) :
    Nonempty (Representation.Equiv (resInd K J τ)
      (ind (Subgroup.inclusion (inf_le_right : K ⊓ J ≤ J))
        (τ.comp (Subgroup.inclusion (inf_le_left : K ⊓ J ≤ K))))) :=
  Mackey.index_two hK hJ τ

end MackeyFormula
