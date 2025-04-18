import Mathlib.GroupTheory.Index

/-!
# TODO

* Rename `relindex` to `relIndex`
* Rename `FiniteIndex.finiteIndex` to `FiniteIndex.index_ne_zero`
-/

open Function
open scoped Pointwise

-- This is cool notation. Should mathlib have it? And what should the `relindex` version be?
scoped[GroupTheory] notation "[" G ":" H "]" => @AddSubgroup.index G _ H

namespace Subgroup
variable {G G' : Type*} [Group G] [Group G'] {f : G →* G'} {H K : Subgroup G}

class _root_.AddSubgroup.FiniteRelIndex {G : Type*} [AddGroup G] (H K : AddSubgroup G) : Prop where
  protected relIndex_ne_zero : H.relindex K ≠ 0

@[to_additive] class FiniteRelIndex (H K : Subgroup G) : Prop where
  protected relIndex_ne_zero : H.relindex K ≠ 0

@[to_additive]
lemma relIndex_ne_zero [H.FiniteRelIndex K] : H.relindex K ≠ 0 := FiniteRelIndex.relIndex_ne_zero

@[to_additive]
instance FiniteRelIndex.to_finiteIndex_subgroupOf [H.FiniteRelIndex K] :
    (H.subgroupOf K).FiniteIndex where
  index_ne_zero := relIndex_ne_zero

end Subgroup
