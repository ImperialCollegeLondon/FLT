import Mathlib.GroupTheory.Index
import Mathlib.Algebra.GroupWithZero.Subgroup

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

@[to_additive]
lemma index_map_of_bijective (S : Subgroup G) (hf : Bijective f) : (S.map f).index = S.index :=
  index_map_eq _ hf.2 (by rw [f.ker_eq_bot_iff.2 hf.1]; exact bot_le)

end Subgroup

namespace AddSubgroup
variable {G A : Type*} [Group G] [AddGroup A] [DistribMulAction G A]

-- TODO: Why does making this lemma simp make `NumberTheory.Padic.PadicIntegers` time out?
lemma index_smul (a : G) (S : AddSubgroup A) : (a • S).index = S.index :=
  index_map_of_bijective _ (MulAction.bijective _)

end AddSubgroup
