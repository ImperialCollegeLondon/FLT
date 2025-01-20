import Mathlib.GroupTheory.Complement
import Mathlib.MeasureTheory.Group.Action
import Mathlib.MeasureTheory.Group.Pointwise
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import FLT.Mathlib.Algebra.Group.Subgroup.Defs
import FLT.Mathlib.GroupTheory.Index

/-!
# TODO

* Make `α` implicit in `SMulInvariantMeasure`
* Rename `SMulInvariantMeasure` to `Measure.IsSMulInvariant`
-/

open Subgroup Set
open scoped Pointwise

namespace MeasureTheory
variable {G α : Type*} [Group G] [MeasurableSpace G] [MeasurableSpace α]
  {H K : Subgroup G}

@[to_additive]
instance [MeasurableMul₂ G] : MeasurableMul₂ H where measurable_mul := by measurability

@[to_additive]
instance [MeasurableInv G] : MeasurableInv H where measurable_inv := sorry

variable [MeasurableMul G]

@[to_additive]
instance : MeasurableMul H where
  measurable_mul_const c := by measurability
  measurable_const_mul c := sorry -- https://github.com/ImperialCollegeLondon/FLT/issues/276

@[to_additive]
instance (μ : Measure G) [μ.IsMulLeftInvariant] :
    (μ.comap Subtype.val : Measure H).IsMulLeftInvariant where
  map_mul_left_eq_self g := sorry -- https://github.com/ImperialCollegeLondon/FLT/issues/276

@[to_additive]
instance (μ : Measure G) [μ.IsMulRightInvariant] :
    (μ.comap Subtype.val : Measure H).IsMulRightInvariant where
  map_mul_right_eq_self g := sorry -- https://github.com/ImperialCollegeLondon/FLT/issues/276

@[to_additive index_mul_addHaar_addSubgroup]
lemma index_mul_haar_subgroup [H.FiniteIndex] (hH : MeasurableSet (H : Set G)) (μ : Measure G)
    [μ.IsMulLeftInvariant] : H.index * μ H = μ univ := by
  obtain ⟨s, hs, -⟩ := H.exists_isComplement_left 1
  have hs' : Finite s := hs.finite_left_iff.mpr inferInstance
  calc
    H.index * μ H = ∑' a : s, μ (a.val • H) := by
      simp [measure_smul]
      rw [← Set.Finite.cast_ncard_eq hs', ← Nat.card_coe_set_eq, hs.card_left]
      norm_cast
    _ = μ univ := by
      rw [← measure_iUnion _ fun _ ↦ hH.const_smul _]
      · simp [hs.mul_eq]
      · exact fun a b hab ↦ hs.pairwiseDisjoint_smul a.2 b.2 (Subtype.val_injective.ne hab)

@[to_additive index_mul_addHaar_addSubgroup_eq_addHaar_addSubgroup]
lemma index_mul_haar_subgroup_eq_haar_subgroup [H.FiniteRelIndex K] (hHK : H ≤ K)
    (hH : MeasurableSet (H : Set G)) (hK : MeasurableSet (K : Set G)) (μ : Measure G)
    [μ.IsMulLeftInvariant] : H.relindex K * μ H = μ K := by
  have := index_mul_haar_subgroup (H := H.subgroupOf K) (measurable_subtype_coe hH)
    (μ.comap Subtype.val)
  simp at this
  rw [MeasurableEmbedding.comap_apply, MeasurableEmbedding.comap_apply] at this
  simp at this
  unfold subgroupOf at this
  rwa [coe_comap, coe_subtype, Set.image_preimage_eq_of_subset (by simpa)] at this
  exact .subtype_coe hK
  exact .subtype_coe hK

end MeasureTheory
