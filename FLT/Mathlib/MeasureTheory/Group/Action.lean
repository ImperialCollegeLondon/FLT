import Mathlib.MeasureTheory.Group.Action
import Mathlib.MeasureTheory.Group.Pointwise
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import FLT.Mathlib.GroupTheory.Complement
import FLT.Mathlib.Data.Set.Card -- shake says remove this but it breaks a simp call
/-!
# TODO

* Make `α` implicit in `SMulInvariantMeasure`
* Rename `SMulInvariantMeasure` to `Measure.IsSMulInvariant`
-/

section MeasurableEmbeddingComap

open MeasureTheory Measure

@[to_additive]
lemma _root_.MeasurableEmbedding.IsMulLeftInvariant_comap {G H : Type*}
    [Group G] [MeasurableSpace G] [MeasurableMul G]
    [Group H] [MeasurableSpace H] [MeasurableMul H]
    {φ : G →* H} (hφ : MeasurableEmbedding φ) (μ : Measure H) [IsMulLeftInvariant μ] :
    IsMulLeftInvariant (comap φ μ) where
  map_mul_left_eq_self g := by
    ext s hs
    rw [map_apply (by fun_prop) hs]
    repeat rw [MeasurableEmbedding.comap_apply hφ]
    have : φ '' ((fun x ↦ g * x) ⁻¹' s) = (fun x ↦ φ g * x) ⁻¹' (φ '' s) := by
      ext
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨g * y, hy, by simp⟩
      · intro ⟨y, yins, hy⟩
        exact ⟨g⁻¹ * y, by simp [yins], by simp [hy]⟩
    rw [this, ← map_apply (by fun_prop), IsMulLeftInvariant.map_mul_left_eq_self]
    exact hφ.measurableSet_image.mpr hs

@[to_additive]
lemma _root_.MeasurableEmbedding.isMulRightInvariant_comap {G H : Type*}
    [Group G] [MeasurableSpace G] [MeasurableMul G]
    [Group H] [MeasurableSpace H] [MeasurableMul H]
    {φ : G →* H} (hφ : MeasurableEmbedding φ) (μ : Measure H) [IsMulRightInvariant μ] :
    IsMulRightInvariant (comap φ μ) where
  map_mul_right_eq_self g := by
    ext s hs
    rw [map_apply (by fun_prop) hs]
    repeat rw [MeasurableEmbedding.comap_apply hφ]
    have : φ '' ((fun x ↦ x * g) ⁻¹' s) = (fun x ↦ x * φ g) ⁻¹' (φ '' s) := by
      ext
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨y * g, hy, by simp⟩
      · intro ⟨y, yins, hy⟩
        exact ⟨y * g⁻¹, by simp [yins], by simp [hy]⟩
    rw [this, ← map_apply (by fun_prop), IsMulRightInvariant.map_mul_right_eq_self]
    exact hφ.measurableSet_image.mpr hs

end MeasurableEmbeddingComap

open Subgroup Set
open scoped Pointwise

namespace MeasureTheory
variable {G α : Type*} [Group G] [MeasurableSpace G] [MeasurableSpace α]
  {H K : Subgroup G}

@[to_additive]
instance [MeasurableMul₂ G] : MeasurableMul₂ H where measurable_mul := by measurability

@[to_additive]
instance [MeasurableInv G] : MeasurableInv H where
  measurable_inv := Measurable.subtype_mk (by measurability)

variable [MeasurableMul G]

@[to_additive]
instance : MeasurableMul H where
  measurable_mul_const c := by measurability
  measurable_const_mul c := Measurable.subtype_mk (by measurability)

@[to_additive]
lemma isMulLeftInvariant_subtype_coe (μ : Measure G) [μ.IsMulLeftInvariant]
  (hH : MeasurableSet (H : Set G)) : (μ.comap Subtype.val : Measure H).IsMulLeftInvariant :=
  have hφ : MeasurableEmbedding H.subtype := MeasurableEmbedding.subtype_coe hH
  hφ.IsMulLeftInvariant_comap μ

@[to_additive]
lemma isMulRightInvariant_subtype_coe (μ : Measure G) [μ.IsMulRightInvariant]
    (hH : MeasurableSet (H : Set G)) : (μ.comap Subtype.val : Measure H).IsMulRightInvariant :=
  have hφ : MeasurableEmbedding H.subtype := MeasurableEmbedding.subtype_coe hH
  MeasurableEmbedding.IsMulRightInvariant_comap hφ μ

@[to_additive index_mul_addHaar_addSubgroup]
lemma index_mul_haar_subgroup [H.FiniteIndex] (hH : MeasurableSet (H : Set G)) (μ : Measure G)
    [μ.IsMulLeftInvariant] : H.index * μ H = μ univ := by
  obtain ⟨s, hs, -⟩ := H.exists_isComplement_left 1
  have hs' : Finite s := hs.finite_left_iff.mpr inferInstance
  calc
    H.index * μ H = ∑' a : s, μ (a.val • H) := by simp [measure_smul, hs.encard_left]
    _ = μ univ := by
      rw [← measure_iUnion _ fun _ ↦ hH.const_smul _]
      · simp [hs.mul_eq]
      · exact fun a b hab ↦ hs.pairwiseDisjoint_smul a.2 b.2 (Subtype.val_injective.ne hab)

@[to_additive index_mul_addHaar_addSubgroup_eq_addHaar_addSubgroup]
lemma index_mul_haar_subgroup_eq_haar_subgroup [H.IsFiniteRelIndex K] (hHK : H ≤ K)
    (hH : MeasurableSet (H : Set G)) (hK : MeasurableSet (K : Set G)) (μ : Measure G)
    [μ.IsMulLeftInvariant] : H.relindex K * μ H = μ K := by
  have := isMulLeftInvariant_subtype_coe μ hK
  have := index_mul_haar_subgroup (H := H.subgroupOf K) (measurable_subtype_coe hH)
    (μ.comap Subtype.val)
  simp only at this
  rw [MeasurableEmbedding.comap_apply, MeasurableEmbedding.comap_apply] at this
  · simp only [image_univ, Subtype.range_coe_subtype, SetLike.setOf_mem_eq] at this
    unfold subgroupOf at this
    rwa [coe_comap, coe_subtype, Set.image_preimage_eq_of_subset (by simpa)] at this
  · exact .subtype_coe hK
  · exact .subtype_coe hK

end MeasureTheory
