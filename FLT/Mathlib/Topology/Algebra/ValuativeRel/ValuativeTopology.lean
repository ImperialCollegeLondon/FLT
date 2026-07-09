/-
Copyright (c) 2026 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, William Coram
-/
module

public import Mathlib.Topology.Algebra.LinearTopology
public import Mathlib.Topology.Algebra.ValuativeRel.ValuativeTopology
public import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-!
# Valuative topologies

Material destined for Mathlib.
-/

@[expose] public section

open ValuativeRel

section Ring

variable (R : Type*) [Ring R] [ValuativeRel R] [TopologicalSpace R] [IsValuativeTopology R]

/-- A ring with a valuative topology is nonarchimedean. Mathlib proves this for the
valuation-induced topology (`ValuativeRel.nonarchimedeanRing`, a local instance there) and
registers the weaker transported instance `IsValuativeTopology.isTopologicalRing`, but not this
nonarchimedean strengthening; transport it along `Valuation.toTopologicalSpace_eq` in the same
way. -/
instance (priority := low) IsValuativeTopology.nonarchimedeanRing : NonarchimedeanRing R := by
  convert! ValuativeRel.nonarchimedeanRing R
  exact Valuation.toTopologicalSpace_eq _

end Ring

variable {K : Type*} [DivisionRing K] [ValuativeRel K] [TopologicalSpace K]
  [IsValuativeTopology K]

/-- A division ring with a valuative topology is Hausdorff: `{y : |y| < |x|}` is a
neighbourhood of `0` not containing `x`. (Mathlib has this for `Valued` fields,
`ValuedRing.separated`, but not for `IsValuativeTopology`.) -/
instance : T2Space K := by
  apply IsTopologicalAddGroup.t2Space_of_zero_sep
  intro x hx
  refine ⟨{y | valuation K y < valuation K x}, ?_,
    fun h ↦ lt_irrefl _ (show valuation K x < valuation K x from h)⟩
  rw [IsValuativeTopology.mem_nhds_zero_iff]
  exact ⟨Units.mk0 (valuation K x) ((valuation K).ne_zero_iff.mpr hx), fun y hy ↦ hy⟩

/-- The open ball `{x ∈ 𝒪[K] | v(x) < γ}` of the ring of integers is an ideal:
ultrametrically it is closed under addition, and multiplying by an integral element only
shrinks the valuation. -/
def ValuativeRel.integerBallIdeal (γ : (ValueGroupWithZero K)ˣ) :
    Ideal (valuation K).integer where
  carrier := {x | valuation K (x : K) < γ}
  add_mem' {a b} ha hb := by
    simpa using (valuation K).map_add_lt ha hb
  zero_mem' := by
    simp
  smul_mem' r x hx :=
    calc valuation K ((r • x : (valuation K).integer) : K)
        = valuation K (r : K) * valuation K (x : K) := by
          rw [show ((r • x : (valuation K).integer) : K) = (r : K) * (x : K) from rfl, map_mul]
      _ ≤ 1 * valuation K (x : K) := mul_le_mul_left r.2 _
      _ = valuation K (x : K) := one_mul _
      _ < γ := hx

/-- The ring of integers of a valuative topology is linearly topologized: the open balls
`integerBallIdeal` are ideals and form a basis of neighbourhoods of `0`. This is the
hypothesis under which mathlib's topological power-series evaluation
(`PowerSeries.eval₂Hom`) applies to `𝒪[K]` — it can never apply to the field `K` itself,
which has no nontrivial ideals. -/
instance : IsLinearTopology (valuation K).integer (valuation K).integer := by
  refine IsLinearTopology.mk_of_hasBasis _
    (s := ValuativeRel.integerBallIdeal (K := K)) (p := fun _ ↦ True) ?_
  have h := (IsValuativeTopology.hasBasis_nhds (0 : K)).comap
    (Subtype.val : (valuation K).integer → K)
  rw [← nhds_subtype_eq_comap] at h
  refine h.congr (fun _ ↦ Iff.rfl) fun γ _ ↦ ?_
  ext x
  simp [ValuativeRel.integerBallIdeal]

variable {R : Type*} [Ring R] [ValuativeRel R] [TopologicalSpace R] [IsValuativeTopology R]

/-
Relationship to mathlib's `Valuation.isClosed_closedBall`.

Mathlib's `Valuation.isClosed_closedBall` is stated for an *arbitrary* compatible valuation
`v : Valuation R Γ₀` `[v.Compatible]`, as `IsClosed {x | v.restrict x ≤ r}` with `r` in the
abstract value group `(MonoidWithZeroHom.ofClass v).ValueGroup₀`. (The name
`IsValuativeTopology.isClosed_closedBall` is only a deprecated alias of it.)

`ValuativeRel.isClosed_closedBall` below is that lemma specialized to the *canonical* valuation
`valuation R`, whose value group is the concrete `ValueGroupWithZero R`. Feeding
`v := valuation R` into the mathlib lemma leaves `(valuation R).restrict x ≤ r'` with `r'` in the
abstract value group, not the clean `valuation R x ≤ r`; bridging the two needs the two rewrites
`Valuation.restrict_le_iff_le_embedding` and
`ValueGroupWithZero.embedding_orderMonoidIso_valuation_eq`. We package that bridge once here so
downstream canonical-valuation code gets the ergonomic form.
-/

/-- The closed ball `{x | v x ≤ r}` of the canonical valuation, bundled as an additive subgroup
of `R`: ultrametrically it is closed under subtraction. Unlike `ValuativeRel.integerBallIdeal`
it is **not** in general an ideal of `R` — the closed ball absorbs multiplication only by
integral elements, and over a field the only ideals are `⊥` and `⊤`. (Mathlib bundles the
general compatible-valuation version as `Valuation.leAddSubgroup`.) -/
def ValuativeRel.closedBall (r : ValueGroupWithZero R) : AddSubgroup R where
  carrier := {x | valuation R x ≤ r}
  add_mem' {a b} ha hb := le_trans ((valuation R).map_add a b) (max_le ha hb)
  zero_mem' := by simp
  neg_mem' {a} ha := by simpa using ha

omit [TopologicalSpace R] [IsValuativeTopology R] in
@[simp]
theorem ValuativeRel.mem_closedBall {r : ValueGroupWithZero R} {x : R} :
    x ∈ closedBall r ↔ valuation R x ≤ r := Iff.rfl

/-- The closed ball `{x | v x ≤ r}` of the canonical valuation on a ring with a valuative
topology is closed. (Mathlib's `Valuation.isClosed_closedBall` states this for `v.restrict`
of a compatible valuation `v`; this is the version for `ValuativeRel.valuation` itself.) -/
theorem ValuativeRel.isClosed_closedBall (r : ValueGroupWithZero R) :
    IsClosed (closedBall r : Set R) := by
  change IsClosed {x | valuation R x ≤ r}
  simpa only [Valuation.restrict_le_iff_le_embedding,
    ValueGroupWithZero.embedding_orderMonoidIso_valuation_eq] using
    Valuation.isClosed_closedBall (ValueGroupWithZero.orderMonoidIso (valuation R) r)

/-- The valuation of a convergent sum is at most any uniform bound on its terms: the `tsum`
analogue of the finite-sum bound `Valuation.map_sum_le`. -/
theorem ValuativeRel.valuation_tsum_le {ι : Type*} {f : ι → R} {B : ValueGroupWithZero R}
    (hf : Summable f) (hB : ∀ i, valuation R (f i) ≤ B) : valuation R (∑' i, f i) ≤ B :=
  (isClosed_closedBall B).mem_of_tendsto hf.hasSum <|
    .of_forall fun _ ↦ (valuation R).map_sum_le fun i _ ↦ hB i
