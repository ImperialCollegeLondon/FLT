/-
Copyright (c) 2025 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McCarthy
-/
module

public import FLT.Slop.BrauerInduction.Background.FDRep.Induced
public import FLT.Slop.BrauerInduction.Background.FDRep.CoindBasic

@[expose] public section

/-!

# Base change for coinduction along quotient maps

Let `K` be a normal subgroup of `G`, let `π : G → G ⧸ K` be the quotient map,
and let `Q ≤ G ⧸ K`. Writing `H = π⁻¹ Q`, this file proves that pulling back
a coinduced representation along `π` agrees with coinducing the pulled-back
representation from `H` to `G`.

The main result is

* `FDRep.CoindBaseChange.comap_coind_quotient_iso`:
  `comap π (coind Q σ) ≅ coind H (comap (H → Q) σ)`.
-/

universe u v

variable {k : Type u} [Field k]
variable {G : Type u} [Group G]

namespace FDRep

namespace CoindBaseChange

/-- The quotient map `G → G ⧸ K`. -/
abbrev quotientMap (K : Subgroup G) [K.Normal] : G →* G ⧸ K :=
  QuotientGroup.mk' K

/-- The inverse image in `G` of a subgroup of `G ⧸ K`. -/
abbrev quotientPreimage
    (K : Subgroup G) [K.Normal]
    (Q : Subgroup (G ⧸ K)) : Subgroup G :=
  Q.comap (quotientMap K)

/--
The restricted quotient map `π⁻¹(Q) → Q`.
-/
abbrev quotientPreimageMap
    (K : Subgroup G) [K.Normal]
    (Q : Subgroup (G ⧸ K)) :
    quotientPreimage K Q →* Q :=
  ((quotientMap K).comp (quotientPreimage K Q).subtype).codRestrict
    Q
    (fun x => x.2)

noncomputable def comapCoindToCoindComap
    [Finite G]
    (K : Subgroup G) [K.Normal]
    (Q : Subgroup (G ⧸ K))
    (σ : FDRep k Q) :
    (FDRep.comap (quotientMap K) (FDRep.coind Q σ)) →ₗ[k]
      (FDRep.coind (quotientPreimage K Q)
        (FDRep.comap (quotientPreimageMap K Q) σ)) where
  toFun v :=
    { val := fun x => v.val ((quotientMap K) x)
      property := by
        intro h x
        change
          v.val ((quotientMap K) ((h : G) * x))
            =
          σ.ρ ((quotientPreimageMap K Q) h)
            (v.val ((quotientMap K) x))
        exact v.property (quotientPreimageMap K Q h) (quotientMap K x)
  }
  map_add' := by
    intro v w
    apply FDRep.coind_ext_val
      (I := quotientPreimage K Q)
      (σ := FDRep.comap (quotientPreimageMap K Q) σ)
    intro x
    rfl
  map_smul' := by
    intro c v
    apply FDRep.coind_ext_val
      (I := quotientPreimage K Q)
      (σ := FDRep.comap (quotientPreimageMap K Q) σ)
    intro x
    rfl

private lemma coindComap_apply_eq_of_mul_inv_mem_kernel
    [Finite G]
    (K : Subgroup G) [K.Normal]
    (Q : Subgroup (G ⧸ K))
    (σ : FDRep k Q)
    {x y : G}
    (hxy : x * y⁻¹ ∈ K)
    (w :
      (FDRep.coind (quotientPreimage K Q)
        (FDRep.comap (quotientPreimageMap K Q) σ))) :
    w.val x = w.val y := by
  let π : G →* G ⧸ K := quotientMap K
  let H : Subgroup G := quotientPreimage K Q
  let π_res : H →* Q := quotientPreimageMap K Q
  have hπ : π (x * y⁻¹) = 1 := by
    simpa [π, quotientMap] using
      ((QuotientGroup.eq_one_iff (N := K) (x := x * y⁻¹)).mpr hxy)
  let h : H :=
    ⟨x * y⁻¹, by
      change π (x * y⁻¹) ∈ Q
      rw [hπ]
      exact Q.one_mem⟩
  have hw := w.property h y
  change
    w.val ((x * y⁻¹) * y)  = σ.ρ (π_res h) (w.val y)  at hw
  have hxy_mul : (x * y⁻¹) * y = x := by
    group
  have hπ_res : π_res h = 1 := by
    ext
    change π (x * y⁻¹) = 1
    exact hπ
  rw [hxy_mul] at hw
  rw [hπ_res, map_one] at hw
  simpa using hw

private lemma coindComap_apply_eq_of_quotientMap_eq
    [Finite G]
    (K : Subgroup G) [K.Normal]
    (Q : Subgroup (G ⧸ K))
    (σ : FDRep k Q)
    {x y : G}
    (hxy : quotientMap K x = quotientMap K y)
    (w :
      (FDRep.coind (quotientPreimage K Q)
        (FDRep.comap (quotientPreimageMap K Q) σ))) :
    w.val x = w.val y := by
  apply coindComap_apply_eq_of_mul_inv_mem_kernel K Q σ ?_ w
  have hπ : quotientMap K (x * y⁻¹) = 1 := by
    rw [MonoidHom.map_mul, MonoidHom.map_inv, hxy, mul_inv_cancel]
  exact
    ((QuotientGroup.eq_one_iff
      (N := K) (x := x * y⁻¹)).mp
      (by simpa [quotientMap] using hπ))

noncomputable def coindComapToComapCoind
    [Finite G]
    (K : Subgroup G) [K.Normal]
    (Q : Subgroup (G ⧸ K))
    (σ : FDRep k Q) :
    (FDRep.coind (quotientPreimage K Q)
        (FDRep.comap (quotientPreimageMap K Q) σ)) →ₗ[k]
      (FDRep.comap (quotientMap K) (FDRep.coind Q σ)) where
  toFun w :=
    { val := fun q => w.val q.out
      property := by
        intro q h
        let hG : quotientPreimage K Q :=
          ⟨q.1.out, by
            change quotientMap K q.1.out ∈ Q
            have: quotientMap K q.1.out = q.1 := by
              simp [quotientMap]
            rw [this]
            exact q.2⟩
        have hπ_res : quotientPreimageMap K Q hG = q := by
          ext
          change quotientMap K q.1.out = q.1
          simp [quotientMap]
        have hout :
            w.val ((q.1 * h).out) =
              w.val (q.1.out * h.out) := by
          apply coindComap_apply_eq_of_quotientMap_eq K Q σ ?_ w
          calc
            quotientMap K ((q.1 * h).out)
                = q.1 * h := by simp [quotientMap]
            _ = quotientMap K (q.1.out * h.out) := by
                    rw [MonoidHom.map_mul]
                    congr 2
                    · simp [quotientMap]
                    · simp [quotientMap]
        have hw := w.property hG h.out
        change
          w.val (q.1.out * h.out) =
            ((FDRep.comap (quotientPreimageMap K Q) σ).ρ hG)
              (w.val h.out)
          at hw
        have hact :
            ((FDRep.comap (quotientPreimageMap K Q) σ).ρ hG)
                (w.val h.out)
              =
            σ.ρ q (w.val h.out) := by
          change
            σ.ρ (quotientPreimageMap K Q hG) (w.val h.out)
              =
            σ.ρ q (w.val h.out)
          rw [hπ_res]
        -- 1. Force Lean to beta-reduce the (fun q => ...) expressions in the goal
        change w.val ((q.1 * h).out) = σ.ρ q (w.val h.out)
        rw [hout, hw, hact]
}
  map_add' := by
    intro w₁ w₂
    apply FDRep.coind_ext_val Q σ
    intro q
    rfl
  map_smul' := by
    intro c w
    apply FDRep.coind_ext_val Q σ
    intro q
    rfl

noncomputable def comap_coind_quotient_linearEquiv
    [Finite G]
    (K : Subgroup G) [K.Normal]
    (Q : Subgroup (G ⧸ K))
    (σ : FDRep k Q) :
    (FDRep.comap (quotientMap K) (FDRep.coind Q σ)) ≃ₗ[k]
      (FDRep.coind (quotientPreimage K Q)
        (FDRep.comap (quotientPreimageMap K Q) σ)) where
  toFun := comapCoindToCoindComap K Q σ
  invFun := coindComapToComapCoind K Q σ
  left_inv := by
    intro v
    apply FDRep.coind_ext_val Q σ
    intro q
    change v.val (quotientMap K q.out) = v.val q
    exact congrArg v.val <| by simp [quotientMap]
  right_inv := by
    intro w
    apply FDRep.coind_ext_val
      (quotientPreimage K Q)
      (FDRep.comap (quotientPreimageMap K Q) σ)
    intro x
    change w.val ((quotientMap K x).out) = w.val x
    apply coindComap_apply_eq_of_quotientMap_eq K Q σ ?_ w
    simp [quotientMap]
  map_add' := by
    intro v w
    exact map_add (comapCoindToCoindComap K Q σ) v w
  map_smul' := by
    intro c v
    exact map_smul (comapCoindToCoindComap K Q σ) c v

/--
Coinduction commutes with pullback along a quotient map.

Let `π : G → G ⧸ K`, let `Q ≤ G ⧸ K`, and let `H = π⁻¹ Q`.
If `σ` is a representation of `Q`, then the pullback to `G` of
`Coind_Q^{G ⧸ K} σ` is naturally isomorphic to
`Coind_H^G` of the pullback of `σ` to `H`.
-/
noncomputable def comap_coind_quotient_iso
    [Finite G]
    (K : Subgroup G) [K.Normal]
    (Q : Subgroup (G ⧸ K))
    (σ : FDRep k Q) :
    FDRep.comap (quotientMap K) (FDRep.coind Q σ) ≅
      FDRep.coind (quotientPreimage K Q)
        (FDRep.comap (quotientPreimageMap K Q) σ) := by
  refine FDRep.isoOfAsRepIso ?_
  refine Rep.mkIso ?_
  refine Representation.Equiv.mk
    (comap_coind_quotient_linearEquiv K Q σ) ?_
  intro g
  ext v
  rfl

end CoindBaseChange
end FDRep
