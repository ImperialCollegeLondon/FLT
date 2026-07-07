/-
Copyright (c) 2025 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McCarthy
-/
module

public import FLT.Slop.Background.LinearChar.InducedCharacter
public import FLT.Slop.Background.FDRep.Character.Iso
public import FLT.Slop.Background.FDRep.CoindBaseChange

@[expose] public section

/-!
# Descent of induced linear characters through quotients

This file contains compatibility results for induced linear characters under
quotient maps, especially when a linear character is pulled back along a
quotient.
-/

universe u v

variable {k : Type u} [Field k]
variable {G : Type v} [Group G]

namespace FDRep

open BigOperators

open Classical in
/--
Compatibility of one summand with pullback along the quotient map.
-/
private lemma comap_quotient_linearChar_summand_eq
    (K : Subgroup G) [K.Normal]
    (Q : Subgroup (G ⧸ K))
    (ψ_Q : Q →* kˣ)
    (g x : G) :
    let π : G →* G ⧸ K := QuotientGroup.mk' K
    let H : Subgroup G := Q.comap π
    let π_res : H →* Q :=
      (π.comp H.subtype).codRestrict Q (fun h ↦ h.2)
    let ψ_H : H →* kˣ := ψ_Q.comp π_res
    (if hx : π x * π g * (π x)⁻¹ ∈ Q then
        (ψ_Q ⟨π x * π g * (π x)⁻¹, hx⟩ : k)
      else 0)
      =
    (if hx : x * g * x⁻¹ ∈ H then (ψ_H ⟨x * g * x⁻¹, hx⟩ : k)
      else 0) := by
  intro π H π_res ψ_H
  have hiff :
      π x * π g * (π x)⁻¹ ∈ Q ↔ x * g * x⁻¹ ∈ H := by
    dsimp [H]
    rw [Subgroup.mem_comap]
    simp [map_mul, map_inv]
  by_cases hxH : x * g * x⁻¹ ∈ H
  · have hxQ : π x * π g * (π x)⁻¹ ∈ Q := hiff.mpr hxH
    rw [dif_pos hxQ, dif_pos hxH]
    dsimp [ψ_H, π_res]
    simp [map_mul, map_inv]
  · have hxQ : ¬ π x * π g * (π x)⁻¹ ∈ Q := by
      intro hxQ
      exact hxH (hiff.mp hxQ)
    rw [dif_neg hxQ, dif_neg hxH]

open Classical in
/--
The linear-character summand is invariant under the relevant right-coset relation.
-/
private lemma rightRel_conj_linearChar_summand_eq
    {Γ : Type v} [Group Γ]
    (S : Subgroup Γ) (ψ : S →* kˣ) (g : Γ)
    {x y : Γ}
    (hxy : QuotientGroup.rightRel S x y) :
    (if hx : x * g * x⁻¹ ∈ S then
        (ψ ⟨x * g * x⁻¹, hx⟩ : k)
      else 0)
      =
    (if hy : y * g * y⁻¹ ∈ S then
        (ψ ⟨y * g * y⁻¹, hy⟩ : k)
      else 0) := by
  have hxyS : x * y⁻¹ ∈ S := by
    exact (QuotientGroup.rightRel_iff_mul_inv_mem S x y).1 hxy
  let s : S := ⟨x * y⁻¹, hxyS⟩
  have h_conj :
      x * g * x⁻¹ =
        (s : Γ) * (y * g * y⁻¹) * (s : Γ)⁻¹ := by
    dsimp [s]
    group
  have hmem_iff :
      x * g * x⁻¹ ∈ S ↔ y * g * y⁻¹ ∈ S := by
    constructor
    · intro hx
      have hs_inv : (s : Γ)⁻¹ ∈ S := S.inv_mem s.2
      have hs : (s : Γ) ∈ S := s.2
      have htmp :
          (s : Γ)⁻¹ * (x * g * x⁻¹) * (s : Γ) ∈ S :=
        S.mul_mem (S.mul_mem hs_inv hx) hs
      simpa [h_conj, mul_assoc] using htmp
    · intro hy
      rw [h_conj]
      exact S.mul_mem (S.mul_mem s.2 hy) (S.inv_mem s.2)
  by_cases hy : y * g * y⁻¹ ∈ S
  · have hx : x * g * x⁻¹ ∈ S := hmem_iff.mpr hy
    rw [dif_pos hx, dif_pos hy]
    have hsub :
        (⟨x * g * x⁻¹, hx⟩ : S) =
          s * ⟨y * g * y⁻¹, hy⟩ * s⁻¹ := by
      apply Subtype.ext
      simp only [h_conj, Subgroup.coe_mul, InvMemClass.coe_inv]
    rw [hsub]
    simp [map_mul, map_inv, mul_assoc]
  · have hx : ¬ x * g * x⁻¹ ∈ S := by
      intro hx
      exact hy (hmem_iff.mp hx)
    rw [dif_neg hx, dif_neg hy]

/--
Coinduced linear characters commute with pullback along a quotient map. For
`π : G → G ⧸ K`, `Q ≤ G ⧸ K`, and `H = π⁻¹(Q)`, the pullback to `G` of
`coindLin Q ψ_Q` is naturally isomorphic to the coinduced representation
attached to the pulled-back character on `H`.
-/
noncomputable def comap_coindLin_quotient_iso
     {G : Type u} [Group G] [Finite G]
    (K : Subgroup G) [K.Normal]
    (Q : Subgroup (G ⧸ K))
    (ψ_Q : Q →* kˣ) :
    FDRep.comap (FDRep.CoindBaseChange.quotientMap K)
        (FDRep.coindLin Q ψ_Q) ≅
      FDRep.coindLin
        (FDRep.CoindBaseChange.quotientPreimage K Q)
        (ψ_Q.comp (FDRep.CoindBaseChange.quotientPreimageMap K Q)) := by
  change
    FDRep.comap (FDRep.CoindBaseChange.quotientMap K)
        (FDRep.coind Q (FDRep.ofLinearChar ψ_Q)) ≅
      FDRep.coind
        (FDRep.CoindBaseChange.quotientPreimage K Q)
        (FDRep.ofLinearChar
          (ψ_Q.comp (FDRep.CoindBaseChange.quotientPreimageMap K Q)))
  exact
    FDRep.CoindBaseChange.comap_coind_quotient_iso
      K Q (FDRep.ofLinearChar ψ_Q)

open CoindBaseChange in
/--
The character of a coinduced linear character is unchanged by quotient
descent. Equivalently, evaluating the coinduced character on `π g` in `G ⧸ K`
agrees with evaluating the coinduced pulled-back character on `g` in `G`.
-/
lemma char_coindLin_comap_quotient
     {G : Type u} [Group G] [Finite G] [CharZero k]
    (K : Subgroup G) [K.Normal]
    (Q : Subgroup (G ⧸ K)) (ψ_Q : Q →* kˣ) (g : G) :
    let π : G →* G ⧸ K := QuotientGroup.mk' K
    let H : Subgroup G := Q.comap π
    let π_res : H →* Q :=
      (π.comp H.subtype).codRestrict Q (fun x => x.2)
    let ψ_H : H →* kˣ := ψ_Q.comp π_res
    (FDRep.coindLin (k := k) (G := G ⧸ K) Q ψ_Q).character (π g) =
      (FDRep.coindLin (k := k) (G := G) H ψ_H).character g := by
  dsimp
  have hχ :
      ClassFun.character
          (FDRep.comap (quotientMap K)
            (FDRep.coindLin Q ψ_Q))
        =
      ClassFun.character
          (FDRep.coindLin (quotientPreimage K Q)
            (ψ_Q.comp (quotientPreimageMap K Q))) := by
    exact ClassFun.char_eq_of_iso
      (FDRep.comap_coindLin_quotient_iso (k := k) K Q ψ_Q)
  have hχg :=
    congrArg (fun χ : ClassFun k G => χ g) hχ
  change
    (FDRep.comap (quotientMap K)
      (FDRep.coindLin (k := k) (G := G ⧸ K) Q ψ_Q)).character g
      =
    (FDRep.coindLin (k := k) (G := G)
      (quotientPreimage K Q)
      (ψ_Q.comp (quotientPreimageMap K Q))).character g
  exact hχg

/--
A coinduced linear representation descends through a quotient whenever its
linear character factors through that quotient. This is the representation-level
form of quotient descent for induced linear characters.
-/
theorem exists_indLin_of_lift_exists_indLin
     {G : Type u} [Group G] [Finite G] [CharZero k] [IsAlgClosed k]
    (ρ : FDRep k G)
    (K : Subgroup G) [K.Normal]
    (hK : ∀ x ∈ K, ρ.ρ x = 1) :
    (∃ (Q : Subgroup (G ⧸ K)) (ψ : Q →* kˣ),
      Nonempty (FDRep.lift ρ K hK ≅ FDRep.indLin Q ψ)) →
    ∃ (H : Subgroup G) (ψ : H →* kˣ),
      Nonempty (ρ ≅ FDRep.indLin H ψ) := by
  rintro ⟨Q, ψQ, ⟨eQ⟩⟩
  let π : G →* G ⧸ K := QuotientGroup.mk' K
  let H : Subgroup G := Q.comap π
  let πH : H →* Q :=
    (π.comp H.subtype).codRestrict Q (by
      intro h
      exact h.2)
  let ψH : H →* kˣ := ψQ.comp πH
  refine ⟨H, ψH, ?_⟩
  refine ⟨?_⟩
  apply FDRep.iso_of_char_eq
  ext g
  rw [← FDRep.char_lift (ρ := ρ) (K := K) hK g]
  have hchar :
      (FDRep.lift ρ K hK).character (π g) =
        (FDRep.indLin Q ψQ).character (π g) := by
    simpa using congrFun (FDRep.char_eq_of_iso eQ) (π g)
  rw [hchar]
  rw [FDRep.char_indLin_eq_char_coindLin]
  rw [FDRep.char_indLin_eq_char_coindLin]
  simpa [π, H, πH, ψH] using
    char_coindLin_comap_quotient
      (K := K) (Q := Q) (ψ_Q := ψQ) g

end FDRep
