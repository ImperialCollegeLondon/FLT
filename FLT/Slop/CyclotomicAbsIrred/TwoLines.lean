/-
Copyright (c) 2026 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/
module

public import FLT.Slop.CyclotomicAbsIrred.CliffordTheory
public import FLT.Slop.RepresentationTheory.OddAbsIrredSlop
public import Mathlib.GroupTheory.Index
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# The stabilizer of a line, and the determinant of a line-swapping operator

Let `ρ : Representation k G V` be a representation on a two-dimensional space `V` which
restricted to a normal subgroup `H` splits as two distinct characters `χ ≠ η` on complementary
lines `L` and `M` (the situation produced by the Clifford dichotomy of
`FLT.Slop.CyclotomicAbsIrred.CliffordTheory` when `ρ|H` is reducible).  This file develops
Steps 2–5 of the proof of the main theorem of `FLT.Slop.CyclotomicAbsIrred.Main`:

* `lineStabilizer ρ L` : the subgroup of `g : G` with `ρ g L = L`;
* `lineCharacter` : the character by which the line stabilizer acts on `L`;
* `map_line_eq_of_notMem` : every `g` outside the stabilizer *swaps* the two lines;
* `index_lineStabilizer_eq_two` : the stabilizer has index two (Step 3);
* `det_eq_neg_lineScalar_sq` : for `τ` outside the stabilizer (with `τ² ` inside, as it must
  be for an index-two subgroup), `det ρ(τ) = -ψ(τ²)` where `ψ` is the line character (Step 5).
-/

@[expose] public section

open Module

namespace CyclotomicAbsIrred

open Representation

variable {k G V : Type*} [Field k] [Group G] [AddCommGroup V] [Module k V]

variable (ρ : Representation k G V)

/-- The stabilizer of a submodule `L` under a representation `ρ`: the subgroup of those `g`
with `ρ g L = L`. -/
def lineStabilizer (L : Submodule k V) : Subgroup G where
  carrier := {g | Submodule.map (ρ g) L = L}
  one_mem' := by simp [Module.End.one_eq_id]
  mul_mem' {a b} ha hb := by
    have : ρ (a * b) = (ρ a) ∘ₗ (ρ b) := by rw [map_mul]; rfl
    simp only [Set.mem_setOf_eq, this, Submodule.map_comp] at *
    rw [hb, ha]
  inv_mem' {a} ha := by
    simp only [Set.mem_setOf_eq] at *
    conv_lhs => rw [← ha]
    rw [← Submodule.map_comp, ← show ρ (a⁻¹ * a) = (ρ a⁻¹) ∘ₗ (ρ a) from by rw [map_mul]; rfl]
    simp [Module.End.one_eq_id]

variable {ρ}

lemma mem_lineStabilizer {L : Submodule k V} {g : G} :
    g ∈ lineStabilizer ρ L ↔ Submodule.map (ρ g) L = L := Iff.rfl

lemma apply_mem_of_mem_lineStabilizer {L : Submodule k V} {g : G}
    (hg : g ∈ lineStabilizer ρ L) {v : V} (hv : v ∈ L) : ρ g v ∈ L := by
  rw [mem_lineStabilizer] at hg
  rw [← hg]
  exact Submodule.mem_map_of_mem hv

/-- A subgroup acting on a line `L` by a character stabilizes `L`. -/
lemma le_lineStabilizer_of_actsByCharacterOn [FiniteDimensional k V] {H : Subgroup G}
    {L : Submodule k V} {χ : H →* kˣ} (hχL : ActsByCharacterOn H ρ L χ) :
    H ≤ lineStabilizer ρ L := by
  intro h hh
  rw [mem_lineStabilizer]
  apply Submodule.eq_of_le_of_finrank_le
  · rintro x ⟨v, hv, rfl⟩
    rw [hχL ⟨h, hh⟩ hv]
    exact L.smul_mem _ hv
  · rw [finrank_map_apply_eq]

/-- If `ρ` is irreducible and `L` is a line in a two-dimensional space, the stabilizer of `L`
is a proper subgroup. -/
lemma lineStabilizer_ne_top (hρ : ρ.IsIrreducible)
    {L : Submodule k V} (hL : finrank k L = 1) (hV : finrank k V = 2) :
    lineStabilizer ρ L ≠ ⊤ := by
  intro htop
  obtain ⟨-, hforall⟩ := (Slop.OddRep.isIrreducible_iff_forall ρ).mp hρ
  have hstable : ∀ g : G, ∀ v ∈ L, ρ g v ∈ L := by
    intro g v hv
    exact apply_mem_of_mem_lineStabilizer (htop ▸ Subgroup.mem_top g) hv
  rcases hforall L hstable with h | h
  · rw [h, finrank_bot] at hL
    omega
  · rw [h, finrank_top, hV] at hL
    omega

section Splitting

variable {H : Subgroup G} [H.Normal] {χ η : H →* kˣ} {L M : Submodule k V}

/-- In the two-distinct-characters situation, the two lines are distinct. -/
lemma line_ne_line (hL : finrank k L = 1) (hLM : IsCompl L M) : L ≠ M := by
  intro h
  have : L = ⊥ := by
    rw [← le_bot_iff, ← hLM.inf_eq_bot]
    exact le_inf le_rfl h.le
  rw [this, finrank_bot] at hL
  omega

/-- Any `g` outside the stabilizer of `L` swaps the two lines of the splitting. -/
lemma map_line_eq_of_notMem
    (hχη : χ ≠ η) (hLdim : finrank k L = 1) (hMdim : finrank k M = 1)
    (hLM : IsCompl L M) (hχL : ActsByCharacterOn H ρ L χ) (hηM : ActsByCharacterOn H ρ M η)
    {g : G} (hg : g ∉ lineStabilizer ρ L) :
    Submodule.map (ρ g) L = M := by
  rcases character_line_eq_left_or_right H ρ hχη hLdim hMdim
    ((finrank_map_apply_eq ρ g L).trans hLdim) hLM hχL hηM
    (actsByCharacterOn_map_apply H ρ g hχL) with ⟨h, -⟩ | ⟨h, -⟩
  · exact absurd h hg
  · exact h

/-- Any `g` outside the stabilizer of `L` maps `M` back to `L`. -/
lemma map_other_line_eq_of_notMem
    (hχη : χ ≠ η) (hLdim : finrank k L = 1) (hMdim : finrank k M = 1)
    (hLM : IsCompl L M) (hχL : ActsByCharacterOn H ρ L χ) (hηM : ActsByCharacterOn H ρ M η)
    {g : G} (hg : g ∉ lineStabilizer ρ L) :
    Submodule.map (ρ g) M = L := by
  rcases character_line_eq_left_or_right H ρ hχη hLdim hMdim
    ((finrank_map_apply_eq ρ g M).trans hMdim) hLM hχL hηM
    (actsByCharacterOn_map_apply H ρ g hηM) with ⟨h, -⟩ | ⟨h, -⟩
  · exact h
  · -- `ρ g` maps both `L` and `M` to `M`, contradicting injectivity
    exfalso
    have hL' := map_line_eq_of_notMem hχη hLdim hMdim hLM hχL hηM hg
    have : L = M := by
      have e : ∀ N : Submodule k V, Submodule.map (ρ g⁻¹) (Submodule.map (ρ g) N) = N := by
        intro N
        rw [← Submodule.map_comp,
          ← show ρ (g⁻¹ * g) = (ρ g⁻¹) ∘ₗ (ρ g) from by rw [map_mul]; rfl]
        simp [Module.End.one_eq_id]
      rw [← e L, ← e M, hL', h]
    exact line_ne_line hLdim hLM this

/-- Step 3: the line stabilizer has index two. -/
lemma index_lineStabilizer_eq_two
    (hχη : χ ≠ η) (hLdim : finrank k L = 1) (hMdim : finrank k M = 1)
    (hLM : IsCompl L M) (hχL : ActsByCharacterOn H ρ L χ) (hηM : ActsByCharacterOn H ρ M η)
    (hne : lineStabilizer ρ L ≠ ⊤) :
    (lineStabilizer ρ L).index = 2 := by
  obtain ⟨g₀, hg₀⟩ : ∃ g₀, g₀ ∉ lineStabilizer ρ L := by
    by_contra h
    refine hne ((Subgroup.eq_top_iff' _).mpr fun g => ?_)
    by_contra hg
    exact h ⟨g, hg⟩
  rw [Subgroup.index_eq_two_iff]
  refine ⟨g₀, fun b => ?_⟩
  by_cases hb : b ∈ lineStabilizer ρ L
  · refine Or.inr ⟨hb, fun hmem => hg₀ ?_⟩
    have : g₀ = b⁻¹ * (b * g₀) := by group
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hb) hmem
  · refine Or.inl ⟨?_, hb⟩
    rw [mem_lineStabilizer]
    have : ρ (b * g₀) = (ρ b) ∘ₗ (ρ g₀) := by rw [map_mul]; rfl
    rw [this, Submodule.map_comp,
      map_line_eq_of_notMem hχη hLdim hMdim hLM hχL hηM hg₀,
      map_other_line_eq_of_notMem hχη hLdim hMdim hLM hχL hηM hb]

end Splitting

section LineCharacter

/-- A one-dimensional submodule is spanned by any of its nonzero vectors. -/
lemma exists_span_singleton [FiniteDimensional k V] {L : Submodule k V}
    (hL : finrank k L = 1) :
    ∃ v₀ : V, v₀ ≠ 0 ∧ L = Submodule.span k {v₀} := by
  have hbot : L ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at hL
    omega
  obtain ⟨v₀, hv₀L, hv₀⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
  refine ⟨v₀, hv₀, ?_⟩
  symm
  apply Submodule.eq_of_le_of_finrank_le
  · rwa [Submodule.span_singleton_le_iff_mem]
  · rw [hL, finrank_span_singleton hv₀]

variable {L : Submodule k V} {v₀ : V}

lemma existsUnique_smul_of_mem_lineStabilizer
    (hspan : L = Submodule.span k {v₀}) (hv₀ : v₀ ≠ 0) (g : lineStabilizer ρ L) :
    ∃! c : k, ρ (g : G) v₀ = c • v₀ := by
  have hv₀L : v₀ ∈ L := by rw [hspan]; exact Submodule.mem_span_singleton_self v₀
  have hgL : ρ (g : G) v₀ ∈ L := apply_mem_of_mem_lineStabilizer g.2 hv₀L
  have hgL2 : ρ (g : G) v₀ ∈ Submodule.span k {v₀} := by rw [← hspan]; exact hgL
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hgL2
  refine ⟨c, hc.symm, fun c' hc' => ?_⟩
  have hsub : (c' - c) • v₀ = 0 := by rw [sub_smul, ← hc', hc, sub_self]
  have hzero := (smul_eq_zero.mp hsub).resolve_right hv₀
  exact sub_eq_zero.mp hzero

variable (ρ)

/-- The scalar by which an element of the line stabilizer acts on the spanning vector. -/
noncomputable def lineScalar (hspan : L = Submodule.span k {v₀}) (hv₀ : v₀ ≠ 0)
    (g : lineStabilizer ρ L) : k :=
  (existsUnique_smul_of_mem_lineStabilizer hspan hv₀ g).choose

lemma lineScalar_spec (hspan : L = Submodule.span k {v₀}) (hv₀ : v₀ ≠ 0)
    (g : lineStabilizer ρ L) :
    ρ (g : G) v₀ = lineScalar ρ hspan hv₀ g • v₀ :=
  (existsUnique_smul_of_mem_lineStabilizer hspan hv₀ g).choose_spec.1

lemma lineScalar_eq_of (hspan : L = Submodule.span k {v₀}) (hv₀ : v₀ ≠ 0)
    {g : lineStabilizer ρ L} {c : k} (hc : ρ (g : G) v₀ = c • v₀) :
    lineScalar ρ hspan hv₀ g = c :=
  (existsUnique_smul_of_mem_lineStabilizer hspan hv₀ g).unique
    (lineScalar_spec ρ hspan hv₀ g) hc

lemma lineScalar_ne_zero (hspan : L = Submodule.span k {v₀}) (hv₀ : v₀ ≠ 0)
    (g : lineStabilizer ρ L) : lineScalar ρ hspan hv₀ g ≠ 0 := by
  intro h
  apply hv₀
  apply (ρ.apply_bijective (g : G)).1
  rw [lineScalar_spec ρ hspan hv₀ g, h, zero_smul, map_zero]

lemma lineScalar_mul (hspan : L = Submodule.span k {v₀}) (hv₀ : v₀ ≠ 0)
    (g h : lineStabilizer ρ L) :
    lineScalar ρ hspan hv₀ (g * h) = lineScalar ρ hspan hv₀ g * lineScalar ρ hspan hv₀ h := by
  apply lineScalar_eq_of
  have : ρ ((g : G) * (h : G)) = (ρ (g : G)) ∘ₗ (ρ (h : G)) := by rw [map_mul]; rfl
  change ρ ((g : G) * (h : G)) v₀ = _
  rw [this]
  change ρ (g : G) (ρ (h : G) v₀) = _
  rw [lineScalar_spec ρ hspan hv₀ h, map_smul, lineScalar_spec ρ hspan hv₀ g,
    smul_smul, mul_comm]

/-- Step 3 (character): the character by which the line stabilizer acts on the line `L`. -/
noncomputable def lineCharacter (hspan : L = Submodule.span k {v₀}) (hv₀ : v₀ ≠ 0) :
    lineStabilizer ρ L →* kˣ :=
  MonoidHom.mk' (fun g => Units.mk0 (lineScalar ρ hspan hv₀ g) (lineScalar_ne_zero ρ hspan hv₀ g))
    (fun g h => by
      ext
      simp [lineScalar_mul ρ hspan hv₀ g h])

@[simp]
lemma lineCharacter_apply (hspan : L = Submodule.span k {v₀}) (hv₀ : v₀ ≠ 0)
    (g : lineStabilizer ρ L) :
    (lineCharacter ρ hspan hv₀ g : k) = lineScalar ρ hspan hv₀ g := rfl

/-- The line stabilizer acts on `L` through `lineCharacter`. -/
lemma actsByCharacterOn_lineCharacter (hspan : L = Submodule.span k {v₀}) (hv₀ : v₀ ≠ 0) :
    ActsByCharacterOn (lineStabilizer ρ L) ρ L (lineCharacter ρ hspan hv₀) := by
  intro g v hv
  rw [hspan, Submodule.mem_span_singleton] at hv
  obtain ⟨a, rfl⟩ := hv
  rw [map_smul, lineScalar_spec ρ hspan hv₀ g, lineCharacter_apply, smul_smul, smul_smul,
    mul_comm]

end LineCharacter

section Determinant

variable {H : Subgroup G} [H.Normal] {χ η : H →* kˣ}
  {L M : Submodule k V} {v₀ : V}

/-- Step 5: if `τ` swaps the two lines and `τ ^ 2` stabilizes `L`, then
`det ρ(τ) = -ψ(τ²)` where `ψ` is the character of the stabilizer of `L` acting on `L`. -/
lemma det_eq_neg_lineScalar_sq
    (hχη : χ ≠ η) (hLdim : finrank k L = 1) (hMdim : finrank k M = 1)
    (hLM : IsCompl L M) (hχL : ActsByCharacterOn H ρ L χ) (hηM : ActsByCharacterOn H ρ M η)
    (hdim : finrank k V = 2)
    (hspan : L = Submodule.span k {v₀}) (hv₀ : v₀ ≠ 0)
    {τ : G} (hτ : τ ∉ lineStabilizer ρ L) (hτ2 : τ ^ 2 ∈ lineStabilizer ρ L) :
    LinearMap.det (ρ τ) = -(lineScalar ρ hspan hv₀ ⟨τ ^ 2, hτ2⟩) := by
  classical
  have hv₀L : v₀ ∈ L := by rw [hspan]; exact Submodule.mem_span_singleton_self v₀
  set w : V := ρ τ v₀ with hw
  have hwM : w ∈ M := by
    rw [← map_line_eq_of_notMem hχη hLdim hMdim hLM hχL hηM hτ]
    exact Submodule.mem_map_of_mem hv₀L
  have hwne : w ≠ 0 := by
    intro h
    apply hv₀
    apply (ρ.apply_bijective τ).1
    rw [← hw, h, map_zero]
  -- the pair (v₀, w) is a basis
  have hli : LinearIndependent k ![v₀, w] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have hsv : s • v₀ = -(t • w) := by
      rw [eq_neg_iff_add_eq_zero]
      exact hst
    have hmem : s • v₀ ∈ L ⊓ M := by
      constructor
      · exact L.smul_mem s hv₀L
      · rw [hsv]
        exact M.neg_mem (M.smul_mem t hwM)
    rw [hLM.inf_eq_bot, Submodule.mem_bot] at hmem
    have hs : s = 0 := by
      rcases smul_eq_zero.mp hmem with h | h
      · exact h
      · exact absurd h hv₀
    have htw : t • w = 0 := by
      rw [← neg_eq_zero, ← hsv, hmem]
    have ht : t = 0 := by
      rcases smul_eq_zero.mp htw with h | h
      · exact h
      · exact absurd h hwne
    exact ⟨hs, ht⟩
  have hcard : Fintype.card (Fin 2) = finrank k V := by simp [hdim]
  set b := basisOfLinearIndependentOfCardEqFinrank hli hcard with hbdef
  have hb : ⇑b = ![v₀, w] := coe_basisOfLinearIndependentOfCardEqFinrank hli hcard
  have hb0 : b 0 = v₀ := by rw [hb]; rfl
  have hb1 : b 1 = w := by rw [hb]; rfl
  set c : k := lineScalar ρ hspan hv₀ ⟨τ ^ 2, hτ2⟩ with hc
  have hρτ0 : ρ τ (b 0) = b 1 := by rw [hb0, hb1]
  have hρτ1 : ρ τ (b 1) = c • b 0 := by
    rw [hb0, hb1, hw]
    have : ρ τ (ρ τ v₀) = ρ (τ ^ 2) v₀ := by
      rw [pow_two, map_mul]
      rfl
    rw [this, lineScalar_spec ρ hspan hv₀ ⟨τ ^ 2, hτ2⟩]
  have hmat : LinearMap.toMatrix b b (ρ τ) = !![0, c; 1, 0] := by
    ext i j
    rw [LinearMap.toMatrix_apply]
    fin_cases i <;> fin_cases j <;>
      simp [hρτ0, hρτ1, Basis.repr_self]
  rw [← LinearMap.det_toMatrix b, hmat, Matrix.det_fin_two_of]
  ring

end Determinant

end CyclotomicAbsIrred

end
