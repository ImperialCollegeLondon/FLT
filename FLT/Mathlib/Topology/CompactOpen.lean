/-
Copyright (c) 2026 Yunzhou Xie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Edison Xie
-/
module

public import Mathlib.Topology.CompactOpen

/-!
# Joint continuity of pairing into a product

This file shows that the pairing `C(α, β) × C(α, δ) → C(α, β × δ)` is continuous in the
compact-open topologies whenever `α` is an R₁ space, with no local compactness assumption.

Material destined for `Mathlib.Topology.CompactOpen`.
-/

@[expose] public section

open ContinuousMap Set Topology in
/-- The pairing map `C(α, β) × C(α, δ) → C(α, β × δ)` is continuous in the compact-open
topologies when `α` is an R₁ space, for instance a topological group, with no assumptions on
`β` and `δ`. No local compactness of `α` is required: a compact set mapped into an open set of
`β × δ` splits into finitely many compact pieces on each of which both components map into an
open rectangle. -/
lemma ContinuousMap.continuous_prodMk {α β δ : Type*} [TopologicalSpace α] [R1Space α]
    [TopologicalSpace β] [TopologicalSpace δ] :
    Continuous fun p : C(α, β) × C(α, δ) ↦ p.1.prodMk p.2 := by
  simp_rw [continuous_iff_continuousAt, ContinuousAt, tendsto_nhds_compactOpen]
  rintro ⟨f, g⟩ K hK U hU hfg
  have hrect : ∀ x ∈ K, ∃ V W, IsOpen V ∧ IsOpen W ∧ f x ∈ V ∧ g x ∈ W ∧ V ×ˢ W ⊆ U :=
    fun x hx ↦ isOpen_prod_iff.1 hU (f x) (g x) (hfg hx)
  choose! V W hVopen hWopen hfV hgW hsubU using hrect
  obtain ⟨s, hsK, hsfin, hscov⟩ := hK.elim_finite_subcover_image
    (fun x hx ↦ ((hVopen x hx).preimage f.continuous).inter ((hWopen x hx).preimage g.continuous))
    (fun x hx ↦ mem_biUnion hx ⟨hfV x hx, hgW x hx⟩)
  obtain ⟨C, hCcomp, hCsub, hCeq⟩ := hK.finite_compact_cover hsfin.toFinset
    (fun x ↦ f ⁻¹' V x ∩ g ⁻¹' W x)
    (fun x hx ↦ ((hVopen x (hsK (hsfin.mem_toFinset.1 hx))).preimage f.continuous).inter
      ((hWopen x (hsK (hsfin.mem_toFinset.1 hx))).preimage g.continuous))
    (by simpa only [Set.Finite.mem_toFinset] using hscov)
  have key : ∀ x ∈ hsfin.toFinset, ∀ᶠ p : C(α, β) × C(α, δ) in 𝓝 (f, g),
      MapsTo p.1 (C x) (V x) ∧ MapsTo p.2 (C x) (W x) := by
    intro x hx
    have h1 : ∀ᶠ f' : C(α, β) in 𝓝 f, MapsTo f' (C x) (V x) :=
      eventually_mapsTo (hCcomp x) (hVopen x (hsK (hsfin.mem_toFinset.1 hx)))
        fun z hz ↦ (hCsub x hz).1
    have h2 : ∀ᶠ g' : C(α, δ) in 𝓝 g, MapsTo g' (C x) (W x) :=
      eventually_mapsTo (hCcomp x) (hWopen x (hsK (hsfin.mem_toFinset.1 hx)))
        fun z hz ↦ (hCsub x hz).2
    rw [nhds_prod_eq]
    exact (Filter.tendsto_fst.eventually h1).and (Filter.tendsto_snd.eventually h2)
  filter_upwards [(Filter.eventually_all_finset hsfin.toFinset).2 key] with p hp z hzK
  rw [hCeq] at hzK
  obtain ⟨x, hxs, hzC⟩ := mem_iUnion₂.1 hzK
  exact hsubU x (hsK (hsfin.mem_toFinset.1 hxs)) ⟨(hp x hxs).1 hzC, (hp x hxs).2 hzC⟩
