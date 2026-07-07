/-
Copyright (c) 2026 Bryan Hu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zachary Feng, Bryan Hu, Y. Samanda Zhang
-/
module

public import FLT.Slop.Ribet_Lemma.stable_lattices

/-!
# Extensions of characters, lattice modification, and Brauer–Nesbitt

Sections 5–7 of the Ribet's-lemma development (see the overview in the header
of `stable_lattices.lean`; `Ribet_Lemma.lean` §8–10 is the goal).

§5.  The predicates `StableLattice.IsExtensionOf`,
`StableLattice.IsSplitExtensionOf` and `StableLattice.HasSemisimplification`
are defined in `FLT.KnownIn1980s.Ribet_Lemma.Defs`; this section develops the
elementary geometry of stable lines in dimension 2: a stable line carries a
character (`exists_character_of_stable_line`), any stable line of an
extension realizes the two characters in one of the two orders
(`isExtensionOf_along_stable_line`), and the stable line of a non-split
extension is unique (`stable_line_unique_of_not_isSplitExtensionOf`).

§6 is the engine of the whole development.  For a stable lattice `Λ` and a
subspace `W` of its reduction, `preimageLattice Λ W` is the sub-lattice of
elements of `Λ` reducing into `W`; together with `reductionImage` this sets
up the standard correspondence between subspaces of `Λ ⧸ 𝔪Λ` and lattices
between `𝔪Λ` and `Λ`.  The **key computation**
(`preimageLattice_extension_spec`) says that if the reduction of `Λ` is an
extension with sub `φ₁` and quotient `φ₂` realized by a line `L`, then the
reduction of the neighbor `preimageLattice Λ L` is an extension the other
way around, with sub-line the image of `𝔪Λ`.  In Ribet's paper this is the
conjugation by the matrix `P = (1 0; 0 π)` on p. 155.

§7 proves that the semisimplification of the reduction is independent of the
stable lattice (`hasSemisimplification_independent_of_lattice_slop`).  Ribet
quotes this from Curtis–Reiner (30.16); Mathlib (as of July 2026) has
neither semisimplification nor the Brauer–Nesbitt theorem, so a direct proof
is given instead: after scaling, any two stable lattices are connected by a
chain of neighbors (`hasSemisimplification_of_le`), and each neighbor step
merely swaps the two characters by the key computation.  This independence
is *not* used in the proof of Ribet's lemma itself, which is anchored to the
given lattice; it is what makes the hypothesis of Ribet's lemma checkable on
any convenient lattice.  See the remarks in §10.

## Design decisions

* `reductionImage` and `preimageLattice` keep all lattices inside the fixed
  ambient space `V` (as `Submodule O V`), so chains of neighbors can be
  compared without transporting along isomorphisms.

The file is `sorry`-free.
-/

@[expose] public section

open Pointwise IsLocalRing

namespace StableLattice

/-! ## 5. Extensions of characters -/

section Characters

variable {G : Type*} [Group G]
variable {F : Type*} [Field F] {W : Type*} [AddCommGroup W] [Module F W]

/-- Sanity check for the definitions in `FLT.KnownIn1980s.Ribet_Lemma.Defs`:
a split extension is in particular an extension (write `x = l + l'` and
compute `ρ' g x - φ₂ g • x = (φ₁ g - φ₂ g) • l ∈ L`). -/
theorem IsSplitExtensionOf.isExtensionOf {ρ' : Representation F G W}
    {φ₁ φ₂ : G →* Fˣ} (h : IsSplitExtensionOf ρ' φ₁ φ₂) :
    IsExtensionOf ρ' φ₁ φ₂ := by
  obtain ⟨L, L', hL₁, hLact, hL'act, hcompl⟩ := h
  refine ⟨L, hL₁, hLact, fun g x => ?_⟩
  have hx : x ∈ L ⊔ L' := by rw [hcompl.codisjoint.eq_top]; trivial
  obtain ⟨l, hl, l', hl', rfl⟩ := Submodule.mem_sup.mp hx
  have hcalc : ρ' g (l + l') - (φ₂ g : F) • (l + l')
      = ((φ₁ g : F) - (φ₂ g : F)) • l := by
    rw [map_add, hLact g l hl, hL'act g l' hl']
    module
  rw [hcalc]
  exact L.smul_mem _ hl

/-- A stable line carries a character: if `L` is a `G`-stable 1-dimensional
subspace, then `G` acts on `L` through some `φ : G →* Fˣ`.  (Produces the
witnesses for `IsExtensionOf` from lattice-theoretic data.) -/
theorem exists_character_of_stable_line (ρ' : Representation F G W)
    {L : Submodule F W} (hL : Module.finrank F L = 1)
    (hstab : ∀ g : G, L.map (ρ' g) ≤ L) :
    ∃ φ : G →* Fˣ, ∀ g : G, ∀ x ∈ L, ρ' g x = (φ g : F) • x := by
  obtain ⟨v₀, hv₀, hspan⟩ := finrank_eq_one_iff'.mp hL
  have hv₀W : (v₀ : W) ≠ 0 := fun h0 => hv₀ (Subtype.ext h0)
  -- the scalar by which `g` acts on the generator
  choose c hc using fun g : G =>
    hspan ⟨ρ' g (v₀ : W), hstab g (Submodule.mem_map_of_mem v₀.2)⟩
  have hcoe : ∀ g : G, c g • (v₀ : W) = ρ' g (v₀ : W) :=
    fun g => congrArg Subtype.val (hc g)
  have hne : ∀ g : G, c g ≠ 0 := by
    intro g hg0
    apply hv₀W
    have h1 : ρ' g (v₀ : W) = 0 := by rw [← hcoe g, hg0, zero_smul]
    have h2 := congrArg (ρ' g⁻¹) h1
    rwa [map_zero, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
      Module.End.one_apply] at h2
  have hmul : ∀ g h : G, c (g * h) = c g * c h := by
    intro g h
    refine smul_left_injective F hv₀W ?_
    change c (g * h) • (v₀ : W) = (c g * c h) • (v₀ : W)
    rw [hcoe (g * h), map_mul, Module.End.mul_apply, ← hcoe h, map_smul, ← hcoe g,
      smul_smul, mul_comm (c h)]
  refine ⟨MonoidHom.mk' (fun g => Units.mk0 (c g) (hne g))
    (fun g h => Units.ext (hmul g h)), fun g x hx => ?_⟩
  obtain ⟨d, hd⟩ := hspan ⟨x, hx⟩
  have hdW : d • (v₀ : W) = x := congrArg Subtype.val hd
  simp only [MonoidHom.mk'_apply, Units.val_mk0]
  rw [← hdW, map_smul, ← hcoe g, smul_smul, smul_smul, mul_comm]

/-- The stable line of a *non-split* extension is unique.  (A second stable
line `L'` would satisfy `L ⊓ L' = ⊥`, hence be a complement of `L`; by
`hLquot` the character of `L'` is forced to be `φ₂`, so `L, L'` would split
the extension.  Note that `φ₁ ≠ φ₂` is not needed.)  This is what steers the
walk in the proof of Ribet's lemma: the next lattice is determined. -/
theorem stable_line_unique_of_not_isSplitExtensionOf
    {ρ' : Representation F G W} {φ₁ φ₂ : G →* Fˣ}
    (hdim : Module.finrank F W = 2)
    (hns : ¬ IsSplitExtensionOf ρ' φ₁ φ₂)
    {L : Submodule F W} (hL₁ : Module.finrank F L = 1)
    (hLchar : ∀ g : G, ∀ x ∈ L, ρ' g x = (φ₁ g : F) • x)
    (hLquot : ∀ g : G, ∀ x : W, ρ' g x - (φ₂ g : F) • x ∈ L)
    {L' : Submodule F W} (hL'₁ : Module.finrank F L' = 1)
    (hL'stab : ∀ g : G, L'.map (ρ' g) ≤ L') :
    L' = L := by
  haveI : FiniteDimensional F W := Module.finite_of_finrank_pos (by omega)
  by_contra hne
  apply hns
  -- two distinct lines are disjoint …
  have hdisj : L ⊓ L' = ⊥ := by
    by_contra hbot
    have hnt : Nontrivial ↥(L ⊓ L') := Submodule.nontrivial_iff_ne_bot.mpr hbot
    have hfr : 1 ≤ Module.finrank F ↥(L ⊓ L') := Module.finrank_pos_iff.mpr hnt
    have e1 : L ⊓ L' = L :=
      Submodule.eq_of_le_of_finrank_le inf_le_left (hL₁ ▸ hfr)
    have e2 : L ⊓ L' = L' :=
      Submodule.eq_of_le_of_finrank_le inf_le_right (hL'₁ ▸ hfr)
    exact hne (e2.symm.trans e1)
  -- … and, in dimension 2, complementary
  have hsup : L ⊔ L' = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    have hh := Submodule.finrank_sup_add_finrank_inf_eq L L'
    rw [hdisj, finrank_bot, hL₁, hL'₁] at hh
    rw [hdim]
    omega
  -- `hLquot` forces the character of the second line to be `φ₂`
  have hL'act : ∀ g : G, ∀ x ∈ L', ρ' g x = (φ₂ g : F) • x := by
    intro g x hx
    have h1 : ρ' g x - (φ₂ g : F) • x ∈ L := hLquot g x
    have h2 : ρ' g x - (φ₂ g : F) • x ∈ L' :=
      Submodule.sub_mem _ (hL'stab g (Submodule.mem_map_of_mem hx))
        (Submodule.smul_mem _ _ hx)
    have h3 : ρ' g x - (φ₂ g : F) • x ∈ L ⊓ L' := Submodule.mem_inf.mpr ⟨h1, h2⟩
    rw [hdisj, Submodule.mem_bot] at h3
    exact sub_eq_zero.mp h3
  exact ⟨L, L', hL₁, hLchar, hL'act, IsCompl.of_eq hdisj hsup⟩

/-- `φ₁ ⊕ φ₂` and `φ₂ ⊕ φ₁` are the same semisimplification. -/
theorem HasSemisimplification.symm {ρ' : Representation F G W} {φ₁ φ₂ : G →* Fˣ}
    (h : HasSemisimplification ρ' φ₁ φ₂) : HasSemisimplification ρ' φ₂ φ₁ :=
  Or.symm h

/-- In dimension 2, splitness is symmetric in the two characters. -/
theorem IsSplitExtensionOf.symm (hdim : Module.finrank F W = 2)
    {ρ' : Representation F G W} {φ₁ φ₂ : G →* Fˣ}
    (h : IsSplitExtensionOf ρ' φ₁ φ₂) : IsSplitExtensionOf ρ' φ₂ φ₁ := by
  haveI : FiniteDimensional F W := Module.finite_of_finrank_pos (by omega)
  obtain ⟨L, L', hL₁, hLact, hL'act, hcompl⟩ := h
  have hL'₁ : Module.finrank F L' = 1 := by
    have hh := Submodule.finrank_sup_add_finrank_inf_eq L L'
    rw [hcompl.inf_eq_bot, hcompl.sup_eq_top, finrank_bot, finrank_top, hdim, hL₁] at hh
    omega
  exact ⟨L', L, hL'₁, hL'act, hLact, hcompl.symm⟩

/-- In a 2-dimensional extension with characters `φ₁, φ₂`, *any* stable line
realizes the two characters, in one of the two orders.  (If the line is the
given one, the order is `(φ₁, φ₂)`; otherwise it is a complement, its
character is forced to be `φ₂` by the quotient condition, and the given line
maps isomorphically to the new quotient.) -/
theorem isExtensionOf_along_stable_line
    (hdim : Module.finrank F W = 2)
    {ρ' : Representation F G W} {φ₁ φ₂ : G →* Fˣ} (hext : IsExtensionOf ρ' φ₁ φ₂)
    {N : Submodule F W} (hN₁ : Module.finrank F N = 1)
    (hNstab : ∀ g : G, N.map (ρ' g) ≤ N) :
    ((∀ g : G, ∀ x ∈ N, ρ' g x = (φ₁ g : F) • x) ∧
      (∀ g : G, ∀ x : W, ρ' g x - (φ₂ g : F) • x ∈ N)) ∨
    ((∀ g : G, ∀ x ∈ N, ρ' g x = (φ₂ g : F) • x) ∧
      (∀ g : G, ∀ x : W, ρ' g x - (φ₁ g : F) • x ∈ N)) := by
  haveI : FiniteDimensional F W := Module.finite_of_finrank_pos (by omega)
  obtain ⟨L, hL₁, hLchar, hLquot⟩ := hext
  by_cases hNL : N = L
  · subst hNL; exact Or.inl ⟨hLchar, hLquot⟩
  have hdisj : L ⊓ N = ⊥ := by
    by_contra hbot
    have hnt : Nontrivial ↥(L ⊓ N) := Submodule.nontrivial_iff_ne_bot.mpr hbot
    have hfr : 1 ≤ Module.finrank F ↥(L ⊓ N) := Module.finrank_pos_iff.mpr hnt
    exact hNL ((Submodule.eq_of_le_of_finrank_le inf_le_right (hN₁ ▸ hfr)).symm.trans
      (Submodule.eq_of_le_of_finrank_le inf_le_left (hL₁ ▸ hfr)))
  have hsup : L ⊔ N = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    have hh := Submodule.finrank_sup_add_finrank_inf_eq L N
    rw [hdisj, finrank_bot, hL₁, hN₁] at hh
    rw [hdim]; omega
  have hNchar : ∀ g : G, ∀ x ∈ N, ρ' g x = (φ₂ g : F) • x := by
    intro g x hx
    have h1 : ρ' g x - (φ₂ g : F) • x ∈ L := hLquot g x
    have h2 : ρ' g x - (φ₂ g : F) • x ∈ N :=
      Submodule.sub_mem _ (hNstab g (Submodule.mem_map_of_mem hx))
        (Submodule.smul_mem _ _ hx)
    have h3 := Submodule.mem_inf.mpr ⟨h1, h2⟩
    rw [hdisj, Submodule.mem_bot] at h3
    exact sub_eq_zero.mp h3
  refine Or.inr ⟨hNchar, fun g x => ?_⟩
  have hx : x ∈ L ⊔ N := by rw [hsup]; trivial
  obtain ⟨l, hl, n, hn, rfl⟩ := Submodule.mem_sup.mp hx
  have hcalc : ρ' g (l + n) - (φ₁ g : F) • (l + n)
      = ((φ₂ g : F) - (φ₁ g : F)) • n := by
    rw [map_add, hLchar g l hl, hNchar g n hn]
    module
  rw [hcalc]
  exact N.smul_mem _ hn

/-- `IsExtensionOf` transports along a `G`-equivariant isomorphism. -/
theorem IsExtensionOf.congr {W₂ : Type*} [AddCommGroup W₂] [Module F W₂]
    {ρ₁ : Representation F G W} {ρ₂ : Representation F G W₂}
    (e : W ≃ₗ[F] W₂) (hcomm : ∀ (g : G) (x : W), e (ρ₁ g x) = ρ₂ g (e x))
    {φ₁ φ₂ : G →* Fˣ} (h : IsExtensionOf ρ₁ φ₁ φ₂) :
    IsExtensionOf ρ₂ φ₁ φ₂ := by
  obtain ⟨L, hL₁, hLchar, hLquot⟩ := h
  refine ⟨L.map (e : W →ₗ[F] W₂), ?_, ?_, ?_⟩
  · rw [LinearEquiv.finrank_map_eq]; exact hL₁
  · rintro g x ⟨l, hl, rfl⟩
    rw [show ((e : W →ₗ[F] W₂) l : W₂) = e l from rfl, ← hcomm, hLchar g l hl, map_smul]
  · intro g x
    obtain ⟨y, rfl⟩ := e.surjective x
    have hy : ρ₂ g (e y) - (φ₂ g : F) • e y = e (ρ₁ g y - (φ₂ g : F) • y) := by
      rw [map_sub, map_smul, hcomm]
    rw [hy]
    exact Submodule.mem_map_of_mem (hLquot g y)

/-- `HasSemisimplification` transports along a `G`-equivariant isomorphism. -/
theorem HasSemisimplification.congr {W₂ : Type*} [AddCommGroup W₂] [Module F W₂]
    {ρ₁ : Representation F G W} {ρ₂ : Representation F G W₂}
    (e : W ≃ₗ[F] W₂) (hcomm : ∀ (g : G) (x : W), e (ρ₁ g x) = ρ₂ g (e x))
    {φ₁ φ₂ : G →* Fˣ} (h : HasSemisimplification ρ₁ φ₁ φ₂) :
    HasSemisimplification ρ₂ φ₁ φ₂ :=
  h.imp (fun h' => h'.congr e hcomm) (fun h' => h'.congr e hcomm)

end Characters

/-! ## 6. Lattice modification: neighbor lattices and the key computation -/

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
variable {K : Type*} [Field K] [Algebra O K] [IsFractionRing O K]
variable {V : Type*} [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V]
variable [FiniteDimensional K V]
variable {G : Type*} [Group G]

/-! Images of sub-lattices in reductions: for `Λ₁ ≤ Λ₂`, the image of `Λ₁` in
`Λ₂ ⧸ 𝔪Λ₂` is a subspace over the residue field, with membership, `⊥` and `⊤`
criteria phrased at the level of submodules of `V`. -/

variable (O) in
/-- The image of a sub-lattice `Λ₁ ≤ Λ₂` in the reduction of `Λ₂`. -/
noncomputable def reductionImage {Λ₁ Λ₂ : Submodule O V} (h : Λ₁ ≤ Λ₂) :
    Submodule (ResidueField O) (Reduction O V Λ₂) :=
  LinearMap.range (reductionMap (Submodule.inclusion h))

omit [IsFractionRing O K] [FiniteDimensional K V] in
theorem mk_mem_reductionImage {Λ₁ Λ₂ : Submodule O V} (h : Λ₁ ≤ Λ₂) (y : Λ₂) :
    Submodule.Quotient.mk y ∈ reductionImage O h
      ↔ ∃ z ∈ Λ₁, (y : V) - z ∈ maximalIdeal O • Λ₂ := by
  constructor
  · rintro ⟨ξ, hξ⟩
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ ξ
    refine ⟨z, z.2, ?_⟩
    rw [reductionMap_mk] at hξ
    have hd := (Submodule.Quotient.eq _).mp hξ
    rw [mem_smul_top_iff] at hd
    simp only [Submodule.coe_sub, Submodule.coe_inclusion] at hd
    simpa using Submodule.neg_mem _ hd
  · rintro ⟨z, hz, hd⟩
    refine ⟨Submodule.Quotient.mk ⟨z, hz⟩, ?_⟩
    rw [reductionMap_mk]
    rw [Submodule.Quotient.eq, mem_smul_top_iff]
    simp only [Submodule.coe_sub, Submodule.coe_inclusion]
    simpa using Submodule.neg_mem _ hd

omit [IsFractionRing O K] [FiniteDimensional K V] in
theorem reductionImage_eq_bot {Λ₁ Λ₂ : Submodule O V} (h : Λ₁ ≤ Λ₂) :
    reductionImage O h = ⊥ ↔ Λ₁ ≤ maximalIdeal O • Λ₂ := by
  constructor
  · intro hbot x hx
    have hm : Submodule.Quotient.mk (⟨x, h hx⟩ : Λ₂) ∈ reductionImage O h :=
      (mk_mem_reductionImage h _).mpr ⟨x, hx, by simp⟩
    rw [hbot, Submodule.mem_bot, Submodule.Quotient.mk_eq_zero,
      mem_smul_top_iff] at hm
    exact hm
  · intro hle
    rw [eq_bot_iff]
    rintro ξ ⟨η, hη⟩
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ η
    rw [← hη, reductionMap_mk, Submodule.mem_bot, Submodule.Quotient.mk_eq_zero,
      mem_smul_top_iff]
    exact hle z.2

omit [IsFractionRing O K] [FiniteDimensional K V] in
theorem reductionImage_eq_top {Λ₁ Λ₂ : Submodule O V} (h : Λ₁ ≤ Λ₂) :
    reductionImage O h = ⊤ ↔ Λ₁ ⊔ maximalIdeal O • Λ₂ = Λ₂ := by
  constructor
  · intro htop
    refine le_antisymm (sup_le h Submodule.smul_le_right) fun y hy => ?_
    have hm : Submodule.Quotient.mk (⟨y, hy⟩ : Λ₂) ∈ reductionImage O h := by
      rw [htop]; trivial
    obtain ⟨z, hz, hd⟩ := (mk_mem_reductionImage h _).mp hm
    have hyz : y = z + (y - z) := by abel
    rw [hyz]
    exact Submodule.add_mem_sup hz hd
  · intro hsup
    rw [eq_top_iff]
    rintro ξ -
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ ξ
    have hy : (y : V) ∈ Λ₁ ⊔ maximalIdeal O • Λ₂ := by rw [hsup]; exact y.2
    obtain ⟨z, hz, m, hm, hzm⟩ := Submodule.mem_sup.mp hy
    exact (mk_mem_reductionImage h y).mpr ⟨z, hz, by rw [← hzm]; simpa using hm⟩

variable {ρ : Representation K G V}

/-- The preimage in `Λ` (viewed inside `V`) of a subspace `W` of the reduction
`Λ ⧸ 𝔪Λ`.  (Uses the `Module (ResidueField O)` and
`IsScalarTower O (ResidueField O)` instances on `Reduction O V Λ` from
`FLT.KnownIn1980s.Ribet_Lemma.Defs`.) -/
noncomputable def preimageLattice (Λ : Submodule O V)
    (W : Submodule (ResidueField O) (Reduction O V Λ)) : Submodule O V :=
  ((W.restrictScalars O).comap
    (maximalIdeal O • ⊤ : Submodule O Λ).mkQ).map Λ.subtype

theorem preimageLattice_le (Λ : Submodule O V)
    (W : Submodule (ResidueField O) (Reduction O V Λ)) :
    preimageLattice Λ W ≤ Λ :=
  Submodule.map_subtype_le _ _

/-- The neighbor lattice contains `𝔪Λ`. -/
theorem smul_le_preimageLattice (Λ : Submodule O V)
    (W : Submodule (ResidueField O) (Reduction O V Λ)) :
    maximalIdeal O • Λ ≤ preimageLattice Λ W := by
  intro x hx
  have hmap : (maximalIdeal O • ⊤ : Submodule O Λ).map Λ.subtype
      = maximalIdeal O • Λ := by
    rw [Submodule.map_smul'', Submodule.map_top, Submodule.range_subtype]
  rw [← hmap] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  refine Submodule.mem_map_of_mem ?_
  rw [Submodule.mem_comap, Submodule.mkQ_apply]
  have h0 : (Submodule.Quotient.mk y : Reduction O V Λ) = 0 :=
    (Submodule.Quotient.mk_eq_zero _).mpr hy
  rw [h0]
  exact Submodule.zero_mem _

omit [FiniteDimensional K V] in
/-- The neighbor of a lattice is a lattice (finitely generated since `O` is
noetherian and `preimageLattice Λ W ≤ Λ`; spans since it contains
`𝔪Λ = πΛ`, which is a lattice). -/
theorem isLattice_preimageLattice (Λ : Submodule O V) [Submodule.IsLattice K Λ]
    (W : Submodule (ResidueField O) (Reduction O V Λ)) :
    Submodule.IsLattice K (preimageLattice Λ W) := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hsmul : (π • Λ : Submodule O V) ≤ preimageLattice Λ W := by
    rw [← Submodule.ideal_span_singleton_smul, ← hπ.maximalIdeal_eq]
    exact smul_le_preimageLattice Λ W
  haveI := Submodule.IsLattice.smul_of_ne_zero (K := K) Λ hπ.ne_zero
  refine Submodule.IsLattice.of_le_of_isLattice_of_fg K hsmul ?_
  haveI : IsNoetherian O Λ := isNoetherian_of_isNoetherianRing_of_finite O Λ
  haveI : IsNoetherian O ↥(preimageLattice Λ W) :=
    isNoetherian_of_le (preimageLattice_le Λ W)
  rw [← Module.Finite.iff_fg]
  infer_instance

omit [IsFractionRing O K] [FiniteDimensional K V] in
/-- Membership in the neighbor lattice, for elements already in `Λ`. -/
theorem mem_preimageLattice {Λ : Submodule O V}
    {W : Submodule (ResidueField O) (Reduction O V Λ)} (y : Λ) :
    (y : V) ∈ preimageLattice Λ W ↔ Submodule.Quotient.mk y ∈ W := by
  constructor
  · rintro ⟨z, hz, hzy⟩
    rwa [show z = y from Subtype.ext hzy] at hz
  · intro hy
    exact ⟨y, hy, rfl⟩

omit [IsFractionRing O K] [FiniteDimensional K V] in
/-- The correspondence between intermediate lattices and subspaces of the
reduction, one way: the preimage of the image of a sub-lattice `Λ₁ ≤ Λ` is
`Λ₁ ⊔ 𝔪Λ`. -/
theorem preimageLattice_reductionImage {Λ₁ Λ : Submodule O V} (h : Λ₁ ≤ Λ) :
    preimageLattice Λ (reductionImage O h) = Λ₁ ⊔ maximalIdeal O • Λ := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    simp only [Submodule.subtype_apply]
    obtain ⟨z, hz, hd⟩ := (mk_mem_reductionImage h y).mp hy
    have hyz : (y : V) = z + ((y : V) - z) := by abel
    rw [hyz]
    exact Submodule.add_mem_sup hz hd
  · intro hx
    have hxΛ : x ∈ Λ := by
      rcases Submodule.mem_sup.mp hx with ⟨a, ha, b, hb, rfl⟩
      exact Submodule.add_mem _ (h ha) (Submodule.smul_le_right hb)
    refine (mem_preimageLattice (⟨x, hxΛ⟩ : Λ)).mpr ?_
    rcases Submodule.mem_sup.mp hx with ⟨a, ha, b, hb, hab⟩
    refine (mk_mem_reductionImage h _).mpr ⟨a, ha, ?_⟩
    change x - a ∈ _
    rw [← hab]
    simpa using hb

omit [IsFractionRing O K] [FiniteDimensional K V] in
/-- The correspondence, the other way: the image of the neighbor lattice
recovers the subspace. -/
theorem reductionImage_preimageLattice {Λ : Submodule O V}
    (W : Submodule (ResidueField O) (Reduction O V Λ)) :
    reductionImage O (preimageLattice_le Λ W) = W := by
  ext ξ
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ ξ
  rw [mk_mem_reductionImage]
  constructor
  · rintro ⟨z, hz, hd⟩
    have hzΛ : z ∈ Λ := preimageLattice_le Λ W hz
    have hmk : (Submodule.Quotient.mk y : Reduction O V Λ)
        = Submodule.Quotient.mk (⟨z, hzΛ⟩ : Λ) := by
      rw [Submodule.Quotient.eq, mem_smul_top_iff]
      simpa using hd
    rw [hmk]
    exact (mem_preimageLattice ⟨z, hzΛ⟩).mp hz
  · intro hy
    exact ⟨(y : V), (mem_preimageLattice y).mpr hy, by simp⟩

omit [IsFractionRing O K] [FiniteDimensional K V] in
/-- Distinct subspaces of the reduction have distinct neighbor lattices. -/
theorem preimageLattice_injective {Λ : Submodule O V}
    {W₁ W₂ : Submodule (ResidueField O) (Reduction O V Λ)}
    (hW : preimageLattice Λ W₁ = preimageLattice Λ W₂) : W₁ = W₂ := by
  rw [← reductionImage_preimageLattice (Λ := Λ) W₁,
    ← reductionImage_preimageLattice (Λ := Λ) W₂]
  congr 1

omit [IsFractionRing O K] [FiniteDimensional K V] in
/-- The neighbor of a stable lattice along a stable subspace is stable. -/
theorem stabilizes_preimageLattice {Λ : Submodule O V} (hΛ : Stabilizes ρ Λ)
    {W : Submodule (ResidueField O) (Reduction O V Λ)}
    (hW : ∀ g : G, W.map (reducedRep ρ Λ hΛ g) ≤ W) :
    Stabilizes ρ (preimageLattice Λ W) := by
  refine Stabilizes.of_le fun g => ?_
  rintro x ⟨y, hy, rfl⟩
  obtain ⟨z, hz, rfl⟩ := hy
  -- `ρ g` sends the preimage of `W` into itself: apply `latticeRep` inside `Λ`
  -- and use that `mkQ ∘ latticeRep g = reducedRep g ∘ mkQ` definitionally.
  refine ⟨latticeRep ρ Λ hΛ g z, ?_, rfl⟩
  have hz' : (maximalIdeal O • ⊤ : Submodule O Λ).mkQ z ∈ W := hz
  exact hW g (Submodule.mem_map_of_mem hz')

omit [FiniteDimensional K V] in
/-- **Key computation** (moving to a neighbor swaps sub and quotient): if the
reduction of `Λ` is an extension with sub `φ₁` and quotient `φ₂`, realized by
the line `L`, then the reduction of `preimageLattice Λ L` is an extension with
sub `φ₂` and quotient `φ₁` — and the new sub-line is precisely the image of
`𝔪Λ`.  (The walk in `ribet_lemma_slop` needs to know the new line, to avoid
stepping straight back.)

The stability hypothesis `hstab` is derivable from
`stabilizes_preimageLattice` and `hLchar`; it is taken as an argument so that
`reducedRep` can be formed in the statement. -/
theorem preimageLattice_extension_spec
    (hdim : Module.finrank K V = 2)
    {Λ : Submodule O V} (h : IsStableLattice ρ Λ)
    {φ₁ φ₂ : G →* (ResidueField O)ˣ}
    {L : Submodule (ResidueField O) (Reduction O V Λ)}
    (hL₁ : Module.finrank (ResidueField O) L = 1)
    (hLchar : ∀ g : G, ∀ x ∈ L,
      reducedRep ρ Λ h.stable g x = (φ₁ g : ResidueField O) • x)
    (hLquot : ∀ g : G, ∀ x,
      reducedRep ρ Λ h.stable g x - (φ₂ g : ResidueField O) • x ∈ L)
    (hstab : Stabilizes ρ (preimageLattice Λ L)) :
    Module.finrank (ResidueField O)
        ↥(reductionImage O (smul_le_preimageLattice Λ L)) = 1 ∧
    (∀ g : G, ∀ x ∈ reductionImage O (smul_le_preimageLattice Λ L),
      reducedRep ρ (preimageLattice Λ L) hstab g x
        = (φ₂ g : ResidueField O) • x) ∧
    (∀ g : G, ∀ x, reducedRep ρ (preimageLattice Λ L) hstab g x
        - (φ₁ g : ResidueField O) • x
        ∈ reductionImage O (smul_le_preimageLattice Λ L)) := by
  haveI := h.isLattice
  haveI := isLattice_preimageLattice (K := K) Λ L
  have hdimΛ : Module.finrank (ResidueField O) (Reduction O V Λ) = 2 := by
    rw [finrank_reduction (K := K) Λ, hdim]
  have hdimΛ' : Module.finrank (ResidueField O)
      (Reduction O V (preimageLattice Λ L)) = 2 := by
    rw [finrank_reduction (K := K) (preimageLattice Λ L), hdim]
  haveI : FiniteDimensional (ResidueField O) (Reduction O V (preimageLattice Λ L)) :=
    Module.finite_of_finrank_pos (by omega)
  -- `hLquot`, at the level of `V`: `ρ g` differs from (a lift of) `φ₂ g` by `Λ'`
  have hquotV : ∀ (g : G) (u : O), residue O u = (φ₂ g : ResidueField O) →
      ∀ y : Λ, ρ g (y : V) - u • (y : V) ∈ preimageLattice Λ L := by
    intro g u hu y
    have h1 : ((latticeRep ρ Λ h.stable g y - u • y : Λ) : V) ∈ preimageLattice Λ L := by
      rw [mem_preimageLattice, Submodule.Quotient.mk_sub, ← residue_smul_mk, hu,
        ← reducedRep_mk]
      exact hLquot g _
    simpa using h1
  -- `hLchar`, at the level of `V`: on `Λ'`, `ρ g` differs from `φ₁ g` by `𝔪Λ`
  have hcharV : ∀ (g : G) (w : O), residue O w = (φ₁ g : ResidueField O) →
      ∀ y : Λ, Submodule.Quotient.mk y ∈ L →
        ρ g (y : V) - w • (y : V) ∈ maximalIdeal O • Λ := by
    intro g w hw y hyL
    have h0 : (Submodule.Quotient.mk (latticeRep ρ Λ h.stable g y - w • y) :
        Reduction O V Λ) = 0 := by
      rw [Submodule.Quotient.mk_sub, ← residue_smul_mk, hw, ← reducedRep_mk,
        hLchar g _ hyL]
      exact sub_eq_zero.mpr rfl
    rw [Submodule.Quotient.mk_eq_zero, mem_smul_top_iff] at h0
    simpa using h0
  refine ⟨?_, ?_, ?_⟩
  · -- the new line is one-dimensional
    have hne_bot : reductionImage O (smul_le_preimageLattice Λ L) ≠ ⊥ := by
      intro hbot
      have hcon := (reductionImage_eq_bot _).mp hbot
      -- otherwise `Λ ≤ Λ'`, so `L = ⊤`, contradicting `finrank L = 1`
      obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
      have hπK : algebraMap O K π ≠ 0 := fun h0 =>
        hπ.ne_zero (IsFractionRing.injective O K (by rw [h0, map_zero]))
      have hΛΛ' : Λ ≤ preimageLattice Λ L := by
        intro x hx
        have hπx : π • x ∈ maximalIdeal O • Λ := by
          rw [hπ.maximalIdeal_eq, Submodule.ideal_span_singleton_smul]
          exact Submodule.smul_mem_pointwise_smul x π Λ hx
        have h1 := hcon hπx
        rw [hπ.maximalIdeal_eq, Submodule.ideal_span_singleton_smul] at h1
        obtain ⟨y, hy, hxy⟩ := h1
        have hcancel : y = x := by
          apply smul_right_injective V hπK
          change algebraMap O K π • y = algebraMap O K π • x
          rw [algebraMap_smul, algebraMap_smul]
          exact hxy
        rwa [← hcancel]
      have hLtop : L = ⊤ := by
        rw [eq_top_iff]
        rintro ξ -
        obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ ξ
        exact (mem_preimageLattice y).mp (hΛΛ' y.2)
      rw [hLtop, finrank_top, hdimΛ] at hL₁
      omega
    have hne_top : reductionImage O (smul_le_preimageLattice Λ L) ≠ ⊤ := by
      intro hcon
      have hLne : L ≠ ⊥ := by
        intro hL0
        rw [hL0, finrank_bot] at hL₁
        omega
      obtain ⟨ξ, hξL, hξ0⟩ := Submodule.ne_bot_iff L |>.mp hLne
      obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ ξ
      have hyΛ' : (y : V) ∈ preimageLattice Λ L := (mem_preimageLattice y).mpr hξL
      have hyS : (Submodule.Quotient.mk (⟨(y : V), hyΛ'⟩ : preimageLattice Λ L) :
          Reduction O V (preimageLattice Λ L))
          ∈ reductionImage O (smul_le_preimageLattice Λ L) := by
        rw [hcon]; trivial
      obtain ⟨z, hz𝔪, hd⟩ := (mk_mem_reductionImage _ _).mp hyS
      have h1 : (y : V) - z ∈ maximalIdeal O • Λ :=
        smul_mono_right _ (preimageLattice_le Λ L) hd
      have hy𝔪 : (y : V) ∈ maximalIdeal O • Λ := by
        have hyzz : (y : V) = ((y : V) - z) + z := by abel
        rw [hyzz]
        exact Submodule.add_mem _ h1 hz𝔪
      exact hξ0 ((Submodule.Quotient.mk_eq_zero _).mpr
        ((mem_smul_top_iff _ _ _).mpr hy𝔪))
    have hle : Module.finrank (ResidueField O)
        ↥(reductionImage O (smul_le_preimageLattice Λ L)) ≤ 2 := by
      have h2 := Submodule.finrank_le (reductionImage O (smul_le_preimageLattice Λ L))
      rwa [hdimΛ'] at h2
    have hpos : 0 < Module.finrank (ResidueField O)
        ↥(reductionImage O (smul_le_preimageLattice Λ L)) :=
      Module.finrank_pos_iff.mpr (Submodule.nontrivial_iff_ne_bot.mpr hne_bot)
    have hne2 : Module.finrank (ResidueField O)
        ↥(reductionImage O (smul_le_preimageLattice Λ L)) ≠ 2 := by
      intro h2
      exact hne_top (Submodule.eq_top_of_finrank_eq (by rw [h2, hdimΛ']))
    omega
  · -- `G` acts on the new line through `φ₂`
    intro g x hx
    obtain ⟨ξ, rfl⟩ := hx
    obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ ξ
    obtain ⟨u, hu⟩ := residue_surjective (R := O) (φ₂ g : ResidueField O)
    have hkey : ∀ m ∈ maximalIdeal O • Λ,
        ρ g m - u • m ∈ maximalIdeal O • preimageLattice Λ L := by
      intro m hm
      refine Submodule.smul_induction_on hm ?_ ?_
      · intro a ha n hn
        have hn' : ρ g n - u • n ∈ preimageLattice Λ L := hquotV g u hu ⟨n, hn⟩
        have heq : ρ g (a • n) - u • a • n = a • (ρ g n - u • n) := by
          rw [(ρ g).map_smul_of_tower, smul_comm u a n, smul_sub]
        rw [heq]
        exact Submodule.smul_mem_smul ha hn'
      · intro x y hx hy
        have heq : ρ g (x + y) - u • (x + y)
            = (ρ g x - u • x) + (ρ g y - u • y) := by
          rw [map_add, smul_add]; abel
        rw [heq]
        exact Submodule.add_mem _ hx hy
    have hmem : ρ g (m : V) - u • (m : V) ∈ maximalIdeal O • preimageLattice Λ L :=
      hkey _ m.2
    rw [reductionMap_mk, reducedRep_mk, ← hu, residue_smul_mk, ← sub_eq_zero,
      ← Submodule.Quotient.mk_sub, Submodule.Quotient.mk_eq_zero, mem_smul_top_iff]
    simpa using hmem
  · -- the quotient by the new line carries `φ₁`
    intro g x
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    obtain ⟨w, hw⟩ := residue_surjective (R := O) (φ₁ g : ResidueField O)
    have hyΛ : (y : V) ∈ Λ := preimageLattice_le Λ L y.2
    have hm : ρ g (y : V) - w • (y : V) ∈ maximalIdeal O • Λ :=
      hcharV g w hw ⟨(y : V), hyΛ⟩ ((mem_preimageLattice _).mp y.2)
    rw [reducedRep_mk, ← hw, residue_smul_mk, ← Submodule.Quotient.mk_sub]
    exact (mk_mem_reductionImage _ _).mpr ⟨_, hm, by simp⟩

omit [FiniteDimensional K V] in
/-- The `∃`-packaged form of `preimageLattice_extension_spec`: passing to the
neighbor lattice swaps sub and quotient. -/
theorem isExtensionOf_preimageLattice
    (hdim : Module.finrank K V = 2)
    {Λ : Submodule O V} (h : IsStableLattice ρ Λ)
    {φ₁ φ₂ : G →* (ResidueField O)ˣ}
    {L : Submodule (ResidueField O) (Reduction O V Λ)}
    (hL₁ : Module.finrank (ResidueField O) L = 1)
    (hLchar : ∀ g : G, ∀ x ∈ L,
      reducedRep ρ Λ h.stable g x = (φ₁ g : ResidueField O) • x)
    (hLquot : ∀ g : G, ∀ x,
      reducedRep ρ Λ h.stable g x - (φ₂ g : ResidueField O) • x ∈ L)
    (hstab : Stabilizes ρ (preimageLattice Λ L)) :
    IsExtensionOf (reducedRep ρ (preimageLattice Λ L) hstab) φ₂ φ₁ :=
  have s := preimageLattice_extension_spec hdim h hL₁ hLchar hLquot hstab
  ⟨_, s.1, s.2.1, s.2.2⟩

/-! ## 7. Independence of the lattice (Brauer–Nesbitt) -/

omit [FiniteDimensional K V] in
/-- Descent step for the independence of the semisimplification: it passes
from a stable lattice `Θ` down to any stable sub-lattice `Λ'' ≤ Θ` not
contained in `𝔪Θ`, by induction on `s` with `𝔪^s Θ ≤ Λ''`.  Each step replaces
`Θ` by the neighbor `Λ'' ⊔ 𝔪Θ` and applies the key computation
`isExtensionOf_preimageLattice`. -/
theorem hasSemisimplification_of_le {ρ : Representation K G V}
    (hdim : Module.finrank K V = 2) :
    ∀ (s : ℕ) {Λ'' Θ : Submodule O V} (hc : IsStableLattice ρ Λ'')
      (hΘ : IsStableLattice ρ Θ), Λ'' ≤ Θ → ¬ Λ'' ≤ maximalIdeal O • Θ →
      maximalIdeal O ^ s • Θ ≤ Λ'' →
      ∀ {φ₁ φ₂ : G →* (ResidueField O)ˣ},
        HasSemisimplification (reducedRep ρ Θ hΘ.stable) φ₁ φ₂ →
        HasSemisimplification (reducedRep ρ Λ'' hc.stable) φ₁ φ₂ := by
  intro s
  induction s with
  | zero =>
    intro Λ'' Θ hc hΘ hle hnsub hpow φ₁ φ₂ hss
    rw [pow_zero, Ideal.one_eq_top, Submodule.top_smul] at hpow
    have heq : Λ'' = Θ := le_antisymm hle hpow
    subst heq
    exact hss
  | succ n ih =>
    intro Λ'' Θ hc hΘ hle hnsub hpow φ₁ φ₂ hss
    haveI := hΘ.isLattice
    by_cases heq : Λ'' = Θ
    · subst heq; exact hss
    have hdimΘ : Module.finrank (ResidueField O) (Reduction O V Θ) = 2 := by
      rw [finrank_reduction (K := K) Θ, hdim]
    haveI : FiniteDimensional (ResidueField O) (Reduction O V Θ) :=
      Module.finite_of_finrank_pos (by omega)
    -- the image of `Λ''` in the reduction of `Θ` is a stable line
    have hne_bot : reductionImage O hle ≠ ⊥ := fun hb =>
      hnsub ((reductionImage_eq_bot hle).mp hb)
    have hne_top : reductionImage O hle ≠ ⊤ := by
      intro ht
      have hsup := (reductionImage_eq_top hle).mp ht
      have hiter : ∀ k : ℕ, Θ ≤ Λ'' ⊔ maximalIdeal O ^ k • Θ := by
        intro k
        induction k with
        | zero =>
          rw [pow_zero, Ideal.one_eq_top, Submodule.top_smul]
          exact le_sup_right
        | succ m ihm =>
          refine ihm.trans ?_
          have h1 : maximalIdeal O ^ m • Θ
              ≤ maximalIdeal O ^ m • (Λ'' ⊔ maximalIdeal O • Θ) :=
            smul_mono_right _ hsup.ge
          refine sup_le le_sup_left (h1.trans ?_)
          rw [Submodule.smul_sup]
          refine sup_le (le_sup_of_le_left Submodule.smul_le_right) ?_
          rw [← Submodule.mul_smul, ← pow_succ]
          exact le_sup_right
      have hΘΛ : Θ ≤ Λ'' := (hiter (n + 1)).trans (sup_le le_rfl hpow)
      exact heq (le_antisymm hle hΘΛ)
    have hL1 : Module.finrank (ResidueField O) ↥(reductionImage O hle) = 1 := by
      have hle2 := Submodule.finrank_le (reductionImage O hle)
      rw [hdimΘ] at hle2
      have hpos : 0 < Module.finrank (ResidueField O) ↥(reductionImage O hle) :=
        Module.finrank_pos_iff.mpr (Submodule.nontrivial_iff_ne_bot.mpr hne_bot)
      have hne2 : Module.finrank (ResidueField O) ↥(reductionImage O hle) ≠ 2 :=
        fun h2 => hne_top (Submodule.eq_top_of_finrank_eq (by rw [h2, hdimΘ]))
      omega
    have hstabL : ∀ g : G, (reductionImage O hle).map (reducedRep ρ Θ hΘ.stable g)
        ≤ reductionImage O hle := by
      rintro g ξ ⟨η, ⟨ζ, rfl⟩, rfl⟩
      obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ ζ
      refine ⟨Submodule.Quotient.mk (latticeRep ρ Λ'' hc.stable g z), ?_⟩
      rw [reductionMap_mk, reductionMap_mk, reducedRep_mk]
      exact congrArg Submodule.Quotient.mk (Subtype.ext rfl)
    -- the line realizes the two characters, in one of the two orders
    have hres : ((∀ g : G, ∀ x ∈ reductionImage O hle,
          reducedRep ρ Θ hΘ.stable g x = (φ₁ g : ResidueField O) • x) ∧
        (∀ g : G, ∀ x, reducedRep ρ Θ hΘ.stable g x
          - (φ₂ g : ResidueField O) • x ∈ reductionImage O hle)) ∨
        ((∀ g : G, ∀ x ∈ reductionImage O hle,
          reducedRep ρ Θ hΘ.stable g x = (φ₂ g : ResidueField O) • x) ∧
        (∀ g : G, ∀ x, reducedRep ρ Θ hΘ.stable g x
          - (φ₁ g : ResidueField O) • x ∈ reductionImage O hle)) := by
      cases hss with
      | inl hext => exact isExtensionOf_along_stable_line hdimΘ hext hL1 hstabL
      | inr hext => exact (isExtensionOf_along_stable_line hdimΘ hext hL1 hstabL).symm
    -- step to the intermediate lattice `Λ'' ⊔ 𝔪Θ` and recurse
    have hstab' : Stabilizes ρ (preimageLattice Θ (reductionImage O hle)) :=
      stabilizes_preimageLattice hΘ.stable hstabL
    have hΘ₁ : IsStableLattice ρ (preimageLattice Θ (reductionImage O hle)) :=
      ⟨isLattice_preimageLattice (K := K) Θ _, hstab'⟩
    have hpre : preimageLattice Θ (reductionImage O hle) = Λ'' ⊔ maximalIdeal O • Θ :=
      preimageLattice_reductionImage hle
    have hle₁ : Λ'' ≤ preimageLattice Θ (reductionImage O hle) := by
      rw [hpre]; exact le_sup_left
    have hnsub₁ : ¬ Λ'' ≤ maximalIdeal O • preimageLattice Θ (reductionImage O hle) :=
      fun hcon => hnsub (hcon.trans (smul_mono_right _ (preimageLattice_le Θ _)))
    have hpow₁ : maximalIdeal O ^ n • preimageLattice Θ (reductionImage O hle) ≤ Λ'' := by
      rw [hpre, Submodule.smul_sup]
      refine sup_le Submodule.smul_le_right ?_
      rw [← Submodule.mul_smul, ← pow_succ]
      exact hpow
    have hssΘ₁ : HasSemisimplification
        (reducedRep ρ (preimageLattice Θ (reductionImage O hle)) hΘ₁.stable) φ₁ φ₂ := by
      cases hres with
      | inl hre =>
        exact Or.inr (isExtensionOf_preimageLattice hdim hΘ hL1 hre.1 hre.2 hΘ₁.stable)
      | inr hre =>
        exact Or.inl (isExtensionOf_preimageLattice hdim hΘ hL1 hre.1 hre.2 hΘ₁.stable)
    exact ih hc hΘ₁ hle₁ hnsub₁ hpow₁ hssΘ₁

omit [FiniteDimensional K V] in
/-- Brauer–Nesbitt, 2-dimensional statement-level version: the
semisimplification of the reduction is independent of the choice of stable
lattice.  (Proved by connecting any two stable lattices through a chain of
neighbors, each step of which swaps the two characters by
`isExtensionOf_preimageLattice`; no character theory is needed.)  Slop proof
of `StableLattice.hasSemisimplification_independent_of_lattice` in
`FLT.KnownIn1980s.Ribet_Lemma.Defs`. -/
theorem hasSemisimplification_independent_of_lattice_slop
    (ρ : Representation K G V) (hdim : Module.finrank K V = 2)
    {Λ Λ' : Submodule O V}
    (h : IsStableLattice ρ Λ) (h' : IsStableLattice ρ Λ')
    (φ₁ φ₂ : G →* (ResidueField O)ˣ)
    (hss : HasSemisimplification (reducedRep ρ Λ h.stable) φ₁ φ₂) :
    HasSemisimplification (reducedRep ρ Λ' h'.stable) φ₁ φ₂ := by
  classical
  haveI := h.isLattice
  haveI := h'.isLattice
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have h𝔪pow : ∀ (j : ℕ) (N : Submodule O V),
      maximalIdeal O ^ j • N = (π ^ j) • N := by
    intro j N
    rw [hπ.maximalIdeal_eq, Ideal.span_singleton_pow,
      Submodule.ideal_span_singleton_smul]
  have hunit : ∀ (u₀ : Oˣ) (N : Submodule O V), (u₀ : O) • N = N := by
    intro u₀ N
    refine le_antisymm ?_ fun x hx => ?_
    · rintro _ ⟨y, hy, rfl⟩
      exact N.smul_mem _ hy
    · refine ⟨(u₀⁻¹ : Oˣ) • x, N.smul_mem _ hx, ?_⟩
      change (u₀ : O) • ((u₀⁻¹ : Oˣ) • x) = x
      rw [Units.smul_def, smul_smul]
      simp
  -- scale `Λ'` into `Λ`
  obtain ⟨a, ha0, hale⟩ := Submodule.IsLattice.exists_smul_le (K := K) Λ Λ'
  have hc : IsStableLattice ρ (a • Λ') :=
    ⟨Submodule.IsLattice.smul_of_ne_zero (K := K) Λ' ha0, h'.stable.smul a⟩
  -- a nonzero element of `a • Λ'`, to bound the normalization exponent
  haveI hΛ'nt : Nontrivial ↥Λ' := Module.nontrivial_of_finrank_pos (R := O)
    (by rw [Submodule.IsLattice.finrank_eq (K := K) Λ', hdim]; omega)
  obtain ⟨⟨v, hv⟩, hv0⟩ := exists_ne (0 : ↥Λ')
  have hvV : v ≠ 0 := fun h0 => hv0 (Subtype.ext h0)
  have haK : algebraMap O K a ≠ 0 := fun h0 =>
    ha0 (IsFractionRing.injective O K (by rw [h0, map_zero]))
  have hav : a • v ≠ 0 := by
    rw [← algebraMap_smul K a v]
    exact smul_ne_zero haK hvV
  have hbdd : ∃ k, ¬ (a • Λ' : Submodule O V) ≤ maximalIdeal O ^ k • Λ := by
    by_contra hall
    push Not at hall
    have havΛ : a • v ∈ Λ := hale (Submodule.smul_mem_pointwise_smul v a Λ' hv)
    have hzero : (⟨a • v, havΛ⟩ : ↥Λ) = 0 := by
      refine IsHausdorff.haus (inferInstance : IsHausdorff (maximalIdeal O) ↥Λ)
        _ fun n => ?_
      rw [SModEq.zero, mem_smul_top_iff]
      exact hall n (Submodule.smul_mem_pointwise_smul v a Λ' hv)
    exact hav (by simpa using congrArg Subtype.val hzero)
  -- the largest `j` with `a • Λ' ≤ 𝔪^j Λ`; then normalize against `Θ := π^j Λ`
  have hkpos : Nat.find hbdd ≠ 0 := by
    intro h0
    apply Nat.find_spec hbdd
    rw [h0, pow_zero, Ideal.one_eq_top, Submodule.top_smul]
    exact hale
  obtain ⟨j, hjk⟩ := Nat.exists_eq_succ_of_ne_zero hkpos
  have hlej : (a • Λ' : Submodule O V) ≤ maximalIdeal O ^ j • Λ :=
    not_not.mp (Nat.find_min hbdd (by omega))
  have hΘlat : IsStableLattice ρ ((π ^ j) • Λ) :=
    ⟨Submodule.IsLattice.smul_of_ne_zero (K := K) Λ (pow_ne_zero _ hπ.ne_zero),
      h.stable.smul _⟩
  obtain ⟨e, he⟩ := reducedRep_smul_equiv ρ Λ h.stable (pow_ne_zero j hπ.ne_zero)
  have hssΘ : HasSemisimplification
      (reducedRep ρ ((π ^ j) • Λ) hΘlat.stable) φ₁ φ₂ := hss.congr e he
  have hle'' : (a • Λ' : Submodule O V) ≤ (π ^ j) • Λ := by
    rw [← h𝔪pow]; exact hlej
  have hnsub'' : ¬ (a • Λ' : Submodule O V) ≤ maximalIdeal O • ((π ^ j) • Λ) := by
    intro hcon
    apply Nat.find_spec hbdd
    rw [hjk]
    have hΘeq : maximalIdeal O • ((π ^ j) • Λ) = maximalIdeal O ^ (j + 1) • Λ := by
      rw [← h𝔪pow, ← Submodule.mul_smul, ← pow_succ']
    rwa [hΘeq] at hcon
  haveI := hc.isLattice
  haveI := hΘlat.isLattice
  obtain ⟨b, hb0, hble⟩ :=
    Submodule.IsLattice.exists_smul_le (K := K) (a • Λ') ((π ^ j) • Λ)
  obtain ⟨s, u, hbu⟩ := IsDiscreteValuationRing.associated_pow_irreducible hb0 hπ
  have hpow'' : maximalIdeal O ^ s • ((π ^ j) • Λ) ≤ (a • Λ' : Submodule O V) := by
    rw [h𝔪pow, ← hbu, mul_smul, hunit u]
    exact hble
  have hssc : HasSemisimplification (reducedRep ρ (a • Λ') hc.stable) φ₁ φ₂ :=
    hasSemisimplification_of_le hdim s hc hΘlat hle'' hnsub'' hpow'' hssΘ
  -- transfer back along the scaling `Λ' ≃ a • Λ'`
  obtain ⟨e', he'⟩ := reducedRep_smul_equiv ρ Λ' h'.stable ha0
  have hcomm' : ∀ (g : G) (y), e'.symm (reducedRep ρ (a • Λ') (h'.stable.smul a) g y)
      = reducedRep ρ Λ' h'.stable g (e'.symm y) := by
    intro g y
    conv_lhs => rw [← e'.apply_symm_apply y]
    rw [← he' g (e'.symm y), e'.symm_apply_apply]
  exact hssc.congr e'.symm hcomm'

end StableLattice
