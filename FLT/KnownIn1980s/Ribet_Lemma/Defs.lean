/-
Copyright (c) 2026 Zachary Feng, Bryan Hu, Y. Samanda Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zachary Feng, Bryan Hu, Y. Samanda Zhang
-/
module

public import Mathlib.Algebra.Module.Lattice
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.RepresentationTheory.Irreducible
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.Topology.Algebra.Group.Basic

/-!
# Public statements for Ribet's lemma

This file contains the non-slop API for Ribet's lemma
(Ribet, *A modular construction of unramified p-extensions of `Q(μₚ)`*,
Invent. Math. 34 (1976), 151–162; Proposition 2.1, p. 154), together with the
definitions needed to state it.  The proofs live in
`FLT.KnownIn1980s.Ribet_Lemma.Proofs`, which imports the AI-generated
development in `FLT.Slop.Ribet_Lemma`.

Setting: `O` is a DVR with fraction field `K` and residue field `F = O ⧸ 𝔪`,
and `V` is a finite-dimensional `K`-vector space with a representation `ρ` of a
group `G`.  This file provides:

* `StableLattice.IsExtensionOf`, `StableLattice.IsSplitExtensionOf`,
  `StableLattice.HasSemisimplification` — extensions of characters in
  dimension 2 (the semisimplification is phrased as "extension in one of the
  two orders", avoiding a development of semisimplification itself);
* `StableLattice.Reduction O V Λ` — the reduction `Λ ⧸ 𝔪Λ` as a vector space
  over the residue field;
* `StableLattice.Stabilizes ρ Λ` and `StableLattice.IsStableLattice ρ Λ` —
  `G`-stability, and `G`-stable lattices;
* `StableLattice.reducedRep` — the induced representation of `G` on `Λ ⧸ 𝔪Λ`;
* `StableLattice.latticeStabilizer` — the stabilizer of a lattice, as a
  subgroup of `G`;

and the public statements:

* `StableLattice.exists_isStableLattice` — a stable lattice exists when `G` is
  compact and some lattice has open stabilizer;
* `StableLattice.hasSemisimplification_independent_of_lattice` — the
  semisimplification of the reduction does not depend on the stable lattice
  (Brauer–Nesbitt, 2-dimensional statement-level version);
* `StableLattice.ribet_lemma` — Ribet's lemma: for `O` complete and `ρ`
  2-dimensional irreducible with a stable lattice whose reduction has
  semisimplification `φ₁ ⊕ φ₂`, some stable lattice has reduction a
  **non-split** extension with sub `φ₁` and quotient `φ₂`.
-/

@[expose] public section

open Pointwise IsLocalRing

noncomputable section

namespace StableLattice

/-! ## Extensions of characters

For a representation `ρ'` of `G` on a vector space `W` over a field `F` and
characters `φ₁ φ₂ : G →* Fˣ`.  The action on the quotient by a stable line `L`
is encoded by the pointwise condition `ρ' g x - φ₂ g • x ∈ L`, avoiding
quotient-module instances in statements. -/

section Characters

variable {G : Type*} [Group G]
variable {F : Type*} [Field F] {W : Type*} [AddCommGroup W] [Module F W]

/-- `ρ'` admits a stable line `L` on which `G` acts by `φ₁`, with `G` acting by
`φ₂` on the quotient `W ⧸ L`; that is, `ρ'` is an extension of `φ₂` by `φ₁`
(sub `φ₁`, quotient `φ₂`).  The quotient action is encoded as
`ρ' g x - φ₂ g • x ∈ L`. -/
def IsExtensionOf (ρ' : Representation F G W) (φ₁ φ₂ : G →* Fˣ) : Prop :=
  ∃ L : Submodule F W,
    Module.finrank F L = 1 ∧
    (∀ g : G, ∀ x ∈ L, ρ' g x = (φ₁ g : F) • x) ∧
    (∀ g : G, ∀ x : W, ρ' g x - (φ₂ g : F) • x ∈ L)

/-- `ρ'` is a *split* extension with sub `φ₁` and quotient `φ₂`: the stable
line has a stable complement, on which `G` necessarily acts by `φ₂`. -/
def IsSplitExtensionOf (ρ' : Representation F G W) (φ₁ φ₂ : G →* Fˣ) : Prop :=
  ∃ L L' : Submodule F W,
    Module.finrank F L = 1 ∧
    (∀ g : G, ∀ x ∈ L, ρ' g x = (φ₁ g : F) • x) ∧
    (∀ g : G, ∀ x ∈ L', ρ' g x = (φ₂ g : F) • x) ∧
    IsCompl L L'

/-- The semisimplification of `ρ'` is `φ₁ ⊕ φ₂`.  In dimension 2 this holds
iff `ρ'` is an extension in one of the two orders, which we take as the
definition: it is the statement-level stand-in for
"`(ρ')^ss ≅ φ₁ ⊕ φ₂`", avoiding a development of semisimplification. -/
def HasSemisimplification (ρ' : Representation F G W) (φ₁ φ₂ : G →* Fˣ) : Prop :=
  IsExtensionOf ρ' φ₁ φ₂ ∨ IsExtensionOf ρ' φ₂ φ₁

end Characters

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
variable {K : Type*} [Field K] [Algebra O K] [IsFractionRing O K]
variable {V : Type*} [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V]
variable [FiniteDimensional K V]

/-! ## Reduction modulo the maximal ideal -/

variable (O V) in
/-- The reduction of `Λ` modulo the maximal ideal `𝔪` of `O`: the vector space
`Λ ⧸ 𝔪Λ` over the residue field `F = O ⧸ 𝔪`. -/
abbrev Reduction (Λ : Submodule O V) : Type _ :=
  Λ ⧸ (maximalIdeal O • ⊤ : Submodule O Λ)

/-- The residue-field module structure on `Λ ⧸ 𝔪Λ`.  This is Mathlib's
`O ⧸ I`-module instance on `M ⧸ I • ⊤`, rephrased through the definitional
equality `ResidueField O = O ⧸ 𝔪`. -/
instance (Λ : Submodule O V) : Module (ResidueField O) (Reduction O V Λ) :=
  inferInstanceAs
    (Module (O ⧸ maximalIdeal O) (Λ ⧸ (maximalIdeal O • ⊤ : Submodule O Λ)))

/-- The `O`-action on `Λ ⧸ 𝔪Λ` factors through the residue field.  (Needed to
`restrictScalars` subspaces of the reduction back to `O`, as in the
lattice-modification arguments of the development.) -/
instance (Λ : Submodule O V) : IsScalarTower O (ResidueField O) (Reduction O V Λ) :=
  inferInstanceAs
    (IsScalarTower O (O ⧸ maximalIdeal O) (Λ ⧸ (maximalIdeal O • ⊤ : Submodule O Λ)))

/-! ## Group actions: stable lattices and reduced representations -/

variable {G : Type*} [Group G]

/-- The `O`-submodule `Λ` is stable under the representation `ρ`. -/
def Stabilizes (ρ : Representation K G V) (Λ : Submodule O V) : Prop :=
  ∀ g : G, Λ.map ((ρ g).restrictScalars O) = Λ

/-- A `G`-stable `O`-lattice in `(V, ρ)`. -/
structure IsStableLattice (ρ : Representation K G V) (Λ : Submodule O V) : Prop where
  isLattice : Submodule.IsLattice K Λ
  stable : Stabilizes ρ Λ

/-- The `O`-linear representation of `G` on a stable submodule (each `ρ g`
restricts to an `O`-linear automorphism of `Λ`). -/
def latticeRep (ρ : Representation K G V) (Λ : Submodule O V)
    (h : Stabilizes ρ Λ) : Representation O G Λ where
  toFun g := ((ρ g).restrictScalars O).restrict
    fun x hx => (h g).le (Submodule.mem_map_of_mem hx)
  map_one' := by ext x; simp
  map_mul' g₁ g₂ := by ext x; simp

/-- Any `O`-linear map sends `𝔪M` into `𝔪N`. -/
theorem smul_top_le_comap {M N : Type*} [AddCommGroup M] [Module O M]
    [AddCommGroup N] [Module O N] (f : M →ₗ[O] N) :
    (maximalIdeal O • ⊤ : Submodule O M) ≤ (maximalIdeal O • ⊤ : Submodule O N).comap f :=
  Submodule.map_le_iff_le_comap.mp <| by
    rw [Submodule.map_smul'']
    exact smul_mono_right _ le_top

/-- An `O`-linear map between submodules of `V` induces a residue-field-linear
map between their reductions mod `𝔪`. -/
noncomputable def reductionMap {Λ₁ Λ₂ : Submodule O V} (f : Λ₁ →ₗ[O] Λ₂) :
    Reduction O V Λ₁ →ₗ[ResidueField O] Reduction O V Λ₂ where
  toFun := Submodule.mapQ _ _ f (smul_top_le_comap f)
  map_add' _ _ := map_add _ _ _
  map_smul' r x := by
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective r
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    exact congrArg Submodule.Quotient.mk (map_smul f b y)

/-- The reduced representation of `G` on `Λ ⧸ 𝔪Λ` over the residue field,
induced by `latticeRep` on the quotient. -/
noncomputable def reducedRep (ρ : Representation K G V) (Λ : Submodule O V)
    (h : Stabilizes ρ Λ) :
    Representation (ResidueField O) G (Reduction O V Λ) where
  toFun g := reductionMap (latticeRep ρ Λ h g)
  map_one' := LinearMap.ext fun x => by
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    simp [reductionMap, Submodule.mapQ_apply]
  map_mul' g₁ g₂ := LinearMap.ext fun x => by
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    simp [reductionMap, Submodule.mapQ_apply]

/-- The stabilizer of a submodule under `ρ`, as a subgroup of `G`. -/
def latticeStabilizer (ρ : Representation K G V) (Λ : Submodule O V) : Subgroup G where
  carrier := {g | Λ.map ((ρ g).restrictScalars O) = Λ}
  one_mem' := by
    change Λ.map ((ρ 1).restrictScalars O) = Λ
    rw [map_one]
    exact Submodule.map_id Λ
  mul_mem' := by
    intro a b ha hb
    change Λ.map ((ρ (a * b)).restrictScalars O) = Λ
    rw [map_mul,
      show ((ρ a * ρ b).restrictScalars O)
          = ((ρ a).restrictScalars O).comp ((ρ b).restrictScalars O) from rfl,
      Submodule.map_comp, hb, ha]
  inv_mem' := by
    intro a ha
    change Λ.map ((ρ a⁻¹).restrictScalars O) = Λ
    conv_lhs => rw [← ha]
    rw [← Submodule.map_comp,
      show ((ρ a⁻¹).restrictScalars O).comp ((ρ a).restrictScalars O)
          = ((ρ a⁻¹ * ρ a).restrictScalars O) from rfl,
      ← map_mul, inv_mul_cancel, map_one]
    exact Submodule.map_id Λ

/-! ## The public statements -/

omit [IsDomain O] [IsDiscreteValuationRing O] [IsFractionRing O K] [FiniteDimensional K V] in
/-- If `G` is compact and some lattice has open stabilizer, then a `G`-stable
lattice exists.  (Openness of the stabilizer is where continuity of `ρ` would
be used; it is taken as a hypothesis, so the statement is usable without
developing the topology of `GL(V)` over a valued field.) -/
theorem exists_isStableLattice [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] (ρ : Representation K G V)
    (Λ₀ : Submodule O V) [Submodule.IsLattice K Λ₀]
    (hopen : IsOpen (latticeStabilizer ρ Λ₀ : Set G)) :
    ∃ Λ : Submodule O V, IsStableLattice ρ Λ := by
  sorry

omit [FiniteDimensional K V] in
/-- Brauer–Nesbitt, 2-dimensional statement-level version: the
semisimplification of the reduction is independent of the choice of stable
lattice.  This is what makes the hypothesis of Ribet's lemma checkable on any
convenient lattice. -/
theorem hasSemisimplification_independent_of_lattice
    (ρ : Representation K G V) (hdim : Module.finrank K V = 2)
    {Λ Λ' : Submodule O V}
    (h : IsStableLattice ρ Λ) (h' : IsStableLattice ρ Λ')
    (φ₁ φ₂ : G →* (ResidueField O)ˣ)
    (hss : HasSemisimplification (reducedRep ρ Λ h.stable) φ₁ φ₂) :
    HasSemisimplification (reducedRep ρ Λ' h'.stable) φ₁ φ₂ := by
  sorry

omit [FiniteDimensional K V] in
/-- **Ribet's lemma** (Ribet 1976, Proposition 2.1).

`O` a complete DVR, `ρ` a 2-dimensional irreducible representation of `G` over
`K = Frac O`, and `Λ₀` a stable lattice whose reduction has semisimplification
`φ₁ ⊕ φ₂`.  Then there is a stable lattice whose reduction is a **non-split**
extension with sub `φ₁` and quotient `φ₂` — in the matrix form of the paper,
"of the form `(φ₁ *; 0 φ₂)` but not semi-simple".  Applying the theorem with
`φ₁, φ₂` swapped realizes the other ordering, and by
`hasSemisimplification_independent_of_lattice` the hypothesis may be checked
on any single stable lattice.

Compared to the paper, the statement is for an arbitrary complete DVR (Ribet
works over the ring of integers of a finite extension of `ℚ_p`; the proof only
uses completeness), and Ribet's standing hypothesis that `G` leaves some
lattice stable is the explicit argument `Λ₀` here — `exists_isStableLattice`
produces one when `G` is compact and the stabilizer of a lattice is open,
matching the parenthetical remark on p. 154 of the paper. -/
theorem ribet_lemma [IsAdicComplete (maximalIdeal O) O]
    (ρ : Representation K G V) [ρ.IsIrreducible]
    (hdim : Module.finrank K V = 2)
    (Λ₀ : Submodule O V) (h₀ : IsStableLattice ρ Λ₀)
    (φ₁ φ₂ : G →* (ResidueField O)ˣ)
    (hss : HasSemisimplification (reducedRep ρ Λ₀ h₀.stable) φ₁ φ₂) :
    ∃ (Λ : Submodule O V) (h : IsStableLattice ρ Λ),
      IsExtensionOf (reducedRep ρ Λ h.stable) φ₁ φ₂ ∧
      ¬ IsSplitExtensionOf (reducedRep ρ Λ h.stable) φ₁ φ₂ := by
  sorry

end StableLattice

end
