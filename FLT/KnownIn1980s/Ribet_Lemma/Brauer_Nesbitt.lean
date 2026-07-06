import FLT.KnownIn1980s.Ribet_Lemma.stable_lattices

/-!
# Two-dimensional reductions: extensions of characters, and Brauer–Nesbitt

Sections 5–6 of the Ribet's-lemma directory (see `stable_lattices.lean` §1–4
for the lattice/reduction API, and the directory overview in its header;
`Ribet_Lemma.lean` §7–9 is the goal).

§5.  For a representation `ρ'` of `G` on a vector space `W` over a field `F`
and characters `φ₁ φ₂ : G →* Fˣ`, we define what it means for `ρ'` to be

* an extension with sub `φ₁` and quotient `φ₂` (`StableLattice.IsExtensionOf`),
* a *split* such extension (`StableLattice.IsSplitExtensionOf`),
* of semisimplification `φ₁ ⊕ φ₂` (`StableLattice.HasSemisimplification`) —
  in dimension 2, "the semisimplification is `φ₁ ⊕ φ₂`" is *equivalent* to
  "`ρ'` is an extension in one of the two orders", and we take the latter as
  the definition to avoid developing semisimplification itself,

together with the two elementary facts that steer the walk in the proof of
Ribet's lemma: a stable line carries a character
(`exists_character_of_stable_line`), and the stable line of a non-split
extension is unique (`stable_line_unique_of_not_isSplitExtensionOf`).

§6 states the consequence of the Brauer–Nesbitt theorem relevant here: the
semisimplification of the reduction of a stable lattice does not depend on the
lattice (`hasSemisimplification_independent_of_lattice`).  This is *not* used
in the proof of Ribet's lemma itself, but is needed to apply it — it lets one
verify the semisimplification hypothesis on any convenient lattice; see the
remarks in §9.

## Design decisions

* The action on the quotient by a stable line `L` is encoded by the pointwise
  condition `ρ' g x - φ₂ g • x ∈ L`, avoiding quotient-module instances in
  statements.
* Mathlib (as of July 2026) has `IsSemisimpleRepresentation`
  (`Mathlib.RepresentationTheory.Semisimple`) but neither semisimplification
  nor the Brauer–Nesbitt theorem, so the lattice-independence statement is a
  standalone target here.  Its expected proof: the characteristic polynomial
  of `reducedRep ρ Λ _ g` is the reduction mod `𝔪` of the characteristic
  polynomial of `ρ g` (which has coefficients in `O`), hence is independent of
  `Λ`; in dimension 2 this pins down the pair `{φ₁, φ₂}`.  If a general
  Brauer–Nesbitt lands in Mathlib or elsewhere in FLT first, this should be
  derived from it instead.

Everything whose proof is `sorry` is a stated target.
-/

open IsLocalRing

namespace StableLattice

/-! ## 5. Extensions of characters -/

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

/-- Sanity check for the two definitions above: a split extension is in
particular an extension (write `x = l + l'` and compute
`ρ' g x - φ₂ g • x = (φ₁ g - φ₂ g) • l ∈ L`). -/
theorem IsSplitExtensionOf.isExtensionOf {ρ' : Representation F G W}
    {φ₁ φ₂ : G →* Fˣ} (h : IsSplitExtensionOf ρ' φ₁ φ₂) :
    IsExtensionOf ρ' φ₁ φ₂ := sorry

/-- A stable line carries a character: if `L` is a `G`-stable 1-dimensional
subspace, then `G` acts on `L` through some `φ : G →* Fˣ`.  (Produces the
witnesses for `IsExtensionOf` from lattice-theoretic data.) -/
theorem exists_character_of_stable_line (ρ' : Representation F G W)
    {L : Submodule F W} (hL : Module.finrank F L = 1)
    (hstab : ∀ g : G, L.map (ρ' g) ≤ L) :
    ∃ φ : G →* Fˣ, ∀ g : G, ∀ x ∈ L, ρ' g x = (φ g : F) • x := sorry

/-- The stable line of a *non-split* extension is unique.  (A second stable
line `L'` would satisfy `L ⊓ L' = ⊥`, hence be a complement of `L`; by
`hLquot` the character of `L'` is forced to be `φ₂`, so `L, L'` would split
the extension.  Note that `φ₁ ≠ φ₂` is not needed.)  This is what steers the
walk in the proof of Ribet's lemma: the next lattice is determined. -/
theorem stable_line_unique_of_not_isSplitExtensionOf [FiniteDimensional F W]
    {ρ' : Representation F G W} {φ₁ φ₂ : G →* Fˣ}
    (hdim : Module.finrank F W = 2)
    (hns : ¬ IsSplitExtensionOf ρ' φ₁ φ₂)
    {L : Submodule F W} (hL₁ : Module.finrank F L = 1)
    (hLchar : ∀ g : G, ∀ x ∈ L, ρ' g x = (φ₁ g : F) • x)
    (hLquot : ∀ g : G, ∀ x : W, ρ' g x - (φ₂ g : F) • x ∈ L)
    {L' : Submodule F W} (hL'₁ : Module.finrank F L' = 1)
    (hL'stab : ∀ g : G, L'.map (ρ' g) ≤ L') :
    L' = L := sorry

/-- The semisimplification of `ρ'` is `φ₁ ⊕ φ₂`.  In dimension 2 this holds
iff `ρ'` is an extension in one of the two orders, which we take as the
definition: it is the statement-level stand-in for
"`(ρ')^ss ≅ φ₁ ⊕ φ₂`", avoiding a development of semisimplification. -/
def HasSemisimplification (ρ' : Representation F G W) (φ₁ φ₂ : G →* Fˣ) : Prop :=
  IsExtensionOf ρ' φ₁ φ₂ ∨ IsExtensionOf ρ' φ₂ φ₁

/-- `φ₁ ⊕ φ₂` and `φ₂ ⊕ φ₁` are the same semisimplification. -/
theorem HasSemisimplification.symm {ρ' : Representation F G W} {φ₁ φ₂ : G →* Fˣ}
    (h : HasSemisimplification ρ' φ₁ φ₂) : HasSemisimplification ρ' φ₂ φ₁ :=
  Or.symm h

end Characters

/-! ## 6. Independence of the lattice (Brauer–Nesbitt) -/

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
variable {K : Type*} [Field K] [Algebra O K] [IsFractionRing O K]
variable {V : Type*} [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V]
variable [FiniteDimensional K V]
variable {G : Type*} [Group G]

/-- Brauer–Nesbitt, 2-dimensional statement-level version: the
semisimplification of the reduction is independent of the choice of stable
lattice.  (See the module docstring for the expected proof via characteristic
polynomials.) -/
theorem hasSemisimplification_independent_of_lattice
    (ρ : Representation K G V) (hdim : Module.finrank K V = 2)
    {Λ Λ' : Submodule O V}
    (h : IsStableLattice ρ Λ) (h' : IsStableLattice ρ Λ')
    (φ₁ φ₂ : G →* (ResidueField O)ˣ)
    (hss : HasSemisimplification (reducedRep ρ Λ h.stable) φ₁ φ₂) :
    HasSemisimplification (reducedRep ρ Λ' h'.stable) φ₁ φ₂ := sorry

end StableLattice
