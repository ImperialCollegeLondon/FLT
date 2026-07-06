import FLT.KnownIn1980s.Ribet_Lemma.Brauer_Nesbitt

/-!
# Ribet's lemma (Ribet, Invent. Math. 34 (1976), Prop. 2.1)

Sections 7–9, and the goal, of this directory (see the overview in the header
of `stable_lattices.lean`).  In the notation of §1–6:

  Let `O` be a *complete* DVR with fraction field `K` and residue field `F`,
  and `ρ` an irreducible 2-dimensional representation of a group `G` over `K`
  admitting a `G`-stable lattice.  If the reduction of one (equivalently, by
  `hasSemisimplification_independent_of_lattice`, any) stable lattice has
  semisimplification `φ₁ ⊕ φ₂`, then there is a stable lattice whose reduction
  is a *non-split* extension with sub `φ₁` and quotient `φ₂`.  Applying the
  theorem with `φ₁, φ₂` swapped (via `HasSemisimplification.symm`) realizes
  the other ordering.

Contents:

* §7 — lattice modification: the neighbor lattice `preimageLattice Λ L`, the
  key computation that passing to a neighbor swaps sub and quotient, and the
  chain lemma where completeness enters (`exists_stable_line_of_chain`);
* §8 — the statement of Ribet's lemma, `ribet_lemma`;
* §9 — remarks on what is (not) needed where, and alternative proofs.

Conventions: irreducibility is Mathlib's `Representation.IsIrreducible`, i.e.
`IsSimpleOrder (Subrepresentation ρ)`; the elementary reformulation "`V ≠ 0`
and every `G`-stable `K`-subspace is `⊥` or `⊤`" is available as
`OddRep.isIrreducible_iff_forall` in `FLT/KnownIn1980s/absirred.lean`.
Completeness of `O` is `IsAdicComplete (maximalIdeal O) O`; it is genuinely
needed (`exists_stable_line_of_chain`), and §7 is the only place in the
directory where it appears.
-/

open IsLocalRing

namespace StableLattice

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
variable {K : Type*} [Field K] [Algebra O K] [IsFractionRing O K]
variable {V : Type*} [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V]
variable [FiniteDimensional K V]
variable {G : Type*} [Group G]

/-! ## 7. Lattice modification: the engine of the proof

From a stable lattice `Λ` and a stable line `L` in its reduction, pass to the
*neighbor lattice* `preimageLattice Λ L`: the preimage of `L` in `Λ`.  Its
reduction is again 2-dimensional with the same two Jordan–Hölder factors, but
with sub and quotient **swapped** (`isExtensionOf_preimageLattice`).

The proof of `ribet_lemma` walks through neighbors: as long as the reduction
at the current lattice splits, move along the `φ₂`-line — this preserves the
ordering sub-`φ₁`/quotient-`φ₂`.  If the walk never terminated it would be a
"straight" chain (no backtracking), i.e. a geodesic ray in the Bruhat–Tits
tree of `GL₂ K`, whose vertices are homothety classes of lattices (cf. the
docstring of `Mathlib.Algebra.Module.Lattice`); completeness of `O` would turn
it into a `ρ`-stable `K`-line (`exists_stable_line_of_chain`), contradicting
irreducibility.  So the walk terminates, at a lattice whose reduction is the
desired non-split extension.

The character-level facts steering the walk — a stable line carries a
character, and the stable line of a non-split extension is unique — are
`exists_character_of_stable_line` and
`stable_line_unique_of_not_isSplitExtensionOf` in §5.  No matrices are
needed anywhere. -/

section Modification

variable {ρ : Representation K G V}

/-- The preimage in `Λ` (viewed inside `V`) of a subspace `W` of the reduction
`Λ ⧸ 𝔪Λ`.  (Uses the `Module (ResidueField O)` and
`IsScalarTower O (ResidueField O)` instances on `Reduction O V Λ` from §2.) -/
noncomputable def preimageLattice (Λ : Submodule O V)
    (W : Submodule (ResidueField O) (Reduction O V Λ)) : Submodule O V :=
  ((W.restrictScalars O).comap
    (maximalIdeal O • ⊤ : Submodule O Λ).mkQ).map Λ.subtype

theorem preimageLattice_le (Λ : Submodule O V)
    (W : Submodule (ResidueField O) (Reduction O V Λ)) :
    preimageLattice Λ W ≤ Λ := sorry

/-- The neighbor lattice contains `𝔪Λ`. -/
theorem smul_le_preimageLattice (Λ : Submodule O V)
    (W : Submodule (ResidueField O) (Reduction O V Λ)) :
    maximalIdeal O • Λ ≤ preimageLattice Λ W := sorry

/-- The neighbor of a lattice is a lattice (finitely generated since `O` is
noetherian and `preimageLattice Λ W ≤ Λ`; spans since it contains `𝔪Λ`). -/
theorem isLattice_preimageLattice (Λ : Submodule O V) [Submodule.IsLattice K Λ]
    (W : Submodule (ResidueField O) (Reduction O V Λ)) :
    Submodule.IsLattice K (preimageLattice Λ W) := sorry

/-- The neighbor of a stable lattice along a stable subspace is stable. -/
theorem stabilizes_preimageLattice {Λ : Submodule O V} (hΛ : Stabilizes ρ Λ)
    {W : Submodule (ResidueField O) (Reduction O V Λ)}
    (hW : ∀ g : G, W.map (reducedRep ρ Λ hΛ g) ≤ W) :
    Stabilizes ρ (preimageLattice Λ W) := sorry

/-- **Key computation** (moving to a neighbor swaps sub and quotient): if the
reduction of `Λ` is an extension with sub `φ₁` and quotient `φ₂`, realized by
the line `L`, then the reduction of `preimageLattice Λ L` is an extension with
sub `φ₂` and quotient `φ₁`.  (Via the isomorphisms
`(preimageLattice Λ L)/𝔪Λ ≅ L` and
`𝔪Λ/𝔪·(preimageLattice Λ L) ≅ Λ/(preimageLattice Λ L)`; needs equivariant
second/third-isomorphism plumbing for the `Reduction` quotients.

The stability hypothesis `hstab` is derivable from
`stabilizes_preimageLattice` and `hLchar`; it is taken as an argument so that
`reducedRep` can be formed in the statement.) -/
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
    IsExtensionOf (reducedRep ρ (preimageLattice Λ L) hstab) φ₂ φ₁ := sorry

/-- **Where completeness enters.**  A "straight" infinite chain of neighboring
stable lattices (no backtracking: `f (n + 2) ≠ 𝔪 • f n`) yields a `ρ`-stable
`K`-line — which `ribet_lemma` rules out by irreducibility.  The line is
extracted as an `𝔪`-adic limit.  Mathlib has the Hausdorff half
(`IsHausdorff (maximalIdeal O) M` for finite `M` over a noetherian local ring,
in `Mathlib.RingTheory.AdicCompletion.Noetherian`); the completeness half —
finite free modules over an `IsAdicComplete` ring are `IsAdicComplete` — is
missing as of July 2026 and is itself a target. -/
theorem exists_stable_line_of_chain
    [IsAdicComplete (maximalIdeal O) O]
    (hdim : Module.finrank K V = 2)
    (f : ℕ → Submodule O V) (hf : ∀ n, IsStableLattice ρ (f n))
    (hstep : ∀ n, ∃ L : Submodule (ResidueField O) (Reduction O V (f n)),
      Module.finrank (ResidueField O) L = 1 ∧ f (n + 1) = preimageLattice (f n) L)
    (hstraight : ∀ n, f (n + 2) ≠ maximalIdeal O • f n) :
    ∃ W : Submodule K V, Module.finrank K W = 1 ∧ ∀ g : G, W.map (ρ g) ≤ W := sorry

end Modification

/-! ## 8. Ribet's lemma -/

/-- **Ribet's lemma** (Ribet 1976, Proposition 2.1).

`O` a complete DVR, `ρ` a 2-dimensional irreducible representation of `G` over
`K = Frac O`, and `Λ₀` a stable lattice whose reduction has semisimplification
`φ₁ ⊕ φ₂`.  Then there is a stable lattice whose reduction is a **non-split**
extension with sub `φ₁` and quotient `φ₂`.

Proof outline, from §7: normalize so that the reduction of the starting
lattice realizes the ordering sub-`φ₁` — if `hss` provides the other order,
one application of `isExtensionOf_preimageLattice` swaps it.  Then walk along
`φ₂`-lines while the reduction splits.  By `exists_stable_line_of_chain` and
irreducibility the walk terminates, and the terminal lattice witnesses the
conclusion. -/
theorem ribet_lemma [IsAdicComplete (maximalIdeal O) O]
    (ρ : Representation K G V) [ρ.IsIrreducible]
    (hdim : Module.finrank K V = 2)
    (Λ₀ : Submodule O V) (h₀ : IsStableLattice ρ Λ₀)
    (φ₁ φ₂ : G →* (ResidueField O)ˣ)
    (hss : HasSemisimplification (reducedRep ρ Λ₀ h₀.stable) φ₁ φ₂) :
    ∃ (Λ : Submodule O V) (h : IsStableLattice ρ Λ),
      IsExtensionOf (reducedRep ρ Λ h.stable) φ₁ φ₂ ∧
      ¬ IsSplitExtensionOf (reducedRep ρ Λ h.stable) φ₁ φ₂ := sorry

/-! ## 9. Remarks

* Neither §4 (existence of stable lattices) nor §6 (Brauer–Nesbitt) is needed
  for the proof of `ribet_lemma` itself: the hypothesis is anchored to the
  given `Λ₀`, and the walk of §7 tracks the Jordan–Hölder factors
  constructively.  Both are needed to *apply* the lemma as in Ribet's paper:
  §4 produces `Λ₀` (for a continuous representation of a compact group), and
  §6 lets one verify `hss` on any convenient lattice (e.g. from
  characteristic-polynomial data).
* Alternative routes: Ribet's original successive-approximation argument in
  `GL₂ O`, or Bellaïche's proof ("À propos d'un lemme de Ribet", Rend. Sem.
  Mat. Univ. Padova 109 (2003)).  The tree-flavored version of §7 seems the
  most Lean-friendly: it stays inside `Submodule` language and never chooses
  a basis.
-/

end StableLattice
