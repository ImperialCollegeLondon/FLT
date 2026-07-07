/-
Copyright (c) 2026 Jack McKoen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McKoen
-/
module

public import FLT.Slop.Clifford

/-!
# Two-dimensional restrictions to a normal subgroup

This file contains a self-contained Lean development for two related statements about a
two-dimensional representation `ρ : Representation k G V`.

The first statement, `main_theorem_1_3`, says that if `H` is normal, `G ⧸ H` is cyclic, and the
restriction of `ρ` to `H` acts by scalar operators through a character `χ : H →* kˣ`, then `ρ`
is not irreducible.  The proof chooses an eigenline for a lift of a generator of `G ⧸ H`; scalar
action of `H` and cyclicity of the quotient make that line stable under all of `G`.

The second statement, `main_theorem_1_8`, is a Clifford-type dichotomy.  If `ρ` is irreducible
and `V` has dimension two, then the restriction to `H` is either irreducible, or it splits as a
direct sum of two distinct `G`-conjugate characters of `H`.

The file works with Mathlib's unbundled `Representation k G V`, i.e. a monoid homomorphism
`G →* V →ₗ[k] V`.  Direct sums of characters are encoded by complementary one-dimensional
submodules rather than by a bundled representation isomorphism.
-/

@[expose] public section

open scoped Pointwise

namespace Representation

variable {k G V : Type*} [Field k] [Group G] [AddCommGroup V] [Module k V]

variable (ρ : Representation k G V)

/--
The main Clifford-type restriction dichotomy for this file.

Let `ρ` be an irreducible two-dimensional representation of `G`, and let `H` be a finite-index
normal subgroup with cyclic quotient.  Then either the restricted representation `ρ|H` is
irreducible, or `ρ|H` splits as the direct sum of a character `χ` and a distinct conjugate
character `gχ`.
-/
theorem isIrreducible_comp_subtype_or_splitsAsDistinctConjugateCharacters [IsAlgClosed k]
    (H : Subgroup G) [H.Normal] [IsCyclic (G ⧸ H)]
    (ρ : Representation k G V) (hV : Module.finrank k V = 2) (hρ : IsIrreducible ρ) :
    IsIrreducible (ρ.comp H.subtype) ∨ SplitsAsDistinctConjugateCharacters H ρ := by
  by_cases hres : IsIrreducible (ρ.comp H.subtype)
  · exact Or.inl hres
  · right
    rcases clifford_splitting_of_not_irreducible_restriction (ρ := ρ) H hV hρ hres with
      ⟨χ, g, hsplit⟩
    refine ⟨χ, g, ?_, hsplit⟩
    intro hsame
    apply main_theorem_1_8_no_equal_character (ρ := ρ) H hV hρ
    refine ⟨χ, ?_⟩
    rcases hsplit with ⟨L, M, hLdim, hMdim, hLM, hL, hM⟩
    refine ⟨L, M, hLdim, hMdim, hLM, hL, ?_⟩
    intro h v hv
    simpa [hsame] using hM h hv

/--
Scalar-restriction non-irreducibility for cyclic quotients.

The hypothesis `hχ` means that every element of `H` acts on all of `V` as the scalar
`χ h`.  In informal representation-theoretic language, this is the equal-character case
`ρ|H = χ ⊕ χ`.  Under the cyclic quotient hypothesis, such a representation has a nonzero proper
`G`-stable line, hence is not irreducible.
-/
theorem not_isIrreducible_of_scalar_restriction_of_finrank_eq_two
    [IsAlgClosed k] (H : Subgroup G) [H.Normal]
    [IsCyclic (G ⧸ H)] (ρ : Representation k G V) (hV : Module.finrank k V = 2)
    (χ : H →* kˣ)
    (hχ : ∀ h : H, ρ h = ((χ h : k) • LinearMap.id : V →ₗ[k] V)) :
    ¬ IsIrreducible ρ :=
  scalar_restriction_not_irreducible (ρ := ρ) H hV χ hχ

end Representation
