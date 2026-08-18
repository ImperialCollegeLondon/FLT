/-
Copyright (c) 2026 baimurzzin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: baimurzzin
-/
-- NOTE: this file is deliberately in the pre-`module` style, matching `FLT.Slop.Clifford`
-- (PR #1067), which it imports: a `module` file cannot import a non-`module` one.  Once #1067
-- migrates to the module system, convert this file too (`module` + `public import` +
-- `@[expose] public section`); that conversion has been tested and the full project builds.
import FLT.Slop.Clifford
import FLT.Slop.UniqueIndexTwo

/-!
# Two conjugate characters ⟹ the representation is induced

Let `ρ` be a two-dimensional representation of `G` over a field, and let `H` be a normal
subgroup with `G ⧸ H` finite cyclic, such that the restriction `ρ|H` splits as the direct sum
of two distinct `G`-conjugate characters `χ` and `η = ᵃχ`, witnessed by complementary lines `L`
and `M`.  Then `ρ` is induced from a character of the unique index-two subgroup `K` of `G`
containing `H` (namely the stabilizer of `χ`): there is a character `ψ : K →* kˣ` extending `χ`
(given by the `K`-action on the `K`-stable line `L`) and an isomorphism of representations
`Ind_K^G ψ ≅ ρ`.

No evenness hypothesis on `Nat.card (G ⧸ H)` is needed: the splitting data already forces the
stabilizer of `χ` to have index two (`characterStabilizer_index_eq_two_of_splitting`), so the
order of `G ⧸ H` is automatically even.

The induced-form isomorphism itself is `Representation.theorem_1_6_induced_form`
(`FLT.Slop.Clifford`); the group-theoretic input making the index-two subgroup unique — a
finite cyclic group has at most one index-two subgroup — is
`CliffordInduced.index_two_eq_over` (`FLT.Slop.UniqueIndexTwo`).

Combined with the Clifford dichotomy
`Representation.isIrreducible_comp_subtype_or_splitsAsDistinctConjugateCharacters`, this
completes the chain: a two-dimensional irreducible `ρ` whose restriction to `H` is reducible is
induced from a character of an index-two subgroup.
-/

open Subgroup CliffordInduced

namespace Representation

variable {k G V : Type*} [Field k] [Group G] [AddCommGroup V] [Module k V]

/--
If a two-dimensional representation `ρ` restricted to a normal subgroup `H` with `G ⧸ H` finite
cyclic splits as two distinct conjugate characters, then `ρ` is induced from a character `ψ` of
the unique index-two subgroup `K` containing `H`.
-/
theorem conjugate_characters_imp_induced
    (H : Subgroup G) [H.Normal] [Finite (G ⧸ H)] [IsCyclic (G ⧸ H)]
    (ρ : Representation k G V)
    {χ η : H →* kˣ} {L M : Submodule k V} {a : G}
    (hη : η = conjCharacter H χ a) (hχη : χ ≠ η)
    (hLdim : Module.finrank k L = 1) (hMdim : Module.finrank k M = 1)
    (hLM : IsCompl L M) (hχL : ActsByCharacterOn H ρ L χ)
    (hηM : ActsByCharacterOn H ρ M η) :
    ∃ (K : Subgroup G) (hHK : H ≤ K), K.index = 2 ∧
      ∃ (hKstable : ∀ x : K, ∀ ⦃v : V⦄, v ∈ L → ρ (x : G) v ∈ L) (ψ : K →* kˣ),
        ActsByCharacterOn K ρ L ψ ∧ (∀ h : H, ψ ⟨h, hHK h.2⟩ = χ h) ∧
          Nonempty ((Representation.ind K.subtype
            (stableLineRepresentation K ρ L hKstable)).Equiv ρ) := by
  -- the index-two subgroup is the stabilizer of `χ`; its index is two by the splitting data,
  -- and it is the unique such subgroup because `G ⧸ H` is finite cyclic.
  set K := characterStabilizer H χ with hKdef
  have hHK : H ≤ K := subgroup_le_characterStabilizer H χ
  have hKidx : K.index = 2 :=
    characterStabilizer_index_eq_two_of_splitting H ρ hη hχη hLdim hMdim hLM hχL hηM
  have hK_unique : ∀ S : Subgroup G, H ≤ S → S.index = 2 → S = K :=
    fun S hHS hS2 => index_two_eq_over H hHS hHK hS2 hKidx
  obtain ⟨hKstable, ψ, hψchar, hψext, e, _he⟩ :=
    theorem_1_6_induced_form H K ρ hHK hK_unique hη hχη hLdim hMdim hLM hχL hηM
  exact ⟨K, hHK, hKidx, hKstable, ψ, hψchar, hψext, ⟨e⟩⟩

end Representation
