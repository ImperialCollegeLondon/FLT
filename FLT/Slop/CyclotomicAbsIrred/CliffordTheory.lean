/-
Copyright (c) 2026 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/
module

public import Mathlib.RepresentationTheory.Irreducible
public import Mathlib.GroupTheory.GroupAction.ConjAct
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic

/-!
# Clifford theory for two-dimensional representations (quoted from PRs #1067/#1084)

This file contains material **quoted from the unmerged PRs #1067 and #1084**
(`FLT/Slop/Clifford.lean` on those branches).  The definitions and the small
supporting lemmas are copied verbatim (with proofs); the main Clifford-type
dichotomy `Representation.isIrreducible_comp_subtype_or_splitsAsDistinctConjugateCharacters`
is quoted as a statement with a `sorry` proof, since its ~1000-line proof lives in
PR #1067 and will land independently.

**Reconciliation plan**: once PR #1067/#1084 are merged, delete this file and
import `FLT.Slop.Clifford` (or `FLT.KnownIn1980s.RepresentationTheory.Clifford`)
instead; all names and statements here match those PRs exactly.
-/

@[expose] public section

open scoped Pointwise

namespace Representation

variable {k G V : Type*} [Field k] [Group G] [AddCommGroup V] [Module k V]

/--
The subgroup `H` acts on the subspace `L` through the character `χ`.

That is, for every `h : H`, every vector of `L` is an eigenvector for the operator `ρ h`, with
eigenvalue `χ h`.
-/
def ActsByCharacterOn (H : Subgroup G) (ρ : Representation k G V) (L : Submodule k V)
    (χ : H →* kˣ) : Prop :=
  ∀ h : H, ∀ ⦃v : V⦄, v ∈ L → ρ h v = (χ h : k) • v

/--
The restriction of `ρ` to `H` is a direct sum of two characters.

The witnesses are two one-dimensional submodules `L` and `M` of `V`.  The condition
`IsCompl L M` means `L ∩ M = 0` and `L + M = V`, so every vector of `V` has a unique decomposition
as a vector in `L` plus a vector in `M`.  The last two fields say that `H` acts on these two lines
through the characters `χ` and `ψ`.
-/
def SplitsAsCharacters (H : Subgroup G) (ρ : Representation k G V) (χ ψ : H →* kˣ) :
    Prop :=
  ∃ L M : Submodule k V,
    Module.finrank k L = 1 ∧
      Module.finrank k M = 1 ∧
        IsCompl L M ∧ ActsByCharacterOn H ρ L χ ∧ ActsByCharacterOn H ρ M ψ

/--
The conjugate character `(gχ)(h) = χ(g⁻¹hg)`.

Normality of `H` is used by `MulAut.conjNormal` to regard `g⁻¹ * h * g` as an element of `H`,
so that `χ` can be applied to it.
-/
def conjCharacter (H : Subgroup G) [H.Normal] (χ : H →* kˣ) (g : G) : H →* kˣ :=
  χ.comp (MulAut.conjNormal g).symm.toMonoidHom

/--
The restriction of `ρ` to `H` splits as a character plus one of its `G`-conjugates.

This allows the conjugate character to equal the original character; the distinct version below
records the sharper non-scalar alternative.
-/
def SplitsAsConjugateCharacters (H : Subgroup G) [H.Normal]
    (ρ : Representation k G V) : Prop :=
  ∃ χ : H →* kˣ, ∃ g : G, SplitsAsCharacters H ρ χ (conjCharacter H χ g)

/--
The non-scalar splitting alternative: the restriction to `H` is a direct sum
`χ ⊕ gχ`, and the conjugate character `gχ` is not equal to `χ`.
-/
def SplitsAsDistinctConjugateCharacters (H : Subgroup G) [H.Normal]
    (ρ : Representation k G V) : Prop :=
  ∃ χ : H →* kˣ, ∃ g : G,
    conjCharacter H χ g ≠ χ ∧ SplitsAsCharacters H ρ χ (conjCharacter H χ g)

lemma finrank_map_apply_eq (ρ : Representation k G V) (g : G) (L : Submodule k V) :
    Module.finrank k (Submodule.map (ρ g) L) = Module.finrank k L := by
  let e : V ≃ₗ[k] V := LinearEquiv.ofBijective (ρ g) (ρ.apply_bijective g)
  change Module.finrank k (Submodule.map (e : V →ₗ[k] V) L) = Module.finrank k L
  exact LinearEquiv.finrank_map_eq e L

lemma actsByCharacterOn_map_apply (H : Subgroup G) [H.Normal]
    (ρ : Representation k G V) {L : Submodule k V} {χ : H →* kˣ} (g : G)
    (hχL : ActsByCharacterOn H ρ L χ) :
    ActsByCharacterOn H ρ (Submodule.map (ρ g) L) (conjCharacter H χ g) := by
  intro h m hm
  rcases Submodule.mem_map.1 hm with ⟨v, hvL, rfl⟩
  let hgh : H := (MulAut.conjNormal g).symm h
  change ρ h (ρ g v) = (χ hgh : k) • ρ g v
  calc
    ρ h (ρ g v) = ρ ((h : G) * g) v := by
      rw [map_mul, Module.End.mul_apply]
    _ = ρ (g * hgh) v := by
      rw [show (h : G) * g = g * (hgh : G) by
        rw [show (hgh : G) = g⁻¹ * h * g by
          simp [hgh, MulAut.conjNormal_symm_apply]]
        group]
    _ = ρ g (ρ hgh v) := by
      rw [map_mul, Module.End.mul_apply]
    _ = ρ g ((χ hgh : k) • v) := by rw [hχL hgh hvL]
    _ = (χ hgh : k) • ρ g v := by simp

lemma character_eq_of_common_nonzero_vector (H : Subgroup G)
    (ρ : Representation k G V) {L N : Submodule k V} {χ θ : H →* kˣ}
    (hχL : ActsByCharacterOn H ρ L χ) (hθN : ActsByCharacterOn H ρ N θ)
    {v : V} (hvL : v ∈ L) (hvN : v ∈ N) (hv_ne : v ≠ 0) :
    χ = θ := by
  ext h
  have hχ := hχL h hvL
  have hθ := hθN h hvN
  have hscalar : (χ h : k) • v = (θ h : k) • v := hχ.symm.trans hθ
  have hzero : ((χ h : k) - (θ h : k)) • v = 0 := by
    rw [sub_smul, hscalar, sub_self]
  exact sub_eq_zero.mp ((smul_eq_zero.mp hzero).resolve_right hv_ne)

lemma character_line_eq_left_or_right (H : Subgroup G) (ρ : Representation k G V)
    {χ η θ : H →* kˣ} {L M N : Submodule k V}
    (hχη : χ ≠ η) (hLdim : Module.finrank k L = 1)
    (hMdim : Module.finrank k M = 1) (hNdim : Module.finrank k N = 1)
    (hLM : IsCompl L M) (hχL : ActsByCharacterOn H ρ L χ)
    (hηM : ActsByCharacterOn H ρ M η) (hθN : ActsByCharacterOn H ρ N θ) :
    (N = L ∧ θ = χ) ∨ (N = M ∧ θ = η) := by
  classical
  have hN_ne_bot : N ≠ ⊥ := by
    intro hbot
    have hzero : Module.finrank k N = 0 := by rw [hbot, finrank_bot]
    omega
  obtain ⟨n, hnN, hn_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hN_ne_bot
  obtain ⟨x, y, hxy, -⟩ := Submodule.existsUnique_add_of_isCompl hLM n
  have hNatom : IsAtom N := (Submodule.isAtom_iff_finrank_eq_one).2 hNdim
  have hLatom : IsAtom L := (Submodule.isAtom_iff_finrank_eq_one).2 hLdim
  have hMatom : IsAtom M := (Submodule.isAtom_iff_finrank_eq_one).2 hMdim
  by_cases hy : (y : V) = 0
  · have hx_eq_n : (x : V) = n := by
      simpa [hy] using hxy
    have hxN : (x : V) ∈ N := by
      rw [hx_eq_n]
      exact hnN
    have hx_ne : (x : V) ≠ 0 := by
      rw [hx_eq_n]
      exact hn_ne
    have hNL : N = L := by
      by_contra hne
      have hd := hNatom.disjoint_of_ne hLatom hne
      exact hx_ne (Submodule.disjoint_def.mp hd (x : V) hxN x.2)
    have hθχ : θ = χ :=
      (character_eq_of_common_nonzero_vector H ρ hχL hθN x.2 hxN hx_ne).symm
    exact Or.inl ⟨hNL, hθχ⟩
  · by_cases hx : (x : V) = 0
    · have hy_eq_n : (y : V) = n := by
        simpa [hx] using hxy
      have hyN : (y : V) ∈ N := by
        rw [hy_eq_n]
        exact hnN
      have hy_ne : (y : V) ≠ 0 := by
        rw [hy_eq_n]
        exact hn_ne
      have hNM : N = M := by
        by_contra hne
        have hd := hNatom.disjoint_of_ne hMatom hne
        exact hy_ne (Submodule.disjoint_def.mp hd (y : V) hyN y.2)
      have hθη : θ = η :=
        (character_eq_of_common_nonzero_vector H ρ hηM hθN y.2 hyN hy_ne).symm
      exact Or.inr ⟨hNM, hθη⟩
    · exfalso
      have hdiff : ∃ h : H, χ h ≠ η h := by
        by_contra h
        apply hχη
        ext h₀
        exact not_not.mp (by
          intro hne
          exact h ⟨h₀, fun hunit => hne (congrArg Units.val hunit)⟩)
      obtain ⟨h₀, hχη_ne⟩ := hdiff
      have hcomponents :
          (χ h₀ : k) • (x : V) + (η h₀ : k) • (y : V) =
            (θ h₀ : k) • (x : V) + (θ h₀ : k) • (y : V) := by
        calc
          (χ h₀ : k) • (x : V) + (η h₀ : k) • (y : V)
              = ρ h₀ ((x : V) + (y : V)) := by
                rw [map_add, hχL h₀ x.2, hηM h₀ y.2]
          _ = ρ h₀ n := by rw [hxy]
          _ = (θ h₀ : k) • n := hθN h₀ hnN
          _ = (θ h₀ : k) • ((x : V) + (y : V)) := by rw [hxy]
          _ = (θ h₀ : k) • (x : V) + (θ h₀ : k) • (y : V) := by rw [smul_add]
      have hxscalar : (χ h₀ : k) • (x : V) = (θ h₀ : k) • (x : V) := by
        have hp := congrArg (fun z => L.projection M hLM z) hcomponents
        simpa [map_add, map_smul] using hp
      have hχθ : χ h₀ = θ h₀ := by
        apply Units.ext
        have hzero : ((χ h₀ : k) - (θ h₀ : k)) • (x : V) = 0 := by
          rw [sub_smul, hxscalar, sub_self]
        exact sub_eq_zero.mp ((smul_eq_zero.mp hzero).resolve_right hx)
      have hyscalar : (η h₀ : k) • (y : V) = (θ h₀ : k) • (y : V) := by
        have hp := congrArg (fun z => M.projection L hLM.symm z) hcomponents
        simpa [map_add, map_smul] using hp
      have hηθ : η h₀ = θ h₀ := by
        apply Units.ext
        have hzero : ((η h₀ : k) - (θ h₀ : k)) • (y : V) = 0 := by
          rw [sub_smul, hyscalar, sub_self]
        exact sub_eq_zero.mp ((smul_eq_zero.mp hzero).resolve_right hy)
      exact hχη_ne (hχθ.trans hηθ.symm)

/--
The main Clifford-type restriction dichotomy.

Let `ρ` be an irreducible two-dimensional representation of `G` over an algebraically
closed field, and let `H` be a normal subgroup with cyclic quotient.  Then either the
restricted representation `ρ|H` is irreducible, or `ρ|H` splits as the direct sum of a
character `χ` and a distinct conjugate character `gχ`.

**Quoted from PR #1067** (`FLT/Slop/Clifford.lean` +
`FLT/KnownIn1980s/RepresentationTheory/Clifford.lean`), where it is proved in full;
the `sorry` here will disappear when that PR is merged.
-/
theorem isIrreducible_comp_subtype_or_splitsAsDistinctConjugateCharacters [IsAlgClosed k]
    (H : Subgroup G) [H.Normal] [IsCyclic (G ⧸ H)]
    (ρ : Representation k G V) (hV : Module.finrank k V = 2) (hρ : IsIrreducible ρ) :
    IsIrreducible (ρ.comp H.subtype) ∨ SplitsAsDistinctConjugateCharacters H ρ := by
  sorry

end Representation

end
