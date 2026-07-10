/-
Copyright (c) 2026 Y. Samanda Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Y. Samanda Zhang
-/
module

public import Mathlib
public import FLT.Slop.PoitouTate.GKSDefn
public import FLT.Slop.PoitouTate.LocalGlobalMaps
public import FLT.Slop.PoitouTate.DualModule
public import FLT.Slop.PoitouTate.LocalTateDuality
public import FLT.Slop.PoitouTate.KerPairing

/-!
# The statement of Poitou–Tate (blueprint §§2–5)

This file scaffolds the main objects and the nine-term exact sequence of `PTblueprint.tex`.
Throughout, `𝔽` is a finite field, `F` a number field, `S` a finite set of finite places of
`F`, `G_{F,S} = Gal(F_S/F)` the Galois group of the maximal extension unramified outside `S`
(`GKSDefn.lean`), and `M : TopRep 𝔽 G_{F,S}` a finite discrete module.

## Main declarations

* `NumberField.PoitouTate.alpha` — blueprint §2: the restriction maps
  `αᵢ : Hⁱ(G_S, X) → ∏_{v ∈ S} Hⁱ(G_v, X)`, induced by `localToGlobal`.
* `NumberField.PoitouTate.kerAlpha` — blueprint §4: `Kerⁱ(G_S, X) = ker αᵢ`.
* `NumberField.PoitouTate.localDualCompat` — the identification of the restriction of the
  global dual `M*` at `v ∈ S` with the local dual of the restriction of `M` (the blueprint
  glosses this; it needs `#M` to be a unit in `R_{F,S}` so that `K_S` contains the relevant
  roots of unity).
* `NumberField.PoitouTate.beta` — blueprint §3: `βᵢ`, the dual of the restriction map through
  local Tate duality, `βᵢ(x)(g) = ∑_{v ∈ S} ⟨(α_{2-i} g)_v, x_v⟩_v`.
* `NumberField.PoitouTate.kerPairing` — blueprint §4: the pairing
  `Ker²(G_S, M) × Ker¹(G_S, M*) → ℚ/ℤ`, `⟨f, g⟩ = ∑_{v ∈ S} inv_v(x_v)` where
  `x_v = f_v ∪ ψ_v − h_v` for cochain-level choices `f ∪ g = dh`, `res_v f = dφ_v`,
  `res_v g = dψ_v` (using the `H³` lemma of `DualModule.lean`; the cochain-level cup products
  are those of `cupprod.lean`).
* `NumberField.PoitouTate.kerPairing_bijective_left` / `_right` — blueprint Proposition
  ("perfect-pairing"): the pairing is perfect.
* `NumberField.PoitouTate.connectOne` — blueprint §"Connecting maps", steps 1–2: the composite
  `H²(G_S, M*)^∨ ↠ Ker²(G_S, M*)^∨ ≅ Ker¹(G_S, M) ↪ H¹(G_S, M)` (the middle map `psi` comes
  from the perfect pairing applied to `M*`, together with `M** ≅ M`).
* `NumberField.PoitouTate.connectTwo` — the second connecting map
  `H¹(G_S, M*)^∨ → H²(G_S, M)` (the blueprint does not spell out its construction).
* `NumberField.PoitouTate.poitouTateSeq` / `NumberField.PoitouTate.poitouTate` — **the
  Poitou–Tate nine-term exact sequence** (blueprint §"Statement"), as a
  `ComposableArrows (ModuleCat 𝔽) 10`:

  `0 → H⁰(G_S, M) → ∏_S H⁰(G_v, M) → H²(G_S, M*)^∨`
  `  → H¹(G_S, M) → ∏_S H¹(G_v, M) → H¹(G_S, M*)^∨`
  `  → H²(G_S, M) → ∏_S H²(G_v, M) → H⁰(G_S, M*)^∨ → 0`

  with `poitouTate` asserting its exactness (which at the two ends encodes injectivity of
  `α₀` and surjectivity of `β₂`).

## Deviations from the blueprint

* `S` contains only **finite** places; the blueprint's archimedean places are dropped. This is
  justified by `isZero_tateCohomology_of_invertible_card` (the blueprint's red note): for
  `p = char 𝔽 > 2` — stated here as `(2 : 𝔽) ≠ 0` — the (Tate) cohomology of the real places
  vanishes, and `F` totally real is not needed. Likewise `Ĥ⁰` at finite places is plain `H⁰`
  (the Tate modification only matters at archimedean places).
* The blueprint's "`#M` is a unit in `R_{F,S}`" is stated as: every prime `w` with
  `#M ∈ w.asIdeal` lies in `S` (for `M` an `𝔽`-module this says exactly that the primes above
  `p` are in `S`).
* All maps in the sequence are `𝔽`-linear; the pairings into `ℚ/ℤ` are additive (as they must
  be — `ℚ/ℤ` is not an `𝔽`-module).

All theorem bodies are `sorry`; this file only fixes the statements.
-/

@[expose] public section

universe u w

open IsDedekindDomain CategoryTheory CategoryTheory.Limits

namespace NumberField.PoitouTate

/-- **Blueprint §2, red note**: if `#G` is invertible in `k`, then the Tate cohomology of `G`
with coefficients in any `k`-linear representation vanishes in every degree. Applied with
`G = Gal(ℂ/ℝ)` (order `2`) and `k = 𝔽` of odd characteristic, this is the reason the
archimedean places contribute nothing to the Poitou–Tate sequence and are omitted from it. -/
theorem isZero_tateCohomology_of_invertible_card {k G : Type w} [CommRing k] [Group G]
    [Fintype G] (N : Rep k G) [Invertible (Fintype.card G : k)] (i : ℤ) :
    IsZero (tateCohomology N i) :=
  sorry

variable (𝔽 : Type*) [Field 𝔽] [Finite 𝔽] [TopologicalSpace 𝔽] [DiscreteTopology 𝔽]
variable (F : Type u) [Field F] [NumberField F]
variable (S : Finset (HeightOneSpectrum (RingOfIntegers F)))

/-- A `G_{F,S}`-module, restricted to the local Galois group `G_v` along
`localToGlobal F S v`. -/
noncomputable abbrev localRes (X : TopRep 𝔽 (unramifiedOutsideGaloisGroup F S))
    (v : HeightOneSpectrum (RingOfIntegers F)) :
    TopRep 𝔽 (Field.absoluteGaloisGroup (v.adicCompletion F)) :=
  TopRep.res (localToGlobal F S v : _ →* _) X

/-- **Blueprint §2**: the map `αᵢ : Hⁱ(G_S, X) → ∏_{v ∈ S} Hⁱ(G_v, X)` induced by the
restriction maps `localToGlobal`. (For `i = 0` and `v` finite, `Ĥ⁰ = H⁰`, so this is also the
first map of the nine-term sequence; the archimedean `Ĥ⁰`-factors of the blueprint vanish for
odd `p` and are omitted.) -/
noncomputable def alpha (X : TopRep 𝔽 (unramifiedOutsideGaloisGroup F S)) (i : ℕ) :
    ↥(continuousCohomology i X) →ₗ[𝔽]
      ∀ v : S, ↥(continuousCohomology i (localRes 𝔽 F S X v.1)) where
  toFun x v := ContinuousCohomology.map (localToGlobal F S v.1)
    (𝟙 (localRes 𝔽 F S X v.1)) i x
  map_add' x y := by
    funext v
    exact map_add _ x y
  map_smul' c x := by
    funext v
    exact map_smul _ c x

/-- **Blueprint §4**: `Kerⁱ(G_S, X) = ker αᵢ`, the classes locally trivial at every `v ∈ S`. -/
noncomputable def kerAlpha (X : TopRep 𝔽 (unramifiedOutsideGaloisGroup F S)) (i : ℕ) :
    Submodule 𝔽 ↥(continuousCohomology i X) :=
  LinearMap.ker (alpha 𝔽 F S X i)

variable (M : TopRep.{u} 𝔽 (unramifiedOutsideGaloisGroup F S)) [Finite M] [DiscreteTopology M]

/-- Restricting the global dual `M* = Hom_ℤ(M, K_S^×)` to `G_v` agrees with the local dual
`Hom_ℤ(M, K̄ᵥ^×)` of the restriction of `M`. The blueprint glosses this identification; it
holds because `#M` is a unit in `R_{F,S}` (hypothesis `hS`), so `K_S` already contains the
roots of unity in which `M*` takes values, and the embedding `K_S ↪ K̄ᵥ` is the one implicit
in `localToGlobal`. -/
noncomputable def localDualCompat
    (hS : ∀ w : HeightOneSpectrum (RingOfIntegers F),
      (Nat.card ↥M : RingOfIntegers F) ∈ w.asIdeal → w ∈ S)
    (v : S) :
    localRes 𝔽 F S (dualRep 𝔽 F S M) v.1 ≅ localDualRep 𝔽 F v.1 (localRes 𝔽 F S M v.1) :=
  sorry

/-- **Blueprint §3**: the map `βᵢ`, for `i + j = 2`, from the local classes of `M` to the
`ℚ/ℤ`-dual of `Hʲ(G_S, M*)`. It is the dual of the restriction map `α_j` for `M*` through
local Tate duality: `βᵢ(x)(g) = ∑_{v ∈ S} ⟨(α_j g)_v, x_v⟩_v`, where `⟨·,·⟩_v` is
`localTatePairing` transported along `localDualCompat`. The construction lives at the
`ℤ`-linear level (cup products, `cupprod.lean`), so the definition is left as `sorry` at this
`𝔽`-linear statement layer; `𝔽`-linearity holds because the local pairings are `𝔽`-balanced. -/
noncomputable def beta (i j : ℕ) (hij : i + j = 2)
    (hS : ∀ w : HeightOneSpectrum (RingOfIntegers F),
      (Nat.card ↥M : RingOfIntegers F) ∈ w.asIdeal → w ∈ S) :
    (∀ v : S, ↥(continuousCohomology i (localRes 𝔽 F S M v.1))) →ₗ[𝔽]
      CharacterModule ↥(continuousCohomology j (dualRep 𝔽 F S M)) :=
  sorry

/-- **Blueprint §4** ("Explicitly defining the pairing"): the pairing
`Ker²(G_S, M) × Ker¹(G_S, M*) → ℚ/ℤ`. For cocycle representatives `f, g`: `f ∪ g` is
`n`-torsion in `H³(G_S, K_S^×)` hence zero (`eq_zero_of_smul_continuousCohomology_three`),
so `f ∪ g = dh` for a `2`-cochain `h`; local triviality gives `res_v f = dφ_v` and
`res_v g = dψ_v`; then `x_v := f_v ∪ ψ_v − h_v` is a local `2`-cocycle and
`⟨f, g⟩ := ∑_{v ∈ S} inv_v(x_v)`. The cochain-level cup products are those of `cupprod.lean`;
the construction is `NumberField.PoitouTate.kerPairingFun` of `KerPairing.lean`, whose
well-definedness (`pairingValue_congr`) and biadditivity rest on the reciprocity input
`sum_localInvariantMap_map_eq_zero`. -/
noncomputable def kerPairing
    (hS : ∀ w : HeightOneSpectrum (RingOfIntegers F),
      (Nat.card ↥M : RingOfIntegers F) ∈ w.asIdeal → w ∈ S) :
    ↥(kerAlpha 𝔽 F S M 2) →+ ↥(kerAlpha 𝔽 F S (dualRep 𝔽 F S M) 1) →+ AddCircle (1 : ℚ) :=
  AddMonoidHom.mk'
    (fun f => AddMonoidHom.mk'
      (fun g => kerPairingFun hS f.1 g.1
        (fun v => congrFun (LinearMap.mem_ker.mp g.2) v))
      (fun g₁ g₂ => kerPairingFun_add_right hS f.1 g₁.1 g₂.1
        (fun v => congrFun (LinearMap.mem_ker.mp f.2) v)
        (fun v => congrFun (LinearMap.mem_ker.mp g₁.2) v)
        (fun v => congrFun (LinearMap.mem_ker.mp g₂.2) v)
        (fun v => congrFun (LinearMap.mem_ker.mp (g₁ + g₂).2) v)))
    (fun f₁ f₂ => AddMonoidHom.ext fun g =>
      kerPairingFun_add_left hS f₁.1 f₂.1 g.1
        (fun v => congrFun (LinearMap.mem_ker.mp f₁.2) v)
        (fun v => congrFun (LinearMap.mem_ker.mp f₂.2) v)
        (fun v => congrFun (LinearMap.mem_ker.mp (f₁ + f₂).2) v)
        (fun v => congrFun (LinearMap.mem_ker.mp g.2) v))

/-- **Blueprint Proposition "perfect-pairing"**, left half: `⟨·,·⟩` identifies `Ker²(G_S, M)`
with the `ℚ/ℤ`-dual of `Ker¹(G_S, M*)` (nondegeneracy plus finiteness). Needs `p ≠ 2`, stated
as `(2 : 𝔽) ≠ 0`. -/
theorem kerPairing_bijective_left (h2 : (2 : 𝔽) ≠ 0)
    (hS : ∀ w : HeightOneSpectrum (RingOfIntegers F),
      (Nat.card ↥M : RingOfIntegers F) ∈ w.asIdeal → w ∈ S) :
    Function.Bijective (kerPairing 𝔽 F S M hS) :=
  sorry

/-- **Blueprint Proposition "perfect-pairing"**, right half: `⟨·,·⟩` identifies
`Ker¹(G_S, M*)` with the `ℚ/ℤ`-dual of `Ker²(G_S, M)`. -/
theorem kerPairing_bijective_right (h2 : (2 : 𝔽) ≠ 0)
    (hS : ∀ w : HeightOneSpectrum (RingOfIntegers F),
      (Nat.card ↥M : RingOfIntegers F) ∈ w.asIdeal → w ∈ S) :
    Function.Bijective (kerPairing 𝔽 F S M hS).flip :=
  sorry

/-- **Blueprint §"Connecting maps", step 1**: the surjection
`ι^∨ : H²(G_S, M*)^∨ ↠ Ker²(G_S, M*)^∨` dual to the inclusion
`ι : Ker²(G_S, M*) ↪ H²(G_S, M*)`. -/
noncomputable def dualShaInclusion :
    CharacterModule ↥(continuousCohomology 2 (dualRep 𝔽 F S M)) →ₗ[𝔽]
      CharacterModule ↥(kerAlpha 𝔽 F S (dualRep 𝔽 F S M) 2) :=
  CharacterModule.dual (kerAlpha 𝔽 F S (dualRep 𝔽 F S M) 2).subtype

/-- **Blueprint §"Connecting maps", step 2**: the isomorphism
`ψ : Ker²(G_S, M*)^∨ ≅ Ker¹(G_S, M)` induced by the perfect pairing applied to `M*` (together
with the identification `M** ≅ M`, which holds since `#M` is a unit in `R_{F,S}`). -/
noncomputable def psi (h2 : (2 : 𝔽) ≠ 0)
    (hS : ∀ w : HeightOneSpectrum (RingOfIntegers F),
      (Nat.card ↥M : RingOfIntegers F) ∈ w.asIdeal → w ∈ S) :
    CharacterModule ↥(kerAlpha 𝔽 F S (dualRep 𝔽 F S M) 2) →ₗ[𝔽] ↥(kerAlpha 𝔽 F S M 1) :=
  sorry

/-- **Blueprint §"Connecting maps"**: the first connecting map
`H²(G_S, M*)^∨ → H¹(G_S, M)` of the nine-term sequence, the composite
`H²(G_S, M*)^∨ →ι^∨→ Ker²(G_S, M*)^∨ →ψ→ Ker¹(G_S, M) ↪ H¹(G_S, M)`. -/
noncomputable def connectOne (h2 : (2 : 𝔽) ≠ 0)
    (hS : ∀ w : HeightOneSpectrum (RingOfIntegers F),
      (Nat.card ↥M : RingOfIntegers F) ∈ w.asIdeal → w ∈ S) :
    CharacterModule ↥(continuousCohomology 2 (dualRep 𝔽 F S M)) →ₗ[𝔽]
      ↥(continuousCohomology 1 M) :=
  (kerAlpha 𝔽 F S M 1).subtype ∘ₗ psi 𝔽 F S M h2 hS ∘ₗ dualShaInclusion 𝔽 F S M

/-- The second connecting map `H¹(G_S, M*)^∨ → H²(G_S, M)` of the nine-term sequence (the
blueprint does not spell out its construction; it is the analogue of `connectOne` one degree
up, cf. Milne I.4.10). -/
noncomputable def connectTwo (h2 : (2 : 𝔽) ≠ 0)
    (hS : ∀ w : HeightOneSpectrum (RingOfIntegers F),
      (Nat.card ↥M : RingOfIntegers F) ∈ w.asIdeal → w ∈ S) :
    CharacterModule ↥(continuousCohomology 1 (dualRep 𝔽 F S M)) →ₗ[𝔽]
      ↥(continuousCohomology 2 M) :=
  sorry

open ZeroObject in
/-- **Blueprint §"Statement"**: the Poitou–Tate nine-term sequence, as a chain of composable
arrows in `ModuleCat 𝔽` (with zero objects capping both ends, so that exactness encodes
injectivity of `α₀` and surjectivity of `β₂`):

`0 → H⁰(G_S, M) →α₀→ ∏_S H⁰(G_v, M) →β₀→ H²(G_S, M*)^∨`
`  →∂→ H¹(G_S, M) →α₁→ ∏_S H¹(G_v, M) →β₁→ H¹(G_S, M*)^∨`
`  →∂→ H²(G_S, M) →α₂→ ∏_S H²(G_v, M) →β₂→ H⁰(G_S, M*)^∨ → 0` -/
noncomputable def poitouTateSeq (h2 : (2 : 𝔽) ≠ 0)
    (hS : ∀ w : HeightOneSpectrum (RingOfIntegers F),
      (Nat.card ↥M : RingOfIntegers F) ∈ w.asIdeal → w ∈ S) :
    ComposableArrows (ModuleCat 𝔽) 10 :=
  (((((ComposableArrows.mk₅
    (ModuleCat.ofHom (beta 𝔽 F S M 1 1 rfl hS))
    (ModuleCat.ofHom (connectTwo 𝔽 F S M h2 hS))
    (ModuleCat.ofHom (alpha 𝔽 F S M 2))
    (ModuleCat.ofHom (beta 𝔽 F S M 2 0 rfl hS))
    (0 : ModuleCat.of 𝔽
        (CharacterModule ↥(continuousCohomology 0 (dualRep 𝔽 F S M))) ⟶ 0)).precomp
    (ModuleCat.ofHom (alpha 𝔽 F S M 1))).precomp
    (ModuleCat.ofHom (connectOne 𝔽 F S M h2 hS))).precomp
    (ModuleCat.ofHom (beta 𝔽 F S M 0 2 rfl hS))).precomp
    (ModuleCat.ofHom (alpha 𝔽 F S M 0))).precomp
    (0 : (0 : ModuleCat 𝔽) ⟶ ModuleCat.of 𝔽 ↥(continuousCohomology 0 M))

/-- **Poitou–Tate** (blueprint §"Statement"; Milne I.4.10 for `p > 2` over a finite `S`
containing the primes above `p`): the nine-term sequence is exact. -/
theorem poitouTate (h2 : (2 : 𝔽) ≠ 0)
    (hS : ∀ w : HeightOneSpectrum (RingOfIntegers F),
      (Nat.card ↥M : RingOfIntegers F) ∈ w.asIdeal → w ∈ S) :
    (poitouTateSeq 𝔽 F S M h2 hS).Exact :=
  sorry

end NumberField.PoitouTate
