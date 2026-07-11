/-
Copyright (c) 2026 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/
module

public import FLT.Slop.CyclotomicAbsIrred.Assumed
public import FLT.Slop.CyclotomicAbsIrred.TwoLines
public import FLT.Slop.CyclotomicAbsIrred.InvolutionFixedSpace
public import FLT.KnownIn1980s.RepresentationTheory.OddAbsIrred
import Mathlib.LinearAlgebra.Charpoly.BaseChange
import Mathlib.GroupTheory.IndexNormal
import Mathlib.Data.Nat.Totient
import Mathlib.FieldTheory.Galois.Infinite

/-!
# Absolute irreducibility over `ℚ(ζ_ℓ)`

The main theorem (`absolutelyIrreducible_comp_ker_modCycChar`): let `ℓ ≥ 5` be a prime, `k` a
finite field of characteristic `ℓ`, and

  `ρ : Gal(ℚ̄/ℚ) → GL₂(k)`

a continuous representation which is irreducible, flat at `ℓ`, and of cyclotomic determinant.
Then the restriction of `ρ` to `Gal(ℚ̄/ℚ(ζ_ℓ))` — the kernel of the mod-`ℓ` cyclotomic
character — is absolutely irreducible.

This is Theorem 1 of `abs_irred_v2.tex`, whose proof (§3, Steps 1–7) is followed exactly.
Everything is proved here except:

* the four *assumed* statements S1–S4 of `FLT.Slop.CyclotomicAbsIrred.Assumed` (the local
  theorem on flat characters of ramified quadratic extensions of `ℚ_ℓ` — the permanent
  `sorry` —, flatness of stable-line characters, existence of a complex conjugation, and
  total ramification of `ℓ` in `ℚ(ζ_ℓ)`); and
* the Clifford dichotomy quoted from PR #1067
  (`Representation.isIrreducible_comp_subtype_or_splitsAsDistinctConjugateCharacters` and the
  supporting lemma `character_line_eq_left_or_right`, in
  `FLT.Slop.CyclotomicAbsIrred.CliffordTheory`).

The proof, in outline (write `χ` for the mod-`ℓ` cyclotomic character, `H = ker χ`,
`G = Gal(ℚ̄/ℚ)`, `𝕂` for the algebraic closure of `k`, and `I ⊆ G_{ℚ_ℓ}` for inertia):

1. A complex conjugation `c` (S3) has `ρ(c)² = 1` and `det ρ(c) = χ(c) = -1`, so its fixed
   space is a line (`InvolutionFixedSpace`); hence `ρ` is absolutely irreducible
   (PR #1075, `OddRep.isIrreducible_iff_isAbsolutelyIrreducible`, already in the repo).
2. `χ` is surjective (by S4), so `G/H ≅ (ℤ/ℓ)ˣ` is cyclic; if `ρ ⊗ 𝕂` restricted to `H` is
   reducible, the Clifford dichotomy splits it as two distinct characters on complementary
   lines `L ⊕ M`.
3. The stabilizer `S` of `L` in `G` is then a proper subgroup of index 2 containing `H`,
   acting on `L` by a character `ψ`, and every `g ∉ S` swaps `L` and `M` (`TwoLines`).
4. Choosing `τ ∈ I` with `χ(τ)` a generator of `(ℤ/ℓ)ˣ` (possible by S4), we get `τ ∉ S`
   (else `S ⊇ H` and `χ(S) ∋ χ(τ)` would force `S = G`) and `τ² ∈ S`.
5. In the basis `(v₀, ρ(τ)v₀)` one computes `det ρ(τ) = -ψ(τ²)`, so `χ(τ) = -ψ(τ²)` in `𝕂`.
6. The preimage `Δ` of `S` in `G_{ℚ_ℓ}` is open of index 2 and does not contain `I`; by the
   infinite Galois correspondence it is `Gal(ℚ̄_ℓ/K)` for a ramified quadratic `K/ℚ_ℓ`.  The
   character of `Δ` on `L` is flat (S2), so the local theorem (S1) gives
   `ψ(τ²) = χ(τ)^d` for some `0 ≤ d ≤ 2`.
7. Hence `χ(τ) = -χ(τ)^d` in `𝕂ˣ` with `χ(τ)` of order `ℓ - 1 ≥ 4`: each of `d = 0, 1, 2`
   is absurd.
-/

@[expose] public section

open IsDedekindDomain NumberField Module

open scoped TensorProduct

local notation3 "Γ" K:max => Field.absoluteGaloisGroup K

namespace CyclotomicAbsIrred

variable {ℓ : ℕ} [Fact ℓ.Prime]

/-- **Absolute irreducibility over `ℚ(ζ_ℓ)`** (Theorem 1 of `abs_irred_v2.tex`).

Let `ℓ ≥ 5` be a prime, let `k` be a finite field of characteristic `ℓ`, and let
`ρ : Gal(ℚ̄/ℚ) → Aut_k(V)` be a continuous representation on a two-dimensional `k`-vector
space `V` which is irreducible, flat at `ℓ`, and of mod-`ℓ` cyclotomic determinant.  Then
the restriction of `ρ` to the kernel of the mod-`ℓ` cyclotomic character — that is, to
`Gal(ℚ̄/ℚ(ζ_ℓ))` — is absolutely irreducible. -/
theorem absolutelyIrreducible_comp_ker_modCycChar
    (hℓ5 : 5 ≤ ℓ)
    {k : Type} [Field k] [Finite k] [CharP k ℓ] [TopologicalSpace k] [DiscreteTopology k]
    {V : Type} [AddCommGroup V] [Module k V] [Module.Finite k V] [Module.Free k V]
    (hdim : Module.finrank k V = 2)
    (ρ : GaloisRep ℚ k V)
    (hirr : ρ.IsIrreducible)
    (hflat : ρ.IsFlatAt (ellPlace ℓ))
    (hdet : ∀ g, ρ.det g =
      ZMod.castHom (dvd_refl ℓ) k ((modCycChar ℓ ℚ g : (ZMod ℓ)ˣ) : ZMod ℓ)) :
    Slop.OddRep.IsAbsolutelyIrreducible
      (ρ.toRepresentation.comp (modCycChar ℓ ℚ).ker.subtype) := by
  classical
  have hℓ2 : (2 : ℕ) < ℓ := by omega
  have hchark2 : (2 : k) ≠ 0 := by
    intro h
    have h2 := (CharP.cast_eq_zero_iff k ℓ 2).mp (by exact_mod_cast h)
    have := Nat.le_of_dvd (by norm_num) h2
    omega
  -- notation
  set χ : Γ ℚ →* (ZMod ℓ)ˣ := modCycChar ℓ ℚ with hχdef
  set H : Subgroup (Γ ℚ) := χ.ker with hHdef
  set ι : Γ (Qell ℓ) →ₜ* Γ ℚ :=
    Field.absoluteGaloisGroup.map (algebraMap ℚ (Qell ℓ)) with hιdef
  -- surjectivity of the cyclotomic character, from S4 (total ramification)
  have hχsurj : Function.Surjective χ := by
    intro u
    have hmem : u ∈ Subgroup.map (χ.comp ι.toMonoidHom) (localInertiaGroup (ellPlace ℓ)) := by
      rw [modCycChar_image_localInertia ℓ]
      exact Subgroup.mem_top u
    obtain ⟨σ, -, rfl⟩ := hmem
    exact ⟨ι σ, rfl⟩
  -- the quotient by `H` is cyclic (isomorphic to `(ℤ/ℓ)ˣ`) and finite
  let e : Γ ℚ ⧸ H ≃* (ZMod ℓ)ˣ := QuotientGroup.quotientKerEquivOfSurjective χ hχsurj
  haveI : Finite (Γ ℚ ⧸ H) := Finite.of_equiv _ e.symm.toEquiv
  haveI : IsCyclic (Γ ℚ ⧸ H) := isCyclic_of_surjective e.symm.toMonoidHom e.symm.surjective
  -- Step 1: `ρ` is absolutely irreducible, via a complex conjugation (S3)
  obtain ⟨c, hc2, hcχ⟩ := exists_complex_conjugation ℓ
  have hdet_c : LinearMap.det (ρ.toRepresentation c) = -1 := by
    have h1 : ρ.det c = LinearMap.det (ρ.toRepresentation c) := rfl
    rw [← h1, hdet c, hcχ]
    simp
  have hinv_c : ρ.toRepresentation c * ρ.toRepresentation c = 1 := by
    rw [← map_mul, ← pow_two, hc2, map_one]
  have heig : finrank k (Module.End.eigenspace (ρ.toRepresentation c) 1) = 1 :=
    finrank_eigenspace_one_eq_one_of_involution _ hdim hchark2 hinv_c hdet_c
  have habs : Slop.OddRep.IsAbsolutelyIrreducible ρ.toRepresentation :=
    (OddRep.isIrreducible_iff_isAbsolutelyIrreducible ρ.toRepresentation heig).mp hirr
  -- the base-changed representation
  have hρbar_irr : (Slop.OddRep.baseChange (AlgebraicClosure k) ρ.toRepresentation).IsIrreducible :=
    habs
  have hdim2 : finrank (AlgebraicClosure k) (AlgebraicClosure k ⊗[k] V) = 2 := by
    rw [Module.finrank_baseChange, hdim]
  -- restriction commutes with base change, so it suffices to prove irreducibility of
  -- the base change restricted to `H`
  have hbc_comp : Slop.OddRep.baseChange (AlgebraicClosure k)
      (ρ.toRepresentation.comp H.subtype) =
      (Slop.OddRep.baseChange (AlgebraicClosure k) ρ.toRepresentation).comp H.subtype := by
    ext σ v
    rfl
  change (Slop.OddRep.baseChange (AlgebraicClosure k)
    (ρ.toRepresentation.comp H.subtype)).IsIrreducible
  rw [hbc_comp]
  -- Step 2: the Clifford dichotomy (quoted from PR #1067)
  rcases Representation.isIrreducible_comp_subtype_or_splitsAsDistinctConjugateCharacters
    H (Slop.OddRep.baseChange (AlgebraicClosure k) ρ.toRepresentation) hdim2 hρbar_irr with
    hgoal | hsplit
  · exact hgoal
  exfalso
  obtain ⟨χ₁, a, hne, L, M, hLdim, hMdim, hLM, hχL, hηM⟩ := hsplit
  set ρbar : Representation (AlgebraicClosure k) (Γ ℚ) (AlgebraicClosure k ⊗[k] V) :=
    Slop.OddRep.baseChange (AlgebraicClosure k) ρ.toRepresentation with hρbardef
  set η : H →* (AlgebraicClosure k)ˣ := Representation.conjCharacter H χ₁ a with hηdef
  have hχη : χ₁ ≠ η := hne.symm
  -- Step 3: the stabilizer `S` of the line `L` has index 2, contains `H`, and acts on `L`
  -- by a character `ψ`
  set S : Subgroup (Γ ℚ) := lineStabilizer ρbar L with hSdef
  have hHS : H ≤ S := le_lineStabilizer_of_actsByCharacterOn hχL
  have hSne : S ≠ ⊤ := lineStabilizer_ne_top hρbar_irr hLdim hdim2
  have hSidx : S.index = 2 := index_lineStabilizer_eq_two hχη hLdim hMdim hLM hχL hηM hSne
  obtain ⟨v₀, hv₀, hspan⟩ := exists_span_singleton hLdim
  set ψ : S →* (AlgebraicClosure k)ˣ := lineCharacter ρbar hspan hv₀ with hψdef
  have hψacts : Representation.ActsByCharacterOn S ρbar L ψ :=
    actsByCharacterOn_lineCharacter ρbar hspan hv₀
  -- Step 4: a well-chosen element of inertia: `τ ∈ I` with `χ(τ)` a generator of `(ℤ/ℓ)ˣ`
  obtain ⟨g₀, hg₀gen⟩ := IsCyclic.exists_generator (α := (ZMod ℓ)ˣ)
  have hg₀ord : orderOf g₀ = ℓ - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg₀gen, Nat.card_eq_fintype_card,
      ZMod.card_units_eq_totient, Nat.totient_prime (Fact.out : ℓ.Prime)]
  obtain ⟨τ, hτI, hτχ⟩ : ∃ τ ∈ localInertiaGroup (ellPlace ℓ), χ (ι τ) = g₀ := by
    have hmem : g₀ ∈ Subgroup.map (χ.comp ι.toMonoidHom) (localInertiaGroup (ellPlace ℓ)) := by
      rw [modCycChar_image_localInertia ℓ]
      exact Subgroup.mem_top g₀
    obtain ⟨τ, hτ, hτeq⟩ := hmem
    exact ⟨τ, hτ, hτeq⟩
  -- `τ̄ := ι τ` is not in `S` ...
  have hτS : ι τ ∉ S := by
    intro hmem
    apply hSne
    have hmapS : Subgroup.map χ S = ⊤ := by
      refine top_unique fun u _ => ?_
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hg₀gen u)
      exact Subgroup.zpow_mem _ (Subgroup.mem_map.mpr ⟨ι τ, hmem, hτχ⟩) n
    have hcomap := Subgroup.comap_map_eq χ S
    rw [hmapS, Subgroup.comap_top, sup_eq_left.mpr hHS] at hcomap
    exact hcomap.symm
  -- ... but its square is
  have hτ2S : (ι τ) ^ 2 ∈ S := Subgroup.sq_mem_of_index_two hSidx (ι τ)
  -- Step 5: the determinant computation gives `χ(τ) = -ψ(τ²)` in `𝕂 := AlgebraicClosure k`
  have hstar : (ZMod.castHom (dvd_refl ℓ) (AlgebraicClosure k) ((χ (ι τ) : (ZMod ℓ)ˣ) : ZMod ℓ))
      = -((ψ ⟨(ι τ) ^ 2, hτ2S⟩ : (AlgebraicClosure k)ˣ) : AlgebraicClosure k) := by
    have hdetτ : LinearMap.det (ρbar (ι τ)) =
        -(lineScalar ρbar hspan hv₀ ⟨(ι τ) ^ 2, hτ2S⟩) :=
      det_eq_neg_lineScalar_sq hχη hLdim hMdim hLM hχL hηM hdim2 hspan hv₀ hτS hτ2S
    have hbc : LinearMap.det (ρbar (ι τ)) =
        algebraMap k (AlgebraicClosure k) (LinearMap.det (ρ.toRepresentation (ι τ))) :=
      LinearMap.det_baseChange _
    have hdet' : LinearMap.det (ρ.toRepresentation (ι τ)) =
        ZMod.castHom (dvd_refl ℓ) k ((χ (ι τ) : (ZMod ℓ)ˣ) : ZMod ℓ) := hdet (ι τ)
    have hcomp : (algebraMap k (AlgebraicClosure k)).comp (ZMod.castHom (dvd_refl ℓ) k) =
        ZMod.castHom (dvd_refl ℓ) (AlgebraicClosure k) := RingHom.ext_zmod _ _
    calc ZMod.castHom (dvd_refl ℓ) (AlgebraicClosure k) ((χ (ι τ) : (ZMod ℓ)ˣ) : ZMod ℓ)
        = (algebraMap k (AlgebraicClosure k)).comp (ZMod.castHom (dvd_refl ℓ) k)
            ((χ (ι τ) : (ZMod ℓ)ˣ) : ZMod ℓ) := by rw [hcomp]
      _ = algebraMap k (AlgebraicClosure k) (LinearMap.det (ρ.toRepresentation (ι τ))) := by
            rw [RingHom.comp_apply, hdet']
      _ = LinearMap.det (ρbar (ι τ)) := hbc.symm
      _ = -(lineScalar ρbar hspan hv₀ ⟨(ι τ) ^ 2, hτ2S⟩) := hdetτ
      _ = -((ψ ⟨(ι τ) ^ 2, hτ2S⟩ : (AlgebraicClosure k)ˣ) : AlgebraicClosure k) := by
            rw [hψdef, lineCharacter_apply]
  -- Step 6: the local subgroup `Δ`, its fixed field `K`, and the local theorem
  set Δ : Subgroup (Γ (Qell ℓ)) := S.comap ι.toMonoidHom with hΔdef
  have hΔopen : IsOpen (Δ : Set (Γ (Qell ℓ))) := by
    have hHopen : IsOpen (H : Set (Γ ℚ)) := isOpen_ker_modCycChar ℓ ℚ (by omega)
    have hSopen : IsOpen (S : Set (Γ ℚ)) := Subgroup.isOpen_mono hHS hHopen
    have : (Δ : Set (Γ (Qell ℓ))) = ι ⁻¹' (S : Set (Γ ℚ)) := rfl
    rw [this]
    exact hSopen.preimage ι.continuous_toFun
  have hΔclosed : IsClosed (Δ : Set (Γ (Qell ℓ))) := Subgroup.isClosed_of_isOpen _ hΔopen
  set Kfld : IntermediateField (Qell ℓ) (AlgebraicClosure (Qell ℓ)) :=
    IntermediateField.fixedField Δ with hKflddef
  have hfix : Kfld.fixingSubgroup = Δ :=
    InfiniteGalois.fixingSubgroup_fixedField ⟨Δ, hΔclosed⟩
  have hτΔ : τ ∉ Δ := fun hmem => hτS hmem
  have hΔidx : Δ.index = 2 := by
    rw [hΔdef, Subgroup.index_comap]
    haveI hSnormal : S.Normal := Subgroup.normal_of_index_eq_two hSidx
    have hdvd : S.relIndex ι.toMonoidHom.range ∣ S.index :=
      Subgroup.relIndex_dvd_index_of_normal S ι.toMonoidHom.range
    have hne1 : S.relIndex ι.toMonoidHom.range ≠ 1 := by
      intro h1
      have hle := Subgroup.relIndex_eq_one.mp h1
      exact hτS (hle ⟨τ, rfl⟩)
    rw [hSidx] at hdvd
    rcases (Nat.Prime.eq_one_or_self_of_dvd Nat.prime_two _ hdvd) with h | h
    · exact absurd h hne1
    · rw [h]
  have hK2 : Kfld.fixingSubgroup.index = 2 := by rw [hfix]; exact hΔidx
  have hram : ¬ localInertiaGroup (ellPlace ℓ) ≤ Kfld.fixingSubgroup := by
    rw [hfix]
    intro hle
    exact hτΔ (hle hτI)
  haveI hKfd : FiniteDimensional (Qell ℓ) Kfld := by
    rw [← InfiniteGalois.isOpen_iff_finite]
    rw [hfix]
    exact hΔopen
  -- the character of `Gal(ℚ̄_ℓ/K)` on the line `L`
  have hfixle : Kfld.fixingSubgroup ≤ S.comap ι.toMonoidHom := le_of_eq hfix
  set ψloc : Kfld.fixingSubgroup →* (AlgebraicClosure k)ˣ :=
    ψ.comp ((ι.toMonoidHom.subgroupComap S).comp
      (Subgroup.inclusion hfixle)) with hψlocdef
  have hψΛ : ∀ (σ : Kfld.fixingSubgroup), ∀ x ∈ L,
      Slop.OddRep.baseChange (AlgebraicClosure k) ρ.toRepresentation
        (Field.absoluteGaloisGroup.map (algebraMap ℚ (Qell ℓ)) σ.1) x
        = (ψloc σ : AlgebraicClosure k) • x := by
    intro σ x hx
    have hσΔ : σ.1 ∈ Δ := hfix ▸ σ.2
    exact hψacts ⟨ι σ.1, hσΔ⟩ hx
  -- S2: this character is flat
  have hflatψ : IsFlatCharacter ℓ Kfld (AlgebraicClosure k) ψloc :=
    isFlatCharacter_of_stable_line ℓ hdim ρ hflat Kfld L hLdim ψloc hψΛ
  -- S1: the local theorem
  obtain ⟨d, hd2, hdψ⟩ := flat_character_tame_bound ℓ hℓ5 (AlgebraicClosure k) Kfld hK2
    hram ψloc hflatψ
  have hτ2Δ : τ ^ 2 ∈ Kfld.fixingSubgroup := by
    rw [hfix]
    change ι (τ ^ 2) ∈ S
    rw [map_pow]
    exact hτ2S
  have heq := hdψ τ hτI hτ2Δ
  -- rewrite `ψloc(τ²)` as `ψ(τ̄²)` and the local cyclotomic character as the global one
  have hψloc_eq : ψloc ⟨τ ^ 2, hτ2Δ⟩ = ψ ⟨(ι τ) ^ 2, hτ2S⟩ := by
    change ψ (((ι.toMonoidHom.subgroupComap S).comp (Subgroup.inclusion hfixle)) ⟨τ ^ 2, hτ2Δ⟩)
      = ψ ⟨(ι τ) ^ 2, hτ2S⟩
    apply congrArg ψ
    apply Subtype.ext
    change ι (τ ^ 2) = (ι τ) ^ 2
    exact map_pow ι.toMonoidHom τ 2
  have hcyc_compat : modCycChar ℓ (Qell ℓ) τ = χ (ι τ) :=
    (modCycChar_absoluteGaloisGroup_map (algebraMap ℚ (Qell ℓ)) τ).symm
  rw [hψloc_eq, hcyc_compat] at heq
  -- Step 7: the contradiction.  Let `x := χ(τ)` viewed in `𝕂ˣ`; then `x = -x^d` with
  -- `x` of order `ℓ - 1 ≥ 4`.
  set x : (AlgebraicClosure k)ˣ :=
    Units.map (ZMod.castHom (dvd_refl ℓ) (AlgebraicClosure k)).toMonoidHom (χ (ι τ)) with hxdef
  have hxval : (x : AlgebraicClosure k) =
      ZMod.castHom (dvd_refl ℓ) (AlgebraicClosure k) ((χ (ι τ) : (ZMod ℓ)ˣ) : ZMod ℓ) := rfl
  have hxord : orderOf x = ℓ - 1 := by
    rw [hxdef, orderOf_injective _ (Units.map_injective (f := (ZMod.castHom (dvd_refl ℓ)
      (AlgebraicClosure k)).toMonoidHom) (ZMod.castHom (dvd_refl ℓ)
      (AlgebraicClosure k)).injective) (χ (ι τ)), hτχ, hg₀ord]
  have hx0 : (x : AlgebraicClosure k) ≠ 0 := Units.ne_zero x
  -- the key equation `x = -x^d` in `𝕂`
  have hkey : (x : AlgebraicClosure k) = -((x : AlgebraicClosure k)) ^ d := by
    have h1 : (x : AlgebraicClosure k) =
        -((ψ ⟨(ι τ) ^ 2, hτ2S⟩ : (AlgebraicClosure k)ˣ) : AlgebraicClosure k) := by
      rw [hxval, hstar]
    have h2 : ((ψ ⟨(ι τ) ^ 2, hτ2S⟩ : (AlgebraicClosure k)ˣ) : AlgebraicClosure k)
        = ((x ^ d : (AlgebraicClosure k)ˣ) : AlgebraicClosure k) := by
      rw [heq]
    calc (x : AlgebraicClosure k)
        = -((ψ ⟨(ι τ) ^ 2, hτ2S⟩ : (AlgebraicClosure k)ˣ) : AlgebraicClosure k) := h1
      _ = -((x ^ d : (AlgebraicClosure k)ˣ) : AlgebraicClosure k) := by rw [h2]
      _ = -((x : AlgebraicClosure k)) ^ d := by rw [Units.val_pow_eq_pow_val]
  -- `x = -1` is impossible since `x` has order `ℓ - 1 ≥ 4`
  have hx_ne_neg_one : (x : AlgebraicClosure k) ≠ -1 := by
    intro hx
    have hx2 : x ^ 2 = 1 := by
      ext
      rw [Units.val_pow_eq_pow_val, hx, Units.val_one]
      ring
    have hdvd : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one hx2
    rw [hxord] at hdvd
    have := Nat.le_of_dvd (by norm_num) hdvd
    omega
  interval_cases d
  · -- d = 0 : `x = -1`
    apply hx_ne_neg_one
    rw [hkey]
    norm_num
  · -- d = 1 : `x = -x`, so `2 = 0` in `𝕂`
    rw [pow_one] at hkey
    have h2 : (2 : AlgebraicClosure k) * (x : AlgebraicClosure k) = 0 := by
      rw [two_mul]
      nth_rewrite 1 [hkey]
      exact neg_add_cancel _
    rcases mul_eq_zero.mp h2 with h | h
    · have hℓdvd := (CharP.cast_eq_zero_iff (AlgebraicClosure k) ℓ 2).mp (by exact_mod_cast h)
      have := Nat.le_of_dvd (by norm_num) hℓdvd
      omega
    · exact hx0 h
  · -- d = 2 : `x = -x²`, so `x = -1`
    apply hx_ne_neg_one
    have h1 : (x : AlgebraicClosure k) * 1 =
        (x : AlgebraicClosure k) * (-(x : AlgebraicClosure k)) := by
      rw [mul_one, mul_neg, ← pow_two]
      exact hkey
    have h3 : (1 : AlgebraicClosure k) = -(x : AlgebraicClosure k) :=
      mul_left_cancel₀ hx0 h1
    have h4 : -(1 : AlgebraicClosure k) = (x : AlgebraicClosure k) := by rw [h3, neg_neg]
    exact h4.symm

end CyclotomicAbsIrred

end
