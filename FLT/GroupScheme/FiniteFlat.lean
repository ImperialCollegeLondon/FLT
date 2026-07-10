/-
Copyright (c) 2026 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Bryan Wang Peng Jun
-/
module

public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.RingTheory.Bialgebra.Convolution
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.HopfAlgebra.TensorProduct
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Valuation.RamificationGroup

/-!

# Flat Galois modules: finite flat group schemes over a DVR, Hopf-algebraically

Let `R` be a discrete valuation ring with field of fractions `K`, and let `Kˢᵉᵖ` be a
separable closure of `K`. This file concerns actions of `Gal(Kˢᵉᵖ/K)` on finite abelian
groups (given as functions `ρ : (Kˢᵉᵖ ≃ₐ[K] Kˢᵉᵖ) → M ≃+ M`, with multiplicativity
hypothesised where needed), and what it
means for such an action to be *flat*: mathlib has no group schemes, so we say throughout
"commutative Hopf algebra, finite flat as a module" for "affine group scheme, finite flat
over the base".

## Main definitions

* `GroupScheme.GaloisModule.IsContinuous ρ` : every element of `M` is fixed by the
  subgroup fixing some finite subextension of `Kˢᵉᵖ/K`. (This is continuity of the action
  for the Krull topology on the Galois group and the discrete topology on `M`.)

* `GroupScheme.GaloisModule.IsUnramified R ρ` : for every valuation subring `𝒪` of `Kˢᵉᵖ`
  lying above `R`, the inertia subgroup at `𝒪` acts trivially on `M`.

* `GroupScheme.GaloisModule.IsFlat R ρ` : there is a commutative Hopf algebra `H` over
  `R`, finite and flat as an `R`-module (over the DVR `R` this means finite free; it is
  the Hopf algebra of functions on a finite flat group scheme over `R`), whose generic
  fibre `K ⊗[R] H` is étale over `K`, together with an isomorphism of groups from the
  `Kˢᵉᵖ`-points `K ⊗[R] H →ₐ[K] Kˢᵉᵖ` of the generic fibre (a group under convolution) to
  `M`, equivariant for the `Gal(Kˢᵉᵖ/K)`-actions on the two sides. This is the definition
  promised in the TODO of `FLT.KnownIn1980s.EllipticCurves.Flat`, and the conclusion of
  `WeierstrassCurve.torsion_flat_of_good_reduction` is exactly
  `IsFlat R (torsion action on E(Kˢᵉᵖ)[n])`, unfolded.

## Main statements

* `GroupScheme.GaloisModule.IsFlat.prod` (proved) : flat ⊓ flat = flat for a product of two
  Galois modules; the underlying Hopf algebra is the tensor product `H₁ ⊗[R] H₂` (whose Hopf
  algebra structure is already in mathlib, `Mathlib.RingTheory.HopfAlgebra.TensorProduct`),
  and the point is that `Kˢᵉᵖ`-points of a tensor product are pairs of `Kˢᵉᵖ`-points,
  compatibly with convolution.

* `GroupScheme.GaloisModule.IsFlat.congr` (proved) : flatness transports along an equivariant
  isomorphism of Galois modules; more of this formal API can be added as needed (e.g. flatness
  of sub/quotient modules via schematic closure, which is the hard Raynaud-style direction and
  is *not* formal).

* `GroupScheme.GaloisModule.IsFlat.of_isUnramified` (proved modulo the sorried descent
  helper below) : a continuous unramified action on a finite abelian group is flat; indeed
  it prolongs to a finite *étale* group scheme over `R`. This is pure descent/Galois
  theory, with no elliptic curves anywhere. The Galois-theoretic reduction
  (`exists_finiteGalois_of_isContinuous`: the action factors through a finite Galois
  subextension `L/K`) is proved.

## Main statements (currently sorried)

* `GroupScheme.GaloisModule.IsFlat.of_finiteGalois_unramified` : the Galois-descent core.
  Given the finite Galois `L/K` through which the action factors, unramifiedness lets one
  produce the prolongation: `H` is the algebra of `Gal(L/K)`-invariant functions `M → R'`,
  where `R'` is the integral closure of `R` in `L` (finite étale over `R` because `L/K`
  is unramified and `R` is a DVR); its Hopf structure is pointwise multiplication, with
  comultiplication dual to the addition of `M`. See [Tate, *Finite flat group schemes*,
  in *Modular forms and Fermat's Last Theorem*, §1.3–1.4] or [Waterhouse, *Introduction
  to affine group schemes*, §6].

## TODO

* Prove the one remaining sorried statement, `IsFlat.of_finiteGalois_unramified`.

-/

@[expose] public section

open scoped TensorProduct

universe u

namespace GroupScheme

-- let R be a discrete valuation ring with field of fractions K
variable (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

-- let Ksep be a separable closure of K
variable {Ksep : Type*} [Field Ksep] [Algebra K Ksep] [IsSepClosure K Ksep]

-- and let M be an abelian group with an action of Gal(Ksep/K), given as a function
-- to additive automorphisms. (Multiplicativity `ρ (σ * τ) = ρ σ ∘ ρ τ` is hypothesised
-- explicitly where it is needed, rather than being baked into the type of `ρ`.)
variable {M : Type*} [AddCommGroup M] (ρ : (Ksep ≃ₐ[K] Ksep) → M ≃+ M)

namespace GaloisModule

/-- An action `ρ` of `Gal(Kˢᵉᵖ/K)` on an abelian group `M` is *continuous* (for the Krull
topology on the Galois group and the discrete topology on `M`) if every element of `M` is
fixed by the subgroup of `Gal(Kˢᵉᵖ/K)` fixing some finite subextension of `Kˢᵉᵖ/K`. -/
def IsContinuous : Prop :=
  ∀ m : M, ∃ L : IntermediateField K Ksep, FiniteDimensional K L ∧
    ∀ σ ∈ L.fixingSubgroup, ρ σ m = m

/-- An action `ρ` of `Gal(Kˢᵉᵖ/K)` on an abelian group `M` is *unramified* over the
discrete valuation ring `R ⊆ K` if for every valuation subring `𝒪` of `Kˢᵉᵖ` lying above
`R`, the inertia subgroup at `𝒪` acts trivially on `M`. (All such `𝒪` are conjugate under
`Gal(Kˢᵉᵖ/K)`, so it would be equivalent to ask this for a single `𝒪`.) -/
def IsUnramified : Prop :=
  ∀ 𝒪 : ValuationSubring Ksep,
    (𝒪.comap (algebraMap K Ksep)).toSubring = (algebraMap R K).range →
    ∀ σ ∈ 𝒪.inertiaSubgroup K, ∀ m : M, ρ (σ : Ksep ≃ₐ[K] Ksep) m = m

/-- An action `ρ` of `Gal(Kˢᵉᵖ/K)` on an abelian group `M` is *flat* over the discrete
valuation ring `R ⊆ K` if `M` is, Galois-equivariantly, the group of `Kˢᵉᵖ`-points of the
generic fibre of a finite flat group scheme over `R`. Since mathlib has no group schemes
we phrase this via the (commutative) Hopf algebra `H` of functions on the group scheme:
`H` is finite flat as an `R`-module, its generic fibre `K ⊗[R] H` is étale over `K` (this
pins the generic fibre down as the finite étale group scheme attached to the Galois module
`M`; it is automatic in characteristic zero by Cartier's theorem), and the group
`K ⊗[R] H →ₐ[K] Kˢᵉᵖ` of `Kˢᵉᵖ`-points under convolution is isomorphic to `M`,
equivariantly for `Gal(Kˢᵉᵖ/K)`. -/
def IsFlat : Prop :=
  ∃ (H : Type u) (_ : CommRing H) (_ : HopfAlgebra R H)
    (_ : Module.Finite R H) (_ : Module.Flat R H)
    (_ : Algebra.Etale K (K ⊗[R] H))
    (f : Additive (WithConv (K ⊗[R] H →ₐ[K] Ksep)) ≃+ M),
    ∀ (σ : Ksep ≃ₐ[K] Ksep) (φ : K ⊗[R] H →ₐ[K] Ksep),
      f (Additive.ofMul (WithConv.toConv (σ.toAlgHom.comp φ))) =
        ρ σ (f (Additive.ofMul (WithConv.toConv φ)))

/-- **Step A: a continuous action on a finite module factors through a finite Galois
subextension.** If `M` is finite and the action `ρ` is continuous, then there is a finite
Galois subextension `L/K` of `Kˢᵉᵖ/K` such that the subgroup of `Gal(Kˢᵉᵖ/K)` fixing `L`
acts trivially on all of `M`. Concretely, one takes the compositum of the finitely many
finite subextensions provided by continuity (one per element of `M`) and passes to its
normal closure, which is finite (as a compositum of finitely many finite extensions) and
Galois (as the normal closure of a separable extension inside the Galois extension
`Kˢᵉᵖ/K`).

This is pure Galois theory and involves neither `R` nor the ring `M`-structure. -/
theorem exists_finiteGalois_of_isContinuous [Finite M] (hcont : IsContinuous ρ) :
    ∃ L : IntermediateField K Ksep, FiniteDimensional K L ∧ IsGalois K L ∧
      ∀ σ ∈ L.fixingSubgroup, ∀ m : M, ρ σ m = m := by
  classical
  -- One finite subextension per element of `M`, by continuity.
  let Lm : M → IntermediateField K Ksep := fun m => (hcont m).choose
  haveI : ∀ m, FiniteDimensional K (Lm m) := fun m => (hcont m).choose_spec.1
  -- Their compositum is finite-dimensional since `M` is finite.
  let L0 : IntermediateField K Ksep := ⨆ m, Lm m
  haveI : FiniteDimensional K L0 := IntermediateField.finiteDimensional_iSup_of_finite
  -- The normal closure is finite Galois and contains the compositum.
  refine ⟨IntermediateField.normalClosure K L0 Ksep, inferInstance, inferInstance, ?_⟩
  intro σ hσ m
  have h1 : σ ∈ L0.fixingSubgroup :=
    IntermediateField.fixingSubgroup_le (IntermediateField.le_normalClosure L0) hσ
  have h3 : σ ∈ (Lm m).fixingSubgroup :=
    IntermediateField.fixingSubgroup_le (le_iSup Lm m) h1
  exact (hcont m).choose_spec.2 σ h3

/-- A finite subextension `L/K` of `Kˢᵉᵖ/K` is *unramified over the DVR `R`* if the inertia
subgroup at every valuation subring of `Kˢᵉᵖ` lying above `R` fixes `L` pointwise (i.e. the
inertia is contained in the subgroup fixing `L`). Equivalently, the integral closure of `R`
in `L` is unramified — indeed finite étale, `R` being a DVR — over `R`.

This is a property of the extension `L/K` only (it does not involve the module `M`); it is
the hypothesis under which the Galois-descent construction of `IsFlat.of_isUnramifiedExtension`
produces an *étale* — not merely flat — integral model. -/
def IsUnramifiedExtension (L : IntermediateField K Ksep) : Prop :=
  ∀ 𝒪 : ValuationSubring Ksep,
    (𝒪.comap (algebraMap K Ksep)).toSubring = (algebraMap R K).range →
    ∀ σ ∈ 𝒪.inertiaSubgroup K, (σ : Ksep ≃ₐ[K] Ksep) ∈ L.fixingSubgroup

/-- **The unramified-kernel-field reduction (pure Galois/ramification theory).** Given a
finite Galois subextension `L/K` through which the action `ρ` factors, and given that `ρ` is
unramified over `R`, one may *shrink* `L` to a finite Galois subextension `L'/K` that still
carries the action and is itself unramified over `R`.

Concretely, take `L'` to be the fixed field of the kernel `{σ : ρ σ = 1}` of the action —
a subgroup of `Gal(Kˢᵉᵖ/K)` containing the (open) fixing subgroup of `L`, hence itself the
fixing subgroup of a finite subextension `L' ⊆ L`, and normal because the kernel of an action
on an abelian group is normal, so `L'/K` is Galois. The action factors through `Gal(L'/K)` by
construction, and `IsUnramified R ρ` says inertia acts trivially on `M`, i.e. inertia lies in
the kernel `= L'.fixingSubgroup`; thus `L'/K` is unramified over `R`. This is exactly the
point that `L` itself need not be unramified — only the subextension through which `ρ`
genuinely factors is. Pure Galois theory, no elliptic curves, no ring structure on `M`.

TODO: prove (currently the only Galois-theoretic gap of the descent). -/
theorem exists_isUnramifiedExtension [Finite M]
    (hρ : ∀ σ τ : Ksep ≃ₐ[K] Ksep, ρ (σ * τ) = (ρ τ).trans (ρ σ))
    (hunr : IsUnramified R ρ)
    (L : IntermediateField K Ksep) [FiniteDimensional K L] [IsGalois K L]
    (hL : ∀ σ ∈ L.fixingSubgroup, ∀ m : M, ρ σ m = m) :
    ∃ L' : IntermediateField K Ksep, FiniteDimensional K L' ∧ IsGalois K L' ∧
      (∀ σ ∈ L'.fixingSubgroup, ∀ m : M, ρ σ m = m) ∧ IsUnramifiedExtension R L' :=
  sorry

/-- **Steps B–D: Galois descent of the finite étale group scheme (deep, not yet
formalised).** Given a finite Galois subextension `L/K` of `Kˢᵉᵖ/K` whose fixing subgroup
acts trivially on the finite module `M`, and given that `L/K` *itself* is unramified over the
DVR `R` (`IsUnramifiedExtension R L`), the module is flat. This is the unramified-extension
case: the reduction to it from a merely unramified *action* is
`exists_isUnramifiedExtension`.

This packages the genuinely hard part of the construction, which has three ingredients
(none involving elliptic curves):

* **(B) the generic fibre.** The `K`-Hopf algebra of `Gal(L/K)`-invariant functions
  `(M → L)^{Gal(L/K)}` (for the action `σ · f = σ ∘ f ∘ ρ(σ)⁻¹`), with pointwise algebra
  structure and comultiplication dual to the addition of `M`; it is finite étale over `K`
  as a Galois-twisted form of `M → K`, and its `Kˢᵉᵖ`-points recover `M` equivariantly.

* **(C) the integral model.** The integral closure `R'` of `R` in `L` is finite étale over
  `R` — here the DVR hypothesis on `R` and unramifiedness of `L/K` over `R` are used — so
  `H := (M → R')^{Gal(L/K)}` is finite flat (indeed finite étale) over `R` with generic
  fibre the algebra of (B).

* **(D) assembly.** Package `H` as the required Hopf algebra and prove the equivariant
  additive equivalence on `Kˢᵉᵖ`-points.

See [Tate, *Finite flat group schemes*, §1.3–1.4] or [Waterhouse, *Introduction to affine
group schemes*, §6]. -/
theorem IsFlat.of_isUnramifiedExtension [Finite M]
    (hρ : ∀ σ τ : Ksep ≃ₐ[K] Ksep, ρ (σ * τ) = (ρ τ).trans (ρ σ))
    (L : IntermediateField K Ksep) [FiniteDimensional K L] [IsGalois K L]
    (hL : ∀ σ ∈ L.fixingSubgroup, ∀ m : M, ρ σ m = m)
    (hunr : IsUnramifiedExtension R L) :
    IsFlat R ρ :=
  sorry

/-- **A continuous unramified action factoring through a finite Galois `L/K` is flat.**
Assembled from the unramified-kernel-field reduction `exists_isUnramifiedExtension` (which
shrinks `L` to a subextension that is genuinely unramified over `R`) and the descent for an
unramified extension `IsFlat.of_isUnramifiedExtension`. See the two lemmas for the
mathematical content. -/
theorem IsFlat.of_finiteGalois_unramified [Finite M]
    (hρ : ∀ σ τ : Ksep ≃ₐ[K] Ksep, ρ (σ * τ) = (ρ τ).trans (ρ σ))
    (hunr : IsUnramified R ρ)
    (L : IntermediateField K Ksep) [FiniteDimensional K L] [IsGalois K L]
    (hL : ∀ σ ∈ L.fixingSubgroup, ∀ m : M, ρ σ m = m) :
    IsFlat R ρ := by
  obtain ⟨L', hfd, hgal, hL', hunr'⟩ := exists_isUnramifiedExtension R ρ hρ hunr L hL
  haveI := hfd
  haveI := hgal
  exact IsFlat.of_isUnramifiedExtension R ρ hρ L' hL' hunr'

/-- **A continuous unramified Galois module is flat.** If `M` is a finite abelian group
and the action `ρ` of `Gal(Kˢᵉᵖ/K)` on `M` is continuous and unramified over `R`, then it
prolongs to a finite flat — indeed finite étale — group scheme over `R`.

Proof sketch (pure Galois theory / descent, no elliptic curves): by continuity and
finiteness of `M` the action factors through `Gal(L/K)` for some finite Galois
subextension `L/K` of `Kˢᵉᵖ/K`, and by unramifiedness `L/K` may be chosen unramified over
`R`. Let `R'` be the integral closure of `R` in `L`, a finite étale `R`-algebra (here
unramifiedness of `L/K` and `R` being a DVR are used). Take `H` to be the
`Gal(L/K)`-invariants of the algebra of functions `M → R'`, where `Gal(L/K)` acts on both
`M` and `R'`; pointwise multiplication makes `H` a commutative `R`-algebra, finite étale
because it is a Galois-twisted form of `M → R`, and the comultiplication dual to addition
`M × M → M` makes it a Hopf algebra. Its `Kˢᵉᵖ`-points recover `M` equivariantly:
evaluation at the `Kˢᵉᵖ`-embeddings of `R'` splits the twist. -/
theorem IsFlat.of_isUnramified [Finite M]
    (hρ : ∀ σ τ : Ksep ≃ₐ[K] Ksep, ρ (σ * τ) = (ρ τ).trans (ρ σ))
    (hcont : IsContinuous ρ) (hunr : IsUnramified R ρ) :
    IsFlat R ρ := by
  obtain ⟨L, hfd, hgal, hL⟩ := exists_finiteGalois_of_isContinuous ρ hcont
  haveI := hfd
  haveI := hgal
  exact IsFlat.of_finiteGalois_unramified R ρ hρ hunr L hL

-- This proof assembles the tensor-product Hopf algebra together with the universal property
-- of tensor products of commutative algebras and the convolution-monoid API, chaining the
-- resulting algebra/bialgebra equivalences.
omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] [IsSepClosure K Ksep] in
/-- **Flatness is stable under products.** If the actions `ρ₁` on `M₁` and `ρ₂` on `M₂`
are flat over `R`, then so is any action `ρ` on `M₁ × M₂` acting componentwise via `ρ₁`
and `ρ₂`. The Hopf algebra is the tensor product `H₁ ⊗[R] H₂` (Hopf algebra structure
from `Mathlib.RingTheory.HopfAlgebra.TensorProduct`), which is again finite flat with
étale generic fibre, and whose `Kˢᵉᵖ`-points are pairs of `Kˢᵉᵖ`-points compatibly with
convolution: `Hom_{K-alg}(A ⊗ B, Kˢᵉᵖ) ≃ Hom_{K-alg}(A, Kˢᵉᵖ) × Hom_{K-alg}(B, Kˢᵉᵖ)`. -/
theorem IsFlat.prod {M₁ M₂ : Type*} [AddCommGroup M₁] [AddCommGroup M₂]
    {ρ₁ : (Ksep ≃ₐ[K] Ksep) → M₁ ≃+ M₁} {ρ₂ : (Ksep ≃ₐ[K] Ksep) → M₂ ≃+ M₂}
    {ρ : (Ksep ≃ₐ[K] Ksep) → (M₁ × M₂) ≃+ (M₁ × M₂)}
    (hρ : ∀ (σ : Ksep ≃ₐ[K] Ksep) (m : M₁ × M₂), ρ σ m = (ρ₁ σ m.1, ρ₂ σ m.2))
    (h₁ : IsFlat R ρ₁) (h₂ : IsFlat R ρ₂) :
    IsFlat R ρ := by
  obtain ⟨H₁, hCR₁, hHopf₁, hFin₁, hFlat₁, hEt₁, f₁, hf₁⟩ := h₁
  obtain ⟨H₂, hCR₂, hHopf₂, hFin₂, hFlat₂, hEt₂, f₂, hf₂⟩ := h₂
  letI := hCR₁; letI := hHopf₁; letI := hFin₁; letI := hFlat₁; letI := hEt₁
  letI := hCR₂; letI := hHopf₂; letI := hFin₂; letI := hFlat₂; letI := hEt₂
  -- The associator/base-change algebra equivalence identifying the generic fibre of the tensor
  -- product with the tensor product (over `K`) of the two generic fibres.
  let Φ : K ⊗[R] (H₁ ⊗[R] H₂) ≃ₐ[K] (K ⊗[R] H₁) ⊗[K] (K ⊗[R] H₂) :=
    (Algebra.TensorProduct.assoc R R K K H₁ H₂).symm.trans
      (Algebra.TensorProduct.cancelBaseChange R K K (K ⊗[R] H₁) H₂).symm
  -- The generic fibre is étale over `K`.
  have hEt : Algebra.Etale K (K ⊗[R] (H₁ ⊗[R] H₂)) := by
    haveI : Algebra.Etale (K ⊗[R] H₁) ((K ⊗[R] H₁) ⊗[K] (K ⊗[R] H₂)) :=
      Algebra.Etale.baseChange K (K ⊗[R] H₂) (K ⊗[R] H₁)
    haveI : Algebra.Etale K ((K ⊗[R] H₁) ⊗[K] (K ⊗[R] H₂)) :=
      Algebra.Etale.comp K (K ⊗[R] H₁) ((K ⊗[R] H₁) ⊗[K] (K ⊗[R] H₂))
    exact Algebra.Etale.of_equiv Φ.symm
  -- The bialgebra inclusions `Hᵢ → H₁ ⊗[R] H₂` (`a ↦ a ⊗ 1` and `b ↦ 1 ⊗ b`).
  let j₁ : H₁ →ₐc[R] H₁ ⊗[R] H₂ :=
    (BialgHom.lTensor H₁ (Bialgebra.unitBialgHom R H₂)).comp
      (Bialgebra.TensorProduct.rid R R H₁).symm.toBialgHom
  let j₂ : H₂ →ₐc[R] H₁ ⊗[R] H₂ :=
    (BialgHom.rTensor H₂ (Bialgebra.unitBialgHom R H₁)).comp
      (Bialgebra.TensorProduct.lid R H₂).symm.toBialgHom
  -- ... base-changed to `K`.
  let i₁ : K ⊗[R] H₁ →ₐc[K] K ⊗[R] (H₁ ⊗[R] H₂) := Bialgebra.TensorProduct.map (BialgHom.id K K) j₁
  let i₂ : K ⊗[R] H₂ →ₐc[K] K ⊗[R] (H₁ ⊗[R] H₂) := Bialgebra.TensorProduct.map (BialgHom.id K K) j₂
  -- These inclusions correspond, under `Φ`, to `includeLeft`/`includeRight`.
  have hi₁ : (i₁ : K ⊗[R] H₁ →ₐ[K] K ⊗[R] (H₁ ⊗[R] H₂)) =
      Φ.symm.toAlgHom.comp Algebra.TensorProduct.includeLeft := by
    ext x; simp [i₁, j₁, Φ, Algebra.TensorProduct.one_def]
  have hi₂ : (i₂ : K ⊗[R] H₂ →ₐ[K] K ⊗[R] (H₁ ⊗[R] H₂)) =
      Φ.symm.toAlgHom.comp Algebra.TensorProduct.includeRight := by
    ext x; simp [i₂, j₂, Φ, Algebra.TensorProduct.one_def]
  -- The convolution-monoid homomorphism `f ↦ (f ∘ i₁, f ∘ i₂)` given by precomposition.
  let T₁ : WithConv (K ⊗[R] (H₁ ⊗[R] H₂) →ₐ[K] Ksep) →* WithConv (K ⊗[R] H₁ →ₐ[K] Ksep) :=
    { toFun := fun f => WithConv.toConv (f.ofConv.comp (i₁ : K ⊗[R] H₁ →ₐ[K] _))
      map_one' := by
        simp only [AlgHom.convOne_def, WithConv.ofConv_toConv, AlgHom.comp_assoc,
          BialgHom.counitAlgHom_comp]
      map_mul' := fun f g => by
        simp only [AlgHom.convMul_comp_bialgHom_distrib f g i₁, WithConv.toConv_ofConv] }
  let T₂ : WithConv (K ⊗[R] (H₁ ⊗[R] H₂) →ₐ[K] Ksep) →* WithConv (K ⊗[R] H₂ →ₐ[K] Ksep) :=
    { toFun := fun f => WithConv.toConv (f.ofConv.comp (i₂ : K ⊗[R] H₂ →ₐ[K] _))
      map_one' := by
        simp only [AlgHom.convOne_def, WithConv.ofConv_toConv, AlgHom.comp_assoc,
          BialgHom.counitAlgHom_comp]
      map_mul' := fun f g => by
        simp only [AlgHom.convMul_comp_bialgHom_distrib f g i₂, WithConv.toConv_ofConv] }
  let T := T₁.prod T₂
  -- `T` is bijective, being (through `WithConv`) the universal property of the tensor product.
  have hbij : Function.Bijective T := by
    let e2 : ((K ⊗[R] H₁) ⊗[K] (K ⊗[R] H₂) →ₐ[K] Ksep) ≃
        ((K ⊗[R] H₁ →ₐ[K] Ksep) × (K ⊗[R] H₂ →ₐ[K] Ksep)) :=
      { toFun := fun ψ => (ψ.comp Algebra.TensorProduct.includeLeft,
          ψ.comp Algebra.TensorProduct.includeRight)
        invFun := fun p => Algebra.TensorProduct.lift p.1 p.2 fun _ _ => Commute.all _ _
        left_inv := fun ψ => by ext <;> simp
        right_inv := fun p => by ext <;> simp }
    let e1 : (K ⊗[R] (H₁ ⊗[R] H₂) →ₐ[K] Ksep) ≃
        ((K ⊗[R] H₁) ⊗[K] (K ⊗[R] H₂) →ₐ[K] Ksep) :=
      { toFun := fun φ => φ.comp Φ.symm.toAlgHom
        invFun := fun ψ => ψ.comp Φ.toAlgHom
        left_inv := fun φ => by ext x; simp
        right_inv := fun ψ => by ext x <;> simp }
    let E' : WithConv (K ⊗[R] (H₁ ⊗[R] H₂) →ₐ[K] Ksep) ≃
        (WithConv (K ⊗[R] H₁ →ₐ[K] Ksep) × WithConv (K ⊗[R] H₂ →ₐ[K] Ksep)) :=
      (WithConv.congr (e1.trans e2)).trans
        ((WithConv.equiv _).trans ((WithConv.equiv _).symm.prodCongr (WithConv.equiv _).symm))
    have hTe : ⇑T = ⇑E' := by
      funext f
      refine Prod.ext ?_ ?_
      · change WithConv.toConv (f.ofConv.comp (i₁ : K ⊗[R] H₁ →ₐ[K] _)) =
          WithConv.toConv ((f.ofConv.comp Φ.symm.toAlgHom).comp Algebra.TensorProduct.includeLeft)
        rw [hi₁, AlgHom.comp_assoc]
      · change WithConv.toConv (f.ofConv.comp (i₂ : K ⊗[R] H₂ →ₐ[K] _)) =
          WithConv.toConv ((f.ofConv.comp Φ.symm.toAlgHom).comp Algebra.TensorProduct.includeRight)
        rw [hi₂, AlgHom.comp_assoc]
    rw [hTe]
    exact E'.bijective
  let E := MulEquiv.ofBijective T hbij
  -- Assemble the additive equivalence to `M₁ × M₂`.
  let fEq : Additive (WithConv (K ⊗[R] (H₁ ⊗[R] H₂) →ₐ[K] Ksep)) ≃+ M₁ × M₂ :=
    (MulEquiv.toAdditive E).trans ((AddEquiv.prodAdditive _ _).trans (f₁.prodCongr f₂))
  refine ⟨H₁ ⊗[R] H₂, inferInstance, inferInstance, inferInstance, inferInstance, hEt, fEq, ?_⟩
  intro σ φ
  -- Both sides reduce to the componentwise action, definitionally through the constructions above.
  have key : ∀ ψ : K ⊗[R] (H₁ ⊗[R] H₂) →ₐ[K] Ksep,
      fEq (Additive.ofMul (WithConv.toConv ψ)) =
        (f₁ (Additive.ofMul (WithConv.toConv (ψ.comp (i₁ : K ⊗[R] H₁ →ₐ[K] _)))),
         f₂ (Additive.ofMul (WithConv.toConv (ψ.comp (i₂ : K ⊗[R] H₂ →ₐ[K] _))))) := by
    intro ψ
    simp only [fEq, AddEquiv.trans_apply]
    rw [show (MulEquiv.toAdditive E) (Additive.ofMul (WithConv.toConv ψ))
          = Additive.ofMul (E (WithConv.toConv ψ)) from rfl,
      show E (WithConv.toConv ψ)
          = (WithConv.toConv (ψ.comp (i₁ : K ⊗[R] H₁ →ₐ[K] _)),
             WithConv.toConv (ψ.comp (i₂ : K ⊗[R] H₂ →ₐ[K] _))) from rfl]
    rfl
  rw [key (σ.toAlgHom.comp φ), key φ, hρ, AlgHom.comp_assoc, AlgHom.comp_assoc,
    hf₁ σ (φ.comp (i₁ : K ⊗[R] H₁ →ₐ[K] _)), hf₂ σ (φ.comp (i₂ : K ⊗[R] H₂ →ₐ[K] _))]

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] [IsSepClosure K Ksep] in
/-- **Flatness transports along equivariant isomorphisms.** If `e : M₁ ≃+ M₂` intertwines
the actions `ρ₁` and `ρ₂`, then flatness of `ρ₁` gives flatness of `ρ₂` (with the same
Hopf algebra). -/
theorem IsFlat.congr {M₁ M₂ : Type*} [AddCommGroup M₁] [AddCommGroup M₂]
    {ρ₁ : (Ksep ≃ₐ[K] Ksep) → M₁ ≃+ M₁} {ρ₂ : (Ksep ≃ₐ[K] Ksep) → M₂ ≃+ M₂}
    (e : M₁ ≃+ M₂) (he : ∀ (σ : Ksep ≃ₐ[K] Ksep) (m : M₁), e (ρ₁ σ m) = ρ₂ σ (e m))
    (h₁ : IsFlat R ρ₁) : IsFlat R ρ₂ := by
  obtain ⟨H, hCR, hHopf, hFin, hFlat, hEt, f, hf⟩ := h₁
  exact ⟨H, hCR, hHopf, hFin, hFlat, hEt, f.trans e, fun σ φ => by
    simp only [AddEquiv.trans_apply, hf σ φ, he]⟩

end GaloisModule

end GroupScheme
