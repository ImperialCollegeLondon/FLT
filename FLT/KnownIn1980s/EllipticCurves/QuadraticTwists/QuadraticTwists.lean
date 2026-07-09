/-
Copyright (c) 2026 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Claude
-/
module

public import FLT.KnownIn1980s.EllipticCurves.QuadraticTwists.Aut
public import FLT.KnownIn1980s.EllipticCurves.QuadraticTwists.VariableChangeEquiv
public import Mathlib.RingTheory.Trace.Basic

import Mathlib.RingTheory.Norm.Transitivity

/-!

# Quadratic twists of elliptic curves

Let `E` be an elliptic curve over a field `K` and let `L/K` be a separable quadratic extension.
The *quadratic twist* `Eᴸ` of `E` by `L/K` is an elliptic curve over `K`, well-defined up to
`K`-isomorphism, characterised by the following two properties:

* `Eᴸ` becomes isomorphic to `E` over `L` (but is not isomorphic to `E` over `K`, at least
  when `j(E) ∉ {0, 1728}`);
* the isomorphism `φ : Eᴸ ≅ E` over `L` can be chosen so that the Galois action on the points
  of `Eᴸ` corresponds, under `φ`, to the Galois action on the points of `E` twisted by the
  quadratic character `χ` of `L/K`. More precisely, for every field `M` in a tower
  `K ⊆ L ⊆ M` and every `σ ∈ Aut(M/K)`, we have `φ(σ P) = χ(σ) • σ(φ P)` on `M`-points,
  where `χ(σ) = 1` if `σ` fixes `L` pointwise and `χ(σ) = -1` otherwise.

Taking `M` to be a separable closure of `K`, the second property says exactly that the Galois
representations attached to `Eᴸ` (for example on torsion points, via
`FLT.KnownIn1980s.EllipticCurves.Torsion`) are the twists by `χ` of those attached to `E`.
Taking `M = L` and `σ` the nontrivial element of `Gal(L/K)`, it says `φ(σ P) = -σ(φ P)`,
which is the classical description of the twist by Galois descent: `Eᴸ` is the descent to `K`
of `E ×_K L` along the twisted action `σ ↦ (-1) ∘ σ`.

Concretely, when `char K ≠ 2` we may complete the square and assume
`E : y² = x³ + a₂x² + a₄x + a₆`, and `L = K(√d)`; then `Eᴸ : y² = x³ + da₂x² + d²a₄x + d³a₆`,
with isomorphism `φ : (x, y) ↦ (x/d, y/(d√d))` over `L`.

## The generality

Twisting by a separable quadratic extension `L/K` is the right generality for quadratic twists,
uniformly in all characteristics:

* Quadratic twists of `E/K` are classified by the continuous characters
  `χ : Gal(Kˢᵉᵖ/K) → {±1} = μ₂ ⊆ Aut(E)`, and by Galois theory the nontrivial such characters
  correspond exactly to separable quadratic extensions `L/K` (take the fixed field of `ker χ`).
  In characteristic 2 the separable quadratic extensions are the Artin–Schreier extensions
  `L = K(℘⁻¹(d))`, which are invisible to the familiar "twist by `d ∈ K^×/(K^×)²`"
  parametrisation available only when `char K ≠ 2`.
* Every degree 2 field extension is automatically normal; separability is precisely the
  condition making `Aut(L/K)` have order 2 rather than 1. An inseparable quadratic extension
  has trivial automorphism group, hence carries no quadratic character and produces no twist.
* A mild generalisation, deliberately not adopted here: one can twist by an arbitrary étale
  quadratic `K`-algebra, allowing the split algebra `K × K` which corresponds to the trivial
  character and gives back `E` itself. This makes twisting an action of the group
  `H¹(Gal(Kˢᵉᵖ/K), ℤ/2)` on curves at the cost of formalisation noise; all the content is in
  the field case.
* When `j(E) ∈ {0, 1728}` the curve has automorphisms beyond `±1` and hence also quartic,
  sextic (and, in characteristics 2 and 3, wilder) twists; but the *quadratic* twist by `L/K`,
  i.e. by the cocycle valued in `{±1} ⊆ Aut(E)`, is defined for every `E`, and everything below
  except the two classification statements holds with no hypothesis on `j`.

## Main definitions and statements

The basic algebraic theory of the twist is carried out in full: the explicit Weierstrass model
(`quadraticTwistOf`, `quadraticTwistBy`), its ellipticity, its independence of the choice of
generator of `L/K` (`exists_smul_quadraticTwistBy_eq`), the invariance of the `j`-invariant
(`j_quadraticTwist`), and the fact that twisting is an involution up to `K`-isomorphism
(`exists_smul_quadraticTwist_quadraticTwist_eq`), together with the Galois-theoretic
statements: the isomorphism on points over `L` and its `χ`-twisted equivariance, and the
classification of forms of `E`. The reduction-theoretic statements are in
`FLT.KnownIn1980s.EllipticCurves.QuadraticTwists.SplitMultiplicativeReduction`.

* `quadraticCharacter K L M` : the quadratic character `Aut(M/K) →* {±1} = ℤˣ` attached to a
  separable quadratic subextension `K ⊆ L ⊆ M`.
* `WeierstrassCurve.quadraticTwistOf`, `WeierstrassCurve.quadraticTwistBy` and
  `WeierstrassCurve.quadraticTwist E L` : an explicit Weierstrass model of the quadratic twist,
  uniform in the characteristic — parametrised respectively by a pair `(t, n)`, by a generator
  `θ` of `L/K` (with `t`, `n` its trace and norm), and by the extension `L/K` itself.
* `WeierstrassCurve.quadraticTwistPointEquiv E L M` : the isomorphism `Eᴸ(M) ≅ E(M)` of groups
  of `M`-points, for every field `M` in a tower `K ⊆ L ⊆ M`, natural in `M`
  (`quadraticTwistPointEquiv_map`).
* `WeierstrassCurve.quadraticTwistPointEquiv_galois` : the key statement
  `φ(σ P) = χ(σ) • σ(φ P)` above.
* `WeierstrassCurve.exists_smul_eq_or_exists_smul_eq_quadraticTwist` : for `j(E) ∉ {0, 1728}`,
  a curve over `K` becoming isomorphic to `E` over `L` is isomorphic over `K` to `E` or to its
  quadratic twist.

## Design notes

* "Separable quadratic extension" is spelled as the pair of mathlib typeclasses
  `[Algebra.IsQuadraticExtension K L] [Algebra.IsSeparable K L]` (the former is free of rank
  2, which over a field just means `[L:K] = 2`).
* A Weierstrass model of the twist is well defined only up to `K`-isomorphism, i.e. up to the
  action of `WeierstrassCurve.VariableChange K` (over a field, isomorphisms of Weierstrass
  curves are exactly the admissible changes of variables), and the isomorphism `φ` over `L` is
  well defined only up to composition with an `L`-automorphism of `E`. Here `quadraticTwist`
  is an explicit model, depending on a choice of generator of `L/K` which is harmless by
  `exists_smul_quadraticTwistBy_eq`, while `quadraticTwistPointEquiv` is a *choice*, pinned
  down up to exactly this ambiguity by the theorems about it. Note that
  `quadraticTwistPointEquiv_galois` is insensitive to replacing `φ` by `-φ`, so the sign
  ambiguity in `φ` (which is the whole ambiguity, generically) is harmless.
* The isomorphism over `L` is recorded twice: once at the level of Weierstrass equations, as a
  change of variables over `L` (`exists_smul_quadraticTwist_baseChange_eq`), and once at the
  level of points, as an `AddEquiv` on `M`-points for every `M` in a tower `K ⊆ L ⊆ M`,
  natural for `L`-algebra maps (`quadraticTwistPointEquiv_map`). The point-level form is the
  one consumed by Galois representations.

## TODO

* Explicit Artin–Schreier formulas for the twist in characteristic 2 (twisting
  `y² + a₁xy + a₃y = x³ + ⋯` by `L = K(℘⁻¹(d))` modifies `a₂` by `d·a₁²`, etc.), analogous to
  `quadraticTwist_of_two_ne_zero` below.
* Galois descent for points, `E(K) ≃ E(L)^{Gal(L/K)}`, and the resulting statement that
  `E(K) × Eᴸ(K) → E(L)` has kernel and cokernel killed by 2; over a number field this gives
  `rank E(L) = rank E(K) + rank Eᴸ(K)`.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.§10, X.§2 and X.§5
* [J.-P. Serre, *Propriétés galoisiennes des points d'ordre fini des courbes elliptiques*],
  §5.3 (for the interaction of twists with reduction types)

-/

@[expose] public section

open scoped WeierstrassCurve.Affine -- `(E⁄K).Point` notation for the group of `K`-points
open Algebra.IsQuadraticExtension


/-! ### Separable quadratic extensions and their quadratic characters

Mathlib's `Algebra.IsQuadraticExtension K L` says that `L` is free of rank 2 over `K`, so for
field extensions it just means `[L:K] = 2`; we add separability as a further hypothesis
`Algebra.IsSeparable K L` throughout. -/

section QuadraticCharacter

variable (K L : Type*) [Field K] [Field L] [Algebra K L]

/-- `1` and any element lying outside the base field are linearly independent over the base
field. -/
theorem linearIndependent_one_of_notMem_range_algebraMap {θ : L}
    (hθ : θ ∉ Set.range (algebraMap K L)) : LinearIndependent K ![(1 : L), θ] := by
  rw [linearIndependent_fin2]
  simp only [Matrix.cons_val_one, Matrix.cons_val_zero]
  refine ⟨fun h ↦ hθ ⟨0, by rw [map_zero, h]⟩, fun c hc ↦ ?_⟩
  rcases eq_or_ne c 0 with rfl | hc0
  · rw [zero_smul] at hc
    exact one_ne_zero hc.symm
  · refine hθ ⟨c⁻¹, ?_⟩
    rw [map_inv₀]
    rw [Algebra.smul_def] at hc
    exact (eq_inv_of_mul_eq_one_right hc).symm

variable [Algebra.IsQuadraticExtension K L]

/-- A quadratic extension contains an element not in the base field. (Used to choose a
generator of `L/K` in the definition of the quadratic twist below.) -/
theorem Algebra.IsQuadraticExtension.exists_notMem_range_algebraMap :
    ∃ θ : L, θ ∉ Set.range (algebraMap K L) := by
  by_contra! h
  have hbot : (⊥ : Subalgebra K L) = ⊤ :=
    Algebra.eq_top_iff.mpr fun x ↦ Algebra.mem_bot.mpr (h x)
  have h1 := Subalgebra.bot_eq_top_iff_finrank_eq_one.mp hbot
  have h2 := finrank_eq_two K L
  lia

/-- Any element of a quadratic extension `L/K` is a `K`-linear combination of `1` and a given
generator `θ`, and the `θ`-coefficient is nonzero if the element also lies outside `K`. -/
theorem Algebra.IsQuadraticExtension.exists_eq_algebraMap_add_algebraMap_mul {θ θ' : L}
    (hθ : θ ∉ Set.range (algebraMap K L)) (hθ' : θ' ∉ Set.range (algebraMap K L)) :
    ∃ a b : K, a ≠ 0 ∧ θ' = algebraMap K L b + algebraMap K L a * θ := by
  have hli := linearIndependent_one_of_notMem_range_algebraMap K L hθ
  have hmem : θ' ∈ Submodule.span K (Set.range ![(1 : L), θ]) := by
    rw [hli.span_eq_top_of_card_eq_finrank
      (by rw [Fintype.card_fin]; exact (finrank_eq_two K L).symm)]
    trivial
  rw [Matrix.range_cons_cons_empty, Submodule.mem_span_pair] at hmem
  obtain ⟨c, d, hcd⟩ := hmem
  refine ⟨d, c, fun hd ↦ hθ' ⟨c, ?_⟩, ?_⟩
  · rw [← hcd, hd, zero_smul, add_zero, Algebra.algebraMap_eq_smul_one]
  · rw [← hcd, Algebra.smul_def, Algebra.smul_def, mul_one]

-- Let `M` be a field extension of `L`, for example `L` itself or a separable closure of `K`.
variable (M : Type*) [Field M] [Algebra K M] [Algebra L M] [IsScalarTower K L M]

/-- For a normal subextension `K ⊆ L ⊆ M`, a `K`-automorphism `σ` of `M` fixes `L` pointwise
if and only if its restriction to `L` (`AlgEquiv.restrictNormal`) is the identity. -/
theorem forall_apply_algebraMap_iff_restrictNormal_eq_one (σ : M ≃ₐ[K] M) :
    (∀ x : L, σ (algebraMap L M x) = algebraMap L M x) ↔ σ.restrictNormal L = 1 := by
  simp only [AlgEquiv.ext_iff, AlgEquiv.one_apply, ← AlgEquiv.restrictNormal_commutes]
  exact forall_congr' fun x ↦ (FaithfulSMul.algebraMap_injective L M).eq_iff

variable [Algebra.IsSeparable K L]

-- Note that mathlib already knows the basic facts about this situation: `L/K` is
-- finite (`Module.Finite` from `Algebra.IsQuadraticExtension`), normal
-- (`Algebra.IsQuadraticExtension.normal`) and hence Galois
-- (`Algebra.IsQuadraticExtension.isGalois`), with cyclic Galois group
-- (`Algebra.IsQuadraticExtension.isCyclic`) of order 2 (`IsGalois.card_aut_eq_finrank`
-- plus `Algebra.IsQuadraticExtension.finrank_eq_two`).

/-- A separable quadratic extension has exactly two automorphisms. -/
theorem Algebra.IsQuadraticExtension.card_algEquiv : Nat.card (L ≃ₐ[K] L) = 2 := by
  rw [IsGalois.card_aut_eq_finrank]
  exact finrank_eq_two K L

/-- A separable quadratic extension has a nontrivial automorphism. -/
theorem Algebra.IsQuadraticExtension.exists_algEquiv_ne_one : ∃ σ : L ≃ₐ[K] L, σ ≠ 1 :=
  ((Nat.card_eq_two_iff' 1).mp (card_algEquiv K L)).exists

/-- The only automorphisms of a separable quadratic extension are the identity and any given
nontrivial automorphism. -/
theorem Algebra.IsQuadraticExtension.algEquiv_eq_one_or_eq {σ : L ≃ₐ[K] L} (hσ : σ ≠ 1)
    (φ : L ≃ₐ[K] L) : φ = 1 ∨ φ = σ := by
  rcases eq_or_ne φ 1 with h1 | h1
  · exact Or.inl h1
  · exact Or.inr (((Nat.card_eq_two_iff' 1).mp (card_algEquiv K L)).unique h1 hσ)

/-- The nontrivial automorphism of a separable quadratic extension is an involution. -/
theorem Algebra.IsQuadraticExtension.algEquiv_mul_self {σ : L ≃ₐ[K] L} (hσ : σ ≠ 1) :
    σ * σ = 1 :=
  (algEquiv_eq_one_or_eq K L hσ (σ * σ)).resolve_right fun h ↦ absurd (mul_eq_left.mp h) hσ

/-- An element fixed by a nontrivial automorphism — hence, `Gal(L/K)` having order two, by all of
`Gal(L/K)` — lies in the base field. -/
theorem Algebra.IsQuadraticExtension.mem_range_algebraMap_of_apply_eq {σ : L ≃ₐ[K] L}
    (hσ : σ ≠ 1) {x : L} (hx : σ x = x) : x ∈ Set.range (algebraMap K L) := by
  rw [IsGalois.mem_range_algebraMap_iff_fixed]
  intro φ
  rcases algEquiv_eq_one_or_eq K L hσ φ with rfl | rfl
  · exact AlgEquiv.one_apply x
  · exact hx

open Classical in
/-- The automorphism group of a separable quadratic extension consists of the identity and one
nontrivial element. -/
theorem Algebra.IsQuadraticExtension.univ_algEquiv {σ : L ≃ₐ[K] L} (hσ : σ ≠ 1) :
    (Finset.univ : Finset (L ≃ₐ[K] L)) = {1, σ} :=
  (Finset.eq_univ_of_forall fun φ ↦ by simpa using algEquiv_eq_one_or_eq K L hσ φ).symm

/-- In a separable quadratic extension, the trace of `x` is `x + σx`, where `σ` is the
nontrivial automorphism. -/
theorem Algebra.IsQuadraticExtension.algebraMap_trace_eq_add {σ : L ≃ₐ[K] L} (hσ : σ ≠ 1)
    (x : L) : algebraMap K L (Algebra.trace K L x) = x + σ x := by
  classical
  rw [trace_eq_sum_automorphisms, univ_algEquiv K L hσ, Finset.sum_pair (Ne.symm hσ)]
  simp

/-- In a separable quadratic extension, the norm of `x` is `x * σx`, where `σ` is the
nontrivial automorphism. -/
theorem Algebra.IsQuadraticExtension.algebraMap_norm_eq_mul {σ : L ≃ₐ[K] L} (hσ : σ ≠ 1)
    (x : L) : algebraMap K L (Algebra.norm K x) = x * σ x := by
  classical
  rw [Algebra.norm_eq_prod_automorphisms, univ_algEquiv K L hσ, Finset.prod_pair (Ne.symm hσ)]
  simp

/-- The trace of `b + aθ` in a separable quadratic extension is `a·tr(θ) + 2b`. -/
theorem Algebra.IsQuadraticExtension.trace_algebraMap_add_algebraMap_mul (a b : K) (θ : L) :
    Algebra.trace K L (algebraMap K L b + algebraMap K L a * θ)
      = a * Algebra.trace K L θ + 2 * b := by
  obtain ⟨σ, hσ⟩ := exists_algEquiv_ne_one K L
  apply FaithfulSMul.algebraMap_injective K L
  simp only [map_add, map_mul, map_ofNat, algebraMap_trace_eq_add K L hσ, AlgEquiv.commutes]
  ring

/-- The norm of `b + aθ` in a separable quadratic extension is `b² + ab·tr(θ) + a²·N(θ)`. -/
theorem Algebra.IsQuadraticExtension.norm_algebraMap_add_algebraMap_mul (a b : K) (θ : L) :
    Algebra.norm K (algebraMap K L b + algebraMap K L a * θ)
      = b ^ 2 + a * b * Algebra.trace K L θ + a ^ 2 * Algebra.norm K θ := by
  obtain ⟨σ, hσ⟩ := exists_algEquiv_ne_one K L
  apply FaithfulSMul.algebraMap_injective K L
  simp only [map_add, map_mul, map_pow, algebraMap_trace_eq_add K L hσ,
    algebraMap_norm_eq_mul K L hσ, AlgEquiv.commutes]
  ring

/-- The nontrivial automorphism of a separable quadratic extension moves every element
lying outside the base field. -/
theorem Algebra.IsQuadraticExtension.algEquiv_apply_ne {σ : L ≃ₐ[K] L} (hσ : σ ≠ 1) {x : L}
    (hx : x ∉ Set.range (algebraMap K L)) : σ x ≠ x :=
  fun heq ↦ hx (mem_range_algebraMap_of_apply_eq K L hσ heq)

/-- If `θ` generates a separable quadratic extension of `K` — that is, lies outside `K` — and
`t`, `n` denote its trace and norm, so that `θ² = tθ - n`, then the discriminant `t² - 4n` of
the minimal polynomial of `θ` is nonzero. (Over the nontrivial automorphism `σ` it equals
`(θ - σθ)²` with `σθ ≠ θ`. In characteristic 2 the statement says `t ≠ 0`: separable quadratic
extensions are Artin–Schreier extensions.) -/
theorem Algebra.IsQuadraticExtension.discrim_ne_zero {θ : L}
    (hθ : θ ∉ Set.range (algebraMap K L)) :
    Algebra.trace K L θ ^ 2 - 4 * Algebra.norm K θ ≠ 0 := by
  obtain ⟨σ, hσ⟩ := exists_algEquiv_ne_one K L
  intro h0
  have h1 : (θ - σ θ) ^ 2 = 0 := by
    have h2 := congrArg (algebraMap K L) h0
    simp only [map_sub, map_pow, map_mul, map_zero, map_ofNat,
      algebraMap_trace_eq_add K L hσ, algebraMap_norm_eq_mul K L hσ] at h2
    linear_combination h2
  exact algEquiv_apply_ne K L hσ hθ
    (sub_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp h1)).symm

/-- A square root `α ∉ K` of `d ∈ K` has trace `0` and norm `-d`: the nontrivial automorphism
sends `α` to `-α`. -/
theorem Algebra.IsQuadraticExtension.trace_eq_zero_and_norm_eq_neg_of_sq_eq {α : L} {d : K}
    (hαK : α ∉ Set.range (algebraMap K L)) (hα : α ^ 2 = algebraMap K L d) :
    Algebra.trace K L α = 0 ∧ Algebra.norm K α = -d := by
  obtain ⟨σ, hσ⟩ := exists_algEquiv_ne_one K L
  have hσα : σ α ≠ α := algEquiv_apply_ne K L hσ hαK
  have hσαα : σ α = -α := by
    have hσ2 : (σ α) ^ 2 = α ^ 2 := by rw [← map_pow, hα, AlgEquiv.commutes]
    have h1 : (σ α - α) * (σ α + α) = 0 := by linear_combination hσ2
    exact eq_neg_of_add_eq_zero_left
      ((mul_eq_zero.mp h1).resolve_left fun h ↦ hσα (sub_eq_zero.mp h))
  constructor
  · apply FaithfulSMul.algebraMap_injective K L
    rw [algebraMap_trace_eq_add K L hσ, hσαα, map_zero, add_neg_cancel]
  · apply FaithfulSMul.algebraMap_injective K L
    rw [algebraMap_norm_eq_mul K L hσ, hσαα, map_neg, ← hα]
    ring

open Classical in
/-- The quadratic character of `Aut(M/K)` attached to a separable quadratic subextension
`K ⊆ L ⊆ M`: it sends `σ` to `1` if `σ` fixes `L` pointwise, and to `-1` otherwise.

Since `L/K` is normal, every `K`-automorphism of `M` maps `L` to `L`, and multiplicativity
(`map_mul'`) follows because restriction to `L` is a homomorphism to the order 2 group
`Gal(L/K)`. Taking `M = L` gives the quadratic character of `Gal(L/K)` itself; if `M/K` is
normal then this character is the composite of the restriction `Aut(M/K) → Gal(L/K)` with the
unique isomorphism `Gal(L/K) ≃ {±1}`, and in particular is surjective
(`quadraticCharacter_surjective`). -/
noncomputable def quadraticCharacter : (M ≃ₐ[K] M) →* ℤˣ where
  toFun σ := if ∀ x : L, σ (algebraMap L M x) = algebraMap L M x then 1 else -1
  map_one' := by simp
  map_mul' φ φ' := by
    -- "Fixes `L` pointwise" means "restricts to `1`" on `L`; restriction is multiplicative
    -- (`restrictNormalHom`), so the claim reduces to the sign map of the order-2 `Gal(L/K)`.
    obtain ⟨σ, hσ⟩ := exists_algEquiv_ne_one K L
    have hor := algEquiv_eq_one_or_eq K L hσ
    have hmul : (φ * φ').restrictNormal L = φ.restrictNormal L * φ'.restrictNormal L :=
      map_mul (AlgEquiv.restrictNormalHom L) φ φ'
    have hsq : σ * σ = 1 := algEquiv_mul_self K L hσ
    simp only [forall_apply_algebraMap_iff_restrictNormal_eq_one]
    rw [hmul]
    rcases hor (φ.restrictNormal L) with h1 | h1 <;>
      rcases hor (φ'.restrictNormal L) with h2 | h2 <;>
      rw [h1, h2] <;> simp [hsq, hσ]

theorem quadraticCharacter_eq_one_iff (σ : M ≃ₐ[K] M) :
    quadraticCharacter K L M σ = 1 ↔ ∀ x : L, σ (algebraMap L M x) = algebraMap L M x := by
  classical
  unfold quadraticCharacter
  simp only [MonoidHom.coe_mk, OneHom.coe_mk]
  split_ifs with h
  · exact iff_of_true rfl h
  · exact iff_of_false (fun hc ↦ by simpa using congrArg Units.val hc) h

/-- If `M/K` is normal (for example `M = L`, or `M` a separable closure of `K`) then the
nontrivial element of `Gal(L/K)` extends to an automorphism of `M`, so the quadratic character
of `Aut(M/K)` attached to `L/K` is surjective. -/
theorem quadraticCharacter_surjective [Normal K M] :
    Function.Surjective (quadraticCharacter K L M) := by
  intro u
  rcases Int.units_eq_one_or u with rfl | rfl
  · exact ⟨1, map_one _⟩
  · -- The nontrivial element of `Gal(L/K)` lifts to some `τ ∈ Aut(M/K)` because `M/K` is normal;
    -- `τ` does not fix `L` pointwise, so `χ(τ) ≠ 1`, hence `χ(τ) = -1`.
    obtain ⟨σ₀, hσ₀⟩ := exists_algEquiv_ne_one K L
    obtain ⟨τ, hτ⟩ := AlgEquiv.restrictNormalHom_surjective (F := K) (K₁ := L) (E := M) σ₀
    refine ⟨τ, (Int.units_eq_one_or _).resolve_left fun heq ↦ hσ₀ ?_⟩
    rw [← hτ]
    exact (forall_apply_algebraMap_iff_restrictNormal_eq_one K L M τ).mp
      ((quadraticCharacter_eq_one_iff K L M τ).mp heq)

end QuadraticCharacter

/-! ### The quadratic twist -/

namespace WeierstrassCurve

universe u

section QuadraticTwistOfRing

variable {A : Type*} [CommRing A] (E : WeierstrassCurve A)

/-- The quadratic twist of a Weierstrass curve `E` over `K` by parameters `t`, `n`, to be
thought of as the trace and norm of a generator `θ` of a separable quadratic extension `L/K`
(see `WeierstrassCurve.quadraticTwistBy`), so that `θ² = tθ - n` and `D := t² - 4n` is the
discriminant of the minimal polynomial of `θ`, nonzero exactly when `θ` is separable.

The construction: writing the equation of `E` as `y² + A(x)y = f(x)` with `A(x) = a₁x + a₃`,
the functions `x` and `Y := (t - 2θ)y - θ·A(x)` on `E` are invariant under the Galois action
twisted by the quadratic character of `L/K`, and satisfy
`Y² + t·A(x)·Y = D·(y² + A(x)y) - n·A(x)²`; clearing denominators via `(x, Y) ↦ (Dx, DY)`
turns this relation into the Weierstrass model below of the twist:

`y² + ta₁·xy + Dta₃·y = x³ + (Da₂ - na₁²)·x² + (D²a₄ - 2Dna₁a₃)·x + (D³a₆ - D²na₃²)`.

Its discriminant is `D⁶·Δ(E)` (`Δ_quadraticTwistOf`), so the twist of an elliptic curve is
elliptic when `D ≠ 0` (`isElliptic_quadraticTwistOf`), with the same `j`-invariant
(`j_quadraticTwistOf`).

Sanity checks. If `char K ≠ 2` we may take `θ = √d`, so `t = 0`, `n = -d`, `D = 4d`; for
`E : y² = x³ + a₂x² + a₄x + a₆` the model is `y² = x³ + 4da₂x² + 16d²a₄x + 64d³a₆`, the
classical twist by `4d ≡ d mod (K^×)²`. If `char K = 2` we may take `θ` with `θ² + θ = d`
(Artin–Schreier), so `t = 1`, `n = -d`, `D = 1`; for ordinary `E : y² + xy = x³ + a₂x² + a₆`
the model is the classical twist `y² + xy = x³ + (a₂ + d)x² + a₆`, and for supersingular
`E : y² + a₃y = x³ + a₄x + a₆` it is `y² + a₃y = x³ + a₄x + (a₆ + da₃²)`. -/
def quadraticTwistOf (t n : A) : WeierstrassCurve A where
  a₁ := t * E.a₁
  a₂ := (t ^ 2 - 4 * n) * E.a₂ - n * E.a₁ ^ 2
  a₃ := (t ^ 2 - 4 * n) * t * E.a₃
  a₄ := (t ^ 2 - 4 * n) ^ 2 * E.a₄ - 2 * (t ^ 2 - 4 * n) * n * E.a₁ * E.a₃
  a₆ := (t ^ 2 - 4 * n) ^ 3 * E.a₆ - (t ^ 2 - 4 * n) ^ 2 * n * E.a₃ ^ 2

variable (t n : A)

theorem c₄_quadraticTwistOf : (E.quadraticTwistOf t n).c₄ = (t ^ 2 - 4 * n) ^ 2 * E.c₄ := by
  simp only [quadraticTwistOf, c₄, b₂, b₄]
  ring

theorem Δ_quadraticTwistOf : (E.quadraticTwistOf t n).Δ = (t ^ 2 - 4 * n) ^ 6 * E.Δ := by
  simp only [quadraticTwistOf, Δ, b₂, b₄, b₆, b₈]
  ring

theorem c₆_quadraticTwistOf : (E.quadraticTwistOf t n).c₆ = (t ^ 2 - 4 * n) ^ 3 * E.c₆ := by
  simp only [quadraticTwistOf, c₆, b₂, b₄, b₆]
  ring

theorem b₂_quadraticTwistOf : (E.quadraticTwistOf t n).b₂ = (t ^ 2 - 4 * n) * E.b₂ := by
  simp only [quadraticTwistOf, b₂]; ring

theorem b₄_quadraticTwistOf : (E.quadraticTwistOf t n).b₄ = (t ^ 2 - 4 * n) ^ 2 * E.b₄ := by
  simp only [quadraticTwistOf, b₄]; ring

theorem b₆_quadraticTwistOf : (E.quadraticTwistOf t n).b₆ = (t ^ 2 - 4 * n) ^ 3 * E.b₆ := by
  simp only [quadraticTwistOf, b₆]; ring

/-- The quadratic twist commutes with a ring homomorphism `f` (in particular with base change):
`(E.quadraticTwistOf t n).map f = (E.map f).quadraticTwistOf (f t) (f n)`. -/
theorem quadraticTwistOf_map {B : Type*} [CommRing B] (f : A →+* B) :
    (E.quadraticTwistOf t n).map f = (E.map f).quadraticTwistOf (f t) (f n) := by
  ext <;>
    simp only [quadraticTwistOf, map_a₁, map_a₂,
      map_a₃, map_a₄, map_a₆, map_mul, map_sub,
      map_pow, map_ofNat]

/-- The discriminant of the node's tangent polynomial `c₄ T² + a₁ c₄ T - (54 b₆ - 3 b₂ b₄ + a₂ c₄)`
(the quadratic controlling split multiplicative reduction) equals `-c₄ c₆`. Hence the tangent
directions at the node are rational over the residue field exactly when `-c₄ c₆` is a square there;
twisting by `(t, n)` multiplies `-c₄ c₆` by `(t² - 4n)⁵ = (t² - 4n)⁴ · (t² - 4n)`, i.e. by the
twisting parameter up to a square (see `c₄_quadraticTwistOf`, `c₆_quadraticTwistOf`). -/
theorem splitPolynomial_discrim :
    (E.a₁ * E.c₄) ^ 2 + 4 * E.c₄ * (54 * E.b₆ - 3 * E.b₂ * E.b₄ + E.a₂ * E.c₄)
      = -(E.c₄ * E.c₆) := by
  simp only [c₄, c₆, b₂, b₄, b₆]; ring

/-- The node-polynomial constant `κ = 54 b₆ - 3 b₂ b₄ + a₂ c₄` of the quadratic twist by `(t, n)`
in terms of that of `E`: `κ_W = D³ κ - D² n a₁² c₄` where `D = t² - 4n`. -/
theorem kappa_quadraticTwistOf :
    54 * (E.quadraticTwistOf t n).b₆
      - 3 * (E.quadraticTwistOf t n).b₂ * (E.quadraticTwistOf t n).b₄
      + (E.quadraticTwistOf t n).a₂ * (E.quadraticTwistOf t n).c₄
      = (t ^ 2 - 4 * n) ^ 3 * (54 * E.b₆ - 3 * E.b₂ * E.b₄ + E.a₂ * E.c₄)
        - (t ^ 2 - 4 * n) ^ 2 * n * E.a₁ ^ 2 * E.c₄ := by
  rw [b₆_quadraticTwistOf, b₂_quadraticTwistOf, b₄_quadraticTwistOf, c₄_quadraticTwistOf,
    show (E.quadraticTwistOf t n).a₂ = (t ^ 2 - 4 * n) * E.a₂ - n * E.a₁ ^ 2 from rfl]
  ring

end QuadraticTwistOfRing

variable {K : Type u} [Field K]

section QuadraticTwistOf

variable (E : WeierstrassCurve K)

variable (t n : K)

theorem isElliptic_quadraticTwistOf [E.IsElliptic] (hD : t ^ 2 - 4 * n ≠ 0) :
    (E.quadraticTwistOf t n).IsElliptic := by
  rw [isElliptic_iff, Δ_quadraticTwistOf]
  exact (isUnit_iff_ne_zero.mpr (pow_ne_zero 6 hD)).mul E.isUnit_Δ

theorem j_quadraticTwistOf [E.IsElliptic] (h : (E.quadraticTwistOf t n).IsElliptic) :
    (E.quadraticTwistOf t n).j = E.j := by
  have hD : t ^ 2 - 4 * n ≠ 0 := fun h0 ↦ (E.quadraticTwistOf t n).isUnit_Δ.ne_zero
    (by rw [Δ_quadraticTwistOf, h0]; ring)
  have hΔ : E.Δ ≠ 0 := E.isUnit_Δ.ne_zero
  simp only [j, Units.val_inv_eq_inv_val, coe_Δ', Δ_quadraticTwistOf, c₄_quadraticTwistOf]
  field_simp

/-- Twisting twice by the same parameters `(t, n)` gives a curve isomorphic to `E` over `K`:
explicitly, the double twist is obtained from `E` by the change of variables
`(x, y) ↦ (D²x, D³y + 2nD²(a₁x + a₃))`, where `D = t² - 4n`. -/
theorem exists_smul_eq_quadraticTwistOf_quadraticTwistOf (hD : t ^ 2 - 4 * n ≠ 0) :
    ∃ C : VariableChange K, C • E = (E.quadraticTwistOf t n).quadraticTwistOf t n := by
  refine ⟨⟨(Units.mk0 _ hD)⁻¹, 0, 2 * n / (t ^ 2 - 4 * n) * E.a₁,
    2 * n / (t ^ 2 - 4 * n) * E.a₃⟩, ?_⟩
  rw [variableChange_def]
  ext <;> simp only [quadraticTwistOf, inv_inv, Units.val_mk0] <;> field_simp <;> ring

/-- Changing the parameters `(t, n)` — the trace and norm of a generator `θ` of a quadratic
extension — into the trace and norm `(at + 2b, b² + abt + a²n)` of another generator `aθ + b`
changes the quadratic twist by an explicit change of variables over `K`. -/
theorem exists_smul_quadraticTwistOf_eq {a : K} (b : K) (ha : a ≠ 0) :
    ∃ C : VariableChange K, C • E.quadraticTwistOf t n
      = E.quadraticTwistOf (a * t + 2 * b) (b ^ 2 + a * b * t + a ^ 2 * n) := by
  refine ⟨⟨(Units.mk0 a ha)⁻¹, 0, a⁻¹ * b * E.a₁, a⁻¹ * b * (t ^ 2 - 4 * n) * E.a₃⟩, ?_⟩
  rw [variableChange_def]
  ext <;> simp only [quadraticTwistOf, inv_inv, Units.val_mk0] <;> field_simp <;> ring

end QuadraticTwistOf

section QuadraticTwistBy

variable {L : Type*} [Field L] [Algebra K L] (E : WeierstrassCurve K)

/-- The quadratic twist of a Weierstrass curve `E` over `K` by an element `θ` of an extension
`L/K`: the twist `WeierstrassCurve.quadraticTwistOf` by the trace and norm of `θ`. This is "the"
quadratic twist of `E` by the extension `L/K` whenever `L/K` is separable quadratic and `θ`
generates it, i.e. `θ ∉ K`; the choice of generator does not matter, up to isomorphism over `K`
(`exists_smul_quadraticTwistBy_eq`). -/
noncomputable def quadraticTwistBy (θ : L) : WeierstrassCurve K :=
  E.quadraticTwistOf (Algebra.trace K L θ) (Algebra.norm K θ)

variable [Algebra.IsQuadraticExtension K L] [Algebra.IsSeparable K L]

theorem isElliptic_quadraticTwistBy [E.IsElliptic] {θ : L}
    (hθ : θ ∉ Set.range (algebraMap K L)) : (E.quadraticTwistBy θ).IsElliptic :=
  E.isElliptic_quadraticTwistOf _ _ (discrim_ne_zero K L hθ)

/-- The quadratic twist by a generator `θ` of a separable quadratic extension `L/K` depends on
the choice of `θ` only up to isomorphism over `K`: all generators give isomorphic twists. -/
theorem exists_smul_quadraticTwistBy_eq {θ θ' : L} (hθ : θ ∉ Set.range (algebraMap K L))
    (hθ' : θ' ∉ Set.range (algebraMap K L)) :
    ∃ C : VariableChange K, C • E.quadraticTwistBy θ = E.quadraticTwistBy θ' := by
  obtain ⟨a, b, ha, rfl⟩ :=
    exists_eq_algebraMap_add_algebraMap_mul K L hθ hθ'
  simp only [quadraticTwistBy, trace_algebraMap_add_algebraMap_mul K L a b θ,
    norm_algebraMap_add_algebraMap_mul K L a b θ]
  exact E.exists_smul_quadraticTwistOf_eq _ _ b ha

end QuadraticTwistBy

/-- The quadratic twist of an elliptic curve `E` over `K` by a separable quadratic extension
`L/K`: the twist `WeierstrassCurve.quadraticTwistBy` by an arbitrarily chosen generator
`θ ∈ L ∖ K`. The twist is independent of this choice up to isomorphism over `K`
(`exists_smul_quadraticTwist_eq_quadraticTwistBy`), that is, up to the action of
`WeierstrassCurve.VariableChange K`; see `WeierstrassCurve.quadraticTwistOf` for the explicit
Weierstrass model. (The separability hypothesis is not used to write down the model, but the
twist is only meaningful for separable extensions — see the module docstring.) -/
@[nolint unusedArguments]
noncomputable def quadraticTwist (E : WeierstrassCurve K) (L : Type*) [Field L] [Algebra K L]
    [Algebra.IsQuadraticExtension K L] [Algebra.IsSeparable K L] : WeierstrassCurve K :=
  E.quadraticTwistBy (exists_notMem_range_algebraMap K L).choose

-- Let `E/K` be an elliptic curve and let `L/K` be a separable quadratic extension.
variable (E : WeierstrassCurve K)
variable (L : Type*) [Field L] [Algebra K L]

/-- The automorphism `[-1]` of `E` over `L` is defined over `K`, hence fixed by the Galois action:
its components `-1, 0, -a₁, -a₃` all lie in `K`. -/
lemma negVariableChange_baseChange_map (σ : L ≃ₐ[K] L) :
    (E.baseChange L).negVariableChange.map σ.toAlgHom.toRingHom
      = (E.baseChange L).negVariableChange := by
  refine VariableChange.ext ?_ ?_ ?_ ?_
  · refine Units.ext ?_
    simp [VariableChange.map, negVariableChange]
  · simp [VariableChange.map, negVariableChange]
  · simp [VariableChange.map, negVariableChange, map_neg, map_a₁, baseChange, AlgEquiv.commutes]
  · simp [VariableChange.map, negVariableChange, map_neg, map_a₃, baseChange, AlgEquiv.commutes]

section

-- Let `M` be a field extension of `L`, for example `L` itself or a separable closure of `K`.
variable (M : Type*) [Field M] [Algebra K M] [Algebra L M] [IsScalarTower K L M]

lemma baseChange_map_algebraMap (V : WeierstrassCurve K) :
    (V.baseChange L).map (algebraMap L M) = V.baseChange M :=
  V.map_baseChange (IsScalarTower.toAlgHom K L M)

end

/-- An element whose square is (the image of) a nonsquare of `K` lies outside `K`. -/
lemma notMem_range_algebraMap_of_not_isSquare {d : K} (hd : ¬IsSquare d) {α : L}
    (hα : α ^ 2 = algebraMap K L d) : α ∉ Set.range (algebraMap K L) := by
  rintro ⟨c, rfl⟩
  refine hd ⟨c, FaithfulSMul.algebraMap_injective K L ?_⟩
  rw [map_mul, ← sq]
  exact hα.symm

/-- Base change commutes with the action of changes of variables. -/
lemma baseChange_smul_baseChange (C : VariableChange K) (V : WeierstrassCurve K) :
    (C.baseChange L) • V.baseChange L = (C • V).baseChange L :=
  map_variableChange (W := V) (C := C) (φ := algebraMap K L)

/-- A relation `Cᴸ • Vᴸ = Wᴸ` between base changes, with `C` defined over `K`, descends to
`C • V = W` over `K`. -/
lemma smul_eq_of_baseChange_smul_eq (C : VariableChange K) {V W : WeierstrassCurve K}
    (h : (C.baseChange L) • V.baseChange L = W.baseChange L) : C • V = W := by
  apply map_injective (FaithfulSMul.algebraMap_injective K L)
  exact (baseChange_smul_baseChange L C V).symm.trans h

/-- The Galois conjugate of an `L`-isomorphism between base-changed curves is again one. -/
lemma map_smul_baseChange_eq (σ : L ≃ₐ[K] L) {V W : WeierstrassCurve K} {ρ : VariableChange L}
    (hρ : ρ • V.baseChange L = W.baseChange L) :
    (ρ.map σ.toAlgHom.toRingHom) • V.baseChange L = W.baseChange L := by
  have hVinv : (V.baseChange L).map σ.toAlgHom.toRingHom = V.baseChange L :=
    map_baseChange (W := V) σ.toAlgHom
  have hWinv : (W.baseChange L).map σ.toAlgHom.toRingHom = W.baseChange L :=
    map_baseChange (W := W) σ.toAlgHom
  have hmv := map_variableChange (W := V.baseChange L) (C := ρ) (φ := σ.toAlgHom.toRingHom)
  rw [hρ, hVinv, hWinv] at hmv
  exact hmv

/-- The base change of an elliptic curve is an elliptic curve. Restates the instance for
`WeierstrassCurve.map`, which does not apply to `baseChange` directly since the latter is a
non-reducible definition. -/
instance {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] (W : WeierstrassCurve R)
    [W.IsElliptic] : (W.baseChange A).IsElliptic :=
  inferInstanceAs (W.map (algebraMap R A)).IsElliptic

section

variable [E.IsElliptic]

/-- If `j(E) ≠ 0` then `c₄ ≠ 0`, also after base change to a field extension. -/
lemma baseChange_c₄_ne_zero (hj₀ : E.j ≠ 0) : (E.baseChange L).c₄ ≠ 0 := by
  simp only [baseChange, map_c₄]
  exact (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective K L)).mpr
    (E.j_eq_zero_iff.not.mp hj₀)

/-- If `j(E) ≠ 1728` then `c₆ ≠ 0`, also after base change to a field extension. -/
lemma baseChange_c₆_ne_zero (hj₁₇₂₈ : E.j ≠ 1728) : (E.baseChange L).c₆ ≠ 0 := by
  simp only [baseChange, map_c₆]
  exact (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective K L)).mpr
    (E.c₆_eq_zero_iff_j_eq_1728.not.mpr hj₁₇₂₈)

end

variable [Algebra.IsQuadraticExtension K L] [Algebra.IsSeparable K L]

/-- The quadratic twist of `E` by `L/K` is isomorphic over `K` to the twist by any given
generator `θ ∈ L ∖ K`: the arbitrary choice made in its definition is harmless. -/
theorem exists_smul_quadraticTwist_eq_quadraticTwistBy {θ : L}
    (hθ : θ ∉ Set.range (algebraMap K L)) :
    ∃ C : VariableChange K, C • E.quadraticTwist L = E.quadraticTwistBy θ :=
  E.exists_smul_quadraticTwistBy_eq (exists_notMem_range_algebraMap K L).choose_spec hθ

/-- An explicit `L`-isomorphism `(Eᶿ)ᴸ ≅ Eᴸ` (the change of variables of the module docstring)
which moreover is **anti-equivariant** for the Galois action: its conjugate by the nontrivial
`σ ∈ Gal(L/K)` differs from it by the automorphism `[-1]` of `E`. This nontrivial cocycle is the
origin of the twist being a nontrivial form of `E`. -/
theorem exists_smul_baseChange_and_map_eq {θ : L} (hθ : θ ∉ Set.range (algebraMap K L))
    {σ : L ≃ₐ[K] L} (hσ : σ ≠ 1) :
    ∃ C : VariableChange L, C • (E.quadraticTwistBy θ).baseChange L = E.baseChange L ∧
      C.map σ.toAlgHom.toRingHom = (E.baseChange L).negVariableChange * C := by
  have hσθ : σ θ ≠ θ := algEquiv_apply_ne K L hσ hθ
  have hw : σ θ - θ ≠ 0 := sub_ne_zero.mpr hσθ
  have hT : algebraMap K L (Algebra.trace K L θ) = θ + σ θ :=
    algebraMap_trace_eq_add K L hσ θ
  have hN : algebraMap K L (Algebra.norm K θ) = θ * σ θ :=
    algebraMap_norm_eq_mul K L hσ θ
  have hσσ : σ (σ θ) = θ := by
    rw [← AlgEquiv.mul_apply, algEquiv_mul_self K L hσ,
      AlgEquiv.one_apply]
  have hap : ⇑σ.toAlgHom.toRingHom = ⇑σ := rfl
  refine ⟨⟨Units.mk0 (σ θ - θ) hw, 0, -(θ * algebraMap K L E.a₁),
    -((σ θ - θ) ^ 2 * θ * algebraMap K L E.a₃)⟩, ?_, ?_⟩
  · rw [variableChange_def]
    ext <;>
      simp only [quadraticTwistBy, quadraticTwistOf, baseChange, map_a₁, map_a₂, map_a₃,
        map_a₄, map_a₆, Units.val_inv_eq_inv_val, Units.val_mk0, map_sub, map_mul,
        map_pow, map_ofNat, hT, hN] <;>
      field_simp <;> ring
  · refine VariableChange.ext ?_ ?_ ?_ ?_
    · refine Units.ext ?_
      simp only [VariableChange.map, VariableChange.mul_def, negVariableChange, Units.coe_map,
        Units.val_mul, Units.val_neg, Units.val_one, Units.val_mk0, hap, MonoidHom.coe_coe]
      rw [map_sub, hσσ]; ring
    · simp [VariableChange.map, VariableChange.mul_def, negVariableChange]
    · simp only [VariableChange.map, VariableChange.mul_def, negVariableChange, hap, Units.val_mk0,
        map_neg, map_mul, map_a₁, baseChange, σ.commutes]
      ring
    · simp only [VariableChange.map, VariableChange.mul_def, negVariableChange, hap, Units.val_mk0,
        map_neg, map_mul, map_pow, map_sub, map_a₃, baseChange, σ.commutes, hσσ]
      ring

/-- The quadratic twist becomes isomorphic to `E` after base change to `L`. (Over a field,
isomorphisms of Weierstrass curves are exactly the admissible changes of variables
`WeierstrassCurve.VariableChange`, acting via `•`.) The point-level consequences of this
isomorphism, which is what most applications need, are recorded separately in
`quadraticTwistPointEquiv` below. -/
theorem exists_smul_quadraticTwist_baseChange_eq :
    ∃ C : VariableChange L, C • (E.quadraticTwist L).baseChange L = E.baseChange L := by
  obtain ⟨σ, hσ⟩ := exists_algEquiv_ne_one K L
  obtain ⟨θ, hθ⟩ := exists_notMem_range_algebraMap K L
  obtain ⟨C₁, hC₁, -⟩ := E.exists_smul_baseChange_and_map_eq L hθ hσ
  -- Bridge the chosen generator in `quadraticTwist L` to `θ`, base changed to `L`.
  obtain ⟨C₀, hC₀⟩ := E.exists_smul_quadraticTwist_eq_quadraticTwistBy L hθ
  exact ⟨C₁ * C₀.baseChange L, by rw [mul_smul, baseChange_smul_baseChange, hC₀, hC₁]⟩

/-- Twisting twice by the same quadratic extension gives back `E`, up to `K`-isomorphism.
(Both twists are taken with respect to the same chosen generator of `L/K`, which is harmless
by `exists_smul_quadraticTwist_eq_quadraticTwistBy`.) -/
theorem exists_smul_quadraticTwist_quadraticTwist_eq :
    ∃ C : VariableChange K, C • (E.quadraticTwist L).quadraticTwist L = E := by
  obtain ⟨C, hC⟩ := E.exists_smul_eq_quadraticTwistOf_quadraticTwistOf _ _
    (discrim_ne_zero K L (exists_notMem_range_algebraMap K L).choose_spec)
  refine ⟨C⁻¹, ?_⟩
  have h2 : C⁻¹ • (C • E) = E := inv_smul_smul C E
  rw [hC] at h2
  exact h2

/-- **Galois descent for changes of variables.** A change of variables over `L` fixed by the
nontrivial `σ ∈ Gal(L/K)` has all its coefficients in `K`, so it is the base change of a change of
variables over `K`. -/
lemma exists_baseChange_eq_of_map_eq {σ : L ≃ₐ[K] L} (hσ : σ ≠ 1) {C : VariableChange L}
    (hCinv : C.map σ.toAlgHom.toRingHom = C) : ∃ CK : VariableChange K, CK.baseChange L = C := by
  have hap : ⇑σ.toAlgHom.toRingHom = ⇑σ := rfl
  have mem : ∀ x : L, σ x = x → x ∈ Set.range (algebraMap K L) :=
    fun x hx ↦ mem_range_algebraMap_of_apply_eq K L hσ hx
  have hu : σ (C.u : L) = (C.u : L) := by
    have := congrArg (fun D ↦ (D.u : L)) hCinv
    simpa [VariableChange.map, Units.coe_map, hap] using this
  have hr : σ C.r = C.r := by
    have := congrArg VariableChange.r hCinv; simpa [VariableChange.map, hap] using this
  have hs : σ C.s = C.s := by
    have := congrArg VariableChange.s hCinv; simpa [VariableChange.map, hap] using this
  have ht : σ C.t = C.t := by
    have := congrArg VariableChange.t hCinv; simpa [VariableChange.map, hap] using this
  obtain ⟨uK, huK⟩ := mem _ hu
  obtain ⟨rK, hrK⟩ := mem _ hr
  obtain ⟨sK, hsK⟩ := mem _ hs
  obtain ⟨tK, htK⟩ := mem _ ht
  have huK' : uK ≠ 0 := by rintro rfl; rw [map_zero] at huK; exact C.u.ne_zero huK.symm
  refine ⟨⟨Units.mk0 uK huK', rK, sK, tK⟩, ?_⟩
  refine VariableChange.ext ?_ hrK hsK htK
  refine Units.ext ?_
  simp only [VariableChange.baseChange, VariableChange.map, Units.coe_map, Units.val_mk0,
    MonoidHom.coe_coe]
  exact huK

/-- The classical formula for the quadratic twist away from characteristic 2. Suppose
`char K ≠ 2`, so that after completing the square we may assume `E` has the form
`y² = x³ + a₂x² + a₄x + a₆`, and suppose `L = K(α)` where `α² = d` is a nonsquare in `K` (every
separable quadratic extension arises this way when `char K ≠ 2`). Then the quadratic twist of
`E` by `L` is `y² = x³ + da₂x² + d²a₄x + d³a₆`, up to `K`-isomorphism. -/
theorem quadraticTwist_of_two_ne_zero (h2 : (2 : K) ≠ 0) (ha₁ : E.a₁ = 0) (ha₃ : E.a₃ = 0)
    {d : K} (hd : ¬IsSquare d) {α : L} (hα : α ^ 2 = algebraMap K L d) :
    ∃ C : VariableChange K, C • E.quadraticTwist L =
      { a₁ := 0, a₂ := d * E.a₂, a₃ := 0, a₄ := d ^ 2 * E.a₄, a₆ := d ^ 3 * E.a₆ } := by
  -- `α` generates `L/K` (`d` is not a square), with trace `0` and norm `-d`.
  have hαK : α ∉ Set.range (algebraMap K L) := notMem_range_algebraMap_of_not_isSquare L hd hα
  obtain ⟨htr, hnm⟩ :=
    trace_eq_zero_and_norm_eq_neg_of_sq_eq K L hαK hα
  -- So `E.quadraticTwistBy α = E.quadraticTwistOf 0 (-d)`; a final scaling by `u = 2` removes
  -- the powers of `4` and yields the classical model.
  obtain ⟨C, hC⟩ := E.exists_smul_quadraticTwist_eq_quadraticTwistBy L hαK
  unfold quadraticTwistBy at hC
  rw [htr, hnm] at hC
  refine ⟨⟨Units.mk0 2 h2, 0, 0, 0⟩ * C, ?_⟩
  rw [mul_smul, hC, variableChange_def]
  ext <;>
    simp only [quadraticTwistOf, ha₁, ha₃, Units.val_inv_eq_inv_val, Units.val_mk0] <;>
    field_simp <;> ring

/-- A choice of change of variables over `L` carrying `E` to its quadratic twist `Eᴸ`. Using the
explicit isomorphism of `exists_smul_baseChange_and_map_eq` (rather than an arbitrary one) ensures
its Galois cocycle is exactly `[-1]` (`quadraticTwistVarChange_map`), unconditionally in `j`. -/
noncomputable def quadraticTwistVarChange : VariableChange L :=
  (E.exists_smul_baseChange_and_map_eq L
    (exists_notMem_range_algebraMap K L).choose_spec
    (exists_algEquiv_ne_one K L).choose_spec).choose⁻¹

lemma quadraticTwistVarChange_smul :
    (E.quadraticTwistVarChange L) • E.baseChange L = (E.quadraticTwist L).baseChange L := by
  have h := (E.exists_smul_baseChange_and_map_eq L
    (exists_notMem_range_algebraMap K L).choose_spec
    (exists_algEquiv_ne_one K L).choose_spec).choose_spec.1
  unfold quadraticTwistVarChange
  rw [inv_smul_eq_iff]
  exact h.symm

/-- **The defining cocycle of the quadratic twist.** The nontrivial `σ ∈ Gal(L/K)` conjugates the
change of variables `quadraticTwistVarChange` (carrying `E` to `Eᴸ`) by the automorphism `[-1]` of
`E`. This is the datum expressing that `Eᴸ` is the descent of `E` along the twisted Galois action
`σ ↦ (-1) ∘ σ`, and it holds for every `j`. -/
lemma quadraticTwistVarChange_map {σ : L ≃ₐ[K] L} (hσ : σ ≠ 1) :
    (E.quadraticTwistVarChange L).map σ.toAlgHom.toRingHom
      = (E.quadraticTwistVarChange L) * (E.baseChange L).negVariableChange := by
  set σ₀ := (exists_algEquiv_ne_one K L).choose with hσ₀def
  have hσ₀ : σ₀ ≠ 1 := (exists_algEquiv_ne_one K L).choose_spec
  obtain rfl : σ = σ₀ := (algEquiv_eq_one_or_eq K L hσ₀ σ).resolve_left hσ
  have hcoc := (E.exists_smul_baseChange_and_map_eq L
    (exists_notMem_range_algebraMap K L).choose_spec
    (exists_algEquiv_ne_one K L).choose_spec).choose_spec.2
  have hinv : ∀ C : VariableChange L,
      C⁻¹.map σ₀.toAlgHom.toRingHom = (C.map σ₀.toAlgHom.toRingHom)⁻¹ :=
    fun C ↦ map_inv (VariableChange.mapHom _) C
  unfold quadraticTwistVarChange
  rw [hinv, hcoc, mul_inv_rev, (E.baseChange L).negVariableChange_inv]

section

variable [E.IsElliptic]

/-- The quadratic twist of an elliptic curve is an elliptic curve: the twisted model has
discriminant `D⁶·Δ(E)`, and `D ≠ 0` by separability
(`Algebra.IsQuadraticExtension.discrim_ne_zero`). -/
instance : (E.quadraticTwist L).IsElliptic :=
  E.isElliptic_quadraticTwistBy (exists_notMem_range_algebraMap K L).choose_spec

/-- Twisting does not change the `j`-invariant, since the curves become isomorphic over `L`. -/
theorem j_quadraticTwist : (E.quadraticTwist L).j = E.j :=
  E.j_quadraticTwistOf _ _ (E.isElliptic_quadraticTwistOf _ _
    (discrim_ne_zero K L (exists_notMem_range_algebraMap K L).choose_spec))

/-- If `j(E) ∉ {0, 1728}` (so that the only automorphisms of `E` are `±1`) then the quadratic
twist is *not* isomorphic to `E` over `K`: twisting by `L/K` is a nontrivial operation. This can
fail for `j ∈ {0, 1728}`: e.g. for `E : y² = x³ + x` of `j`-invariant `1728` over `K = ℚ(i)`,
the quadratic twist by any `L = K(d^{1/2})` with `d ∈ (K^×)⁴ ∖ (K^×)²` is isomorphic to `E`
over `K`, because `E` admits the automorphism `(x, y) ↦ (-x, iy)` of order 4. -/
theorem not_exists_smul_quadraticTwist_eq (hj₀ : E.j ≠ 0) (hj₁₇₂₈ : E.j ≠ 1728) :
    ¬∃ C : VariableChange K, C • E.quadraticTwist L = E := by
  rintro ⟨CK, hCK⟩
  obtain ⟨σ, hσ⟩ := exists_algEquiv_ne_one K L
  obtain ⟨θ, hθ⟩ := exists_notMem_range_algebraMap K L
  obtain ⟨C₁, hiso, hcoc⟩ := E.exists_smul_baseChange_and_map_eq L hθ hσ
  obtain ⟨C₀, hC₀⟩ := E.exists_smul_quadraticTwist_eq_quadraticTwistBy L hθ
  -- Transfer the hypothetical `K`-isomorphism to the twist by `θ`.
  have hDK : (CK * C₀⁻¹) • E.quadraticTwistBy θ = E := by
    rw [mul_smul, ← hC₀, inv_smul_smul, hCK]
  -- Base change it: a `σ`-invariant `L`-isomorphism `(Eᶿ)ᴸ ≅ Eᴸ`.
  set ψ := (CK * C₀⁻¹).baseChange L with hψ
  have hψiso : ψ • (E.quadraticTwistBy θ).baseChange L = E.baseChange L := by
    rw [hψ, baseChange_smul_baseChange, hDK]
  have hψinv : ψ.map σ.toAlgHom.toRingHom = ψ := by
    rw [hψ]; exact VariableChange.map_baseChange (C := CK * C₀⁻¹) σ.toAlgHom
  -- `c₄, c₆` of `Eᴸ` are nonzero, so `Aut(Eᴸ) = {±1}`.
  have hc4L : (E.baseChange L).c₄ ≠ 0 := E.baseChange_c₄_ne_zero L hj₀
  have hc6L : (E.baseChange L).c₆ ≠ 0 := E.baseChange_c₆_ne_zero L hj₁₇₂₈
  -- `a := ψ · C₁⁻¹` is an automorphism of `Eᴸ`, so `a = 1` or `a = [-1]`.
  set a := ψ * C₁⁻¹ with ha
  have hC1inv : C₁⁻¹ • E.baseChange L = (E.quadraticTwistBy θ).baseChange L := by
    rw [← hiso, inv_smul_smul]
  have haut : a • E.baseChange L = E.baseChange L := by
    rw [ha, mul_smul, hC1inv, hψiso]
  have haC : a * C₁ = ψ := by rw [ha, mul_assoc, inv_mul_cancel, mul_one]
  have hamap : a.map σ.toAlgHom.toRingHom = a := by
    rcases (E.baseChange L).eq_one_or_eq_negVariableChange_of_smul_eq_of_c₄_ne_zero hc4L hc6L haut
      with hcase | hcase
    · rw [hcase]; exact map_one (VariableChange.mapHom σ.toAlgHom.toRingHom)
    · rw [hcase]; exact E.negVariableChange_baseChange_map L σ
  -- Applying `σ` to `ψ = a · C₁` forces `[-1] = 1`, a contradiction.
  apply (E.baseChange L).negVariableChange_ne_one
  have hchain : a * ((E.baseChange L).negVariableChange * C₁) = a * C₁ :=
    calc a * ((E.baseChange L).negVariableChange * C₁)
        = a.map σ.toAlgHom.toRingHom * C₁.map σ.toAlgHom.toRingHom := by rw [hamap, hcoc]
      _ = (a * C₁).map σ.toAlgHom.toRingHom :=
          (map_mul (VariableChange.mapHom σ.toAlgHom.toRingHom) a C₁).symm
      _ = ψ.map σ.toAlgHom.toRingHom := by rw [haC]
      _ = ψ := hψinv
      _ = a * C₁ := haC.symm
  have : (E.baseChange L).negVariableChange * C₁ = C₁ := mul_left_cancel hchain
  exact mul_right_cancel (this.trans (one_mul C₁).symm)

/-- Classification of the forms of `E` split by `L/K`, for `j(E) ∉ {0, 1728}`: an elliptic curve
over `K` which becomes isomorphic to `E` over `L` is isomorphic over `K` either to `E` or to its
quadratic twist by `L`. (Such forms are classified by
`H¹(Gal(L/K), Aut(E_L)) = Hom(ℤ/2, {±1})`, which has order 2. For `j ∈ {0, 1728}` the
automorphism group is larger and there can be more forms; the statement including these `j` is
left as a further target.) Together with `not_exists_smul_quadraticTwist_eq` this pins down
`E.quadraticTwist L` up to `K`-isomorphism. -/
theorem exists_smul_eq_or_exists_smul_eq_quadraticTwist (hj₀ : E.j ≠ 0) (hj₁₇₂₈ : E.j ≠ 1728)
    (E' : WeierstrassCurve K) [E'.IsElliptic]
    (h : ∃ C : VariableChange L, C • E'.baseChange L = E.baseChange L) :
    (∃ C : VariableChange K, C • E' = E) ∨ ∃ C : VariableChange K, C • E' = E.quadraticTwist L := by
  obtain ⟨ρ, hρ⟩ := h
  obtain ⟨σ, hσ⟩ := exists_algEquiv_ne_one K L
  obtain ⟨θ, hθ⟩ := exists_notMem_range_algebraMap K L
  obtain ⟨C₁, hiso, hcoc⟩ := E.exists_smul_baseChange_and_map_eq L hθ hσ
  have hc4L : (E.baseChange L).c₄ ≠ 0 := E.baseChange_c₄_ne_zero L hj₀
  have hc6L : (E.baseChange L).c₆ ≠ 0 := E.baseChange_c₆_ne_zero L hj₁₇₂₈
  have hmapmul : ∀ a b : VariableChange L, (a * b).map σ.toAlgHom.toRingHom
      = a.map σ.toAlgHom.toRingHom * b.map σ.toAlgHom.toRingHom :=
    fun a b ↦ map_mul (VariableChange.mapHom σ.toAlgHom.toRingHom) a b
  have hmapinv : ∀ a : VariableChange L, a⁻¹.map σ.toAlgHom.toRingHom
      = (a.map σ.toAlgHom.toRingHom)⁻¹ :=
    fun a ↦ map_inv (VariableChange.mapHom σ.toAlgHom.toRingHom) a
  -- The Galois conjugate `σρ = ρ.map σ` is again an isomorphism `E'ᴸ ≅ Eᴸ`
  -- (`map_smul_baseChange_eq`).
  have hσρ : (ρ.map σ.toAlgHom.toRingHom) • E'.baseChange L = E.baseChange L :=
    map_smul_baseChange_eq L σ hρ
  -- Hence `b := σρ · ρ⁻¹` is an automorphism of `Eᴸ`, so `b = 1` or `b = [-1]`.
  have hρinv : ρ⁻¹ • E.baseChange L = E'.baseChange L := by rw [← hρ, inv_smul_smul]
  have hb : (ρ.map σ.toAlgHom.toRingHom * ρ⁻¹) • E.baseChange L = E.baseChange L := by
    rw [mul_smul, hρinv, hσρ]
  rcases (E.baseChange L).eq_one_or_eq_negVariableChange_of_smul_eq_of_c₄_ne_zero hc4L hc6L hb
    with hbcase | hbcase
  · -- Trivial cocycle: `ρ` is `σ`-invariant, descends, and `E' ≅ E` over `K`.
    left
    have hρmap : ρ.map σ.toAlgHom.toRingHom = ρ := mul_inv_eq_one.mp hbcase
    obtain ⟨ρK, hρK⟩ := exists_baseChange_eq_of_map_eq L hσ hρmap
    exact ⟨ρK, smul_eq_of_baseChange_smul_eq L ρK (by rw [hρK]; exact hρ)⟩
  · -- Nontrivial cocycle: `χ := C₁⁻¹ · ρ` is `σ`-invariant (its cocycle cancels that of `C₁`),
    -- descends, and `E' ≅ Eᶿ`, hence `E' ≅ Eᴸ` after the harmless change of generator.
    right
    have hρmap : ρ.map σ.toAlgHom.toRingHom = (E.baseChange L).negVariableChange * ρ :=
      mul_inv_eq_iff_eq_mul.mp hbcase
    have hC1inv : C₁⁻¹ • E.baseChange L = (E.quadraticTwistBy θ).baseChange L := by
      rw [← hiso, inv_smul_smul]
    have hχiso : (C₁⁻¹ * ρ) • E'.baseChange L = (E.quadraticTwistBy θ).baseChange L := by
      rw [mul_smul, hρ, hC1inv]
    have hχinv : (C₁⁻¹ * ρ).map σ.toAlgHom.toRingHom = C₁⁻¹ * ρ := by
      rw [hmapmul, hmapinv, hcoc, hρmap, mul_inv_rev, (E.baseChange L).negVariableChange_inv]
      have hnn : (E.baseChange L).negVariableChange
          * ((E.baseChange L).negVariableChange * ρ) = ρ := by
        rw [← mul_assoc, (E.baseChange L).negVariableChange_mul_self, one_mul]
      rw [mul_assoc, hnn]
    obtain ⟨χK, hχK⟩ := exists_baseChange_eq_of_map_eq L hσ hχinv
    have hE'Tby : χK • E' = E.quadraticTwistBy θ :=
      smul_eq_of_baseChange_smul_eq L χK (by rw [hχK]; exact hχiso)
    obtain ⟨C₀, hC₀⟩ := E.exists_smul_quadraticTwist_eq_quadraticTwistBy L hθ
    refine ⟨C₀⁻¹ * χK, ?_⟩
    rw [mul_smul, hE'Tby, ← hC₀, inv_smul_smul]

end

/-! ### The isomorphism on points and its Galois anti-equivariance -/

section PointEquiv

-- Let `M` be a field extension of `L`, for example `L` itself or a separable closure of `K`.
variable (M : Type*) [Field M] [Algebra K M] [Algebra L M] [IsScalarTower K L M]

lemma quadraticTwistVarChange_smul_baseChange :
    (E.quadraticTwistVarChange L).baseChange M • E.baseChange M
      = (E.quadraticTwist L).baseChange M := by
  have h := map_variableChange (C := E.quadraticTwistVarChange L) (W := E.baseChange L)
    (φ := algebraMap L M)
  rw [quadraticTwistVarChange_smul, baseChange_map_algebraMap, baseChange_map_algebraMap] at h
  exact h

/-- The `M`-level form of the twist's defining cocycle: any `σ ∈ Aut(M/K)` not fixing `L`
pointwise (i.e. with `χ(σ) = -1`) conjugates the base change to `M` of `quadraticTwistVarChange`
by the automorphism `[-1]` of `E`. This is the base change of `quadraticTwistVarChange_map`. -/
lemma quadraticTwistVarChange_baseChange_map {σ : M ≃ₐ[K] M}
    (hσ : ¬ ∀ x : L, σ (algebraMap L M x) = algebraMap L M x) :
    ((E.quadraticTwistVarChange L).baseChange M).map σ.toAlgHom.toRingHom
      = (E.quadraticTwistVarChange L).baseChange M * (E.baseChange M).negVariableChange := by
  obtain ⟨σ₀, hσ₀⟩ := exists_algEquiv_ne_one K L
  have hres : σ.restrictNormal L = σ₀ :=
    (algEquiv_eq_one_or_eq K L hσ₀ _).resolve_left
      (fun h ↦ hσ ((forall_apply_algebraMap_iff_restrictNormal_eq_one K L M σ).mpr h))
  have hcomp : σ.toAlgHom.toRingHom.comp (algebraMap L M)
      = (algebraMap L M).comp σ₀.toAlgHom.toRingHom := by
    ext l
    have h := (AlgEquiv.restrictNormal_commutes σ L l).symm
    rw [hres] at h
    simpa using h
  have e1 : ((E.quadraticTwistVarChange L).baseChange M).map σ.toAlgHom.toRingHom
      = (E.quadraticTwistVarChange L).map (σ.toAlgHom.toRingHom.comp (algebraMap L M)) :=
    (E.quadraticTwistVarChange L).map_map (algebraMap L M) σ.toAlgHom.toRingHom
  have e2 : ((E.quadraticTwistVarChange L) * (E.baseChange L).negVariableChange).map
        (algebraMap L M)
      = (E.quadraticTwistVarChange L).baseChange M
        * (E.baseChange L).negVariableChange.map (algebraMap L M) :=
    map_mul (VariableChange.mapHom (algebraMap L M)) _ _
  rw [e1, hcomp, ← VariableChange.map_map, E.quadraticTwistVarChange_map L hσ₀, e2,
    negVariableChange_map, baseChange_map_algebraMap]

-- `DecidableEq` is needed for the group structure on points.
variable [E.IsElliptic] [DecidableEq M]

/-- The isomorphism `Eᴸ(M) ≅ E(M)` on `M`-points, for any field `M` in a tower `K ⊆ L ⊆ M`:
the base change to `M` of a choice of isomorphism between `Eᴸ` and `E` over `L`. It is natural
in `M` (`quadraticTwistPointEquiv_map`) and transforms the Galois action into the Galois action
twisted by the quadratic character of `L/K` (`quadraticTwistPointEquiv_galois`).

Like the twist itself, this isomorphism is well defined only up to composition with an
`L`-automorphism of `E` — generically, up to sign — and this definition makes an arbitrary but
single choice, consistent across all `M`. -/
noncomputable def quadraticTwistPointEquiv :
    ((E.quadraticTwist L)⁄M).Point ≃+ (E⁄M).Point :=
  have : (E.baseChange M).IsElliptic := inferInstanceAs (E.map (algebraMap K M)).IsElliptic
  (Affine.Point.equivOfEq (E.quadraticTwistVarChange_smul_baseChange L M).symm).trans
    (Affine.Point.equivVariableChange (E.baseChange M) ((E.quadraticTwistVarChange L).baseChange M))

/-- Naturality of `quadraticTwistPointEquiv` in `M`: the isomorphisms on `M`-points over varying
`M ⊇ L` are all induced by a single isomorphism of curves over `L`, so they commute with the
maps on points induced by any `L`-algebra homomorphism. -/
theorem quadraticTwistPointEquiv_map {N : Type*} [Field N] [Algebra K N] [Algebra L N]
    [IsScalarTower K L N] [DecidableEq N] (f : M →ₐ[L] N)
    (P : ((E.quadraticTwist L)⁄M).Point) :
    E.quadraticTwistPointEquiv L N (Affine.Point.map f P) =
      Affine.Point.map f (E.quadraticTwistPointEquiv L M P) := by
  -- The base-changed change of variables over `N` is the image under `f` of that over `M`.
  have hu : (((E.quadraticTwistVarChange L).baseChange N).u : N)
      = f (((E.quadraticTwistVarChange L).baseChange M).u : M) := by
    simp only [VariableChange.baseChange, VariableChange.map, Units.coe_map, MonoidHom.coe_coe]
    exact (f.commutes _).symm
  have hr : ((E.quadraticTwistVarChange L).baseChange N).r
      = f ((E.quadraticTwistVarChange L).baseChange M).r := (f.commutes _).symm
  have hs : ((E.quadraticTwistVarChange L).baseChange N).s
      = f ((E.quadraticTwistVarChange L).baseChange M).s := (f.commutes _).symm
  have ht : ((E.quadraticTwistVarChange L).baseChange N).t
      = f ((E.quadraticTwistVarChange L).baseChange M).t := (f.commutes _).symm
  rcases P with _ | ⟨x, y, h⟩
  · simp [← Affine.Point.zero_def]
  · simp only [quadraticTwistPointEquiv, AddEquiv.trans_apply, Affine.Point.equivOfEq_some,
      Affine.Point.equivVariableChange_some, Affine.Point.map_some]
    refine Affine.Point.some_eq_some (E.baseChange N) ?_ ?_
    · simp only [map_add, map_mul, map_pow, hu, hr]
    · simp only [map_add, map_mul, map_pow, hu, hs, ht]

/-- The **anti-equivariance** underlying `quadraticTwistPointEquiv_galois`: if `σ ∈ Aut(M/K)` does
not fix `L` pointwise (`χ(σ) = -1`), then transporting its action through `Eᴸ(M) ≅ E(M)` gives
minus its action. This is the point-level shadow of `quadraticTwistVarChange_baseChange_map`. -/
theorem quadraticTwistPointEquiv_map_of_not_fixed {σ : M ≃ₐ[K] M}
    (hσ : ¬ ∀ x : L, σ (algebraMap L M x) = algebraMap L M x)
    (P : ((E.quadraticTwist L)⁄M).Point) :
    E.quadraticTwistPointEquiv L M (Affine.Point.map σ.toAlgHom P) =
      -Affine.Point.map σ.toAlgHom (E.quadraticTwistPointEquiv L M P) := by
  have hM := E.quadraticTwistVarChange_baseChange_map L M hσ
  have hu : σ.toAlgHom (((E.quadraticTwistVarChange L).baseChange M).u : M)
      = -(((E.quadraticTwistVarChange L).baseChange M).u : M) := by
    have h := congrArg (fun C ↦ (VariableChange.u C : M)) hM
    simpa [VariableChange.mul_def, negVariableChange] using h
  have hr : σ.toAlgHom ((E.quadraticTwistVarChange L).baseChange M).r
      = ((E.quadraticTwistVarChange L).baseChange M).r := by
    have h := congrArg VariableChange.r hM
    simpa [VariableChange.mul_def, negVariableChange] using h
  have hs : σ.toAlgHom ((E.quadraticTwistVarChange L).baseChange M).s
      = -((E.quadraticTwistVarChange L).baseChange M).s - (E.baseChange M).a₁ := by
    have h := congrArg VariableChange.s hM
    simpa [VariableChange.mul_def, negVariableChange, sub_eq_add_neg] using h
  have ht : σ.toAlgHom ((E.quadraticTwistVarChange L).baseChange M).t
      = -((E.quadraticTwistVarChange L).baseChange M).t
        - ((E.quadraticTwistVarChange L).baseChange M).r * (E.baseChange M).a₁
        - (E.baseChange M).a₃ := by
    have h := congrArg VariableChange.t hM
    simpa [VariableChange.mul_def, negVariableChange, sub_eq_add_neg, mul_neg_one,
      (by ring : ((-1 : M)) ^ 3 = -1)] using h
  rcases P with _ | ⟨x, y, hns⟩
  · simp [← Affine.Point.zero_def]
  · simp only [quadraticTwistPointEquiv, AddEquiv.trans_apply, Affine.Point.equivOfEq_some,
      Affine.Point.equivVariableChange_some, Affine.Point.map_some, Affine.Point.neg_some]
    refine Affine.Point.some_eq_some (E.baseChange M) ?_ ?_
    · simp only [map_add, map_mul, map_pow, hu, hr]
      ring
    · simp only [Affine.negY, map_add, map_mul, map_pow, hu, hr, hs, ht]
      ring

/-- **Twisting the Galois action.** The Galois action on the points of the quadratic twist is
the Galois action on the points of `E`, twisted by the quadratic character of `L/K`: for
`σ ∈ Aut(M/K)`, transporting the action of `σ` on `Eᴸ(M)` through `Eᴸ(M) ≅ E(M)` gives `χ(σ)`
times the action of `σ` on `E(M)`.

Taking `M` to be a separable closure of `K`, this says that the Galois representations attached
to `Eᴸ` (e.g. on torsion points) are those attached to `E`, twisted by `χ`. Taking `M = L` and
`σ ≠ 1` recovers the classical anti-equivariance of the isomorphism `φ : Eᴸ ≅ E` over `L`
(see `quadraticTwistPointEquiv_conj`). Note the statement is unchanged under replacing `φ` by
`-φ`, so it does not depend on the sign choice hidden in `quadraticTwistPointEquiv`. Note also
that for `σ` fixing `L` pointwise (i.e. `σ ∈ Aut(M/L)`, `χ(σ) = 1`) it is a special case of
naturality, via the `L`-algebra map underlying `σ`. -/
theorem quadraticTwistPointEquiv_galois (σ : M ≃ₐ[K] M) (P : ((E.quadraticTwist L)⁄M).Point) :
    E.quadraticTwistPointEquiv L M (Affine.Point.map σ.toAlgHom P) =
      (quadraticCharacter K L M σ : ℤ) •
        Affine.Point.map σ.toAlgHom (E.quadraticTwistPointEquiv L M P) := by
  by_cases hσ : ∀ x : L, σ (algebraMap L M x) = algebraMap L M x
  · -- `σ` fixes `L` pointwise (`χ(σ) = 1`): this is naturality for the `L`-algebra map behind `σ`.
    rw [(quadraticCharacter_eq_one_iff K L M σ).mpr hσ, Units.val_one, one_zsmul]
    exact E.quadraticTwistPointEquiv_map L M ({ σ.toAlgHom with commutes' := hσ } : M →ₐ[L] M) P
  · -- `σ` moves `L` (`χ(σ) = -1`): anti-equivariance.
    have hχ : quadraticCharacter K L M σ = -1 :=
      (Int.units_eq_one_or _).resolve_left
        fun h ↦ hσ ((quadraticCharacter_eq_one_iff K L M σ).mp h)
    rw [hχ, Units.val_neg, Units.val_one, neg_one_zsmul]
    exact E.quadraticTwistPointEquiv_map_of_not_fixed L M hσ P

/-- Special case of `quadraticTwistPointEquiv_galois` over `M = L` itself: the isomorphism
`φ : Eᴸ(L) ≅ E(L)` intertwines the action of the nontrivial element `σ ∈ Gal(L/K)` with `-σ`.
This is the datum classically used to define the twist by Galois descent. -/
theorem quadraticTwistPointEquiv_conj [DecidableEq L] {σ : L ≃ₐ[K] L} (hσ : σ ≠ 1)
    (P : ((E.quadraticTwist L)⁄L).Point) :
    E.quadraticTwistPointEquiv L L (Affine.Point.map σ.toAlgHom P) =
      -Affine.Point.map σ.toAlgHom (E.quadraticTwistPointEquiv L L P) := by
  refine E.quadraticTwistPointEquiv_map_of_not_fixed L L (fun hfix ↦ hσ ?_) P
  ext x
  simpa using hfix x

/-- **Galois descent for points.** A point of `W(L)` fixed by the nontrivial `σ ∈ Gal(L/K)` (hence,
as `[L : K] = 2`, by all of `Gal(L/K)`) is the base change of a point of `W(K)`: its coordinates,
being fixed by `σ`, lie in `K`. -/
theorem exists_baseChange_point_eq_of_map_eq [DecidableEq K] [DecidableEq L]
    {W : WeierstrassCurve K} {σ : L ≃ₐ[K] L} (hσ : σ ≠ 1) {R : (W⁄L).Point}
    (hR : Affine.Point.map σ.toAlgHom R = R) :
    ∃ Q : (W⁄K).Point, Affine.Point.baseChange K L Q = R := by
  rcases R with _ | ⟨x, y, h⟩
  · exact ⟨0, rfl⟩
  · rw [Affine.Point.map_some] at hR
    injection hR with hx hy
    obtain ⟨x₀, rfl⟩ := mem_range_algebraMap_of_apply_eq K L hσ hx
    obtain ⟨y₀, rfl⟩ := mem_range_algebraMap_of_apply_eq K L hσ hy
    exact ⟨.some x₀ y₀ ((Affine.baseChange_nonsingular W
      (f := Algebra.ofId K L) (FaithfulSMul.algebraMap_injective K L) x₀ y₀).mp h), rfl⟩

/-- The rational points of the quadratic twist, viewed inside `E(L)`, are exactly the anti-fixed
points of `Gal(L/K)`, via the two preceding results: `map_baseChange` (the base change of a
`K`-point is `σ`-fixed) for one inclusion, and `exists_baseChange_point_eq_of_map_eq` (Galois
descent) with `quadraticTwistPointEquiv_conj` for the other.

The rational points of the quadratic twist, viewed inside `E(L)` via the isomorphism over `L`, are
exactly the points of `E(L)` on which the nontrivial element of `Gal(L/K)` acts as `-1` (just as
`E(K)` consists of the points on which it acts as `+1`). Combined with Galois descent for points
this yields, over a number field, `rank E(L) = rank E(K) + rank Eᴸ(K)`. -/
theorem exists_quadraticTwistPointEquiv_baseChange_eq_iff [DecidableEq K] [DecidableEq L]
    {σ : L ≃ₐ[K] L} (hσ : σ ≠ 1) (P : (E⁄L).Point) :
    (∃ Q : ((E.quadraticTwist L)⁄K).Point,
        E.quadraticTwistPointEquiv L L (Affine.Point.baseChange K L Q) = P) ↔
      Affine.Point.map σ.toAlgHom P = -P := by
  constructor
  · rintro ⟨Q, rfl⟩
    have hfix := Affine.Point.map_baseChange (W' := E.quadraticTwist L) σ.toAlgHom Q
    have hc := E.quadraticTwistPointEquiv_conj L hσ (Affine.Point.baseChange K L Q)
    rw [hfix] at hc
    exact neg_eq_iff_eq_neg.mp hc.symm
  · intro hP
    have hRfix : Affine.Point.map σ.toAlgHom ((E.quadraticTwistPointEquiv L L).symm P)
        = (E.quadraticTwistPointEquiv L L).symm P := by
      apply (E.quadraticTwistPointEquiv L L).injective
      rw [E.quadraticTwistPointEquiv_conj L hσ, AddEquiv.apply_symm_apply, hP, neg_neg]
    obtain ⟨Q, hQ⟩ := exists_baseChange_point_eq_of_map_eq L hσ hRfix
    exact ⟨Q, by rw [hQ, AddEquiv.apply_symm_apply]⟩

end PointEquiv

end WeierstrassCurve

end
