import Mathlib

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
(`exists_smul_quadraticTwist_quadraticTwist_eq`). The Galois-theoretic statements — the
isomorphism on points over `L` and its `χ`-twisted equivariance, the classification of forms
of `E`, and the reduction-theoretic statements — are `sorry`ed targets.

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
* `WeierstrassCurve.exists_quadraticTwist_hasSplitMultiplicativeReduction` : over the fraction
  field of a discrete valuation ring, an elliptic curve with nonsplit multiplicative reduction
  has a quadratic twist with split multiplicative reduction.

## Design notes

* "Separable quadratic extension" is spelled as the pair of mathlib typeclasses
  `[Algebra.IsQuadraticExtension K L] [Algebra.IsSeparable K L]` (the former is free of rank
  2, which over a field just means `[L:K] = 2`).
* A Weierstrass model of the twist is well defined only up to `K`-isomorphism, i.e. up to the
  action of `WeierstrassCurve.VariableChange K` (over a field, isomorphisms of Weierstrass
  curves are exactly the admissible changes of variables), and the isomorphism `φ` over `L` is
  well defined only up to composition with an `L`-automorphism of `E`. Here `quadraticTwist`
  is an explicit model, depending on a choice of generator of `L/K` which is harmless by
  `exists_smul_quadraticTwistBy_eq`, while `quadraticTwistPointEquiv` is a `sorry`ed *choice*,
  pinned down up to exactly this ambiguity by the theorems about it. Note that
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
* Behaviour of reduction types under twisting in general: over the fraction field of a DVR, an
  unramified quadratic twist preserves good and multiplicative reduction (exchanging split and
  nonsplit), while a ramified quadratic twist of a curve with good or multiplicative reduction
  has additive reduction (at least in residue characteristic ≠ 2).
* Compatibility with the Tate curve (`FLT.KnownIn1980s.EllipticCurves.TateCurve`): for `E` with
  nonsplit multiplicative reduction over a nonarchimedean local field, the Galois representation
  of `E` is the unramified quadratic twist of the Tate-curve representation of its split twist.
  This is the main FLT-facing application of this file together with
  `exists_quadraticTwist_hasSplitMultiplicativeReduction`.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.§10, X.§2 and X.§5
* [J.-P. Serre, *Propriétés galoisiennes des points d'ordre fini des courbes elliptiques*],
  §5.3 (for the interaction of twists with reduction types)

-/

open scoped WeierstrassCurve.Affine -- `(E⁄K).Point` notation for the group of `K`-points

/-! ### Separable quadratic extensions and their quadratic characters

Mathlib's `Algebra.IsQuadraticExtension K L` says that `L` is free of rank 2 over `K`, so for
field extensions it just means `[L:K] = 2`; we add separability as a further hypothesis
`Algebra.IsSeparable K L` throughout. -/

section QuadraticCharacter

variable (K L : Type*) [Field K] [Field L] [Algebra K L]
  [Algebra.IsQuadraticExtension K L] [Algebra.IsSeparable K L]

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

omit [Algebra.IsSeparable K L] in
/-- A quadratic extension contains an element not in the base field. (Used to choose a
generator of `L/K` in the definition of the quadratic twist below.) -/
theorem Algebra.IsQuadraticExtension.exists_notMem_range_algebraMap :
    ∃ θ : L, θ ∉ Set.range (algebraMap K L) := by
  by_contra! h
  have hbot : (⊥ : Subalgebra K L) = ⊤ :=
    Algebra.eq_top_iff.mpr fun x ↦ Algebra.mem_bot.mpr (h x)
  have h1 := Subalgebra.bot_eq_top_iff_finrank_eq_one.mp hbot
  have h2 := Algebra.IsQuadraticExtension.finrank_eq_two K L
  omega

open Classical in
/-- The automorphism group of a separable quadratic extension consists of the identity and one
nontrivial element. -/
theorem Algebra.IsQuadraticExtension.univ_algEquiv {σ : L ≃ₐ[K] L} (hσ : σ ≠ 1) :
    (Finset.univ : Finset (L ≃ₐ[K] L)) = {1, σ} := by
  symm
  rw [Finset.eq_univ_iff_forall]
  intro φ
  rw [Finset.mem_insert, Finset.mem_singleton]
  exact algEquiv_eq_one_or_eq K L hσ φ

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

/-- The nontrivial automorphism of a separable quadratic extension moves every element
lying outside the base field. -/
theorem Algebra.IsQuadraticExtension.algEquiv_apply_ne {σ : L ≃ₐ[K] L} (hσ : σ ≠ 1) {x : L}
    (hx : x ∉ Set.range (algebraMap K L)) : σ x ≠ x := by
  intro heq
  refine hx ((IsGalois.mem_range_algebraMap_iff_fixed x).mpr fun φ ↦ ?_)
  rcases algEquiv_eq_one_or_eq K L hσ φ with h | h <;> subst h
  · exact AlgEquiv.one_apply x
  · exact heq

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
    (sub_eq_zero.mp (pow_eq_zero_iff (two_ne_zero) |>.mp h1)).symm

omit [Algebra.IsSeparable K L] in
/-- Any element of a quadratic extension `L/K` is a `K`-linear combination of `1` and a given
generator `θ`, and the `θ`-coefficient is nonzero if the element also lies outside `K`. -/
theorem Algebra.IsQuadraticExtension.exists_eq_algebraMap_add_algebraMap_mul {θ θ' : L}
    (hθ : θ ∉ Set.range (algebraMap K L)) (hθ' : θ' ∉ Set.range (algebraMap K L)) :
    ∃ a b : K, a ≠ 0 ∧ θ' = algebraMap K L b + algebraMap K L a * θ := by
  have hθ0 : θ ≠ 0 := fun h ↦ hθ ⟨0, by rw [map_zero, h]⟩
  have hli : LinearIndependent K ![(1 : L), θ] := by
    rw [linearIndependent_fin2]
    simp only [Matrix.cons_val_one, Matrix.cons_val_zero]
    refine ⟨hθ0, fun c hc ↦ ?_⟩
    rcases eq_or_ne c 0 with rfl | hc0
    · rw [zero_smul] at hc
      exact one_ne_zero hc.symm
    · refine hθ ⟨c⁻¹, ?_⟩
      rw [map_inv₀]
      rw [Algebra.smul_def] at hc
      exact (eq_inv_of_mul_eq_one_right hc).symm
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
  map_one' := sorry
  map_mul' := sorry

theorem quadraticCharacter_eq_one_iff (σ : M ≃ₐ[K] M) :
    quadraticCharacter K L M σ = 1 ↔ ∀ x : L, σ (algebraMap L M x) = algebraMap L M x :=
  sorry

/-- If `M/K` is normal (for example `M = L`, or `M` a separable closure of `K`) then the
nontrivial element of `Gal(L/K)` extends to an automorphism of `M`, so the quadratic character
of `Aut(M/K)` attached to `L/K` is surjective. -/
theorem quadraticCharacter_surjective [Normal K M] :
    Function.Surjective (quadraticCharacter K L M) :=
  sorry

end QuadraticCharacter

/-! ### The quadratic twist -/

namespace WeierstrassCurve

universe u

variable {K : Type u} [Field K]

section QuadraticTwistOf

variable (E : WeierstrassCurve K)

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
def quadraticTwistOf (t n : K) : WeierstrassCurve K where
  a₁ := t * E.a₁
  a₂ := (t ^ 2 - 4 * n) * E.a₂ - n * E.a₁ ^ 2
  a₃ := (t ^ 2 - 4 * n) * t * E.a₃
  a₄ := (t ^ 2 - 4 * n) ^ 2 * E.a₄ - 2 * (t ^ 2 - 4 * n) * n * E.a₁ * E.a₃
  a₆ := (t ^ 2 - 4 * n) ^ 3 * E.a₆ - (t ^ 2 - 4 * n) ^ 2 * n * E.a₃ ^ 2

variable (t n : K)

theorem c₄_quadraticTwistOf : (E.quadraticTwistOf t n).c₄ = (t ^ 2 - 4 * n) ^ 2 * E.c₄ := by
  simp only [quadraticTwistOf, c₄, b₂, b₄]
  ring

theorem Δ_quadraticTwistOf : (E.quadraticTwistOf t n).Δ = (t ^ 2 - 4 * n) ^ 6 * E.Δ := by
  simp only [quadraticTwistOf, Δ, b₂, b₄, b₆, b₈]
  ring

theorem isElliptic_quadraticTwistOf [E.IsElliptic] (hD : t ^ 2 - 4 * n ≠ 0) :
    (E.quadraticTwistOf t n).IsElliptic := by
  rw [isElliptic_iff, Δ_quadraticTwistOf]
  exact (isUnit_iff_ne_zero.mpr (pow_ne_zero 6 hD)).mul E.isUnit_Δ

theorem j_quadraticTwistOf [E.IsElliptic] (h : (E.quadraticTwistOf t n).IsElliptic) :
    (E.quadraticTwistOf t n).j = E.j := by
  have hD : t ^ 2 - 4 * n ≠ 0 := by
    intro h0
    have hu := (E.quadraticTwistOf t n).isUnit_Δ
    rw [Δ_quadraticTwistOf, h0] at hu
    simp at hu
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
  E.isElliptic_quadraticTwistOf _ _ (Algebra.IsQuadraticExtension.discrim_ne_zero K L hθ)

/-- The quadratic twist by a generator `θ` of a separable quadratic extension `L/K` depends on
the choice of `θ` only up to isomorphism over `K`: all generators give isomorphic twists. -/
theorem exists_smul_quadraticTwistBy_eq {θ θ' : L} (hθ : θ ∉ Set.range (algebraMap K L))
    (hθ' : θ' ∉ Set.range (algebraMap K L)) :
    ∃ C : VariableChange K, C • E.quadraticTwistBy θ = E.quadraticTwistBy θ' := by
  obtain ⟨a, b, ha, rfl⟩ :=
    Algebra.IsQuadraticExtension.exists_eq_algebraMap_add_algebraMap_mul K L hθ hθ'
  obtain ⟨σ, hσ⟩ := Algebra.IsQuadraticExtension.exists_algEquiv_ne_one K L
  have ht' : Algebra.trace K L (algebraMap K L b + algebraMap K L a * θ)
      = a * Algebra.trace K L θ + 2 * b := by
    apply FaithfulSMul.algebraMap_injective K L
    simp only [map_add, map_mul, map_ofNat,
      Algebra.IsQuadraticExtension.algebraMap_trace_eq_add K L hσ, AlgEquiv.commutes]
    ring
  have hn' : Algebra.norm K (algebraMap K L b + algebraMap K L a * θ)
      = b ^ 2 + a * b * Algebra.trace K L θ + a ^ 2 * Algebra.norm K θ := by
    apply FaithfulSMul.algebraMap_injective K L
    simp only [map_add, map_mul, map_pow,
      Algebra.IsQuadraticExtension.algebraMap_trace_eq_add K L hσ,
      Algebra.IsQuadraticExtension.algebraMap_norm_eq_mul K L hσ, AlgEquiv.commutes]
    ring
  simp only [quadraticTwistBy, ht', hn']
  exact E.exists_smul_quadraticTwistOf_eq _ _ b ha

end QuadraticTwistBy

/-- The quadratic twist of an elliptic curve `E` over `K` by a separable quadratic extension
`L/K`: the twist `WeierstrassCurve.quadraticTwistBy` by an arbitrarily chosen generator
`θ ∈ L ∖ K`. The twist is independent of this choice up to isomorphism over `K`
(`exists_smul_quadraticTwist_eq_quadraticTwistBy`), that is, up to the action of
`WeierstrassCurve.VariableChange K`; see `WeierstrassCurve.quadraticTwistOf` for the explicit
Weierstrass model. -/
noncomputable def quadraticTwist (E : WeierstrassCurve K) (L : Type*) [Field L] [Algebra K L]
    [Algebra.IsQuadraticExtension K L] [Algebra.IsSeparable K L] : WeierstrassCurve K :=
  E.quadraticTwistBy (Algebra.IsQuadraticExtension.exists_notMem_range_algebraMap K L).choose

-- Let `E/K` be an elliptic curve and let `L/K` be a separable quadratic extension.
variable (E : WeierstrassCurve K) [E.IsElliptic]
variable (L : Type*) [Field L] [Algebra K L]
  [Algebra.IsQuadraticExtension K L] [Algebra.IsSeparable K L]

/-- The quadratic twist of an elliptic curve is an elliptic curve: the twisted model has
discriminant `D⁶·Δ(E)`, and `D ≠ 0` by separability
(`Algebra.IsQuadraticExtension.discrim_ne_zero`). -/
instance : (E.quadraticTwist L).IsElliptic :=
  E.isElliptic_quadraticTwistBy
    (Algebra.IsQuadraticExtension.exists_notMem_range_algebraMap K L).choose_spec

omit [E.IsElliptic] in
/-- The quadratic twist of `E` by `L/K` is isomorphic over `K` to the twist by any given
generator `θ ∈ L ∖ K`: the arbitrary choice made in its definition is harmless. -/
theorem exists_smul_quadraticTwist_eq_quadraticTwistBy {θ : L}
    (hθ : θ ∉ Set.range (algebraMap K L)) :
    ∃ C : VariableChange K, C • E.quadraticTwist L = E.quadraticTwistBy θ :=
  E.exists_smul_quadraticTwistBy_eq
    (Algebra.IsQuadraticExtension.exists_notMem_range_algebraMap K L).choose_spec hθ

/-- The quadratic twist becomes isomorphic to `E` after base change to `L`. (Over a field,
isomorphisms of Weierstrass curves are exactly the admissible changes of variables
`WeierstrassCurve.VariableChange`, acting via `•`.) The point-level consequences of this
isomorphism, which is what most applications need, are recorded separately in
`quadraticTwistPointEquiv` below. -/
theorem exists_smul_quadraticTwist_baseChange_eq :
    ∃ C : VariableChange L, C • (E.quadraticTwist L).baseChange L = E.baseChange L :=
  sorry

/-- Twisting does not change the `j`-invariant, since the curves become isomorphic over `L`. -/
theorem j_quadraticTwist : (E.quadraticTwist L).j = E.j :=
  E.j_quadraticTwistOf _ _ (E.isElliptic_quadraticTwistOf _ _
    (Algebra.IsQuadraticExtension.discrim_ne_zero K L
      (Algebra.IsQuadraticExtension.exists_notMem_range_algebraMap K L).choose_spec))

omit [E.IsElliptic] in
/-- Twisting twice by the same quadratic extension gives back `E`, up to `K`-isomorphism.
(Both twists are taken with respect to the same chosen generator of `L/K`, which is harmless
by `exists_smul_quadraticTwist_eq_quadraticTwistBy`.) -/
theorem exists_smul_quadraticTwist_quadraticTwist_eq :
    ∃ C : VariableChange K, C • (E.quadraticTwist L).quadraticTwist L = E := by
  obtain ⟨C, hC⟩ := E.exists_smul_eq_quadraticTwistOf_quadraticTwistOf _ _
    (Algebra.IsQuadraticExtension.discrim_ne_zero K L
      (Algebra.IsQuadraticExtension.exists_notMem_range_algebraMap K L).choose_spec)
  refine ⟨C⁻¹, ?_⟩
  have h2 : C⁻¹ • (C • E) = E := inv_smul_smul C E
  rw [hC] at h2
  exact h2

/-- If `j(E) ∉ {0, 1728}` (so that the only automorphisms of `E` are `±1`) then the quadratic
twist is *not* isomorphic to `E` over `K`: twisting by `L/K` is a nontrivial operation. This can
fail for `j ∈ {0, 1728}`: e.g. for `E : y² = x³ + x` of `j`-invariant `1728` over `K = ℚ(i)`,
the quadratic twist by any `L = K(d^{1/2})` with `d ∈ (K^×)⁴ ∖ (K^×)²` is isomorphic to `E`
over `K`, because `E` admits the automorphism `(x, y) ↦ (-x, iy)` of order 4. -/
theorem not_exists_smul_quadraticTwist_eq (hj₀ : E.j ≠ 0) (hj₁₇₂₈ : E.j ≠ 1728) :
    ¬∃ C : VariableChange K, C • E.quadraticTwist L = E :=
  sorry

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
    (∃ C : VariableChange K, C • E' = E) ∨ ∃ C : VariableChange K, C • E' = E.quadraticTwist L :=
  sorry

/-- The classical formula for the quadratic twist away from characteristic 2. Suppose
`char K ≠ 2`, so that after completing the square we may assume `E` has the form
`y² = x³ + a₂x² + a₄x + a₆`, and suppose `L = K(α)` where `α² = d` is a nonsquare in `K` (every
separable quadratic extension arises this way when `char K ≠ 2`). Then the quadratic twist of
`E` by `L` is `y² = x³ + da₂x² + d²a₄x + d³a₆`, up to `K`-isomorphism. -/
theorem quadraticTwist_of_two_ne_zero (h2 : (2 : K) ≠ 0) (ha₁ : E.a₁ = 0) (ha₃ : E.a₃ = 0)
    {d : K} (hd : ¬IsSquare d) {α : L} (hα : α ^ 2 = algebraMap K L d) :
    ∃ C : VariableChange K, C • E.quadraticTwist L =
      { a₁ := 0, a₂ := d * E.a₂, a₃ := 0, a₄ := d ^ 2 * E.a₄, a₆ := d ^ 3 * E.a₆ } :=
  sorry

/-! ### The isomorphism on points and its Galois anti-equivariance -/

section PointEquiv

-- Let `M` be a field extension of `L`, for example `L` itself or a separable closure of `K`.
-- `DecidableEq` is needed for the group structure on points.
variable (M : Type*) [Field M] [Algebra K M] [Algebra L M] [IsScalarTower K L M] [DecidableEq M]

/-- The isomorphism `Eᴸ(M) ≅ E(M)` on `M`-points, for any field `M` in a tower `K ⊆ L ⊆ M`:
the base change to `M` of a choice of isomorphism between `Eᴸ` and `E` over `L`. It is natural
in `M` (`quadraticTwistPointEquiv_map`) and transforms the Galois action into the Galois action
twisted by the quadratic character of `L/K` (`quadraticTwistPointEquiv_galois`).

Like the twist itself, this isomorphism is well defined only up to composition with an
`L`-automorphism of `E` — generically, up to sign — and this definition makes an arbitrary but
single choice, consistent across all `M`. -/
noncomputable def quadraticTwistPointEquiv :
    ((E.quadraticTwist L)⁄M).Point ≃+ (E⁄M).Point :=
  sorry

/-- Naturality of `quadraticTwistPointEquiv` in `M`: the isomorphisms on `M`-points over varying
`M ⊇ L` are all induced by a single isomorphism of curves over `L`, so they commute with the
maps on points induced by any `L`-algebra homomorphism. -/
theorem quadraticTwistPointEquiv_map {N : Type*} [Field N] [Algebra K N] [Algebra L N]
    [IsScalarTower K L N] [DecidableEq N] (f : M →ₐ[L] N)
    (P : ((E.quadraticTwist L)⁄M).Point) :
    E.quadraticTwistPointEquiv L N (Affine.Point.map f P) =
      Affine.Point.map f (E.quadraticTwistPointEquiv L M P) :=
  sorry

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
        Affine.Point.map σ.toAlgHom (E.quadraticTwistPointEquiv L M P) :=
  sorry

/-- Special case of `quadraticTwistPointEquiv_galois` over `M = L` itself: the isomorphism
`φ : Eᴸ(L) ≅ E(L)` intertwines the action of the nontrivial element `σ ∈ Gal(L/K)` with `-σ`.
This is the datum classically used to define the twist by Galois descent. -/
theorem quadraticTwistPointEquiv_conj [DecidableEq L] {σ : L ≃ₐ[K] L} (hσ : σ ≠ 1)
    (P : ((E.quadraticTwist L)⁄L).Point) :
    E.quadraticTwistPointEquiv L L (Affine.Point.map σ.toAlgHom P) =
      -Affine.Point.map σ.toAlgHom (E.quadraticTwistPointEquiv L L P) :=
  sorry

/-- The rational points of the quadratic twist, viewed inside `E(L)` via the isomorphism over
`L`, are exactly the points of `E(L)` on which the nontrivial element of `Gal(L/K)` acts as
`-1` (just as `E(K)` consists of the points on which it acts as `+1`). Combined with Galois
descent for points this yields, over a number field, `rank E(L) = rank E(K) + rank Eᴸ(K)`. -/
theorem exists_quadraticTwistPointEquiv_baseChange_eq_iff [DecidableEq K] [DecidableEq L]
    {σ : L ≃ₐ[K] L} (hσ : σ ≠ 1) (P : (E⁄L).Point) :
    (∃ Q : ((E.quadraticTwist L)⁄K).Point,
        E.quadraticTwistPointEquiv L L (Affine.Point.baseChange K L Q) = P) ↔
      Affine.Point.map σ.toAlgHom P = -P :=
  sorry

end PointEquiv

/-! ### Multiplicative reduction becomes split after a quadratic twist -/

section Reduction

-- Let `R` be a discrete valuation ring with fraction field `K` (for example the ring of
-- integers of a nonarchimedean local field).
variable (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Algebra R K] [IsFractionRing R K]

/-- If `E` has multiplicative reduction which is not split, then `E` has a quadratic twist with
split multiplicative reduction — namely the twist by the unramified quadratic extension of `K`:
the reduction of the twist is the same nodal cubic with the Galois action on the two tangent
directions at the node twisted into triviality.

Mathlib's reduction-type predicates apply to a specific Weierstrass equation and require it to
be minimal, while our chosen model `E.quadraticTwist L` of the twist need not be; so the
conclusion is phrased via the minimal model `(E.quadraticTwist L).minimal R`. (Being split
multiplicative is intrinsic, so any other minimal model would do.)

The nonsplitness hypothesis `h` cannot be dropped: if `E` already has split multiplicative
reduction then *no* quadratic twist of `E` has split multiplicative reduction, since the
unramified quadratic twist has nonsplit multiplicative reduction and ramified quadratic twists
have additive reduction. -/
theorem exists_quadraticTwist_hasSplitMultiplicativeReduction [E.HasMultiplicativeReduction R]
    (h : ¬E.HasSplitMultiplicativeReduction R) :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra K L) (_ : Algebra.IsQuadraticExtension K L)
      (_ : Algebra.IsSeparable K L),
      ((E.quadraticTwist L).minimal R).HasSplitMultiplicativeReduction R :=
  sorry

end Reduction

end WeierstrassCurve
