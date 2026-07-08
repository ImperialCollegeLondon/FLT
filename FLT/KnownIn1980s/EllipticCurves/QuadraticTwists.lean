/-
Copyright (c) 2026 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Claude
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.AlgebraicGeometry.EllipticCurve.Reduction
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Norm.Transitivity
public import FLT.KnownIn1980s.EllipticCurves.Aut
public import FLT.KnownIn1980s.EllipticCurves.VariableChangeEquiv
public import FLT.KnownIn1980s.EllipticCurves.LiftSeparableExtension
public import Mathlib.Algebra.QuadraticDiscriminant
public import Mathlib.RingTheory.Localization.NormTrace
public import Mathlib.RingTheory.DedekindDomain.IntegralClosure
public import Mathlib.LinearAlgebra.Charpoly.ToMatrix
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
public import Mathlib.RingTheory.LocalRing.Quotient
public import Mathlib.RingTheory.Trace.Quotient

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

@[expose] public section

open scoped WeierstrassCurve.Affine -- `(E⁄K).Point` notation for the group of `K`-points

/-! ### Quadratic polynomials: separability and splitting criteria -/

namespace Polynomial

/-- The derivative of the quadratic `a X² + b X + c` is `2 a X + b`. -/
theorem derivative_quadratic {R : Type*} [CommSemiring R] (a b c : R) :
    derivative (C a * X ^ 2 + C b * X + C c) = 2 * C a * X + C b := by
  simp only [derivative_add, derivative_mul, derivative_C, derivative_X_pow, derivative_X,
    zero_mul, zero_add, add_zero, mul_one, Nat.cast_ofNat, map_ofNat]
  ring

/-- The Bézout-type identity `(P')² - 4 a · P = C (b² - 4 a c)` for the quadratic
`P = a X² + b X + c`: the discriminant is an explicit combination of `P` and its derivative. -/
theorem sq_derivative_quadratic_sub_mul {R : Type*} [CommRing R] (a b c : R) :
    derivative (C a * X ^ 2 + C b * X + C c) ^ 2
      - 4 * C a * (C a * X ^ 2 + C b * X + C c) = C (b ^ 2 - 4 * a * c) := by
  rw [derivative_quadratic]
  simp only [map_sub, map_mul, map_pow, map_ofNat]
  ring

/-- A polynomial of degree at most `2` over a field splits as soon as it has a root: the root
splits off a linear factor and the cofactor is linear. -/
theorem Splits.of_natDegree_le_two_of_isRoot {k : Type*} [Field k] {p : k[X]}
    (hdeg : p.natDegree ≤ 2) {x : k} (hx : p.IsRoot x) : p.Splits := by
  rcases eq_or_ne p 0 with rfl | hp0
  · exact .zero
  obtain ⟨q, hq⟩ := dvd_iff_isRoot.mpr hx
  have hq0 : q ≠ 0 := fun h => hp0 (by rw [hq, h, mul_zero])
  have hqdeg : q.natDegree ≤ 1 := by
    rw [hq, natDegree_mul (X_sub_C_ne_zero x) hq0, natDegree_X_sub_C] at hdeg
    lia
  rw [hq]
  exact (Splits.of_natDegree_le_one (natDegree_X_sub_C x).le).mul (.of_natDegree_le_one hqdeg)

/-- A quadratic polynomial `a X² + b X + c` (with `a ≠ 0`) over a field is separable exactly when
its discriminant `b² - 4 a c` is nonzero. The `←` direction holds in every characteristic: by the
Bézout identity `sq_derivative_quadratic_sub_mul`, a nonzero (hence invertible) discriminant
exhibits `P` and `P'` as coprime. The `→` direction argues that if the discriminant vanishes then
`P ∣ (P')²`, forcing the coprimality witness `P` to be a unit, contradicting `deg P = 2`. -/
theorem separable_quadratic_iff {k : Type*} [Field k] {a b c : k} (ha : a ≠ 0) :
    (C a * X ^ 2 + C b * X + C c).Separable ↔ b ^ 2 - 4 * a * c ≠ 0 := by
  set P := C a * X ^ 2 + C b * X + C c with hP
  have hid : derivative P ^ 2 - 4 * C a * P = C (b ^ 2 - 4 * a * c) :=
    sq_derivative_quadratic_sub_mul a b c
  constructor
  · intro hsep hdisc
    rw [hdisc, map_zero] at hid
    have hdvd : P ∣ derivative P ^ 2 := ⟨4 * C a, by linear_combination hid⟩
    exact not_isUnit_of_natDegree_pos P (by rw [hP, natDegree_quadratic ha]; norm_num)
      (((separable_def P).mp hsep).pow_right.isUnit_of_dvd' dvd_rfl hdvd)
  · intro hdisc
    rw [separable_def]
    have hdinv : C (b ^ 2 - 4 * a * c)⁻¹ * C (b ^ 2 - 4 * a * c) = 1 := by
      rw [← C_mul, inv_mul_cancel₀ hdisc, C_1]
    exact ⟨-(C (b ^ 2 - 4 * a * c)⁻¹ * 4 * C a), C (b ^ 2 - 4 * a * c)⁻¹ * derivative P,
      by linear_combination C (b ^ 2 - 4 * a * c)⁻¹ * hid + hdinv⟩

/-- A quadratic `a X² + b X + c` (`a ≠ 0`) over a field splits exactly when it has a root
(`Splits.of_natDegree_le_two_of_isRoot`). This is the characteristic-free core of the split
criterion. -/
theorem splits_quadratic_iff_exists_root {k : Type*} [Field k] {a b c : k} (ha : a ≠ 0) :
    (C a * X ^ 2 + C b * X + C c).Splits ↔ ∃ x, a * x ^ 2 + b * x + c = 0 := by
  set p := C a * X ^ 2 + C b * X + C c with hp
  have hdeg : p.natDegree = 2 := natDegree_quadratic ha
  have hp0 : p ≠ 0 := fun h => by rw [h, natDegree_zero] at hdeg; exact two_ne_zero hdeg.symm
  constructor
  · intro hs
    obtain ⟨x, hx⟩ := hs.exists_eval_eq_zero (by simp [degree_eq_natDegree hp0, hdeg])
    rw [hp] at hx
    simp only [eval_add, eval_mul, eval_C, eval_pow, eval_X] at hx
    exact ⟨x, hx⟩
  · rintro ⟨x, hx⟩
    refine Splits.of_natDegree_le_two_of_isRoot hdeg.le (x := x) ?_
    rw [hp, IsRoot]
    simp only [eval_add, eval_mul, eval_C, eval_pow, eval_X]
    linear_combination hx

/-- Over a field of characteristic `≠ 2`, a quadratic `a X² + b X + c` (with `a ≠ 0`) *splits*
exactly when its discriminant `b² - 4 a c` is a square: it splits iff it has a root
(`splits_quadratic_iff_exists_root`), and completing the square
(`discrim_eq_sq_of_quadratic_eq_zero` / `exists_quadratic_eq_zero`) matches roots with square roots
of the discriminant. This is the split-multiplicative-reduction criterion; compare
`separable_quadratic_iff` (separable ↔ discriminant nonzero). -/
theorem splits_quadratic_iff {k : Type*} [Field k] [NeZero (2 : k)] {a b c : k} (ha : a ≠ 0) :
    (C a * X ^ 2 + C b * X + C c).Splits ↔ IsSquare (discrim a b c) := by
  rw [splits_quadratic_iff_exists_root ha]
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨2 * a * x + b, by rw [discrim_eq_sq_of_quadratic_eq_zero (a := a) (b := b) (c := c)
      (x := x) (by linear_combination hx)]; ring⟩
  · rintro ⟨s, hs⟩
    obtain ⟨x, hx⟩ := exists_quadratic_eq_zero ha ⟨s, by rw [hs]⟩
    exact ⟨x, by linear_combination hx⟩

/-- Over a field of characteristic `2`, a *separable* quadratic `a X² + b X + c` (`a, b ≠ 0`)
splits exactly when its Artin–Schreier invariant `a c / b²` lies in the image of `z ↦ z² + z`,
written division-free as `∃ z, b² (z² + z) = a c`. (Substitute `z = a x / b` in a root `x`.) In
residue characteristic `2` this replaces the square-class criterion `splits_quadratic_iff`, since
there `b² - 4 a c = b²`, so separability already forces `b ≠ 0`. -/
theorem splits_quadratic_iff_of_two_eq_zero {k : Type*} [Field k] (h2 : (2 : k) = 0)
    {a b c : k} (ha : a ≠ 0) (hb : b ≠ 0) :
    (C a * X ^ 2 + C b * X + C c).Splits ↔ ∃ z, b ^ 2 * (z ^ 2 + z) = a * c := by
  rw [splits_quadratic_iff_exists_root ha]
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨a * x / b, ?_⟩
    field_simp
    linear_combination hx - c * h2
  · rintro ⟨z, hz⟩
    refine ⟨b * z / a, ?_⟩
    field_simp
    linear_combination hz + a * c * h2

end Polynomial

/-! ### Separable quadratic extensions and their quadratic characters

Mathlib's `Algebra.IsQuadraticExtension K L` says that `L` is free of rank 2 over `K`, so for
field extensions it just means `[L:K] = 2`; we add separability as a further hypothesis
`Algebra.IsSeparable K L` throughout. -/

section QuadraticCharacter

variable (K L : Type*) [Field K] [Field L] [Algebra K L]
  [Algebra.IsQuadraticExtension K L]

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

/-- For a normal subextension `K ⊆ L ⊆ M`, a `K`-automorphism `σ` of `M` fixes `L` pointwise
if and only if its restriction to `L` (`AlgEquiv.restrictNormal`) is the identity. -/
theorem forall_apply_algebraMap_iff_restrictNormal_eq_one (σ : M ≃ₐ[K] M) :
    (∀ x : L, σ (algebraMap L M x) = algebraMap L M x) ↔ σ.restrictNormal L = 1 := by
  simp only [AlgEquiv.ext_iff, AlgEquiv.one_apply, ← AlgEquiv.restrictNormal_commutes]
  exact forall_congr' fun x => (FaithfulSMul.algebraMap_injective L M).eq_iff

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
    obtain ⟨σ, hσ⟩ := Algebra.IsQuadraticExtension.exists_algEquiv_ne_one K L
    have hor := Algebra.IsQuadraticExtension.algEquiv_eq_one_or_eq K L hσ
    have hmul : (φ * φ').restrictNormal L = φ.restrictNormal L * φ'.restrictNormal L :=
      map_mul (AlgEquiv.restrictNormalHom L) φ φ'
    have hsq : σ * σ = 1 := (hor (σ * σ)).resolve_right fun h => absurd (mul_eq_left.mp h) hσ
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
  · exact iff_of_false (fun hc => by simpa using congrArg Units.val hc) h

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
    obtain ⟨σ₀, hσ₀⟩ := Algebra.IsQuadraticExtension.exists_algEquiv_ne_one K L
    obtain ⟨τ, hτ⟩ := AlgEquiv.restrictNormalHom_surjective (F := K) (K₁ := L) (E := M) σ₀
    refine ⟨τ, ?_⟩
    have hne : quadraticCharacter K L M τ ≠ 1 := by
      intro heq
      rw [quadraticCharacter_eq_one_iff] at heq
      refine hσ₀ ?_
      rw [← hτ]
      exact (forall_apply_algebraMap_iff_restrictNormal_eq_one K L M τ).mp heq
    rcases Int.units_eq_one_or (quadraticCharacter K L M τ) with h | h
    · exact absurd h hne
    · exact h

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
    simp only [quadraticTwistOf, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂,
      WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆, map_mul, map_sub,
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
Weierstrass model. (The separability hypothesis is not used to write down the model, but the
twist is only meaningful for separable extensions — see the module docstring.) -/
@[nolint unusedArguments]
noncomputable def quadraticTwist (E : WeierstrassCurve K) (L : Type*) [Field L] [Algebra K L]
    [Algebra.IsQuadraticExtension K L] [Algebra.IsSeparable K L] : WeierstrassCurve K :=
  E.quadraticTwistBy (Algebra.IsQuadraticExtension.exists_notMem_range_algebraMap K L).choose

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
    (V.baseChange L).map (algebraMap L M) = V.baseChange M := by
  simp only [WeierstrassCurve.baseChange]
  rw [map_map, ← IsScalarTower.algebraMap_eq K L M]

end

variable [Algebra.IsQuadraticExtension K L] [Algebra.IsSeparable K L]

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
    ∃ C : VariableChange L, C • (E.quadraticTwist L).baseChange L = E.baseChange L := by
  obtain ⟨σ, hσ⟩ := Algebra.IsQuadraticExtension.exists_algEquiv_ne_one K L
  obtain ⟨θ, hθ⟩ := Algebra.IsQuadraticExtension.exists_notMem_range_algebraMap K L
  have hσθ : σ θ ≠ θ := Algebra.IsQuadraticExtension.algEquiv_apply_ne K L hσ hθ
  have hw : σ θ - θ ≠ 0 := sub_ne_zero.mpr hσθ
  have hT : algebraMap K L (Algebra.trace K L θ) = θ + σ θ :=
    Algebra.IsQuadraticExtension.algebraMap_trace_eq_add K L hσ θ
  have hN : algebraMap K L (Algebra.norm K θ) = θ * σ θ :=
    Algebra.IsQuadraticExtension.algebraMap_norm_eq_mul K L hσ θ
  -- Over `L`, `θ² = tθ - n` (with `t, n` the trace and norm of `θ`), so `w := σθ - θ` satisfies
  -- `w² = t² - 4n = D`; the change of variables with `u = w`, `s = -θa₁`, `t = -Dθa₃` (the
  -- explicit map of the module docstring) carries `E.quadraticTwistBy θ` back to `E` over `L`.
  have hmain : ∃ C : VariableChange L,
      C • (E.quadraticTwistBy θ).baseChange L = E.baseChange L := by
    refine ⟨⟨Units.mk0 (σ θ - θ) hw, 0, -(θ * algebraMap K L E.a₁),
      -((σ θ - θ) ^ 2 * θ * algebraMap K L E.a₃)⟩, ?_⟩
    rw [variableChange_def]
    ext <;>
      simp only [quadraticTwistBy, quadraticTwistOf, baseChange, map_a₁, map_a₂, map_a₃,
        map_a₄, map_a₆, Units.val_inv_eq_inv_val, Units.val_mk0, map_sub, map_mul,
        map_pow, map_ofNat, hT, hN] <;>
      field_simp <;> ring
  -- Bridge the chosen generator in `quadraticTwist L` to `θ`, base changed to `L`.
  obtain ⟨C₁, hC₁⟩ := hmain
  obtain ⟨C₀, hC₀⟩ := E.exists_smul_quadraticTwist_eq_quadraticTwistBy L hθ
  refine ⟨C₁ * C₀.baseChange L, ?_⟩
  have hbase : (C₀.baseChange L) • (E.quadraticTwist L).baseChange L
      = (C₀ • E.quadraticTwist L).baseChange L :=
    map_variableChange (W := E.quadraticTwist L) (C := C₀) (φ := algebraMap K L)
  rw [mul_smul, hbase, hC₀, hC₁]

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

/-- The explicit `L`-isomorphism `Eᴸ ≅ E` from `exists_smul_quadraticTwist_baseChange_eq`, taken
for the twist by a generator `θ`, is **anti-equivariant** for the Galois action: its conjugate by
the nontrivial `σ ∈ Gal(L/K)` differs from it by the automorphism `[-1]` of `E`. This nontrivial
cocycle is the origin of the twist being a nontrivial form of `E`. -/
theorem exists_smul_baseChange_and_map_eq {θ : L} (hθ : θ ∉ Set.range (algebraMap K L))
    {σ : L ≃ₐ[K] L} (hσ : σ ≠ 1) :
    ∃ C : VariableChange L, C • (E.quadraticTwistBy θ).baseChange L = E.baseChange L ∧
      C.map σ.toAlgHom.toRingHom = (E.baseChange L).negVariableChange * C := by
  have hσθ : σ θ ≠ θ := Algebra.IsQuadraticExtension.algEquiv_apply_ne K L hσ hθ
  have hw : σ θ - θ ≠ 0 := sub_ne_zero.mpr hσθ
  have hT : algebraMap K L (Algebra.trace K L θ) = θ + σ θ :=
    Algebra.IsQuadraticExtension.algebraMap_trace_eq_add K L hσ θ
  have hN : algebraMap K L (Algebra.norm K θ) = θ * σ θ :=
    Algebra.IsQuadraticExtension.algebraMap_norm_eq_mul K L hσ θ
  have hσσ : σ (σ θ) = θ := by
    have h2 : σ * σ = 1 := by
      rcases Algebra.IsQuadraticExtension.algEquiv_eq_one_or_eq K L hσ (σ * σ) with h | h
      · exact h
      · exact absurd (mul_eq_left.mp h) hσ
    rw [← AlgEquiv.mul_apply, h2, AlgEquiv.one_apply]
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

/-- **Galois descent for changes of variables.** A change of variables over `L` fixed by the
nontrivial `σ ∈ Gal(L/K)` has all its coefficients in `K`, so it is the base change of a change of
variables over `K`. -/
lemma exists_baseChange_eq_of_map_eq {σ : L ≃ₐ[K] L} (hσ : σ ≠ 1) {C : VariableChange L}
    (hCinv : C.map σ.toAlgHom.toRingHom = C) : ∃ CK : VariableChange K, CK.baseChange L = C := by
  have hap : ⇑σ.toAlgHom.toRingHom = ⇑σ := rfl
  have mem : ∀ x : L, σ x = x → x ∈ Set.range (algebraMap K L) := fun x hx => by
    rw [IsGalois.mem_range_algebraMap_iff_fixed]
    intro φ
    rcases Algebra.IsQuadraticExtension.algEquiv_eq_one_or_eq K L hσ φ with rfl | rfl
    · exact AlgEquiv.one_apply x
    · exact hx
  have hu : σ (C.u : L) = (C.u : L) := by
    have := congrArg (fun D => (D.u : L)) hCinv
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
  -- `α` generates `L/K`: were `α = algebraMap K L c`, then `d = c²` would be a square.
  have hαK : α ∉ Set.range (algebraMap K L) := by
    rintro ⟨c, rfl⟩
    refine hd ⟨c, FaithfulSMul.algebraMap_injective K L ?_⟩
    rw [map_mul, ← sq]
    exact hα.symm
  obtain ⟨σ, hσ⟩ := Algebra.IsQuadraticExtension.exists_algEquiv_ne_one K L
  have hσα : σ α ≠ α := Algebra.IsQuadraticExtension.algEquiv_apply_ne K L hσ hαK
  -- The conjugate of `α` is `-α`, so `θ = α` has trace `0` and norm `-d`.
  have hσαα : σ α = -α := by
    have hσ2 : (σ α) ^ 2 = α ^ 2 := by rw [← map_pow, hα, AlgEquiv.commutes]
    have h1 : (σ α - α) * (σ α + α) = 0 := by linear_combination hσ2
    rcases mul_eq_zero.mp h1 with h | h
    · exact absurd (sub_eq_zero.mp h) hσα
    · exact eq_neg_of_add_eq_zero_left h
  have htr : Algebra.trace K L α = 0 := by
    apply FaithfulSMul.algebraMap_injective K L
    rw [Algebra.IsQuadraticExtension.algebraMap_trace_eq_add K L hσ, hσαα, map_zero, add_neg_cancel]
  have hnm : Algebra.norm K α = -d := by
    apply FaithfulSMul.algebraMap_injective K L
    rw [Algebra.IsQuadraticExtension.algebraMap_norm_eq_mul K L hσ, hσαα, map_neg, ← hα]
    ring
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
    (Algebra.IsQuadraticExtension.exists_notMem_range_algebraMap K L).choose_spec
    (Algebra.IsQuadraticExtension.exists_algEquiv_ne_one K L).choose_spec).choose⁻¹

lemma quadraticTwistVarChange_smul :
    (E.quadraticTwistVarChange L) • E.baseChange L = (E.quadraticTwist L).baseChange L := by
  have h := (E.exists_smul_baseChange_and_map_eq L
    (Algebra.IsQuadraticExtension.exists_notMem_range_algebraMap K L).choose_spec
    (Algebra.IsQuadraticExtension.exists_algEquiv_ne_one K L).choose_spec).choose_spec.1
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
  set σ₀ := (Algebra.IsQuadraticExtension.exists_algEquiv_ne_one K L).choose with hσ₀def
  have hσ₀ : σ₀ ≠ 1 := (Algebra.IsQuadraticExtension.exists_algEquiv_ne_one K L).choose_spec
  obtain rfl : σ = σ₀ :=
    (Algebra.IsQuadraticExtension.algEquiv_eq_one_or_eq K L hσ₀ σ).resolve_left hσ
  have hcoc := (E.exists_smul_baseChange_and_map_eq L
    (Algebra.IsQuadraticExtension.exists_notMem_range_algebraMap K L).choose_spec
    (Algebra.IsQuadraticExtension.exists_algEquiv_ne_one K L).choose_spec).choose_spec.2
  have hinv : ∀ C : VariableChange L,
      C⁻¹.map σ₀.toAlgHom.toRingHom = (C.map σ₀.toAlgHom.toRingHom)⁻¹ :=
    fun C => map_inv (VariableChange.mapHom _) C
  unfold quadraticTwistVarChange
  rw [hinv, hcoc, mul_inv_rev, (E.baseChange L).negVariableChange_inv]

section

variable [E.IsElliptic]

/-- The quadratic twist of an elliptic curve is an elliptic curve: the twisted model has
discriminant `D⁶·Δ(E)`, and `D ≠ 0` by separability
(`Algebra.IsQuadraticExtension.discrim_ne_zero`). -/
instance : (E.quadraticTwist L).IsElliptic :=
  E.isElliptic_quadraticTwistBy
    (Algebra.IsQuadraticExtension.exists_notMem_range_algebraMap K L).choose_spec

/-- Twisting does not change the `j`-invariant, since the curves become isomorphic over `L`. -/
theorem j_quadraticTwist : (E.quadraticTwist L).j = E.j :=
  E.j_quadraticTwistOf _ _ (E.isElliptic_quadraticTwistOf _ _
    (Algebra.IsQuadraticExtension.discrim_ne_zero K L
      (Algebra.IsQuadraticExtension.exists_notMem_range_algebraMap K L).choose_spec))

/-- If `j(E) ∉ {0, 1728}` (so that the only automorphisms of `E` are `±1`) then the quadratic
twist is *not* isomorphic to `E` over `K`: twisting by `L/K` is a nontrivial operation. This can
fail for `j ∈ {0, 1728}`: e.g. for `E : y² = x³ + x` of `j`-invariant `1728` over `K = ℚ(i)`,
the quadratic twist by any `L = K(d^{1/2})` with `d ∈ (K^×)⁴ ∖ (K^×)²` is isomorphic to `E`
over `K`, because `E` admits the automorphism `(x, y) ↦ (-x, iy)` of order 4. -/
theorem not_exists_smul_quadraticTwist_eq (hj₀ : E.j ≠ 0) (hj₁₇₂₈ : E.j ≠ 1728) :
    ¬∃ C : VariableChange K, C • E.quadraticTwist L = E := by
  rintro ⟨CK, hCK⟩
  obtain ⟨σ, hσ⟩ := Algebra.IsQuadraticExtension.exists_algEquiv_ne_one K L
  obtain ⟨θ, hθ⟩ := Algebra.IsQuadraticExtension.exists_notMem_range_algebraMap K L
  obtain ⟨C₁, hiso, hcoc⟩ := E.exists_smul_baseChange_and_map_eq L hθ hσ
  obtain ⟨C₀, hC₀⟩ := E.exists_smul_quadraticTwist_eq_quadraticTwistBy L hθ
  -- Transfer the hypothetical `K`-isomorphism to the twist by `θ`.
  have hDK : (CK * C₀⁻¹) • E.quadraticTwistBy θ = E := by
    rw [mul_smul, ← hC₀, inv_smul_smul, hCK]
  -- Base change it: a `σ`-invariant `L`-isomorphism `(Eᶿ)ᴸ ≅ Eᴸ`.
  set ψ := (CK * C₀⁻¹).baseChange L with hψ
  have hψiso : ψ • (E.quadraticTwistBy θ).baseChange L = E.baseChange L := by
    rw [hψ]
    calc ((CK * C₀⁻¹).baseChange L) • (E.quadraticTwistBy θ).baseChange L
        = ((CK * C₀⁻¹) • E.quadraticTwistBy θ).baseChange L :=
          map_variableChange (W := E.quadraticTwistBy θ) (C := CK * C₀⁻¹) (φ := algebraMap K L)
      _ = E.baseChange L := by rw [hDK]
  have hψinv : ψ.map σ.toAlgHom.toRingHom = ψ := by
    rw [hψ]; exact VariableChange.map_baseChange (C := CK * C₀⁻¹) σ.toAlgHom
  -- `c₄, c₆` of `Eᴸ` are nonzero, so `Aut(Eᴸ) = {±1}`.
  have inj := FaithfulSMul.algebraMap_injective K L
  have hΔL : (E.baseChange L).Δ ≠ 0 := by
    simp only [baseChange, map_Δ]
    exact (map_ne_zero_iff _ inj).mpr E.isUnit_Δ.ne_zero
  have hc4L : (E.baseChange L).c₄ ≠ 0 := by
    simp only [baseChange, map_c₄]
    exact (map_ne_zero_iff _ inj).mpr fun h => hj₀ (E.j_eq_zero h)
  have hc6L : (E.baseChange L).c₆ ≠ 0 := by
    simp only [baseChange, map_c₆]
    exact (map_ne_zero_iff _ inj).mpr (E.c₆_ne_zero_of_j_ne_1728 hj₁₇₂₈)
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
  refine (E.baseChange L).negVariableChange_ne_one hΔL ?_
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
  obtain ⟨σ, hσ⟩ := Algebra.IsQuadraticExtension.exists_algEquiv_ne_one K L
  obtain ⟨θ, hθ⟩ := Algebra.IsQuadraticExtension.exists_notMem_range_algebraMap K L
  obtain ⟨C₁, hiso, hcoc⟩ := E.exists_smul_baseChange_and_map_eq L hθ hσ
  have inj := FaithfulSMul.algebraMap_injective K L
  have hc4L : (E.baseChange L).c₄ ≠ 0 := by
    simp only [baseChange, map_c₄]
    exact (map_ne_zero_iff _ inj).mpr fun hh => hj₀ (E.j_eq_zero hh)
  have hc6L : (E.baseChange L).c₆ ≠ 0 := by
    simp only [baseChange, map_c₆]
    exact (map_ne_zero_iff _ inj).mpr (E.c₆_ne_zero_of_j_ne_1728 hj₁₇₂₈)
  have hmapmul : ∀ a b : VariableChange L, (a * b).map σ.toAlgHom.toRingHom
      = a.map σ.toAlgHom.toRingHom * b.map σ.toAlgHom.toRingHom :=
    fun a b => map_mul (VariableChange.mapHom σ.toAlgHom.toRingHom) a b
  have hmapinv : ∀ a : VariableChange L, a⁻¹.map σ.toAlgHom.toRingHom
      = (a.map σ.toAlgHom.toRingHom)⁻¹ :=
    fun a => map_inv (VariableChange.mapHom σ.toAlgHom.toRingHom) a
  -- The Galois conjugate `σρ = ρ.map σ` is again an isomorphism `E'ᴸ ≅ Eᴸ`.
  have hE'inv : (E'.baseChange L).map σ.toAlgHom.toRingHom = E'.baseChange L :=
    WeierstrassCurve.map_baseChange (W := E') σ.toAlgHom
  have hEinv : (E.baseChange L).map σ.toAlgHom.toRingHom = E.baseChange L :=
    WeierstrassCurve.map_baseChange (W := E) σ.toAlgHom
  have hσρ : (ρ.map σ.toAlgHom.toRingHom) • E'.baseChange L = E.baseChange L := by
    have hmv := map_variableChange (W := E'.baseChange L) (C := ρ) (φ := σ.toAlgHom.toRingHom)
    rw [hρ, hE'inv, hEinv] at hmv
    exact hmv
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
    refine ⟨ρK, WeierstrassCurve.map_injective inj ?_⟩
    calc (ρK • E').baseChange L
        = (ρK.baseChange L) • E'.baseChange L :=
          (map_variableChange (W := E') (C := ρK) (φ := algebraMap K L)).symm
      _ = ρ • E'.baseChange L := by rw [hρK]
      _ = E.baseChange L := hρ
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
    have hE'Tby : χK • E' = E.quadraticTwistBy θ := by
      apply WeierstrassCurve.map_injective inj
      calc (χK • E').baseChange L
          = (χK.baseChange L) • E'.baseChange L :=
            (map_variableChange (W := E') (C := χK) (φ := algebraMap K L)).symm
        _ = (C₁⁻¹ * ρ) • E'.baseChange L := by rw [hχK]
        _ = (E.quadraticTwistBy θ).baseChange L := hχiso
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
  obtain ⟨σ₀, hσ₀⟩ := Algebra.IsQuadraticExtension.exists_algEquiv_ne_one K L
  have hres : σ.restrictNormal L = σ₀ :=
    (Algebra.IsQuadraticExtension.algEquiv_eq_one_or_eq K L hσ₀ _).resolve_left
      (fun h => hσ ((forall_apply_algebraMap_iff_restrictNormal_eq_one K L M σ).mpr h))
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
    (Affine.pointEquivVariableChange (E.baseChange M) ((E.quadraticTwistVarChange L).baseChange M))

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
      Affine.pointEquivVariableChange_some, Affine.Point.map_some]
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
    have h := congrArg (fun C => (VariableChange.u C : M)) hM
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
      Affine.pointEquivVariableChange_some, Affine.Point.map_some, Affine.Point.neg_some]
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
        fun h => hσ ((quadraticCharacter_eq_one_iff K L M σ).mp h)
    rw [hχ, Units.val_neg, Units.val_one, neg_one_zsmul]
    exact E.quadraticTwistPointEquiv_map_of_not_fixed L M hσ P

/-- Special case of `quadraticTwistPointEquiv_galois` over `M = L` itself: the isomorphism
`φ : Eᴸ(L) ≅ E(L)` intertwines the action of the nontrivial element `σ ∈ Gal(L/K)` with `-σ`.
This is the datum classically used to define the twist by Galois descent. -/
theorem quadraticTwistPointEquiv_conj [DecidableEq L] {σ : L ≃ₐ[K] L} (hσ : σ ≠ 1)
    (P : ((E.quadraticTwist L)⁄L).Point) :
    E.quadraticTwistPointEquiv L L (Affine.Point.map σ.toAlgHom P) =
      -Affine.Point.map σ.toAlgHom (E.quadraticTwistPointEquiv L L P) := by
  refine E.quadraticTwistPointEquiv_map_of_not_fixed L L (fun hfix => hσ ?_) P
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
    obtain ⟨x₀, rfl⟩ := (IsGalois.mem_range_algebraMap_iff_fixed x).mpr fun φ => by
      rcases Algebra.IsQuadraticExtension.algEquiv_eq_one_or_eq K L hσ φ with rfl | rfl
      exacts [AlgEquiv.one_apply x, hx]
    obtain ⟨y₀, rfl⟩ := (IsGalois.mem_range_algebraMap_iff_fixed y).mpr fun φ => by
      rcases Algebra.IsQuadraticExtension.algEquiv_eq_one_or_eq K L hσ φ with rfl | rfl
      exacts [AlgEquiv.one_apply y, hy]
    exact ⟨.some x₀ y₀ ((WeierstrassCurve.Affine.baseChange_nonsingular W
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

/-! ### Multiplicative reduction becomes split after a quadratic twist -/

section Reduction

-- Let `R` be a discrete valuation ring with fraction field `K` (for example the ring of
-- integers of a nonarchimedean local field). The instances are introduced in stages, as needed.
variable (R : Type u) [CommRing R] [Algebra R K]

/-- The **node polynomial** `c₄ T² + a₁ c₄ T - (54 b₆ - 3 b₂ b₄ + a₂ c₄)`, whose roots are the
slopes of the two tangent directions at the node of a multiplicative reduction; its splitting over
the residue field governs whether the reduction is split (see `HasSplitMultiplicativeReduction`). -/
noncomputable def nodePoly {A : Type*} [CommRing A] (W : WeierstrassCurve A) : Polynomial A :=
  .C W.c₄ * .X ^ 2 + .C (W.a₁ * W.c₄) * .X - .C (54 * W.b₆ - 3 * W.b₂ * W.b₄ + W.a₂ * W.c₄)

/-- The node polynomial base-changed along a ring homomorphism. -/
lemma nodePoly_map {A : Type*} [CommRing A] {B : Type*} [CommRing B] (φ : A →+* B)
    (W : WeierstrassCurve A) :
    W.nodePoly.map φ = .C (φ W.c₄) * .X ^ 2 + .C (φ (W.a₁ * W.c₄)) * .X
      - .C (φ (54 * W.b₆ - 3 * W.b₂ * W.b₄ + W.a₂ * W.c₄)) := by
  simp only [nodePoly, Polynomial.map_sub, Polynomial.map_add, Polynomial.map_mul,
    Polynomial.map_pow, Polynomial.map_C, Polynomial.map_X]

/-- The root of the (base-changed) node polynomial satisfies its defining quadratic relation. -/
lemma aeval_root_nodePoly_map {A : Type*} [CommRing A] {B : Type*} [CommRing B] (φ : A →+* B)
    (W : WeierstrassCurve A) :
    algebraMap B (AdjoinRoot (W.nodePoly.map φ)) (φ W.c₄) * AdjoinRoot.root (W.nodePoly.map φ) ^ 2
      + algebraMap B (AdjoinRoot (W.nodePoly.map φ)) (φ (W.a₁ * W.c₄))
        * AdjoinRoot.root (W.nodePoly.map φ)
      - algebraMap B (AdjoinRoot (W.nodePoly.map φ))
        (φ (54 * W.b₆ - 3 * W.b₂ * W.b₄ + W.a₂ * W.c₄)) = 0 := by
  have h := congrArg (Polynomial.aeval (AdjoinRoot.root (W.nodePoly.map φ))) (nodePoly_map φ W)
  rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self] at h
  simpa only [map_add, map_sub, map_mul, map_pow, Polynomial.aeval_C, Polynomial.aeval_X]
    using h.symm

/-- Under a change of variables `C = (u, r, s, t)`, the node polynomial transforms by the affine
substitution `T ↦ u T + s` and the unit scalar `u⁻⁶` — reflecting that the tangent slopes `λ`
transform as `λ ↦ (λ - s)/u`. In particular its splitting field is unchanged. -/
lemma nodePoly_smul {A : Type*} [CommRing A] (W : WeierstrassCurve A) (C : VariableChange A) :
    (C • W).nodePoly = .C ((↑C.u⁻¹ : A) ^ 6)
      * W.nodePoly.comp (.C (↑C.u : A) * .X + .C C.s) := by
  have e2 : (↑C.u⁻¹ : A) ^ 6 * (↑C.u : A) ^ 2 = (↑C.u⁻¹ : A) ^ 4 := by
    have := congrArg (Units.val (α := A)) (by group : C.u⁻¹ ^ 6 * C.u ^ 2 = C.u⁻¹ ^ 4)
    simpa only [Units.val_mul, Units.val_pow_eq_pow_val] using this
  have e1 : (↑C.u⁻¹ : A) ^ 6 * (↑C.u : A) = (↑C.u⁻¹ : A) ^ 5 := by
    have := congrArg (Units.val (α := A)) (by group : C.u⁻¹ ^ 6 * C.u = C.u⁻¹ ^ 5)
    simpa only [Units.val_mul, Units.val_pow_eq_pow_val] using this
  have e2p : (algebraMap A (Polynomial A) (↑C.u⁻¹ : A)) ^ 6 * (algebraMap A (Polynomial A) ↑C.u) ^ 2
      = (algebraMap A (Polynomial A) (↑C.u⁻¹ : A)) ^ 4 := by
    rw [← map_pow, ← map_pow, ← map_mul, e2, map_pow]
  have e1p : (algebraMap A (Polynomial A) (↑C.u⁻¹ : A)) ^ 6 * algebraMap A (Polynomial A) ↑C.u
      = (algebraMap A (Polynomial A) (↑C.u⁻¹ : A)) ^ 5 := by
    rw [← map_pow, ← map_mul, e1, map_pow]
  simp only [nodePoly, c₄, variableChange_a₁, variableChange_a₂, variableChange_b₂,
    variableChange_b₄, variableChange_b₆, Polynomial.mul_comp, Polynomial.add_comp,
    Polynomial.sub_comp, Polynomial.C_comp, Polynomial.X_comp, pow_two, mul_add, add_mul,
    mul_sub, sub_mul]
  simp only [Polynomial.C_eq_algebraMap, map_mul, map_pow, map_sub, map_add, map_ofNat]
  linear_combination
    (-(algebraMap A (Polynomial A) W.b₂ ^ 2 - 24 * algebraMap A (Polynomial A) W.b₄) *
        Polynomial.X ^ 2) * e2p +
    (-(2 * (algebraMap A (Polynomial A) W.b₂ ^ 2 - 24 * algebraMap A (Polynomial A) W.b₄) *
            algebraMap A (Polynomial A) C.s +
          algebraMap A (Polynomial A) W.a₁ *
            (algebraMap A (Polynomial A) W.b₂ ^ 2 - 24 * algebraMap A (Polynomial A) W.b₄)) *
        Polynomial.X) * e1p

/-- **Invariance of the node polynomial's splitting under change of variables.** Since a change of
variables transforms the node polynomial by an affine substitution and a nonzero scalar
(`nodePoly_smul`), whether it splits over a field `k` is unchanged. This is what makes split
multiplicative reduction an isomorphism invariant. -/
lemma nodePoly_map_splits_smul_iff {A : Type*} [CommRing A] {k : Type*} [Field k] (φ : A →+* k)
    (W : WeierstrassCurve A) (C : VariableChange A) :
    ((C • W).nodePoly.map φ).Splits ↔ (W.nodePoly.map φ).Splits := by
  have hu : φ (↑C.u : A) ≠ 0 := (RingHom.isUnit_map φ C.u.isUnit).ne_zero
  have hu6 : φ ((↑C.u⁻¹ : A) ^ 6) ≠ 0 := by
    rw [map_pow]; exact pow_ne_zero 6 (RingHom.isUnit_map φ C.u⁻¹.isUnit).ne_zero
  rw [nodePoly_smul, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_comp, Polynomial.map_add,
    Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X, Polynomial.map_C,
    Polynomial.splits_mul_iff_right (Polynomial.C_ne_zero.mpr hu6) (Polynomial.Splits.C _)]
  exact (Polynomial.splits_iff_comp_splits_of_natDegree_eq_one
    (Polynomial.natDegree_linear hu)).symm

open Polynomial in
/-- **Split criterion (residue characteristic ≠ 2).** Over a field `k` of characteristic `≠ 2`, the
node polynomial splits — i.e. the two tangent directions at the node are `k`-rational — exactly when
its discriminant `-c₄ c₆` (`splitPolynomial_discrim`) is a square in `k`. This is the tool that,
applied to a quadratic twist via the scaling `-c₄' c₆' = (t²-4n)⁵ · (-c₄ c₆)`, turns a nonsplit
reduction into a split one after twisting by the right square class. -/
lemma nodePoly_map_splits_iff_isSquare {A : Type*} [CommRing A] {k : Type*} [Field k]
    [NeZero (2 : k)] (φ : A →+* k) (W : WeierstrassCurve A) (hc₄ : φ W.c₄ ≠ 0) :
    (W.nodePoly.map φ).Splits ↔ IsSquare (φ (-(W.c₄ * W.c₆))) := by
  have hform : W.nodePoly.map φ = Polynomial.C (φ W.c₄) * Polynomial.X ^ 2
      + Polynomial.C (φ (W.a₁ * W.c₄)) * Polynomial.X
      + Polynomial.C (-φ (54 * W.b₆ - 3 * W.b₂ * W.b₄ + W.a₂ * W.c₄)) := by
    simp only [nodePoly, Polynomial.map_sub, Polynomial.map_add, Polynomial.map_mul,
      Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C, map_neg]
    ring
  have key : φ (W.a₁ * W.c₄) ^ 2
      - 4 * φ W.c₄ * (-φ (54 * W.b₆ - 3 * W.b₂ * W.b₄ + W.a₂ * W.c₄)) = φ (-(W.c₄ * W.c₆)) := by
    rw [mul_neg, sub_neg_eq_add, ← map_pow, ← map_ofNat φ 4, ← map_mul, ← map_mul, ← map_add]
    refine congrArg φ ?_
    simp only [c₄, c₆, b₂, b₄, b₆]; ring
  rw [hform, Polynomial.splits_quadratic_iff hc₄, discrim, key]

open Polynomial in
/-- **Split criterion (residue characteristic 2).** Over a field `k` of characteristic `2`, where
the square-class criterion `nodePoly_map_splits_iff_isSquare` fails, the node polynomial splits
exactly when its Artin–Schreier invariant lies in the image of `z ↦ z² + z`. Here `c₄` and `c₆` are
units, and separability (`b² = -c₄ c₆ ≠ 0`, since `4 = 0`) forces the linear coefficient
`a₁ c₄` to be nonzero, so `splits_quadratic_iff_of_two_eq_zero` applies. -/
lemma nodePoly_map_splits_iff_of_two_eq_zero {A : Type*} [CommRing A] {k : Type*} [Field k]
    (h2 : (2 : k) = 0) (φ : A →+* k) (W : WeierstrassCurve A) (hc₄ : φ W.c₄ ≠ 0)
    (hc₆ : φ W.c₆ ≠ 0) :
    (W.nodePoly.map φ).Splits ↔ ∃ z, φ (W.a₁ * W.c₄) ^ 2 * (z ^ 2 + z)
      = φ W.c₄ * (-φ (54 * W.b₆ - 3 * W.b₂ * W.b₄ + W.a₂ * W.c₄)) := by
  have hform : W.nodePoly.map φ = Polynomial.C (φ W.c₄) * Polynomial.X ^ 2
      + Polynomial.C (φ (W.a₁ * W.c₄)) * Polynomial.X
      + Polynomial.C (-φ (54 * W.b₆ - 3 * W.b₂ * W.b₄ + W.a₂ * W.c₄)) := by
    simp only [nodePoly, Polynomial.map_sub, Polynomial.map_add, Polynomial.map_mul,
      Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C, map_neg]
    ring
  have hb : φ (W.a₁ * W.c₄) ≠ 0 := by
    have h4 : (4 : k) = 0 := by linear_combination (2 : k) * h2
    have hAk : φ (W.a₁ * W.c₄) ^ 2
        + 4 * (φ W.c₄ * φ (54 * W.b₆ - 3 * W.b₂ * W.b₄ + W.a₂ * W.c₄)) = -(φ W.c₄ * φ W.c₆) := by
      rw [← map_pow, ← map_ofNat φ 4, ← map_mul, ← map_mul, ← map_add, ← map_mul, ← map_neg]
      congr 1
      simp only [c₄, c₆, b₂, b₄, b₆]; ring
    intro h0
    rw [h0, zero_pow two_ne_zero, zero_add, h4, zero_mul] at hAk
    exact (neg_ne_zero.mpr (mul_ne_zero hc₄ hc₆)) hAk.symm
  rw [hform, Polynomial.splits_quadratic_iff_of_two_eq_zero h2 hc₄ hb]

open Polynomial in
/-- **Twisting flips the square class (residue characteristic ≠ 2).** Combining the split criterion
`nodePoly_map_splits_iff_isSquare` with the coefficient scaling of the quadratic twist
(`c₄_quadraticTwistOf`, `c₆_quadraticTwistOf`), the node polynomial of `W.quadraticTwistOf t n`
splits over a field `k` of characteristic `≠ 2` exactly when `D · (-c₄ c₆)` is a square there, where
`D = t² - 4n`. Thus twisting multiplies the square class governing splitting by `D`: it converts a
nonsplit reduction into a split one precisely when `D` and `-c₄ c₆` lie in the same square class. -/
lemma nodePoly_quadraticTwistOf_map_splits_iff {A : Type*} [CommRing A] {k : Type*} [Field k]
    [NeZero (2 : k)] (φ : A →+* k) (W : WeierstrassCurve A) (t n : A) (hc₄ : φ W.c₄ ≠ 0)
    (hD : φ (t ^ 2 - 4 * n) ≠ 0) :
    ((W.quadraticTwistOf t n).nodePoly.map φ).Splits
      ↔ IsSquare (φ ((t ^ 2 - 4 * n) * -(W.c₄ * W.c₆))) := by
  have key : ∀ s y : k, s ≠ 0 → (IsSquare (s ^ 2 * y) ↔ IsSquare y) := fun s y hs =>
    ⟨fun ⟨w, hw⟩ => ⟨w / s, by field_simp; linear_combination hw⟩,
      fun ⟨w, hw⟩ => ⟨s * w, by rw [hw]; ring⟩⟩
  have hc₄' : φ (W.quadraticTwistOf t n).c₄ ≠ 0 := by
    rw [c₄_quadraticTwistOf, map_mul, map_pow]; exact mul_ne_zero (pow_ne_zero 2 hD) hc₄
  rw [nodePoly_map_splits_iff_isSquare φ (W.quadraticTwistOf t n) hc₄',
    show -((W.quadraticTwistOf t n).c₄ * (W.quadraticTwistOf t n).c₆)
        = ((t ^ 2 - 4 * n) ^ 2) ^ 2 * ((t ^ 2 - 4 * n) * -(W.c₄ * W.c₆)) from by
      rw [c₄_quadraticTwistOf, c₆_quadraticTwistOf]; ring,
    map_mul, map_pow,
    key _ _ (show φ ((t ^ 2 - 4 * n) ^ 2) ≠ 0 by rw [map_pow]; exact pow_ne_zero 2 hD)]

/-- The `R`-model twist base-changes to the twist over `K`: for `E` integral over `R`, twisting its
integral model by `t, n : R` and base-changing to `K` equals twisting `E` by the images
`(algebraMap R K t, algebraMap R K n)`. Together with the coefficient laws this is the bridge from
the `K`-twist `E.quadraticTwist L` to a genuine `R`-model whose reduction can be computed. -/
theorem baseChange_integralModel_quadraticTwistOf [IsIntegral R E] (t n : R) :
    ((E.integralModel R).quadraticTwistOf t n)⁄K
      = E.quadraticTwistOf (algebraMap R K t) (algebraMap R K n) := by
  change ((E.integralModel R).quadraticTwistOf t n).map (algebraMap R K) = _
  rw [quadraticTwistOf_map, show (E.integralModel R).map (algebraMap R K) = E
    from baseChange_integralModel_eq R E]

variable [IsFractionRing R K]

/-- The integral model of the base change to `K` of an integral Weierstrass curve `W` over `R` is
`W` itself (integral models are unique, as `R → K` is injective). -/
lemma integralModel_baseChange (W : WeierstrassCurve R) [IsIntegral R (W⁄K)] :
    integralModel R (W⁄K) = W := by
  ext <;> apply IsFractionRing.injective R K <;>
    simp only [integralModel_a₁_eq, integralModel_a₂_eq, integralModel_a₃_eq, integralModel_a₄_eq,
      integralModel_a₆_eq, WeierstrassCurve.baseChange, WeierstrassCurve.map_a₁,
      WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄,
      WeierstrassCurve.map_a₆]

-- From here on, `R` is a discrete valuation ring.
variable [IsDomain R] [IsDiscreteValuationRing R]

/-- **Split multiplicative reduction is a change-of-variables invariant.** If `W` (over `R`) gives a
curve with split multiplicative reduction over `K`, then so does any `R`-change of variables `C • W`
that still has multiplicative reduction — because the split condition is the splitting of the node
polynomial of the integral model, which is invariant by `nodePoly_map_splits_smul_iff`. -/
theorem HasSplitMultiplicativeReduction.baseChange_smul {W : WeierstrassCurve R}
    (C : VariableChange R) [IsMinimal R (W⁄K)]
    (hW : (W⁄K).HasSplitMultiplicativeReduction R)
    [((C • W)⁄K).HasMultiplicativeReduction R] :
    ((C • W)⁄K).HasSplitMultiplicativeReduction R := by
  have hspl := hW.splitMultiplicativeReduction
  rw [show ((W⁄K).integralModel R) = W from integralModel_baseChange R W] at hspl
  refine { ‹((C • W)⁄K).HasMultiplicativeReduction R› with splitMultiplicativeReduction := ?_ }
  rw [show (((C • W)⁄K).integralModel R) = C • W from integralModel_baseChange R (C • W)]
  exact (nodePoly_map_splits_smul_iff (algebraMap R (IsLocalRing.ResidueField R)) W C).mpr hspl

open IsLocalRing IsDedekindDomain.HeightOneSpectrum in
/-- Multiplicative reduction forces `c₄` of the integral model to be a unit: its residue is nonzero
(`valuation c₄ = 1` means `c₄ ∉ maximalIdeal`). -/
lemma residue_integralModel_c₄_ne_zero [E.HasMultiplicativeReduction R] :
    residue R ((E.integralModel R).c₄) ≠ 0 := by
  rw [Ne, residue_eq_zero_iff]
  have hval := ‹E.HasMultiplicativeReduction R›.multiplicativeReduction
  rw [← integralModel_c₄_eq R E, valuation_eq_one_iff_notMem] at hval
  exact hval

open IsLocalRing IsDedekindDomain.HeightOneSpectrum in
/-- Multiplicative reduction (bad reduction) means the discriminant of the integral model has zero
residue. -/
lemma residue_integralModel_Δ_eq_zero [E.HasMultiplicativeReduction R] :
    residue R ((E.integralModel R).Δ) = 0 := by
  rw [residue_eq_zero_iff]
  have hval := ‹E.HasMultiplicativeReduction R›.badReduction
  rw [← integralModel_Δ_eq R E, valuation_lt_one_iff_mem] at hval
  exact hval

open IsLocalRing in
/-- Multiplicative reduction forces `c₆` of the integral model to be a unit too: from
`1728 Δ = c₄³ - c₆²` and `Δ ≡ 0`, `c₆² ≡ c₄³ ≢ 0`. -/
lemma residue_integralModel_c₆_ne_zero [E.HasMultiplicativeReduction R] :
    residue R ((E.integralModel R).c₆) ≠ 0 := by
  intro h
  refine residue_integralModel_c₄_ne_zero E R ?_
  have key : residue R ((E.integralModel R).c₆) ^ 2
      = residue R ((E.integralModel R).c₄) ^ 3 - 1728 * residue R ((E.integralModel R).Δ) := by
    have h1 := congrArg (residue R) ((E.integralModel R).c_relation)
    simp only [map_mul, map_sub, map_pow, map_ofNat] at h1
    linear_combination h1
  rw [h, residue_integralModel_Δ_eq_zero E R, mul_zero, sub_zero, zero_pow (by norm_num)] at key
  exact (pow_eq_zero_iff (by norm_num)).mp key.symm

open IsLocalRing in
/-- Nonsplit multiplicative reduction means precisely that the node polynomial of the integral
model does not split over the residue field. -/
lemma not_splits_nodePoly_of_not_hasSplit [E.HasMultiplicativeReduction R]
    (h : ¬ E.HasSplitMultiplicativeReduction R) :
    ¬ ((E.integralModel R).nodePoly.map (algebraMap R (ResidueField R))).Splits :=
  fun hspl => h { ‹E.HasMultiplicativeReduction R› with splitMultiplicativeReduction := hspl }

open IsLocalRing in
/-- The node polynomial over the residue field is a genuine quadratic (leading coefficient `c₄` is a
unit). -/
lemma natDegree_nodePoly_map [E.HasMultiplicativeReduction R] :
    ((E.integralModel R).nodePoly.map (algebraMap R (ResidueField R))).natDegree = 2 := by
  have ha : algebraMap R (ResidueField R) ((E.integralModel R).c₄) ≠ 0 := by
    rw [ResidueField.algebraMap_eq]; exact residue_integralModel_c₄_ne_zero E R
  simp only [nodePoly, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow,
    Polynomial.map_X, Polynomial.map_C, sub_eq_add_neg, ← Polynomial.C_neg]
  exact Polynomial.natDegree_quadratic ha

open IsLocalRing in
/-- For nonsplit multiplicative reduction, the node polynomial is irreducible over the residue
field: it is a quadratic that does not split, so (over a field) it has no linear factors. -/
lemma irreducible_nodePoly_map [E.HasMultiplicativeReduction R]
    (h : ¬ E.HasSplitMultiplicativeReduction R) :
    Irreducible ((E.integralModel R).nodePoly.map (algebraMap R (ResidueField R))) := by
  set P := (E.integralModel R).nodePoly.map (algebraMap R (ResidueField R)) with hP
  have hns := not_splits_nodePoly_of_not_hasSplit E R h
  have hdeg := natDegree_nodePoly_map E R
  rw [← hP] at hns hdeg
  have hpos : ∀ a : Polynomial (ResidueField R), a ≠ 0 → ¬ IsUnit a → 0 < a.natDegree := by
    intro a ha0 hau
    by_contra hc
    refine hau (Polynomial.isUnit_iff_degree_eq_zero.mpr ?_)
    rw [Polynomial.degree_eq_natDegree ha0, Nat.le_zero.mp (Nat.not_lt.mp hc), Nat.cast_zero]
  have hP0 : P ≠ 0 := fun h0 => by simp [h0] at hdeg
  refine ⟨Polynomial.not_isUnit_of_natDegree_pos P (by rw [hdeg]; norm_num), fun a b hab => ?_⟩
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨hna, hnb⟩ := hcon
  have ha0 : a ≠ 0 := fun h0 => hP0 (by rw [hab, h0, zero_mul])
  have hb0 : b ≠ 0 := fun h0 => hP0 (by rw [hab, h0, mul_zero])
  have hsum : a.natDegree + b.natDegree = 2 := by rw [← hdeg, hab, Polynomial.natDegree_mul ha0 hb0]
  have hda := hpos a ha0 hna
  have hdb := hpos b hb0 hnb
  exact hns (hab ▸ (Polynomial.Splits.of_natDegree_le_one (by omega)).mul
    (Polynomial.Splits.of_natDegree_le_one (by omega)))

open IsLocalRing in
/-- For multiplicative reduction the node polynomial is separable over the residue field: its
discriminant is `-c₄ c₆` (`splitPolynomial_discrim`), a unit, so the quadratic-separability
criterion `Polynomial.separable_quadratic_iff` applies. -/
lemma separable_nodePoly_map [E.HasMultiplicativeReduction R] :
    ((E.integralModel R).nodePoly.map (algebraMap R (ResidueField R))).Separable := by
  set φ := algebraMap R (ResidueField R) with hφ
  set I := E.integralModel R with hI
  have ha : φ I.c₄ ≠ 0 := by
    rw [hφ, ResidueField.algebraMap_eq]; exact residue_integralModel_c₄_ne_zero E R
  -- Present the reduced node polynomial as a quadratic `C c₄ · X² + C (a₁ c₄) · X + C (-D)`.
  have hform : I.nodePoly.map φ = Polynomial.C (φ I.c₄) * Polynomial.X ^ 2
      + Polynomial.C (φ (I.a₁ * I.c₄)) * Polynomial.X
      + Polynomial.C (-φ (54 * I.b₆ - 3 * I.b₂ * I.b₄ + I.a₂ * I.c₄)) := by
    simp only [nodePoly, Polynomial.map_sub, Polynomial.map_add, Polynomial.map_mul,
      Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C, map_neg]
    ring
  rw [hform, Polynomial.separable_quadratic_iff ha]
  -- Its discriminant is `-c₄ c₆` (`splitPolynomial_discrim`), a unit of the residue field.
  have key : φ (I.a₁ * I.c₄) ^ 2 - 4 * φ I.c₄ * (-φ (54 * I.b₆ - 3 * I.b₂ * I.b₄ + I.a₂ * I.c₄))
      = φ (-(I.c₄ * I.c₆)) := by
    rw [mul_neg, sub_neg_eq_add, ← map_pow, ← map_ofNat φ 4, ← map_mul, ← map_mul, ← map_add]
    refine congrArg φ ?_
    simp only [c₄, c₆, b₂, b₄, b₆]; ring
  rw [key, map_neg, map_mul, neg_ne_zero, mul_ne_zero_iff, hφ, ResidueField.algebraMap_eq]
  exact ⟨residue_integralModel_c₄_ne_zero E R, residue_integralModel_c₆_ne_zero E R⟩

open IsDiscreteValuationRing IsDedekindDomain.HeightOneSpectrum in
/-- **Minimality criterion.** An integral Weierstrass equation over `K` whose `c₄` is a unit of `R`
(equivalently, `valuation c₄ = 1`) is already minimal: any change of variables `C` keeping the
equation integral must have `valuation C.u ≥ 1` (else `valuation (C • W).c₄ = valuation C.u⁻⁴ > 1`,
contradicting integrality), so `valuation (C • W).Δ = valuation C.u⁻¹² · valuation W.Δ ≤ valuation
W.Δ`. This is the tool that shows the twist `W` we build is minimal without minimising by hand. -/
theorem isMinimal_of_valuation_c₄_eq_one (W : WeierstrassCurve K) [hint : IsIntegral R W]
    (hc₄ : valuation K (maximalIdeal R) W.c₄ = 1) : IsMinimal R W := by
  refine ⟨⟨by simpa using hint, fun C hC _ => ?_⟩⟩
  have hCi : IsIntegral R (C • W) := hC
  simp only [← Subtype.coe_le_coe, one_smul, valuation_Δ_aux_eq_of_isIntegral R (C • W),
    valuation_Δ_aux_eq_of_isIntegral R W]
  set v := valuation K (maximalIdeal R) with hv
  set y := v ((C.u⁻¹ : Kˣ) : K) with hy
  -- From integrality, `valuation (C • W).c₄ = y⁴ · valuation W.c₄ = y⁴ ≤ 1`, hence `y ≤ 1`.
  have huc : v ((C • W).c₄) ≤ 1 := by
    rw [← integralModel_c₄_eq R (C • W)]; exact valuation_le_one (maximalIdeal R) _
  rw [variableChange_c₄, map_mul, map_pow, ← hy, hc₄, mul_one] at huc
  have hy1 : y ≤ 1 := by
    by_contra hgt
    exact absurd (one_lt_pow₀ (lt_of_not_ge hgt) (by norm_num)) (not_lt.mpr huc)
  -- Therefore `valuation (C • W).Δ = y¹² · valuation W.Δ ≤ valuation W.Δ`.
  rw [variableChange_Δ, map_mul, map_pow, ← hy]
  exact mul_le_of_le_one_left zero_le (pow_le_one₀ zero_le hy1)

open IsLocalRing IsDedekindDomain.HeightOneSpectrum in
/-- **The twist by a unit discriminant keeps multiplicative reduction.** If `E` has multiplicative
reduction and `D = t² - 4n` is a unit of `R` (residue `≠ 0`), then the base change of the `R`-model
twist `(E.integralModel R).quadraticTwistOf t n` again has multiplicative reduction: its
`c₄ = D² · c₄` is a unit (so the model is minimal and the reduction multiplicative) and its
`Δ = D⁶ · Δ` still has positive valuation. -/
theorem hasMultiplicativeReduction_baseChange_quadraticTwistOf [E.HasMultiplicativeReduction R]
    (t n : R) (hD : residue R (t ^ 2 - 4 * n) ≠ 0) :
    (((E.integralModel R).quadraticTwistOf t n)⁄K).HasMultiplicativeReduction R := by
  set W := (E.integralModel R).quadraticTwistOf t n with hW
  have hWint : IsIntegral R (W⁄K) := ⟨⟨W, rfl⟩⟩
  -- `residue W.c₄ = residue D² · residue (E.integralModel R).c₄ ≠ 0`, `residue W.Δ = 0`.
  have hc₄res : residue R W.c₄ ≠ 0 := by
    rw [hW, c₄_quadraticTwistOf, map_mul, map_pow]
    exact mul_ne_zero (pow_ne_zero 2 hD) (residue_integralModel_c₄_ne_zero E R)
  have hΔres : residue R W.Δ = 0 := by
    rw [hW, Δ_quadraticTwistOf, map_mul, map_pow, residue_integralModel_Δ_eq_zero E R, mul_zero]
  -- Convert to the valuation conditions on the base change `W⁄K`.
  have hc₄val : valuation K (IsDiscreteValuationRing.maximalIdeal R) (W⁄K).c₄ = 1 := by
    rw [show (W⁄K).c₄ = algebraMap R K W.c₄ from map_c₄ W (algebraMap R K)]
    exact (IsDiscreteValuationRing.maximalIdeal R).valuation_eq_one_iff_notMem.mpr
      fun hmem => hc₄res ((residue_eq_zero_iff W.c₄).mpr hmem)
  have hΔval : valuation K (IsDiscreteValuationRing.maximalIdeal R) (W⁄K).Δ < 1 := by
    rw [show (W⁄K).Δ = algebraMap R K W.Δ from map_Δ W (algebraMap R K)]
    exact ((IsDiscreteValuationRing.maximalIdeal R).valuation_lt_one_iff_mem W.Δ).mpr
      ((residue_eq_zero_iff W.Δ).mp hΔres)
  have : IsMinimal R (W⁄K) := isMinimal_of_valuation_c₄_eq_one R (W⁄K) hc₄val
  exact { badReduction := hΔval, multiplicativeReduction := hc₄val }

open IsLocalRing in
/-- **Norm and the residue field.** For a finite free algebra `B` over a local ring `A`, the norm of
the reduction of `x` is the reduction of the norm. This is the norm analogue of
`Algebra.trace_quotient_mk`; the proof is identical, using `RingHom.map_det` in place of the matrix
trace map. -/
theorem norm_quotient_mk {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] [IsLocalRing A]
    [Module.Free A B] [Module.Finite A B] (x : B) :
    Algebra.norm (A ⧸ maximalIdeal A)
        (Ideal.Quotient.mk (Ideal.map (algebraMap A B) (maximalIdeal A)) x)
      = Ideal.Quotient.mk (maximalIdeal A) (Algebra.norm A x) := by
  classical
  letI : Field (A ⧸ maximalIdeal A) := Ideal.Quotient.field _
  let b : Module.Basis (Module.Free.ChooseBasisIndex A B) A B := Module.Free.chooseBasis A B
  rw [Algebra.norm_eq_matrix_det (basisQuotient b), Algebra.norm_eq_matrix_det b, RingHom.map_det]
  congr 1
  ext i j
  simp only [Algebra.leftMulMatrix_apply, Algebra.coe_lmul_eq_mul, LinearMap.toMatrix_apply,
    basisQuotient_apply, LinearMap.mul_apply', RingHom.mapMatrix_apply, Matrix.map_apply,
    ← map_mul, basisQuotient_repr]

/-- **Rank-2 Cayley–Hamilton.** Every element `θ` of a free rank-2 `A`-algebra `B` satisfies its
characteristic polynomial `X² - (trace θ) X + (norm θ)`: this is Cayley–Hamilton
(`Algebra.aeval_self_charpoly_lmul`) applied to left multiplication by `θ`, whose characteristic
polynomial is `X² - trace X + norm` in rank two (`Matrix.charpoly_fin_two`). -/
theorem sq_sub_trace_mul_self_add_norm {A B : Type*} [CommRing A] [Nontrivial A] [CommRing B]
    [Algebra A B] [Module.Free A B] [Module.Finite A B] (h2 : Module.finrank A B = 2) (θ : B) :
    θ ^ 2 - algebraMap A B (Algebra.trace A B θ) * θ + algebraMap A B (Algebra.norm A θ) = 0 := by
  classical
  set b : Module.Basis (Fin 2) A B := Module.finBasisOfFinrankEq A B h2 with hb
  have hcp : (Algebra.lmul A B θ).charpoly
      = Polynomial.X ^ 2 - Polynomial.C (Algebra.trace A B θ) * Polynomial.X
        + Polynomial.C (Algebra.norm A θ) := by
    rw [← LinearMap.charpoly_toMatrix (Algebra.lmul A B θ) b, ← Algebra.leftMulMatrix_apply,
      Matrix.charpoly_fin_two, ← Algebra.trace_eq_matrix_trace b, ← Algebra.norm_eq_matrix_det b]
  have hCH := Algebra.aeval_self_charpoly_lmul (R := A) (M := B) θ
  rw [hcp] at hCH
  simpa only [map_add, map_sub, map_mul, map_pow, Polynomial.aeval_X, Polynomial.aeval_C]
    using hCH

/-- An element satisfying a monic quadratic relation with coefficients in `A` is integral. -/
theorem isIntegral_of_sq_add_mul_add_eq_zero {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    {x : B} (a b : A) (h : x ^ 2 + algebraMap A B a * x + algebraMap A B b = 0) :
    _root_.IsIntegral A x := by
  refine ⟨Polynomial.X ^ 2 + (Polynomial.C a * Polynomial.X + Polynomial.C b), ?_, ?_⟩
  · apply Polynomial.monic_X_pow_add
    compute_degree!
  · rw [← Polynomial.aeval_def]
    simp only [map_add, map_mul, map_pow, Polynomial.aeval_X, Polynomial.aeval_C]
    linear_combination h

/-- An element satisfying a monic quartic relation (with no cubic term) with coefficients in `A`
is integral. -/
theorem isIntegral_of_pow_four_add_eq_zero {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    {x : B} (a b c : A)
    (h : x ^ 4 + algebraMap A B a * x ^ 2 + algebraMap A B b * x + algebraMap A B c = 0) :
    _root_.IsIntegral A x := by
  refine ⟨Polynomial.X ^ 4 + (Polynomial.C a * Polynomial.X ^ 2 + Polynomial.C b * Polynomial.X
    + Polynomial.C c), ?_, ?_⟩
  · apply Polynomial.monic_X_pow_add
    compute_degree!
  · rw [← Polynomial.aeval_def]
    simp only [map_add, map_mul, map_pow, Polynomial.aeval_X, Polynomial.aeval_C]
    linear_combination h

/-- For a minimal Weierstrass model `W`, no integral change of variables increases the valuation
of the discriminant. -/
theorem valuation_Δ_aux_smul_le {W : WeierstrassCurve K} [hm : IsMinimal R W]
    (D : VariableChange K) (hint : IsIntegral R (D • W)) :
    valuation_Δ_aux R (D • W) ≤ valuation_Δ_aux R ((1 : VariableChange K) • W) := by
  rcases le_total (valuation_Δ_aux R ((1 : VariableChange K) • W)) (valuation_Δ_aux R (D • W))
    with h | h
  · exact hm.val_Δ_maximal.2 hint h
  · exact h

open IsDedekindDomain.HeightOneSpectrum IsDiscreteValuationRing IsLocalRing in
/-- Two minimal Weierstrass models related by a change of variables have the same valuation of
the discriminant. -/
theorem valuation_Δ_eq_of_isMinimal_smul {W₁ W₂ : WeierstrassCurve K} [IsMinimal R W₁]
    [IsMinimal R W₂] (D : VariableChange K) (hD : D • W₁ = W₂) :
    valuation K (maximalIdeal R) W₂.Δ = valuation K (maximalIdeal R) W₁.Δ := by
  rw [← valuation_Δ_aux_eq_of_isIntegral R W₂, ← valuation_Δ_aux_eq_of_isIntegral R W₁]
  refine le_antisymm (Subtype.coe_le_coe.mpr ?_) (Subtype.coe_le_coe.mpr ?_)
  · have hsub := valuation_Δ_aux_smul_le R D
      (show IsIntegral R (D • W₁) by rw [hD]; infer_instance)
    rwa [hD, one_smul] at hsub
  · have hW₁eq : W₁ = D⁻¹ • W₂ := by rw [← hD, inv_smul_smul]
    have hsub := valuation_Δ_aux_smul_le R D⁻¹
      (show IsIntegral R (D⁻¹ • W₂) by rw [← hW₁eq]; infer_instance)
    rwa [← hW₁eq, one_smul] at hsub

open IsDedekindDomain.HeightOneSpectrum IsDiscreteValuationRing IsLocalRing in
/-- An element of the fraction field of a discrete valuation ring with valuation `1` is the image
of a unit. -/
theorem exists_algebraMap_unit_eq_of_valuation_eq_one {x : K}
    (hx : valuation K (maximalIdeal R) x = 1) : ∃ u : Rˣ, algebraMap R K ↑u = x := by
  obtain ⟨u₀, hu₀⟩ := associated_of_valuation_eq (A := R) (K := K) x 1 (by rw [map_one]; exact hx)
  have h1 : algebraMap R K ↑u₀ * x = 1 := by rw [← Algebra.smul_def]; exact hu₀
  have h2 : algebraMap R K ↑u₀ * algebraMap R K ↑u₀⁻¹ = 1 := by
    rw [← map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, map_one]
  exact ⟨u₀⁻¹, mul_left_cancel₀ (left_ne_zero_of_mul_eq_one h1) (h2.trans h1.symm)⟩

open IsDedekindDomain.HeightOneSpectrum IsDiscreteValuationRing IsLocalRing in
/-- The scaling factor of a change of variables between two minimal models of a curve with
nonzero discriminant has valuation `1`: the valuations of the discriminants agree and differ by
a factor `v(u)⁻¹²`. -/
theorem valuation_u_eq_one_of_isMinimal_smul {W₁ W₂ : WeierstrassCurve K} [IsMinimal R W₁]
    [IsMinimal R W₂] (D : VariableChange K) (hD : D • W₁ = W₂) (hΔ₁ : W₁.Δ ≠ 0) :
    valuation K (maximalIdeal R) ↑D.u = 1 := by
  have hΔ0 : valuation K (maximalIdeal R) W₁.Δ ≠ 0 := (Valuation.ne_zero_iff _).mpr hΔ₁
  have h12 : valuation K (maximalIdeal R) ↑D.u ^ 12 = 1 := by
    have key : valuation K (maximalIdeal R) W₁.Δ
        = (valuation K (maximalIdeal R) ↑D.u)⁻¹ ^ 12 * valuation K (maximalIdeal R) W₁.Δ := by
      conv_lhs => rw [← valuation_Δ_eq_of_isMinimal_smul R D hD, ← hD, variableChange_Δ]
      rw [map_mul, map_pow, Units.val_inv_eq_inv_val, map_inv₀]
    have h1 : (valuation K (maximalIdeal R) ↑D.u)⁻¹ ^ 12 = 1 :=
      mul_right_cancel₀ hΔ0 (key.symm.trans (one_mul _).symm)
    rw [inv_pow] at h1
    exact inv_eq_one.mp h1
  exact (pow_eq_one_iff_of_nonneg zero_le (by norm_num)).mp h12

/-- A change of variables `D` relating two integral Weierstrass models whose scaling factor `D.u`
is the image of a unit of `R` is itself defined over `R`: `r`, `s`, `t` are integral over `R` —
roots of monic polynomials obtained from the change-of-variables formulas for the
`b₆`/`b₈`/`a₂`/`a₆`-invariants — hence lie in `R` since `R` is integrally closed. -/
theorem exists_variableChange_baseChange_eq_of_smul_eq {W₁ W₂ : WeierstrassCurve K}
    [IsIntegral R W₁] [IsIntegral R W₂] (D : VariableChange K) (hD : D • W₁ = W₂) (u₀ : Rˣ)
    (hau : algebraMap R K ↑u₀ = ↑D.u) : ∃ C₀ : VariableChange R, C₀.baseChange K = D := by
  have hune : (↑D.u : K) ≠ 0 := D.u.ne_zero
  -- `D.r ∈ R`: a root of the monic quartic `X⁴ - b₄ X² + (-2b₆ - u⁶b₆')X + (u⁸b₈' - b₈)` obtained
  -- as `r·P₃ - P₄` from the `b₆`- and `b₈`-relations.
  have hb₆ : (↑D.u : K) ^ 6 * W₂.b₆
      = W₁.b₆ + 2 * D.r * W₁.b₄ + D.r ^ 2 * W₁.b₂ + 4 * D.r ^ 3 := by
    rw [← hD, variableChange_b₆]
    simp only [Units.val_inv_eq_inv_val]
    field_simp
  have hb₈ : (↑D.u : K) ^ 8 * W₂.b₈
      = W₁.b₈ + 3 * D.r * W₁.b₆ + 3 * D.r ^ 2 * W₁.b₄ + D.r ^ 3 * W₁.b₂ + 3 * D.r ^ 4 := by
    rw [← hD, variableChange_b₈]
    simp only [Units.val_inv_eq_inv_val]
    field_simp
  obtain ⟨rR, hrR⟩ := IsIntegrallyClosed.isIntegral_iff.mp
    (isIntegral_of_pow_four_add_eq_zero (x := D.r) (-(W₁.integralModel R).b₄)
      (-(2 * (W₁.integralModel R).b₆) - (↑u₀ : R) ^ 6 * (W₂.integralModel R).b₆)
      ((↑u₀ : R) ^ 8 * (W₂.integralModel R).b₈ - (W₁.integralModel R).b₈) (by
        simp only [map_sub, map_neg, map_mul, map_pow, map_ofNat]
        rw [integralModel_b₄_eq R W₁, integralModel_b₆_eq R W₁, integralModel_b₈_eq R W₁,
          integralModel_b₆_eq R W₂, integralModel_b₈_eq R W₂, hau]
        linear_combination hb₈ - D.r * hb₆))
  -- `D.s ∈ R`: a root of the monic quadratic `X² + a₁ X + (u²·a₂' - a₂ - 3r)`.
  have ha₂ : (↑D.u : K) ^ 2 * W₂.a₂ = W₁.a₂ - D.s * W₁.a₁ + 3 * D.r - D.s ^ 2 := by
    rw [← hD, variableChange_a₂]
    simp only [Units.val_inv_eq_inv_val]
    field_simp
  obtain ⟨sR, hsR⟩ := IsIntegrallyClosed.isIntegral_iff.mp
    (isIntegral_of_sq_add_mul_add_eq_zero (x := D.s) (W₁.integralModel R).a₁
      ((↑u₀ : R) ^ 2 * (W₂.integralModel R).a₂ - (W₁.integralModel R).a₂ - 3 * rR) (by
        simp only [map_sub, map_mul, map_pow, map_ofNat]
        rw [integralModel_a₁_eq R W₁, integralModel_a₂_eq R W₁, integralModel_a₂_eq R W₂, hau, hrR]
        linear_combination ha₂))
  -- `D.t ∈ R`: a root of the monic quadratic
  -- `X² + (a₃ + r·a₁) X + (u⁶·a₆' - a₆ - r·a₄ - r²·a₂ - r³)`.
  have ha₆ : (↑D.u : K) ^ 6 * W₂.a₆ = W₁.a₆ + D.r * W₁.a₄ + D.r ^ 2 * W₁.a₂ + D.r ^ 3
      - D.t * W₁.a₃ - D.t ^ 2 - D.r * D.t * W₁.a₁ := by
    rw [← hD, variableChange_a₆]
    simp only [Units.val_inv_eq_inv_val]
    field_simp
  obtain ⟨tR, htR⟩ := IsIntegrallyClosed.isIntegral_iff.mp
    (isIntegral_of_sq_add_mul_add_eq_zero (x := D.t)
      ((W₁.integralModel R).a₃ + rR * (W₁.integralModel R).a₁)
      (-((W₁.integralModel R).a₆ + rR * (W₁.integralModel R).a₄
        + rR ^ 2 * (W₁.integralModel R).a₂ + rR ^ 3) + (↑u₀ : R) ^ 6 * (W₂.integralModel R).a₆) (by
        simp only [map_add, map_neg, map_mul, map_pow]
        rw [integralModel_a₁_eq R W₁, integralModel_a₂_eq R W₁, integralModel_a₃_eq R W₁,
          integralModel_a₄_eq R W₁, integralModel_a₆_eq R W₁, integralModel_a₆_eq R W₂, hau, hrR]
        linear_combination ha₆))
  exact ⟨⟨u₀, rR, sR, tR⟩, VariableChange.ext (Units.ext hau) hrR hsR htR⟩

open IsDedekindDomain.HeightOneSpectrum IsDiscreteValuationRing IsLocalRing in
/-- **Split multiplicative reduction is an isomorphism invariant of minimal models.** If two minimal
Weierstrass models `W₁`, `W₂` over `K` are related by a change of variables (`D • W₁ = W₂`) with
`W₁.Δ ≠ 0`, and `W₁` has split multiplicative reduction, then so does `W₂`.

This is a form of Silverman VII.1.3(b) (uniqueness of minimal models over a discrete valuation
ring): the change `D` has `u ∈ Rˣ` (`valuation_u_eq_one_of_isMinimal_smul`), so it is defined over
`R` (`exists_variableChange_baseChange_eq_of_smul_eq`); then the node polynomial's splitting
transfers by `nodePoly_map_splits_smul_iff`. -/
theorem HasSplitMultiplicativeReduction.of_isMinimal_smul {W₁ W₂ : WeierstrassCurve K}
    [IsMinimal R W₁] [IsMinimal R W₂] (D : VariableChange K) (hD : D • W₁ = W₂)
    (hΔ₁ : W₁.Δ ≠ 0) (h₁ : W₁.HasSplitMultiplicativeReduction R) :
    W₂.HasSplitMultiplicativeReduction R := by
  -- `D.u` is the image of a unit of `R`, so `D` descends to `C₀ : VariableChange R`.
  have hvu := valuation_u_eq_one_of_isMinimal_smul R D hD hΔ₁
  obtain ⟨u₀, hau⟩ := exists_algebraMap_unit_eq_of_valuation_eq_one R hvu
  obtain ⟨C₀, hDC₀⟩ := exists_variableChange_baseChange_eq_of_smul_eq R D hD u₀ hau
  have hW₂eq : (C₀ • W₁.integralModel R)⁄K = W₂ := by
    rw [show ((C₀ • W₁.integralModel R)⁄K)
        = (C₀ • W₁.integralModel R).map (algebraMap R K) from rfl, ← map_variableChange,
      show C₀.map (algebraMap R K) = D from hDC₀,
      show (W₁.integralModel R).map (algebraMap R K) = W₁ from baseChange_integralModel_eq R W₁, hD]
  -- `W₂` has multiplicative reduction: `v(D.u) = 1` fixes the valuations of `Δ` and `c₄`.
  have hΔeq := valuation_Δ_eq_of_isMinimal_smul R D hD
  have hc₄eq : valuation K (maximalIdeal R) W₂.c₄ = valuation K (maximalIdeal R) W₁.c₄ := by
    rw [← hD, variableChange_c₄, map_mul]
    simp only [Units.val_inv_eq_inv_val, map_pow, map_inv₀, hvu, inv_one, one_pow, one_mul]
  have hmult₂ : W₂.HasMultiplicativeReduction R :=
    { badReduction := by rw [hΔeq]; exact h₁.toHasMultiplicativeReduction.badReduction
      multiplicativeReduction := by
        rw [hc₄eq]; exact h₁.toHasMultiplicativeReduction.multiplicativeReduction }
  refine { hmult₂ with splitMultiplicativeReduction := ?_ }
  have hint₂ : W₂.integralModel R = C₀ • W₁.integralModel R := by
    apply WeierstrassCurve.map_injective (IsFractionRing.injective R K)
    change ((W₂.integralModel R)⁄K) = ((C₀ • W₁.integralModel R)⁄K)
    exact (baseChange_integralModel_eq R W₂).trans hW₂eq.symm
  rw [hint₂]
  exact (nodePoly_map_splits_smul_iff (algebraMap R (ResidueField R)) (W₁.integralModel R) C₀).mpr
    h₁.splitMultiplicativeReduction

open IsLocalRing in
/-- If the residue of an integral element `θ` of `S` does not come from the residue field of `R`,
then `θ` does not come from `K` either: an element of `K` integral over the integrally closed `R`
lies in `R`, and residues are compatible. -/
theorem notMem_range_algebraMap_of_residue_notMem {S : Type u} [CommRing S] [IsLocalRing S]
    [Algebra R S] [Algebra.IsIntegral R S] [IsLocalHom (algebraMap R S)] {L : Type u} [Field L]
    [Algebra K L] [Algebra R L] [Algebra S L] [IsScalarTower R S L] [IsScalarTower R K L]
    [IsFractionRing S L] {θ : S}
    (hθ : residue S θ ∉ Set.range (algebraMap (ResidueField R) (ResidueField S))) :
    algebraMap S L θ ∉ Set.range (algebraMap K L) := by
  rintro ⟨a, ha⟩
  have haint : _root_.IsIntegral R a := by
    have h1 : _root_.IsIntegral R (algebraMap S L θ) :=
      _root_.IsIntegral.map (IsScalarTower.toAlgHom R S L) (Algebra.IsIntegral.isIntegral θ)
    rw [← ha] at h1
    exact (isIntegral_algHom_iff (IsScalarTower.toAlgHom R K L)
      (FaithfulSMul.algebraMap_injective K L)).mp h1
  obtain ⟨r, hr⟩ := IsIntegrallyClosed.isIntegral_iff.mp haint
  refine hθ ⟨residue R r, ?_⟩
  rw [show algebraMap (ResidueField R) (ResidueField S) (residue R r)
    = residue S (algebraMap R S r) by simp only [← ResidueField.algebraMap_residue]]
  congr 1
  apply IsFractionRing.injective S L
  rw [← ha, ← hr, ← IsScalarTower.algebraMap_apply R S L, ← IsScalarTower.algebraMap_apply R K L]

open IsLocalRing in
/-- The key identity `φc₄ · φ(t'² - 4n') = -φc₆` of the twisting datum `(t', n')`: if its residues
satisfy the trace and norm relations cut out by the node polynomial
(`κ = 54 b₆ - 3 b₂ b₄ + a₂ c₄`), then the discriminant identity `splitPolynomial_discrim` turns
them into this identity. -/
theorem residue_c₄_mul_residue_eq_neg_c₆ [E.HasMultiplicativeReduction R] (t' n' : R)
    (hA : residue R (E.integralModel R).c₄ * residue R t'
      + residue R ((E.integralModel R).a₁ * (E.integralModel R).c₄) = 0)
    (hB : residue R (E.integralModel R).c₄ * residue R n'
      + residue R (54 * (E.integralModel R).b₆
        - 3 * (E.integralModel R).b₂ * (E.integralModel R).b₄
        + (E.integralModel R).a₂ * (E.integralModel R).c₄) = 0) :
    residue R (E.integralModel R).c₄ * residue R (t' ^ 2 - 4 * n')
      = -residue R (E.integralModel R).c₆ := by
  set c₄' := (E.integralModel R).c₄ with hc₄'
  set κ' := 54 * (E.integralModel R).b₆ - 3 * (E.integralModel R).b₂ * (E.integralModel R).b₄
    + (E.integralModel R).a₂ * c₄' with hκ'
  simp only [map_mul] at hA
  have hRid : ((E.integralModel R).a₁ * c₄') ^ 2 + 4 * c₄' * κ'
      = -(c₄' * (E.integralModel R).c₆) := by
    rw [hκ', hc₄']
    exact splitPolynomial_discrim (E.integralModel R)
  have hdisc := congrArg (residue R) hRid
  simp only [map_add, map_mul, map_pow, map_neg, map_ofNat] at hdisc
  apply mul_left_cancel₀ (residue_integralModel_c₄_ne_zero E R)
  simp only [map_sub, map_mul, map_pow, map_ofNat]
  linear_combination hdisc
    + (residue R c₄' * residue R t' - residue R (E.integralModel R).a₁ * residue R c₄') * hA
    - 4 * residue R c₄' * hB

open IsLocalRing in
/-- If the residues of `(t', n')` satisfy the trace and norm relations cut out by the node
polynomial, then the node polynomial of the quadratic twist of the integral model by `(t', n')`
splits over the residue field: the key identity `φc₄ · φ(t'² - 4n') = -φc₆`
(`residue_c₄_mul_residue_eq_neg_c₆`) reduces this to a square-class computation for residue
characteristic `≠ 2`, and to an Artin–Schreier computation with `z = 0` for residue
characteristic `2`. -/
theorem nodePoly_quadraticTwistOf_map_splits_of_residue
    [E.HasMultiplicativeReduction R] (t' n' : R)
    (hA : residue R (E.integralModel R).c₄ * residue R t'
      + residue R ((E.integralModel R).a₁ * (E.integralModel R).c₄) = 0)
    (hB : residue R (E.integralModel R).c₄ * residue R n'
      + residue R (54 * (E.integralModel R).b₆
        - 3 * (E.integralModel R).b₂ * (E.integralModel R).b₄
        + (E.integralModel R).a₂ * (E.integralModel R).c₄) = 0) :
    Polynomial.Splits (((E.integralModel R).quadraticTwistOf t' n').nodePoly.map
      (algebraMap R (ResidueField R))) := by
  -- `D = t'²-4n'` has nonzero residue (`hkey`: `φc₄·φD = -φc₆ ≠ 0`).
  have hkey := residue_c₄_mul_residue_eq_neg_c₆ E R t' n' hA hB
  have hDne : residue R (t' ^ 2 - 4 * n') ≠ 0 := fun h0 =>
    residue_integralModel_c₆_ne_zero E R (neg_eq_zero.mp (by rw [← hkey, h0, mul_zero]))
  set c₄' := (E.integralModel R).c₄ with hc₄'
  set κ' := 54 * (E.integralModel R).b₆ - 3 * (E.integralModel R).b₂ * (E.integralModel R).b₄
    + (E.integralModel R).a₂ * c₄' with hκ'
  simp only [map_mul] at hA
  rw [hc₄'] at hkey
  have hc₄0 : residue R (E.integralModel R).c₄ ≠ 0 := residue_integralModel_c₄_ne_zero E R
  have hc₄map : algebraMap R (ResidueField R) (E.integralModel R).c₄ ≠ 0 := by
    rw [ResidueField.algebraMap_eq]; exact hc₄0
  rcases ne_or_eq (2 : ResidueField R) 0 with h2 | h2
  · -- Residue characteristic `≠ 2`: split ↔ `IsSquare (φ((t'²-4n')·-(c₄c₆)))`, which `hkey` shows
    -- equals `IsSquare (φc₆²)`.
    haveI : NeZero (2 : ResidueField R) := ⟨h2⟩
    rw [nodePoly_quadraticTwistOf_map_splits_iff (algebraMap R (ResidueField R))
      (E.integralModel R) t' n' hc₄map (by rw [ResidueField.algebraMap_eq]; exact hDne)]
    refine ⟨residue R (E.integralModel R).c₆, ?_⟩
    apply mul_left_cancel₀ hc₄0
    rw [ResidueField.algebraMap_eq]
    simp only [map_mul, map_neg]
    linear_combination
      (-(residue R (E.integralModel R).c₄ * residue R (E.integralModel R).c₆)) * hkey
  · -- Residue characteristic 2: the Artin–Schreier split condition
    -- (`nodePoly_map_splits_iff_of_two_eq_zero`) holds with `z = 0`, because `φ κ_W = 0`. Indeed
    -- `κ_W = D³κ - D²·n·a₁²·c₄` (`kappa_quadraticTwistOf`), and `φκ = -φc₄·φn` (`hB`),
    -- `φa₁ = -φt'` (`hA`), `φD = φt'²` (as `4 = 0`), so
    -- `φκ_W = -φD²·φc₄·φn·(φD + φa₁²) = -φD²·φc₄·φn·(2·φt'²) = 0`.
    set D := t' ^ 2 - 4 * n' with hDdef
    have h4 : (4 : ResidueField R) = 0 := by
      rw [show (4 : ResidueField R) = 2 * 2 by norm_num, h2, mul_zero]
    have hDmap : algebraMap R (ResidueField R) D ≠ 0 := by
      rw [ResidueField.algebraMap_eq]; exact hDne
    have hDt : residue R D = residue R t' ^ 2 := by
      rw [hDdef, map_sub, map_mul, map_pow, map_ofNat, h4, zero_mul, sub_zero]
    have hWc₄ : algebraMap R (ResidueField R)
        ((E.integralModel R).quadraticTwistOf t' n').c₄ ≠ 0 := by
      rw [c₄_quadraticTwistOf, ← hDdef, map_mul, map_pow]
      exact mul_ne_zero (pow_ne_zero 2 hDmap) hc₄map
    have hWc₆ : algebraMap R (ResidueField R)
        ((E.integralModel R).quadraticTwistOf t' n').c₆ ≠ 0 := by
      rw [c₆_quadraticTwistOf, ← hDdef, map_mul, map_pow]
      exact mul_ne_zero (pow_ne_zero 3 hDmap)
        (by rw [ResidueField.algebraMap_eq]; exact residue_integralModel_c₆_ne_zero E R)
    have hta : residue R (E.integralModel R).a₁ = -residue R t' := by
      rcases mul_eq_zero.mp (show residue R c₄'
          * (residue R t' + residue R (E.integralModel R).a₁) = 0 by linear_combination hA)
        with hz | hz
      · exact absurd hz hc₄0
      · linear_combination hz
    have hκW_eq : 54 * ((E.integralModel R).quadraticTwistOf t' n').b₆
        - 3 * ((E.integralModel R).quadraticTwistOf t' n').b₂
            * ((E.integralModel R).quadraticTwistOf t' n').b₄
        + ((E.integralModel R).quadraticTwistOf t' n').a₂
            * ((E.integralModel R).quadraticTwistOf t' n').c₄
        = D ^ 3 * κ' - D ^ 2 * n' * (E.integralModel R).a₁ ^ 2 * c₄' := by
      rw [hDdef, hκ', hc₄']
      exact kappa_quadraticTwistOf (E.integralModel R) t' n'
    have hWc₄eq : ((E.integralModel R).quadraticTwistOf t' n').c₄ = D ^ 2 * c₄' := by
      rw [c₄_quadraticTwistOf, ← hDdef, hc₄']
    have hκW0 : algebraMap R (ResidueField R)
        (D ^ 3 * κ' - D ^ 2 * n' * (E.integralModel R).a₁ ^ 2 * c₄') = 0 := by
      simp only [map_sub, map_mul, map_pow, ResidueField.algebraMap_eq, hDt, hta]
      linear_combination (residue R t') ^ 6 * hB
        - (residue R t') ^ 6 * residue R n' * residue R c₄' * h2
    rw [nodePoly_map_splits_iff_of_two_eq_zero h2 (algebraMap R (ResidueField R))
      ((E.integralModel R).quadraticTwistOf t' n') hWc₄ hWc₆]
    refine ⟨0, ?_⟩
    rw [hκW_eq, hWc₄eq, show (0 : ResidueField R) ^ 2 + 0 = 0 from by ring, mul_zero, hκW0,
      neg_zero, mul_zero]

variable [E.IsElliptic]

open IsLocalRing in
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
      ((E.quadraticTwist L).minimal R).HasSplitMultiplicativeReduction R := by
  classical
  -- The node polynomial reduced to the residue field `k`; nonsplitness makes it irreducible
  -- (`irreducible_nodePoly_map`), and multiplicative reduction makes it separable
  -- (`separable_nodePoly_map`). Its root field `k' = k[X]/(P)` is therefore a separable
  -- quadratic extension of `k`.
  set P := (E.integralModel R).nodePoly.map (algebraMap R (ResidueField R)) with hP
  have hirr : Irreducible P := irreducible_nodePoly_map E R h
  have : Fact (Irreducible P) := ⟨hirr⟩
  have hPdeg2 : P.natDegree = 2 := natDegree_nodePoly_map E R
  have hk'rank : Module.finrank (ResidueField R) (AdjoinRoot P) = 2 :=
    AdjoinRoot.finrank_eq_natDegree.trans hPdeg2
  have : FiniteDimensional (ResidueField R) (AdjoinRoot P) := .of_finrank_eq_succ hk'rank
  have : Algebra.IsSeparable (ResidueField R) (AdjoinRoot P) :=
    AdjoinRoot.isSeparable_of_separable (separable_nodePoly_map E R)
  -- Lift `k'` to the unramified quadratic extension `L/K` (`LiftSeparableExtension`).
  obtain ⟨L, _, _, _, _, _, _, S, _, _, _, _, _, _, _, _, _, hLrank, ⟨resIso⟩⟩ :=
    exists_unramified_extension_of_residueField (R := R) (K := K) (AdjoinRoot P)
  have : Algebra.IsQuadraticExtension K L := ⟨hLrank.trans hk'rank⟩
  refine ⟨L, ‹Field L›, ‹Algebra K L›, ‹Algebra.IsQuadraticExtension K L›,
    ‹Algebra.IsSeparable K L›, ?_⟩
  -- `S = 𝒪_L` is the integral closure of `R` in `L` (now that `Frac S = L` is proved), so `L` is
  -- the base-change localization of `S`, and `R`-trace/norm are compatible with `K`-trace/norm.
  have : Algebra.IsIntegral R S := Algebra.IsIntegral.of_finite R S
  have : IsIntegralClosure S R L := IsIntegralClosure.of_isIntegrallyClosed S R L
  have : IsLocalization (Algebra.algebraMapSubmonoid S (nonZeroDivisors R)) L :=
    IsIntegralClosure.isLocalization_of_isSeparable R K L S
  have : Module.IsTorsionFree R L := Module.IsTorsionFree.trans_faithfulSMul R K L
  have : Module.Free R S := IsIntegralClosure.module_free R K L S
  have hSrank : Module.finrank R S = 2 :=
    (IsIntegralClosure.rank R K L S).trans (Algebra.IsQuadraticExtension.finrank_eq_two K L)
  have htower : ∀ r : R, algebraMap (ResidueField R) (ResidueField S) (residue R r)
      = residue S (algebraMap R S r) := fun r => by
    simp only [← ResidueField.algebraMap_residue]
  obtain ⟨θ', hθ'res⟩ := IsLocalRing.residue_surjective (resIso.symm (AdjoinRoot.root P))
  have hCH' : θ' ^ 2 - algebraMap R S (Algebra.trace R S θ') * θ'
      + algebraMap R S (Algebra.norm R θ') = 0 := sq_sub_trace_mul_self_add_norm hSrank θ'
  have hρ1 : (AdjoinRoot.root P) ^ 2
        - algebraMap (ResidueField R) (AdjoinRoot P) (residue R (Algebra.trace R S θ'))
          * (AdjoinRoot.root P)
        + algebraMap (ResidueField R) (AdjoinRoot P) (residue R (Algebra.norm R θ')) = 0 := by
    have h0 := congrArg (fun x => resIso (residue S x)) hCH'
    simp only [map_sub, map_add, map_mul, map_pow, map_zero, hθ'res, resIso.apply_symm_apply,
      ← htower, resIso.commutes] at h0
    exact h0
  -- `root P` also satisfies its own defining polynomial `P = C(φc₄)X² + C(φ(a₁c₄))X - C(φκ)`
  -- (`aeval_root_nodePoly_map`).
  have hρ2 : algebraMap (ResidueField R) (AdjoinRoot P)
          (algebraMap R (ResidueField R) (E.integralModel R).c₄) * (AdjoinRoot.root P) ^ 2
        + algebraMap (ResidueField R) (AdjoinRoot P)
          (algebraMap R (ResidueField R) ((E.integralModel R).a₁ * (E.integralModel R).c₄))
          * (AdjoinRoot.root P)
        - algebraMap (ResidueField R) (AdjoinRoot P) (algebraMap R (ResidueField R)
          (54 * (E.integralModel R).b₆ - 3 * (E.integralModel R).b₂ * (E.integralModel R).b₄
            + (E.integralModel R).a₂ * (E.integralModel R).c₄)) = 0 :=
    aeval_root_nodePoly_map (algebraMap R (ResidueField R)) (E.integralModel R)
  -- Eliminate `root P ^ 2` between `hρ1` and `hρ2`; linear independence of `1` and `root P`
  -- (`AdjoinRoot.eq_zero_of_mul_root_add_eq_zero`) gives the scalar relations
  -- `φc₄·φt = -φ(a₁c₄)` and `φc₄·φn = -φκ` in `k` (φ = residue).
  set c₄' := (E.integralModel R).c₄ with hc₄'
  set κ' := 54 * (E.integralModel R).b₆ - 3 * (E.integralModel R).b₂ * (E.integralModel R).b₄
    + (E.integralModel R).a₂ * c₄' with hκ'
  set t' := Algebra.trace R S θ' with ht'
  set n' := Algebra.norm R θ' with hn'
  obtain ⟨hA, hB⟩ := AdjoinRoot.eq_zero_of_mul_root_add_eq_zero hPdeg2.ge
    (a := residue R c₄' * residue R t' + residue R ((E.integralModel R).a₁ * c₄'))
    (b := -(residue R c₄' * residue R n' + residue R κ')) (by
    simp only [IsLocalRing.ResidueField.algebraMap_eq, map_add, map_mul, map_neg] at hρ2 ⊢
    linear_combination hρ2
      - algebraMap (ResidueField R) (AdjoinRoot P) (residue R c₄') * hρ1)
  rw [neg_eq_zero] at hB
  -- `root P ∉ k` (its minimal polynomial has degree 2), so `θ'̄ = resIso⁻¹(root P) ∉ k` and, since
  -- `R` is integrally closed, `algebraMap S L θ' ∉ K` — the twist by `θ'` is nontrivial.
  have hθ' : algebraMap S L θ' ∉ Set.range (algebraMap K L) :=
    notMem_range_algebraMap_of_residue_notMem R (by
      rw [hθ'res]
      rintro ⟨c, hc⟩
      exact AdjoinRoot.root_notMem_range_algebraMap hPdeg2.ge
        ⟨c, by rw [← resIso.commutes c, hc, resIso.apply_symm_apply]⟩)
  -- Trace/norm land in `K`, giving the connection to the `R`-model `W = quadraticTwistOf t' n'`.
  have htr : Algebra.trace K L (algebraMap S L θ') = algebraMap R K t' :=
    Algebra.trace_localization R (nonZeroDivisors R) θ'
  have hnr : Algebra.norm K (algebraMap S L θ') = algebraMap R K n' :=
    Algebra.norm_localization R (nonZeroDivisors R) θ'
  obtain ⟨C, hC⟩ := E.exists_smul_quadraticTwist_eq_quadraticTwistBy L hθ'
  rw [quadraticTwistBy, htr, hnr, ← baseChange_integralModel_quadraticTwistOf E R t' n'] at hC
  -- `D = t'²-4n'` is a unit (`residue_c₄_mul_residue_eq_neg_c₆`: `φc₄·φD = -φc₆ ≠ 0`), so `W⁄K`
  -- has multiplicative reduction; the relations `hA`, `hB` make it split
  -- (`nodePoly_quadraticTwistOf_map_splits_of_residue`).
  have hkey := residue_c₄_mul_residue_eq_neg_c₆ E R t' n' hA hB
  have hDne : residue R (t' ^ 2 - 4 * n') ≠ 0 := fun h0 =>
    residue_integralModel_c₆_ne_zero E R (neg_eq_zero.mp (by rw [← hkey, h0, mul_zero]))
  have hWmult := hasMultiplicativeReduction_baseChange_quadraticTwistOf E R t' n' hDne
  have hWsplit :
      (((E.integralModel R).quadraticTwistOf t' n')⁄K).HasSplitMultiplicativeReduction R := by
    refine { hWmult with splitMultiplicativeReduction := ?_ }
    rw [show (((E.integralModel R).quadraticTwistOf t' n')⁄K).integralModel R
      = (E.integralModel R).quadraticTwistOf t' n' from integralModel_baseChange R _]
    exact nodePoly_quadraticTwistOf_map_splits_of_residue E R t' n' hA hB
  -- `hWsplit : (W⁄K).HasSplitMultiplicativeReduction R` with `W⁄K` minimal and
  -- `hC : C • E.quadraticTwist L = W⁄K`. Split multiplicativity transfers to the chosen minimal
  -- model `(E.quadraticTwist L).minimal R`, which is another minimal model of
  -- `E.quadraticTwist L` (`of_isMinimal_smul`).
  have : IsMinimal R (((E.integralModel R).quadraticTwistOf t' n')⁄K) := hWmult.toIsMinimal
  have hD : (((E.quadraticTwist L).exists_isMinimal R).choose * C⁻¹)
      • (((E.integralModel R).quadraticTwistOf t' n')⁄K) = (E.quadraticTwist L).minimal R := by
    rw [mul_smul, ← hC, inv_smul_smul]; rfl
  have hΔ₁ : (((E.integralModel R).quadraticTwistOf t' n')⁄K).Δ ≠ 0 := by
    have hDnz : t' ^ 2 - 4 * n' ≠ 0 := fun h => hDne (by rw [h, map_zero])
    have hΔint : (E.integralModel R).Δ ≠ 0 := fun h =>
      E.isUnit_Δ.ne_zero (by rw [← integralModel_Δ_eq R E, h, map_zero])
    rw [show (((E.integralModel R).quadraticTwistOf t' n')⁄K).Δ
      = algebraMap R K ((E.integralModel R).quadraticTwistOf t' n').Δ from map_Δ _ _,
      Δ_quadraticTwistOf, Ne, map_eq_zero_iff _ (IsFractionRing.injective R K), mul_eq_zero]
    exact not_or.mpr ⟨pow_ne_zero 6 hDnz, hΔint⟩
  exact HasSplitMultiplicativeReduction.of_isMinimal_smul R _ hD hΔ₁ hWsplit

end Reduction

end WeierstrassCurve
