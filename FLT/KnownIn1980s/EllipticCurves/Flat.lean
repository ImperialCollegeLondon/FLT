import Mathlib

/-!

# Good reduction implies flat torsion

Let `E` be an elliptic curve over the field of fractions `K` of a discrete valuation
ring `R`, suppose that `E` has good reduction over `R`, and let `n ≥ 1` be a natural
number. Then the `n`-torsion of `E` "is a finite flat group scheme": the Galois module
`E(Kˢᵉᵖ)[n]` is, Galois-equivariantly, the group of `Kˢᵉᵖ`-points of the generic fibre
of a finite flat group scheme over `R`.

Mathlib has no group schemes, so we speak throughout of the (commutative) Hopf algebra
of functions on the group scheme instead: the statement below produces a commutative
Hopf algebra `H` over `R`, finite and flat as an `R`-module (`R` is a DVR, so this
says finite free; over a general base the right condition is finite locally free),
together with a Galois-equivariant isomorphism of groups from the `Kˢᵉᵖ`-points
`K ⊗[R] H →ₐ[K] Kˢᵉᵖ` of its generic fibre (a group under convolution, `K ⊗[R] H`
being a Hopf algebra over `K`) to the `n`-torsion subgroup of `E(Kˢᵉᵖ)`.

## Mathematical discussion: what is the correct generality?

Good reduction means that the minimal Weierstrass equation of `E` has unit discriminant
over `R`, so it defines an elliptic scheme (an abelian scheme of relative dimension 1)
`𝓔` over `R` with generic fibre `E`. Multiplication by `n` on an elliptic scheme is a
finite locally free morphism of degree `n²` for every `n ≥ 1` [Katz–Mazur, *Arithmetic
moduli of elliptic curves*, Theorem 2.3.1], so its kernel `𝓔[n]` is a finite flat group
scheme over `R` of order `n²` with generic fibre `E[n]`. This is the robust form of the
statement: it holds for every `n` over any DVR (indeed over any base scheme), in every
characteristic.

The statement formalised below is instead about the Galois module `E(Kˢᵉᵖ)[n]`, because
mathlib cannot yet express `E[n]` as a group scheme. How the two statements compare
depends on whether `n` is invertible in `K`:

* If `n` is invertible in `K` then `E[n]` is a finite étale group scheme over `K` of
  order `n²`. It is therefore determined by its Galois module of `Kˢᵉᵖ`-points, which is
  free of rank 2 over `ℤ/nℤ`, and the statement below carries the full content of the
  group-scheme statement.

* If `K` has characteristic `p` and `p ∣ n` then `E[n]` is not étale, and `E(Kˢᵉᵖ)[n]`
  sees only its maximal étale quotient (for `n = p`: a group of order `p` if the
  reduction is ordinary and of order `1` if it is supersingular). The statement below
  should still be true — for `H` one can take the Cartier dual of the schematic closure
  in `𝓔[n]` of the Cartier dual of the maximal étale quotient of `E[n]` — but it is
  strictly weaker than flatness of `E[n]` itself. The honest statement in this case is
  the group-scheme statement of the previous paragraph, which cannot yet be formalised.

Which values of `n` make flatness interesting? Let `p` denote the characteristic of the
residue field of `R`.

* If `n` is invertible in the residue field then the conclusion is equivalent to the
  Galois module `E(Kˢᵉᵖ)[n]` being unramified, which is the statement of
  `FLT.KnownIn1980s.EllipticCurves.GoodReduction`. Indeed, the order of a finite flat
  group scheme kills its module of invariant differentials [Tate, *Finite flat group
  schemes*, in *Modular forms and Fermat's Last Theorem*], so a finite flat group scheme
  over `R` whose order is invertible in `R` is unramified over `R`, hence finite étale;
  and finite étale group schemes over `R` are the same thing as unramified Galois
  modules, via normalization. In particular "unramified implies flat" holds for *any*
  finite abelian Galois module of order invertible in the residue field, for reasons
  having nothing to do with elliptic curves.

* The interesting case is therefore `p > 0` and `p ∣ n`, where flatness is genuinely
  stronger than anything expressible via ramification: for `K` of characteristic zero
  (e.g. a finite extension of `ℚ_p`) and `n = p`, this is the sense in which "`ρ` is
  flat at `p`" is used for mod `p` representations in [Serre, *Sur les représentations
  modulaires de degré 2 de Gal(ℚ̄/ℚ)*, Duke Math. J. 54 (1987), §2.8] and in the
  modularity lifting literature, and it matches the definition `GaloisRep.IsFlatAt` in
  `FLT.Deformations.RepresentationTheory.GaloisRep` (stated there for number fields; the
  theorem below is the local statement feeding into it). Note that flat does *not* imply
  unramified here: the `p`-torsion of a curve with good reduction is flat but in general
  highly ramified at `p`.

The `Algebra.Etale K (K ⊗[R] H)` condition below pins down the generic fibre as the
finite étale group scheme attached to the Galois module `E(Kˢᵉᵖ)[n]` (in particular it
forces the `R`-rank of `H` to equal the number of `n`-torsion points). It is automatic
when `K` has characteristic zero, by Cartier's theorem that finite group schemes in
characteristic zero are étale, and it is what makes the equivalence "flat ⟺ unramified"
above honest; compare the corresponding condition in `GaloisRep.HasFlatProlongationAt`.

## TODO

* `FLT.GroupScheme.FiniteFlat` plans a definition of what it means for an action of
  `Gal(Kˢᵉᵖ/K)` on a finite abelian group to be *flat*, for `K` the field of fractions
  of a DVR. Once that definition exists, the conclusion below should be refactored to
  "the Galois module `E(Kˢᵉᵖ)[n]` is flat".

* Once `E[n]` can be expressed as a group scheme (equivalently, once its Hopf algebra of
  functions is available), state the stronger result that `E[n]` itself, not just its
  Galois module of points, prolongs to a finite flat group scheme over `R`; as explained
  above, this is insensitive to the characteristic of `K`.

* Prove the division polynomial lemmas at the bottom of this file
  (`WeierstrassCurve.resultant_Φ_ΨSq` and `WeierstrassCurve.isCoprime_Φ_ΨSq`), which
  isolate the arithmetic input to the theorem as a purely polynomial statement.

-/

open scoped WeierstrassCurve.Affine -- `(E⁄K).Point` notation for the group of points
open scoped TensorProduct -- `⊗[R]` notation

universe u

-- let R be a discrete valuation ring with field of fractions K
variable (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]

-- Let E/K be an elliptic curve with good reduction over R. Note that mathlib's
-- `HasGoodReduction` asks that the given Weierstrass equation for E is a minimal
-- integral equation whose discriminant has valuation 1; this loses no generality
-- because every elliptic curve over K is isomorphic to one given by a minimal
-- equation (`WeierstrassCurve.exists_isMinimal`).
variable (E : WeierstrassCurve K) [E.IsElliptic] [E.HasGoodReduction R]

-- Let n be a positive natural number. (The interesting case is when n is divisible by
-- the residue characteristic of R; away from it, flatness reduces to the unramifiedness
-- statement of `FLT.KnownIn1980s.EllipticCurves.GoodReduction` — see the discussion above.)
variable (n : ℕ) [NeZero n]

-- Let Ksep be a separable closure of K (`DecidableEq` is needed for the group law on points)
variable (Ksep : Type*) [Field Ksep] [Algebra K Ksep] [IsSepClosure K Ksep] [DecidableEq Ksep]

/-- If `E` is an elliptic curve over the field of fractions `K` of a discrete valuation
ring `R` with good reduction over `R`, then the `n`-torsion of `E` is a finite flat group
scheme: there is a commutative Hopf algebra `H` over `R`, finite and flat as an `R`-module,
whose generic fibre `K ⊗[R] H` is étale over `K` and whose group of `Kˢᵉᵖ`-points (a group
under convolution) is isomorphic, compatibly with the actions of `Gal(Kˢᵉᵖ/K)` on the two
sides, to the `n`-torsion subgroup of `E(Kˢᵉᵖ)`. -/
theorem WeierstrassCurve.torsion_flat_of_good_reduction :
    -- There is a commutative Hopf algebra H over R (the functions on a group scheme over R),
    ∃ (H : Type u) (_ : CommRing H) (_ : HopfAlgebra R H)
      -- finite and flat as an R-module (so the group scheme is finite flat),
      (_ : Module.Finite R H) (_ : Module.Flat R H)
      -- whose generic fibre K ⊗[R] H is étale over K,
      (_ : Algebra.Etale K (K ⊗[R] H))
      -- together with an isomorphism of groups from the Kˢᵉᵖ-points of the generic fibre
      -- (a group under convolution, because K ⊗[R] H is a Hopf algebra over K)
      -- to the n-torsion subgroup of E(Kˢᵉᵖ),
      (f : Additive (WithConv (K ⊗[R] H →ₐ[K] Ksep)) ≃+
        AddSubgroup.torsionBy (E⁄Ksep).Point (n : ℤ)),
      -- which is equivariant for the actions of Gal(Kˢᵉᵖ/K) on the two sides.
      ∀ (σ : Ksep ≃ₐ[K] Ksep) (φ : K ⊗[R] H →ₐ[K] Ksep),
        (f (Additive.ofMul (WithConv.toConv (σ.toAlgHom.comp φ))) : (E⁄Ksep).Point) =
          Affine.Point.map σ.toAlgHom (f (Additive.ofMul (WithConv.toConv φ))) :=
  sorry

/-!
### A step towards the proof, via division polynomials

Mathlib knows the division polynomials of a Weierstrass curve `W` over any commutative
ring: `W.Φ n` is monic of degree `n²`, and `W.ΨSq n` has degree `n² - 1` with leading
coefficient `n²` (see `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/`, in
particular `natDegree_Φ`, `natDegree_ΨSq` and `leadingCoeff_ΨSq`). What mathlib does not
yet know is the dictionary between division polynomials and torsion: for a point `P ≠ 0`
of `E` over a field, `n • P = 0` iff `ΨSq n` vanishes at `x(P)`, and more generally
`x(n • P) = (Φ n).eval x(P) / (ΨSq n).eval x(P)`.

The two lemmas below isolate the arithmetic input to `torsion_flat_of_good_reduction` as
a purely polynomial statement: the resultant of `Φ n` and `ΨSq n` is `±Δ ^ ((n⁴ - n²)/6)`;
in particular the two polynomials are coprime whenever `Δ` is a unit.

Why the identity is true: over a field on which `Δ` is invertible, a common root of `Φ n`
and `ΨSq n` would — via the dictionary and the definition
`Φ n = X * ΨSq n - preΨ (n+1) * preΨ (n-1) * (1 or Ψ₂Sq)` — be the `x`-coordinate of a
nonzero `n`-torsion point which is also `(n+1)`- or `(n-1)`-torsion, hence trivial, a
contradiction. So over `ℤ[a₁, …, a₆]`, where `Δ` is irreducible, the resultant is forced
to be `±c * Δ ^ k` with `c` an integer; running the same no-common-root argument over
`𝔽ₗ` for every prime `ℓ` (it is insensitive to the characteristic) gives `c = ±1`; and
weights (`aᵢ` has weight `i`, `x` has weight `2`, `Δ` has weight `12`, and the resultant
is isobaric of weight `2 * n² * (n² - 1)`) pin `k = (n⁴ - n²)/6`. Sanity check for
`n = 2`, `y² = x³ - x`: `Φ₂ = (x² + 1)²`, `Ψ₂² = 4(x³ - x)`, so the resultant is
`4⁴ * Φ₂(0) * Φ₂(1) * Φ₂(-1) = 4096 = Δ²`, and `(2⁴ - 2²)/6 = 2`.

Why it is a step towards `torsion_flat_of_good_reduction`:

* For `n` invertible in the residue field of `R`, the leading coefficient `n²` of
  `ΨSq n` is a unit of `R`, so the `x`-coordinates of the nonzero `n`-torsion points of
  `E(Kˢᵉᵖ)` (the roots of `ΨSq n`) are integral over `R`, and coprimality of `Φ n` and
  `ΨSq n` over the residue field (`Δ` is a unit there by good reduction) together with a
  companion identity for the discriminant of `ΨSq n` (of the same `±nᵃ * Δᵇ` shape) shows
  that reduction is injective on the `n`-torsion. Since inertia acts trivially on residue
  fields, it then acts trivially on the torsion: this is the unramifiedness statement of
  `FLT.KnownIn1980s.EllipticCurves.GoodReduction`, and by the discussion in the module
  docstring above (an unramified module of order invertible in the residue field prolongs
  étale-ly), it implies `torsion_flat_of_good_reduction` for all such `n`.

* For `n` divisible by the residue characteristic `p`, division polynomials cannot
  produce the Hopf algebra `H` by themselves: the leading coefficient `n²` of `ΨSq n`
  now lies in the maximal ideal, which is the concrete manifestation of the fact that
  part of the `n`-torsion group scheme sits at the origin, outside the affine chart
  where the division polynomials live (the torsion in the kernel of reduction has
  `x`-coordinates of negative valuation). But the identity is still the arithmetic core
  of the scheme-theoretic proof [Katz–Mazur, *Arithmetic moduli of elliptic curves*,
  Theorem 2.3.1] that multiplication by `n` on the elliptic scheme `𝓔` is finite locally
  free of degree `n²`: the polynomial `(Φ n).eval X - ξ * (ΨSq n).eval X` is monic of
  degree `n²` over `R[ξ]`, where `ξ = x ∘ [n]`, which gives finiteness of `[n]`, and
  coprimality on each fibre gives the constant fibre degree `n²`. So nothing proved here
  is wasted on the hard case.

Reference for the resultant identity in short Weierstrass form: M. Ayad, *Points
S-entiers des courbes elliptiques*, Manuscripta Math. 76 (1992), 305–324.
-/

/-- The resultant of the division polynomials `Φ n` (taken with degree `n²`) and `ΨSq n`
(taken with degree `n² - 1`) is `±Δ ^ ((n⁴ - n²)/6)`. The sign presumably depends on `n`
and on the conventions in `Polynomial.resultant`; whoever proves this should pin it down
and upgrade the statement. -/
theorem WeierstrassCurve.resultant_Φ_ΨSq {R₀ : Type*} [CommRing R₀] (W : WeierstrassCurve R₀)
    {n : ℤ} (hn : n ≠ 0) :
    (W.Φ n).resultant (W.ΨSq n) (n.natAbs ^ 2) (n.natAbs ^ 2 - 1) =
        W.Δ ^ ((n.natAbs ^ 4 - n.natAbs ^ 2) / 6) ∨
      (W.Φ n).resultant (W.ΨSq n) (n.natAbs ^ 2) (n.natAbs ^ 2 - 1) =
        -W.Δ ^ ((n.natAbs ^ 4 - n.natAbs ^ 2) / 6) :=
  sorry

/-- If the discriminant of a Weierstrass curve over a commutative ring is a unit then the
division polynomials `Φ n` and `ΨSq n` are coprime, i.e. there is a Bézout identity
`F * Φ n + G * ΨSq n = 1`. This is the form of the resultant identity that the
applications consume. It follows from `resultant_Φ_ΨSq`, because the resultant lies in
the ideal generated by the two polynomials and is a unit here; note also that it is
stable under base change, so it suffices to prove it for the universal Weierstrass curve
over `ℤ[a₁, …, a₆][Δ⁻¹]`. -/
theorem WeierstrassCurve.isCoprime_Φ_ΨSq {R₀ : Type*} [CommRing R₀] (W : WeierstrassCurve R₀)
    {n : ℤ} (hn : n ≠ 0) (hΔ : IsUnit W.Δ) :
    IsCoprime (W.Φ n) (W.ΨSq n) :=
  sorry
