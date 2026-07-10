/-
Copyright (c) 2026 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/
module

public import FLT.GroupScheme.FiniteFlat
public import FLT.KnownIn1980s.EllipticCurves.DivisionPolynomialTorsion
public import FLT.KnownIn1980s.EllipticCurves.GoodReduction
public import Mathlib.Algebra.CharP.Basic
public import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.RingTheory.Int.Basic
public import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree
public import Mathlib.AlgebraicGeometry.EllipticCurve.Reduction
public import Mathlib.RingTheory.Bialgebra.Convolution
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.Polynomial.Resultant.Basic

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

## Current state of the proof

`FLT.GroupScheme.FiniteFlat` now defines what it means for an action of `Gal(Kˢᵉᵖ/K)` on
an abelian group to be *flat* (`GroupScheme.GaloisModule.IsFlat`), and the main theorem
below is *proved* modulo the following sorried inputs, which is exactly the intended
division of labour:

* purely group-scheme-theoretic statements, with no elliptic curves in them
  (`GroupScheme.GaloisModule.IsFlat.of_isUnramified`: a continuous unramified Galois
  module prolongs to a finite étale group scheme; `GroupScheme.GaloisModule.IsFlat.prod`:
  flatness is stable under products, via `H₁ ⊗[R] H₂`);

* the unramifiedness of the prime-to-`p` torsion
  (`WeierstrassCurve.torsion_unramified_of_good_reduction`, in
  `FLT.KnownIn1980s.EllipticCurves.GoodReduction`);

* finiteness of the torsion (`WeierstrassCurve.torsionBy_finite` below, which awaits the
  division-polynomial dictionary of
  `FLT.KnownIn1980s.EllipticCurves.DivisionPolynomialTorsion`);

* the genuinely hard, genuinely elliptic case
  (`WeierstrassCurve.torsion_isFlat_of_good_reduction_residueCharPow` below): flatness of
  the `p^v`-torsion for `p` the residue characteristic, i.e. the Katz–Mazur input
  discussed above.

## TODO

* Prove the sorried statements listed above.

* Once `E[n]` can be expressed as a group scheme (equivalently, once its Hopf algebra of
  functions is available), state the stronger result that `E[n]` itself, not just its
  Galois module of points, prolongs to a finite flat group scheme over `R`; as explained
  above, this is insensitive to the characteristic of `K`.

* Prove the division polynomial lemmas at the bottom of this file
  (`WeierstrassCurve.resultant_Φ_ΨSq` and `WeierstrassCurve.isCoprime_Φ_ΨSq`), which
  isolate the arithmetic input to the theorem as a purely polynomial statement.

-/

@[expose] public section

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

/-!
### The Galois action on the torsion, and the reduction to group-scheme statements

`FLT.GroupScheme.FiniteFlat` defines what it means for an action of `Gal(Kˢᵉᵖ/K)` on an
abelian group to be *flat* over `R` (`GroupScheme.GaloisModule.IsFlat`: it prolongs to a
finite flat group scheme over `R`, phrased Hopf-algebraically). The declarations below
package the Galois action on the `n`-torsion of `E(Kˢᵉᵖ)` in that language and reduce the
main theorem `torsion_flat_of_good_reduction` to three independent inputs:

1. the purely group-scheme-theoretic statement
   `GroupScheme.GaloisModule.IsFlat.of_isUnramified` (a continuous unramified Galois
   module is flat — no elliptic curves involved), applied to the prime-to-`p` part of the
   torsion, whose unramifiedness is `torsion_unramified_of_good_reduction`;
2. the genuinely elliptic hard case `torsion_isFlat_of_good_reduction_residueCharPow`:
   flatness of the `p^v`-torsion, `p` the residue characteristic, which awaits the
   Katz–Mazur-style analysis described in the module docstring above (in mixed
   characteristic this torsion is ramified, so no unramifiedness argument can reach it);
3. finiteness of the torsion and an equivariant primary decomposition
   (`AddSubgroup.exists_torsionBy_mul_addEquiv`), which glue 1 and 2 together via
   `GroupScheme.GaloisModule.IsFlat.prod`.
-/

open GroupScheme

/-- **Coprime splitting of torsion, naturally in the group.** For coprime integers `a`,
`b`, the `a * b`-torsion of an abelian group `A` splits as the product of the `a`-torsion
and the `b`-torsion, by an isomorphism whose two components are (restrictions of)
multiplication by fixed integer multiples of `b` resp. `a` — namely `c * b` and `d * a`
for any Bézout coefficients `c * b + d * a = 1`. Exposing the components in this form
makes the isomorphism manifestly natural in `A`: it commutes with every additive map,
e.g. with a Galois action. TODO: prove this (elementary) and upstream it to mathlib's
`Mathlib.Algebra.Module.Torsion`. -/
theorem AddSubgroup.exists_torsionBy_mul_addEquiv {A : Type*} [AddCommGroup A] {a b : ℤ}
    (h : IsCoprime a b) :
    ∃ (e : AddSubgroup.torsionBy A (a * b) ≃+
        (AddSubgroup.torsionBy A a × AddSubgroup.torsionBy A b)) (c d : ℤ),
      ∀ P : AddSubgroup.torsionBy A (a * b),
        ((e P).1 : A) = (c * b) • (P : A) ∧ ((e P).2 : A) = (d * a) • (P : A) := by
  obtain ⟨u, v, huv⟩ := h
  have hcd : v * b + u * a = 1 := by linarith
  refine ⟨{
    toFun := fun P => (⟨(v * b) • (P : A), (Submodule.mem_torsionBy_iff a _).mpr <| by
        rw [smul_smul, show a * (v * b) = v * (a * b) from by ring, ← smul_smul,
          (Submodule.mem_torsionBy_iff (a * b) _).mp P.2, smul_zero]⟩,
      ⟨(u * a) • (P : A), (Submodule.mem_torsionBy_iff b _).mpr <| by
        rw [smul_smul, show b * (u * a) = u * (a * b) from by ring, ← smul_smul,
          (Submodule.mem_torsionBy_iff (a * b) _).mp P.2, smul_zero]⟩)
    invFun := fun Q => ⟨(Q.1 : A) + (Q.2 : A), (Submodule.mem_torsionBy_iff (a * b) _).mpr <| by
        have h1 : (a * b) • (Q.1 : A) = 0 := by
          rw [mul_comm, ← smul_smul, (Submodule.mem_torsionBy_iff a _).mp Q.1.2, smul_zero]
        have h2 : (a * b) • (Q.2 : A) = 0 := by
          rw [← smul_smul, (Submodule.mem_torsionBy_iff b _).mp Q.2.2, smul_zero]
        rw [smul_add, h1, h2, add_zero]⟩
    left_inv := fun P => Subtype.ext <| by
      change (v * b) • (P : A) + (u * a) • (P : A) = (P : A)
      rw [← add_smul, hcd, one_smul]
    right_inv := fun Q => by
      apply Prod.ext <;> apply Subtype.ext
      · change (v * b) • ((Q.1 : A) + (Q.2 : A)) = (Q.1 : A)
        rw [smul_add, show (v * b) • (Q.2 : A) = 0 from by
          rw [← smul_smul, (Submodule.mem_torsionBy_iff b _).mp Q.2.2, smul_zero],
          show v * b = 1 - u * a from by linarith, sub_smul, one_smul, ← smul_smul,
          (Submodule.mem_torsionBy_iff a _).mp Q.1.2, smul_zero, sub_zero, add_zero]
      · change (u * a) • ((Q.1 : A) + (Q.2 : A)) = (Q.2 : A)
        rw [smul_add, show (u * a) • (Q.1 : A) = 0 from by
          rw [← smul_smul, (Submodule.mem_torsionBy_iff a _).mp Q.1.2, smul_zero],
          show u * a = 1 - v * b from by linarith, sub_smul, one_smul, ← smul_smul,
          (Submodule.mem_torsionBy_iff b _).mp Q.2.2, smul_zero, sub_zero, zero_add]
    map_add' := fun P Q => by
      apply Prod.ext <;> apply Subtype.ext
      · change (v * b) • ((P : A) + (Q : A)) = (v * b) • (P : A) + (v * b) • (Q : A)
        rw [smul_add]
      · change (u * a) • ((P : A) + (Q : A)) = (u * a) • (P : A) + (u * a) • (Q : A)
        rw [smul_add] }, v, u, fun P => ⟨rfl, rfl⟩⟩

/-- The action of `σ ∈ Gal(Kˢᵉᵖ/K)` on the `m`-torsion subgroup of `E(Kˢᵉᵖ)`, as an
additive automorphism: `σ` acts on points coordinatewise, via `Affine.Point.map`. -/
noncomputable def WeierstrassCurve.torsionGaloisAction (m : ℤ) (σ : Ksep ≃ₐ[K] Ksep) :
    AddSubgroup.torsionBy (E⁄Ksep).Point m ≃+ AddSubgroup.torsionBy (E⁄Ksep).Point m where
  toFun P := ⟨Affine.Point.map σ.toAlgHom P.1, (Submodule.mem_torsionBy_iff ..).mpr <| by
    rw [← map_zsmul, (Submodule.mem_torsionBy_iff ..).mp P.2, map_zero]⟩
  invFun P := ⟨Affine.Point.map σ.symm.toAlgHom P.1, (Submodule.mem_torsionBy_iff ..).mpr <| by
    rw [← map_zsmul, (Submodule.mem_torsionBy_iff ..).mp P.2, map_zero]⟩
  left_inv P := Subtype.ext <| by
    change Affine.Point.map _ (Affine.Point.map _ _) = _
    rw [Affine.Point.map_map,
      show σ.symm.toAlgHom.comp σ.toAlgHom = (AlgHom.id K Ksep) from
        AlgHom.ext fun x => σ.symm_apply_apply x]
    cases (P : (E⁄Ksep).Point) <;> rfl
  right_inv P := Subtype.ext <| by
    change Affine.Point.map _ (Affine.Point.map _ _) = _
    rw [Affine.Point.map_map,
      show σ.toAlgHom.comp σ.symm.toAlgHom = (AlgHom.id K Ksep) from
        AlgHom.ext fun x => σ.apply_symm_apply x]
    cases (P : (E⁄Ksep).Point) <;> rfl
  map_add' P Q := Subtype.ext <| map_add (Affine.Point.map σ.toAlgHom) P.1 Q.1

omit [E.IsElliptic] [IsSepClosure K Ksep] in
/-- The action of `Gal(Kˢᵉᵖ/K)` on the torsion is multiplicative (i.e. it is a genuine
group action). -/
theorem WeierstrassCurve.torsionGaloisAction_mul (m : ℤ) (σ τ : Ksep ≃ₐ[K] Ksep) :
    WeierstrassCurve.torsionGaloisAction K E Ksep m (σ * τ) =
      (WeierstrassCurve.torsionGaloisAction K E Ksep m τ).trans
        (WeierstrassCurve.torsionGaloisAction K E Ksep m σ) := by
  refine AddEquiv.ext fun P => Subtype.ext ?_
  change Affine.Point.map (σ * τ).toAlgHom (P : (E⁄Ksep).Point) =
    Affine.Point.map σ.toAlgHom (Affine.Point.map τ.toAlgHom (P : (E⁄Ksep).Point))
  rw [Affine.Point.map_map]
  congr 1

/-- For a Weierstrass curve `W` over a field and a fixed `x`, there are only finitely many
`y` with `W.Equation x y`: such `y` are roots of the monic (hence nonzero) quadratic in `y`
cut out by the Weierstrass equation. -/
private theorem WeierstrassCurve.Affine.finite_setOf_equation {F : Type*} [Field F]
    (W : WeierstrassCurve.Affine F) (x : F) : {y : F | W.Equation x y}.Finite := by
  have hq0 : (Polynomial.X ^ 2 + (Polynomial.C (W.a₁ * x + W.a₃) * Polynomial.X
      - Polynomial.C (x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆)) : Polynomial F) ≠ 0 := by
    refine Polynomial.Monic.ne_zero ?_
    refine Polynomial.monic_X_pow_add (n := 2) ?_
    refine lt_of_le_of_lt (Polynomial.degree_sub_le _ _) (max_lt ?_ ?_)
    · exact lt_of_le_of_lt (Polynomial.degree_C_mul_X_le _) (by norm_num)
    · exact lt_of_le_of_lt Polynomial.degree_C_le (by norm_num)
  refine (Polynomial.finite_setOf_isRoot hq0).subset fun y hy => ?_
  simp only [Set.mem_setOf_eq] at hy
  simp only [Set.mem_setOf_eq, Polynomial.IsRoot.def, Polynomial.eval_add, Polynomial.eval_sub,
    Polynomial.eval_pow, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_C]
  rw [WeierstrassCurve.Affine.equation_iff'] at hy
  linear_combination hy

omit [IsSepClosure K Ksep] in
/-- The `m`-torsion subgroup of `E(Kˢᵉᵖ)` is finite when `m` is nonzero in `Kˢᵉᵖ`. (Proved
via the division polynomials: a nonzero `m`-torsion point has `x`-coordinate a root of the
polynomial `ΨSq m`, which is nonzero precisely because its leading coefficient `m²` is
nonzero in `Kˢᵉᵖ`; there are finitely many such roots, each carrying at most two points of
`E`; see `FLT.KnownIn1980s.EllipticCurves.DivisionPolynomialTorsion`.) -/
theorem WeierstrassCurve.torsionBy_finite (m : ℕ) (hm : (m : Ksep) ≠ 0) :
    Finite (AddSubgroup.torsionBy (E⁄Ksep).Point (m : ℤ)) := by
  haveI : (E⁄Ksep).IsElliptic := inferInstanceAs (E.map (algebraMap K Ksep)).IsElliptic
  have hmK : ((m : ℤ) : Ksep) ≠ 0 := by push_cast; exact hm
  have hmZ : (m : ℤ) ≠ 0 := by intro h; apply hmK; rw [h]; simp
  have hΨ : (E⁄Ksep).ΨSq (m : ℤ) ≠ 0 := (E⁄Ksep).ΨSq_ne_zero hmK
  -- the coordinate-pair encoding of a point
  let φ : (E⁄Ksep).Point → Option (Ksep × Ksep) := fun P =>
    match P with
    | .zero => none
    | .some x y _ => some (x, y)
  have hφinj : Function.Injective φ := by
    rintro (_ | ⟨x, y, h⟩) (_ | ⟨x', y', h'⟩) hPQ
    · rfl
    · exact absurd hPQ (by simp [φ])
    · exact absurd hPQ (by simp [φ])
    · simp only [φ, Option.some.injEq, Prod.mk.injEq] at hPQ
      obtain ⟨rfl, rfl⟩ := hPQ
      rfl
  -- the finite set of coordinate pairs the torsion points map into
  have hTfin : (⋃ x ∈ {x : Ksep | ((E⁄Ksep).ΨSq (m : ℤ)).IsRoot x},
      ({x} : Set Ksep) ×ˢ {y : Ksep | (E⁄Ksep).Equation x y}).Finite :=
    (Polynomial.finite_setOf_isRoot hΨ).biUnion fun x _ =>
      (Set.finite_singleton x).prod (WeierstrassCurve.Affine.finite_setOf_equation _ x)
  -- finiteness of the torsion subgroup as a set of points
  have hfin : (AddSubgroup.torsionBy (E⁄Ksep).Point (m : ℤ) : Set (E⁄Ksep).Point).Finite := by
    refine Set.Finite.of_finite_image (f := φ) ?_ hφinj.injOn
    refine ((hTfin.image some).insert none).subset ?_
    rintro _ ⟨P, hP, rfl⟩
    rw [SetLike.mem_coe] at hP
    obtain (_ | ⟨x, y, h⟩) := P
    · exact Set.mem_insert _ _
    · refine Set.mem_insert_of_mem _ ⟨(x, y), ?_, rfl⟩
      have htors : (m : ℤ) • (Affine.Point.some x y h : (E⁄Ksep).Point) = 0 :=
        (Submodule.mem_torsionBy_iff (m : ℤ) _).mp hP
      have hxroot : ((E⁄Ksep).ΨSq (m : ℤ)).IsRoot x :=
        Affine.Point.eval_ΨSq_eq_zero_of_smul_eq_zero h hmZ htors
      exact Set.mem_biUnion hxroot ⟨rfl, h.1⟩
  exact hfin.to_subtype

omit [E.IsElliptic] in
/-- The action of `Gal(Kˢᵉᵖ/K)` on the torsion of `E(Kˢᵉᵖ)` is continuous: every torsion
point is fixed by the subgroup fixing the finite extension of `K` generated by its
coordinates. -/
theorem WeierstrassCurve.torsionGaloisAction_isContinuous (m : ℤ) :
    GaloisModule.IsContinuous (WeierstrassCurve.torsionGaloisAction K E Ksep m) := by
  haveI : Algebra.IsSeparable K Ksep := IsSepClosure.separable
  haveI : Algebra.IsIntegral K Ksep := Algebra.IsAlgebraic.isIntegral
  rintro ⟨(_ | ⟨x, y, hxy⟩), hP⟩
  · exact ⟨⊥, inferInstance, fun σ _ => Subtype.ext rfl⟩
  · refine ⟨IntermediateField.adjoin K {x, y}, ?_, fun σ hσ => ?_⟩
    · exact IntermediateField.finiteDimensional_adjoin fun z _ => Algebra.IsIntegral.isIntegral z
    · have hx : σ.toAlgHom x = x := hσ ⟨x, IntermediateField.subset_adjoin K _ (by simp)⟩
      have hy : σ.toAlgHom y = y := hσ ⟨y, IntermediateField.subset_adjoin K _ (by simp)⟩
      refine Subtype.ext ?_
      change Affine.Point.map σ.toAlgHom (Affine.Point.some x y hxy) =
        Affine.Point.some x y hxy
      rw [Affine.Point.map_some]
      simp only [hx, hy]

/-- If `m` is invertible in the residue field of `R` then the Galois action on the
`m`-torsion of `E(Kˢᵉᵖ)` is flat over `R`: it is unramified by
`torsion_unramified_of_good_reduction` (the elementary Néron–Ogg–Shafarevich direction),
and a continuous unramified Galois module prolongs to a finite étale — in particular
finite flat — group scheme over `R` by the purely group-scheme-theoretic statement
`GroupScheme.GaloisModule.IsFlat.of_isUnramified`. -/
theorem WeierstrassCurve.torsion_isFlat_of_good_reduction_of_isUnit (m : ℕ)
    (hunit : IsUnit (m : IsLocalRing.ResidueField R)) :
    GaloisModule.IsFlat R (WeierstrassCurve.torsionGaloisAction K E Ksep (m : ℤ)) := by
  -- `m` is nonzero in `Kˢᵉᵖ`: otherwise it would be zero in `K`, hence in `R`
  -- (both algebra maps are injective), hence in the residue field, contradicting `hunit`.
  have hmR : (m : R) ≠ 0 := fun h => hunit.ne_zero <| by
    rw [← map_natCast (IsLocalRing.residue R) m, h, map_zero]
  have hmK : (m : Ksep) ≠ 0 := by
    intro hz
    apply hmR
    have e2 : (m : K) = 0 :=
      (algebraMap K Ksep).injective <| by rw [map_natCast, RingHom.map_zero]; exact hz
    exact IsFractionRing.injective R K <| by rw [map_natCast, RingHom.map_zero]; exact e2
  have : Finite (AddSubgroup.torsionBy (E⁄Ksep).Point (m : ℤ)) :=
    WeierstrassCurve.torsionBy_finite K E Ksep m hmK
  refine GaloisModule.IsFlat.of_isUnramified R _
    (WeierstrassCurve.torsionGaloisAction_mul K E Ksep (m : ℤ))
    (WeierstrassCurve.torsionGaloisAction_isContinuous K E Ksep (m : ℤ)) ?_
  intro 𝒪 h𝒪 σ hσ P
  exact Subtype.ext
    (WeierstrassCurve.torsion_unramified_of_good_reduction R K E m Ksep 𝒪 hunit h𝒪 σ hσ P.1 P.2)

/-- **The hard case: flatness of the residue-characteristic-power torsion.** If the
residue characteristic `p` of `R` is positive then the Galois action on the
`p^v`-torsion of `E(Kˢᵉᵖ)` is flat over `R`. This is the genuinely elliptic input to
`torsion_flat_of_good_reduction`, and the one case that cannot be reduced to the
unramifiedness of the torsion: in mixed characteristic the `p`-power torsion of a curve
with good reduction is in general highly ramified, and its flatness is the content of
the Katz–Mazur theorem that multiplication by `p^v` on the elliptic scheme attached to
a good-reduction Weierstrass equation is finite locally free (see the module docstring
and the division-polynomial lemmas below, which are the first step). -/
theorem WeierstrassCurve.torsion_isFlat_of_good_reduction_residueCharPow
    (hp : (ringChar (IsLocalRing.ResidueField R)).Prime) (v : ℕ) :
    GaloisModule.IsFlat R (WeierstrassCurve.torsionGaloisAction K E Ksep
      ((ringChar (IsLocalRing.ResidueField R) ^ v : ℕ) : ℤ)) :=
  sorry

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
          Affine.Point.map σ.toAlgHom (f (Additive.ofMul (WithConv.toConv φ))) := by
  -- It suffices to prove that the torsion Galois action is flat in the sense of
  -- `GroupScheme.GaloisModule.IsFlat`, which is this statement in packaged form.
  suffices key : GaloisModule.IsFlat R (WeierstrassCurve.torsionGaloisAction K E Ksep (n : ℤ)) by
    obtain ⟨H, hCR, hHopf, hFin, hFlat, hEt, f, hf⟩ := key
    exact ⟨H, hCR, hHopf, hFin, hFlat, hEt, f, fun σ φ => congrArg Subtype.val (hf σ φ)⟩
  haveI := ringChar.charP (IsLocalRing.ResidueField R)
  rcases CharP.char_is_prime_or_zero (IsLocalRing.ResidueField R)
      (ringChar (IsLocalRing.ResidueField R)) with hp | hp
  case inr =>
    -- Residue characteristic zero: `n` is invertible in the residue field, so this is the
    -- unramified case.
    haveI : CharP (IsLocalRing.ResidueField R) 0 := hp ▸ ringChar.charP _
    haveI := CharP.charP_to_charZero (IsLocalRing.ResidueField R)
    exact WeierstrassCurve.torsion_isFlat_of_good_reduction_of_isUnit R K E Ksep n
      (isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr (NeZero.ne n)))
  case inl =>
    -- Residue characteristic `p > 0`: split `n = p ^ v * m` with `p ∤ m`. The `m`-part is
    -- flat because it is unramified; the `p ^ v`-part is the sorried hard case; and the two
    -- glue along the equivariant primary decomposition of the torsion.
    set p := ringChar (IsLocalRing.ResidueField R) with hpdef
    obtain ⟨v, m, hpm, hnvm⟩ := Nat.exists_eq_pow_mul_and_not_dvd (NeZero.ne n) p hp.ne_one
    have hmu : IsUnit (m : IsLocalRing.ResidueField R) := by
      rw [isUnit_iff_ne_zero, Ne, CharP.cast_eq_zero_iff _ p]
      exact hpm
    -- the two halves
    have h₁ := WeierstrassCurve.torsion_isFlat_of_good_reduction_of_isUnit R K E Ksep m hmu
    have h₂ := WeierstrassCurve.torsion_isFlat_of_good_reduction_residueCharPow R K E Ksep hp v
    -- the equivariant primary decomposition
    have hcop : IsCoprime ((p ^ v : ℕ) : ℤ) ((m : ℕ) : ℤ) := by
      rw [Nat.isCoprime_iff_coprime]
      exact Nat.Coprime.pow_left v ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpm)
    obtain ⟨e, c, d, he⟩ :=
      AddSubgroup.exists_torsionBy_mul_addEquiv (A := (E⁄Ksep).Point) hcop
    -- flatness of the product action
    have hprod := GaloisModule.IsFlat.prod R
      (ρ := fun σ => AddEquiv.prodCongr
        (WeierstrassCurve.torsionGaloisAction K E Ksep ((p ^ v : ℕ) : ℤ) σ)
        (WeierstrassCurve.torsionGaloisAction K E Ksep ((m : ℕ) : ℤ) σ))
      (fun σ x => rfl) h₂ h₁
    -- the decomposition is equivariant, because its components are multiplications by
    -- fixed integers and the Galois action is additive
    have hfwd : ∀ (σ : Ksep ≃ₐ[K] Ksep)
        (P : AddSubgroup.torsionBy (E⁄Ksep).Point (((p ^ v : ℕ) : ℤ) * ((m : ℕ) : ℤ))),
        e (WeierstrassCurve.torsionGaloisAction K E Ksep (((p ^ v : ℕ) : ℤ) * ((m : ℕ) : ℤ)) σ P)
          = AddEquiv.prodCongr
            (WeierstrassCurve.torsionGaloisAction K E Ksep ((p ^ v : ℕ) : ℤ) σ)
            (WeierstrassCurve.torsionGaloisAction K E Ksep ((m : ℕ) : ℤ) σ) (e P) := by
      intro σ P
      refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
      · change ((e _).1 : (E⁄Ksep).Point) =
          Affine.Point.map σ.toAlgHom ((e P).1 : (E⁄Ksep).Point)
        rw [(he _).1, (he P).1, map_zsmul]
        rfl
      · change ((e _).2 : (E⁄Ksep).Point) =
          Affine.Point.map σ.toAlgHom ((e P).2 : (E⁄Ksep).Point)
        rw [(he _).2, (he P).2, map_zsmul]
        rfl
    have hsymm : ∀ (σ : Ksep ≃ₐ[K] Ksep) x,
        e.symm (AddEquiv.prodCongr
            (WeierstrassCurve.torsionGaloisAction K E Ksep ((p ^ v : ℕ) : ℤ) σ)
            (WeierstrassCurve.torsionGaloisAction K E Ksep ((m : ℕ) : ℤ) σ) x) =
          WeierstrassCurve.torsionGaloisAction K E Ksep (((p ^ v : ℕ) : ℤ) * ((m : ℕ) : ℤ)) σ
            (e.symm x) := by
      intro σ x
      apply e.injective
      rw [AddEquiv.apply_symm_apply, hfwd σ (e.symm x), AddEquiv.apply_symm_apply]
    -- transport flatness of the product across the decomposition, and identify the index
    have hkey := GaloisModule.IsFlat.congr R e.symm hsymm hprod
    have hcast : ((p ^ v : ℕ) : ℤ) * ((m : ℕ) : ℤ) = ((n : ℕ) : ℤ) := by
      exact_mod_cast congrArg (Nat.cast : ℕ → ℤ) hnvm.symm
    rwa [hcast] at hkey

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
    IsCoprime (W.Φ n) (W.ΨSq n) := by
  -- The resultant is a Bézout combination of `Φ n` and `ΨSq n`
  -- (`Polynomial.exists_mul_add_mul_eq_C_resultant`) and, by `resultant_Φ_ΨSq`, equals
  -- `±Δ ^ k` — a unit, as `Δ` is. Scaling the identity by its inverse gives coprimality.
  obtain ⟨p, q, -, -, e⟩ := Polynomial.exists_mul_add_mul_eq_C_resultant (W.Φ n) (W.ΨSq n)
    (W.natDegree_Φ_le n) (W.natDegree_ΨSq_le n) (.inl (pow_ne_zero 2 (Int.natAbs_ne_zero.mpr hn)))
  obtain ⟨u, hu⟩ : IsUnit ((W.Φ n).resultant (W.ΨSq n) (n.natAbs ^ 2) (n.natAbs ^ 2 - 1)) := by
    rcases W.resultant_Φ_ΨSq hn with h | h <;> rw [h]
    exacts [hΔ.pow _, (hΔ.pow _).neg]
  rw [← hu] at e
  refine ⟨Polynomial.C (↑(u⁻¹) : R₀) * p, Polynomial.C (↑(u⁻¹) : R₀) * q, ?_⟩
  have hfactor : Polynomial.C (↑(u⁻¹) : R₀) * p * W.Φ n + Polynomial.C (↑(u⁻¹) : R₀) * q * W.ΨSq n
      = Polynomial.C (↑(u⁻¹) : R₀) * (W.Φ n * p + W.ΨSq n * q) := by ring
  rw [hfactor, e, ← map_mul, Units.inv_mul, map_one]
