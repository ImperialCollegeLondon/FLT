/-
Copyright (c) 2026 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll, Claude
-/
module

public import FLT.KnownIn1980s.EllipticCurves.UnramifiedQuadraticExtension

/-!
# Unramified lifts of separable residue field extensions

This generalizes `exists_unramified_quadraticExtension_of_residueField` (from
`UnramifiedQuadraticExtension.lean`) from quadratic to *arbitrary finite degree*: a finite
separable extension `k'` of the residue field `k` of a discrete valuation ring `R` (with fraction
field `K`) lifts to an unramified extension `L/K` of the same degree. As in the quadratic case,
writing `k' = k[X]/(p̄)` via a power basis (primitive element), we lift `p̄` to a monic `P ∈ R[X]`
and set `L = K[X]/(P)`; the integral extension `S = R[X]/(P)` is again a discrete valuation ring
with maximal ideal `𝔪_R · S` and residue field `k'`.

The `AdjoinRoot` infrastructure of `UnramifiedQuadraticExtension.lean` is already
degree-independent and is reused as is:
* `AdjoinRoot.isSeparable_of_separable`,
* `AdjoinRoot.isDiscreteValuationRing_of_irreducible_map_residue`,
* `AdjoinRoot.isFractionRing_map`.

The genuinely quadratic ingredient was the separability transfer
`Polynomial.Monic.separable_map_algebraMap_of_separable_residue`, proved there via the
discriminant. Its degree-independent analogue is
`Polynomial.Monic.separable_map_algebraMap_of_separable_map_residue` below, proved via Gauss's
lemma instead.

## Main statement

* `exists_unramified_extension_of_residueField`
-/

@[expose] public section

universe u

open IsLocalRing Polynomial

/-! ### Auxiliary lemmas -/

/-- A nonzero polynomial over a field that is not separable has a monic common divisor of
positive degree with its derivative, namely its normalized gcd with the derivative. -/
theorem Polynomial.exists_monic_dvd_dvd_derivative_of_not_separable {k : Type*} [Field k]
    {p : k[X]} (hp : p ≠ 0) (hns : ¬p.Separable) :
    ∃ q : k[X], q.Monic ∧ 0 < q.natDegree ∧ q ∣ p ∧ q ∣ derivative p := by
  classical
  rw [separable_def, ← EuclideanDomain.gcd_isUnit_iff] at hns
  have hg0 : EuclideanDomain.gcd p (derivative p) ≠ 0 := fun h =>
    hp (zero_dvd_iff.mp (h ▸ EuclideanDomain.gcd_dvd_left p (derivative p)))
  exact ⟨normalize (EuclideanDomain.gcd p (derivative p)), monic_normalize hg0,
    (monic_normalize hg0).natDegree_pos.mpr fun h => hns (normalize_eq_one.mp h),
    normalize_dvd_iff.mpr (EuclideanDomain.gcd_dvd_left _ _),
    normalize_dvd_iff.mpr (EuclideanDomain.gcd_dvd_right _ _)⟩

/-- Over an integrally closed domain `R` with fraction field `K`, a monic divisor `q ∈ K[X]` of
the image of a monic polynomial `P ∈ R[X]` is itself the image of a monic polynomial over `R`
(a form of Gauss's lemma, packaging `IsIntegrallyClosed.eq_map_mul_C_of_dvd`). -/
theorem Polynomial.Monic.exists_monic_map_eq_of_monic_dvd_map {R : Type*} [CommRing R]
    [IsDomain R] [IsIntegrallyClosed R] {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    {P : R[X]} (hP : P.Monic) {q : K[X]} (hq : q.Monic) (hdvd : q ∣ P.map (algebraMap R K)) :
    ∃ Q : R[X], Q.Monic ∧ Q.map (algebraMap R K) = q := by
  obtain ⟨Q, hQ⟩ := IsIntegrallyClosed.eq_map_mul_C_of_dvd K hP hdvd
  rw [hq.leadingCoeff, C_1, mul_one] at hQ
  exact ⟨Q, (IsFractionRing.injective R K).monic_map_iff.mpr (hQ ▸ hq), hQ⟩

/-- A finite separable field extension `k'/k` is `k[X]/(p)` for a monic separable irreducible
polynomial `p` of degree `[k' : k]` (the primitive element theorem, packaged via `AdjoinRoot`). -/
theorem Field.exists_monic_irreducible_adjoinRoot_algEquiv (k k' : Type*) [Field k] [Field k']
    [Algebra k k'] [FiniteDimensional k k'] [Algebra.IsSeparable k k'] :
    ∃ p : k[X], p.Monic ∧ p.Separable ∧ Irreducible p ∧ p.natDegree = Module.finrank k k' ∧
      Nonempty (AdjoinRoot p ≃ₐ[k] k') := by
  set pb := Field.powerBasisOfFiniteOfSeparable k k' with hpb
  have hint : IsIntegral k pb.gen := Algebra.IsIntegral.isIntegral pb.gen
  exact ⟨minpoly k pb.gen, minpoly.monic hint, Algebra.IsSeparable.isSeparable k pb.gen,
    minpoly.irreducible hint, by rw [pb.natDegree_minpoly, pb.finrank],
    ⟨AdjoinRoot.equiv' _ pb (by rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]) (minpoly.aeval _ _)⟩⟩

/-- A monic polynomial over the residue field of a local ring lifts to a monic polynomial of the
same degree over the ring. -/
theorem IsLocalRing.exists_monic_map_residue_eq {A : Type u} [CommRing A] [IsLocalRing A]
    {pbar : (ResidueField A)[X]} (h : pbar.Monic) :
    ∃ P : A[X], P.Monic ∧ P.map (residue A) = pbar ∧ P.natDegree = pbar.natDegree := by
  obtain ⟨P0, hP0⟩ := Polynomial.map_surjective (residue A) Ideal.Quotient.mk_surjective pbar
  obtain ⟨P, hP_map, hP_deg, hP_monic⟩ :=
    Polynomial.lifts_and_natDegree_eq_and_monic ⟨P0, hP0⟩ h
  exact ⟨P, hP_monic, hP_map, hP_deg⟩

/-- Reduction along `f : A →+* B` descends to `AdjoinRoot`: the square
`A[X] → B[X] → B[X]/(q)` = `A[X] → A[X]/(p) → B[X]/(q)` commutes when `q = p.map f`. -/
theorem AdjoinRoot.map_comp_mk {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) {p : A[X]}
    {q : B[X]} (h : q = p.map f) :
    (AdjoinRoot.map f p q h.dvd).comp (AdjoinRoot.mk p)
      = (AdjoinRoot.mk q).comp (Polynomial.mapRingHom f) := by
  refine Polynomial.ringHom_ext (fun a => ?_) ?_
  · rw [RingHom.comp_apply, RingHom.comp_apply, AdjoinRoot.mk_C, AdjoinRoot.map_of,
      Polynomial.coe_mapRingHom, Polynomial.map_C, AdjoinRoot.mk_C]
  · rw [RingHom.comp_apply, RingHom.comp_apply, ← AdjoinRoot.root, AdjoinRoot.map_root,
      Polynomial.coe_mapRingHom, Polynomial.map_X, ← AdjoinRoot.root]

/-- If `S = A[X]/(P)` is local with maximal ideal `𝔪_A · S`, then its residue field is
`(A/𝔪_A)[X]/(P mod 𝔪_A)`. -/
noncomputable def AdjoinRoot.residueFieldEquiv {A : Type*} [CommRing A] [IsLocalRing A]
    {P : A[X]} [IsLocalRing (AdjoinRoot P)]
    (hmax : maximalIdeal (AdjoinRoot P) = (maximalIdeal A).map (algebraMap A (AdjoinRoot P))) :
    ResidueField (AdjoinRoot P) ≃ₐ[A] AdjoinRoot (P.map (residue A)) :=
  (Ideal.quotientEquivAlgOfEq A hmax).trans (AdjoinRoot.quotEquivQuotMap P (maximalIdeal A))

/-- The simple extension `F[X]/(q)` by a root of an irreducible `q` has degree `natDegree q`.
(Degree-independent analogue of `AdjoinRoot.isQuadraticExtension`.) -/
theorem AdjoinRoot.finrank_eq_natDegree {F : Type*} [Field F] {q : F[X]}
    [Fact (Irreducible q)] : Module.finrank F (AdjoinRoot q) = q.natDegree := by
  rw [PowerBasis.finrank (AdjoinRoot.powerBasis (Fact.out (p := Irreducible q)).ne_zero),
    AdjoinRoot.powerBasis_dim]

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable {K : Type u} [Field K] [Algebra R K] [IsFractionRing R K]

/-! ### The separability transfer and the main statement -/

/-- A monic polynomial over a discrete valuation ring `R` whose reduction to the residue field is
separable stays separable over the fraction field `K`. This is the degree-independent analogue of
`Polynomial.Monic.separable_map_algebraMap_of_separable_residue` (which is the quadratic case,
proved via the discriminant).

Proof: if `P.map (algebraMap R K)` is not separable, it has a monic common factor `g` of positive
degree with its derivative. Since `R` is integrally closed and `g` is a monic divisor of the
monic `P`, Gauss's lemma descends `g` to a monic `Q ∈ R[X]`, which then divides `P` and
`derivative P` already in `R[X]` (`map_dvd_map`). Reducing mod `𝔪_R`, the reduction of `Q` is a
common factor of positive degree of `P̄` and `derivative P̄`, contradicting `P̄.Separable`. -/
theorem Polynomial.Monic.separable_map_algebraMap_of_separable_map_residue {P : R[X]}
    (hmonic : P.Monic) (hsep : (P.map (residue R)).Separable) :
    (P.map (algebraMap R K)).Separable := by
  by_contra hns
  obtain ⟨g, hgmonic, hgdeg, hgdvd, hgdvd'⟩ :=
    exists_monic_dvd_dvd_derivative_of_not_separable (hmonic.map _).ne_zero hns
  obtain ⟨Q, hQmonic, hQ⟩ := hmonic.exists_monic_map_eq_of_monic_dvd_map hgmonic hgdvd
  have hinj : Function.Injective (algebraMap R K) := IsFractionRing.injective R K
  have hdvdP : Q ∣ P := (map_dvd_map _ hinj hQmonic).mp (by rw [hQ]; exact hgdvd)
  have hdvdP' : Q ∣ derivative P := (map_dvd_map _ hinj hQmonic).mp
    (by rw [hQ, ← derivative_map]; exact hgdvd')
  refine not_isUnit_of_natDegree_pos (Q.map (residue R))
    (by rw [hQmonic.natDegree_map, ← hQmonic.natDegree_map (algebraMap R K), hQ]; exact hgdeg)
    (((separable_def _).mp hsep).isUnit_of_dvd' (map_dvd _ hdvdP) ?_)
  rw [derivative_map]
  exact map_dvd _ hdvdP'

/-- **Unramified lifting, arbitrary degree.** A finite separable extension `k'` of the residue
field of a discrete valuation ring `R` lifts to an unramified extension `L` of its fraction field
`K`: there is a finite separable extension `L/K` with `[L : K] = [k' : k]` and a discrete
valuation ring `S` with fraction field `L`, containing `R` via a local homomorphism, whose residue
field is `k'`. (The residue degree being `[L : K]` forces ramification index `1`.)

This generalizes `exists_unramified_quadraticExtension_of_residueField` to arbitrary degree. -/
theorem exists_unramified_extension_of_residueField
    (k' : Type u) [Field k'] [Algebra (ResidueField R) k']
    [FiniteDimensional (ResidueField R) k'] [Algebra.IsSeparable (ResidueField R) k'] :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra K L) (_ : FiniteDimensional K L)
      (_ : Algebra.IsSeparable K L) (_ : Algebra R L) (_ : IsScalarTower R K L) (S : Type u)
      (_ : CommRing S) (_ : IsDomain S) (_ : IsDiscreteValuationRing S) (_ : Algebra R S)
      (_ : Module.Finite R S) (_ : Algebra S L) (_ : IsScalarTower R S L) (_ : IsFractionRing S L)
      (_ : IsLocalHom (algebraMap R S)),
      Module.finrank K L = Module.finrank (ResidueField R) k'
        ∧ Nonempty (ResidueField S ≃ₐ[ResidueField R] k') := by
  classical
  -- `k' = k[X]/(pbar)` for a monic separable irreducible `pbar` of degree `[k' : k]`.
  obtain ⟨pbar, hpbar_monic, hpbar_sep, hpbar_irr, hpbar_deg, ⟨hk'_equiv⟩⟩ :=
    Field.exists_monic_irreducible_adjoinRoot_algEquiv (ResidueField R) k'
  have hpbar_pos : 0 < pbar.natDegree := hpbar_deg ▸ Module.finrank_pos
  -- Lift `pbar` to a monic `P` over `R`; irreducible over `R`, hence over `K`.
  obtain ⟨P, hP_monic, hP_map, hP_deg⟩ := IsLocalRing.exists_monic_map_residue_eq hpbar_monic
  have hP_redirr : Irreducible (P.map (residue R)) := by rw [hP_map]; exact hpbar_irr
  have hP_irr : Irreducible P :=
    Polynomial.Monic.irreducible_of_irreducible_map (residue R) P hP_monic hP_redirr
  have hPdeg : P.degree ≠ 0 := by
    rw [Polynomial.degree_eq_natDegree hP_monic.ne_zero, hP_deg]
    exact_mod_cast hpbar_pos.ne'
  set pK := P.map (algebraMap R K) with hpK
  have : Fact (Irreducible pK) :=
    ⟨(Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map (K := K) hP_monic).mp hP_irr⟩
  set L := AdjoinRoot pK with hL
  set S := AdjoinRoot P with hS
  have hSdom : IsDomain S := AdjoinRoot.isDomain_of_prime
    (UniqueFactorizationMonoid.irreducible_iff_prime.mp hP_irr)
  -- `S = R[X]/(P)` is a discrete valuation ring, unramified over `R`.
  obtain ⟨hmS_max, hSdvr, hSlocalhom⟩ :=
    AdjoinRoot.isDiscreteValuationRing_of_irreducible_map_residue hP_monic hPdeg hP_redirr
  have hmaxS : maximalIdeal S = (maximalIdeal R).map (algebraMap R S) :=
    (IsLocalRing.eq_maximalIdeal hmS_max).symm
  -- `L = K[X]/(pK)` has degree `[k' : k]` over `K`.
  have hLrank : Module.finrank K L = Module.finrank (ResidueField R) k' :=
    AdjoinRoot.finrank_eq_natDegree.trans
      (by rw [hpK, hP_monic.natDegree_map, hP_deg, hpbar_deg])
  -- The `R`-algebra map `S → L` and the tower `R → S → L`.
  let algSL : Algebra S L := (AdjoinRoot.map (algebraMap R K) P pK hpK.dvd).toAlgebra
  have halg : algebraMap S L = AdjoinRoot.map (algebraMap R K) P pK hpK.dvd :=
    RingHom.algebraMap_toAlgebra _
  have htower : IsScalarTower R S L := IsScalarTower.of_algebraMap_eq fun r => by
    rw [halg, AdjoinRoot.algebraMap_eq (f := P), AdjoinRoot.map_of, AdjoinRoot.algebraMap_eq']
    rfl
  -- Residue field: `S/𝔪_S ≅ k[X]/(pbar) ≅ k'`, as `R`-algebra equivalences, then lift the base
  -- ring to `ResidueField R` (`extendScalarsOfSurjective`).
  let _ : Algebra R k' := ((algebraMap (ResidueField R) k').comp (residue R)).toAlgebra
  have : IsScalarTower R (ResidueField R) k' := .of_algebraMap_eq fun _ => rfl
  have e : ResidueField S ≃ₐ[R] k' :=
    (AdjoinRoot.residueFieldEquiv hmaxS).trans
      ((Ideal.quotientEquivAlgOfEq R (congrArg (fun q => Ideal.span {q}) hP_map)).trans
        (hk'_equiv.restrictScalars R))
  exact ⟨L, inferInstance, inferInstance,
    Module.Finite.of_basis (AdjoinRoot.powerBasis (Fact.out (p := Irreducible pK)).ne_zero).basis,
    AdjoinRoot.isSeparable_of_separable
      (hP_monic.separable_map_algebraMap_of_separable_map_residue
        (by rw [hP_map]; exact hpbar_sep)),
    inferInstance, inferInstance, S, inferInstance, hSdom, hSdvr, inferInstance,
    Module.Finite.of_basis (AdjoinRoot.powerBasis' hP_monic).basis, algSL, htower,
    AdjoinRoot.isFractionRing_map hPdeg hmaxS
      (by rw [halg]; exact AdjoinRoot.map_comp_mk (algebraMap R K) hpK),
    hSlocalhom, hLrank, ⟨e.extendScalarsOfSurjective residue_surjective⟩⟩
