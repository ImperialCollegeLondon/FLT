/-
Copyright (c) 2026 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, William Coram, Samuel Yin
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Reduction
public import Mathlib.NumberTheory.LocalField.Basic
public import FLT.KnownIn1980s.EllipticCurves.WeilPairing
public import FLT.KnownIn1980s.EllipticCurves.TateParameter
public import FLT.KnownIn1980s.EllipticCurves.TateCurveBaseChange
public import FLT.Mathlib.AlgebraicGeometry.EllipticCurve.Affine.VariableChange
public import FLT.KnownIn1980s.EllipticCurves.MaybeMathlib
public import FLT.KnownIn1980s.EllipticCurves.TateCurveUniformisation
public import FLT.KnownIn1980s.EllipticCurves.TateCurveFunctoriality
public import FLT.KnownIn1980s.EllipticCurves.ReductionBaseChange

/-!

# The Tate curve

Let `k` be a nonarchimedean local field and let `E/k` be an elliptic curve, given by a
minimal Weierstrass equation, with split multiplicative reduction. Tate's theory attaches
to `E` a canonical *Tate parameter*, an element `q = q(E)` of `k` with `0 < |q| < 1`, and
an isomorphism of groups `E(k) ≅ kˣ/qᶻ` (Tate's uniformisation). The construction is
functorial: if `k → l` is a valuation-compatible morphism of nonarchimedean local fields
then the base change of `E` to `l` again has split multiplicative reduction, the Tate
parameter of the base change is the image of `q`, and the uniformisations over `k` and `l`
fit into a commutative diagram — in general only up to an unremovable sign, but on the nose
when the morphism is `k`-linear (see `tateEquiv_baseChange` and `tateEquiv_galois`). The
`k`-linear case gives the Galois-equivariance needed to compute the Galois representations
attached to `E`.

These results are due to Tate, in a manuscript which
circulated from the early 1960s and was eventually published in 1995 as *A review of
non-Archimedean elliptic curves*. See also Roquette, *Analytic theory of elliptic
functions over local fields* (1970), and Silverman, *Advanced topics in the arithmetic
of elliptic curves*, V.3 and V.5, for textbook accounts.

## TODO

* **Rank 1 generality.** Tate's theory works over any field complete with respect to a
  nontrivial rank 1 (i.e. real-valued) nonarchimedean valuation, for example `ℂ_p` or the
  completion of the maximal unramified extension of `ℚ_p`: completeness and `|q| < 1` are
  all that is needed for the relevant power series to converge. But right now we can't
  talk about an elliptic curve over `ℂ_p` having split multiplicative reduction, so we
  stick to nonarchimedean local fields: mathlib's
  `WeierstrassCurve.HasSplitMultiplicativeReduction` is defined via minimal Weierstrass
  equations, and mathlib's `WeierstrassCurve.IsMinimal` requires
  `IsDiscreteValuationRing` (its existence theorem `exists_isMinimal` is proved by
  well-foundedness of the value group, which fails for dense value groups).

  Mathematics question: is there a theory of minimal models for elliptic curves
  with multiplicative reduction over fields complete wrt an arbitrary rank 1 valuation?
  For additive reduction you have no chance (consider `y² = x³ + p` over `ℂₚ`).

* **Topology.** `tateEquiv` below should be an isomorphism of *topological* groups, where
  `kˣ/qᶻ` carries the quotient topology and `E(k)` the topology coming from `k`. This
  cannot currently be stated: mathlib has no topology on `WeierstrassCurve.Affine.Point`
  (nor on `Projectivization`, from which it could be induced).

* **Signs.** There is a choice of sign for the Tate uniformisation. I propose that we
  simply use the definition in e.g. Silverman. One could say explicitly what the sign
  is by asking what the pullback of the invariant differential `dx/(2y + a₁x + a₃)` to
  `kˣ` is; it will be some constant times `du/u` (for the Tate curve `E_q` itself, with
  Silverman's series, it is exactly `du/u`).
-/

@[expose] public section

open scoped WeierstrassCurve.Affine -- `(E⁄k).Point` notation for the group of `k`-points
open ValuativeRel -- `𝒪[k]` notation for the ring of integers of `k`, and `valuation`

-- Can be deleted when mathlib#41391 lands
set_option linter.overlappingInstances false

/-! ### The Tate curve `E_q`

For `q` with `0 < |q| < 1` there is an explicit Weierstrass curve `E_q`, whose coefficients
are power series in `q` with integer coefficients, together with a uniformisation
`kˣ/qᶻ ≅ E_q(k)` given by explicit power series `X(u, q)`, `Y(u, q)` — all of it involving
no choices whatsoever, and commuting on the nose with every valuative morphism of fields.
This is constructed in `FLT.KnownIn1980s.EllipticCurves.TateCurveUniformisation` (imported
above): the curve `WeierstrassCurve.tateCurve`, the coordinates `tateX`, `tateY`, the map
`tateCurvePoint : kˣ → E_q(k)` together with its three pillar properties — additivity
(`tateCurvePoint_mul`), the definitional kernel `qᶻ` (`tateCurvePoint_eq_zero_iff`, whence
injectivity `tateCurvePoint_eq_iff`), and surjectivity (`exists_tateCurvePoint_eq`) — are
assembled here into the isomorphism `tateCurveEquiv`.

The uniformisation of a general `E` with split multiplicative reduction is obtained by
transporting this one along an isomorphism `E_{q(E)} ≅ E` of Weierstrass curves
(`exists_variableChange_tateCurve` below), and *that* is the only choice in the theory:
there are exactly two such isomorphisms, differing by negation.
-/

-- let k be a nonarchimedean local field
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k]

-- `DecidableEq k` is needed for the group law on the points
variable [DecidableEq k] in
/-- Tate's uniformisation of the Tate curve `E_q`, given by the explicit power series
`x = X(u, q)`, `y = Y(u, q)` of Silverman, ATAEC V.3. Unlike `tateEquiv` below, this
involves no choices at all: it commutes on the nose with every valuative field morphism
(see `tateCurve_baseChange` for the equation-level statement).

The underlying map sends the class of `u ∈ kˣ` to `tateCurvePoint q hq u`; the
isomorphism is assembled from the three pillars of
`FLT.KnownIn1980s.EllipticCurves.TateCurveUniformisation`: additivity
(`tateCurvePoint_mul`), the definitional kernel (`tateCurvePoint_eq_zero_iff`, which
makes the descended map injective), and surjectivity (`exists_tateCurvePoint_eq`). -/
noncomputable def WeierstrassCurve.tateCurveEquiv (q : kˣ) (hq : valuation k (q : k) < 1) :
    Additive (kˣ ⧸ Subgroup.zpowers q) ≃+ ((tateCurve (q : k))⁄k).Point :=
  AddEquiv.ofBijective
    (AddMonoidHom.mk'
      (fun m : Additive (kˣ ⧸ Subgroup.zpowers q) ↦
        Quotient.liftOn' (Additive.toMul m) (tateCurvePoint q hq) fun u v h ↦
          tateCurvePoint_eq q hq u v (QuotientGroup.leftRel_apply.mp h))
      (fun m n ↦ by
        obtain ⟨x, rfl⟩ : ∃ x, Additive.ofMul x = m := ⟨Additive.toMul m, rfl⟩
        obtain ⟨y, rfl⟩ : ∃ y, Additive.ofMul y = n := ⟨Additive.toMul n, rfl⟩
        obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective x
        obtain ⟨v, rfl⟩ := QuotientGroup.mk_surjective y
        exact tateCurvePoint_mul q hq u v))
    ⟨(injective_iff_map_eq_zero _).mpr fun m hm ↦ by
      obtain ⟨x, rfl⟩ : ∃ x, Additive.ofMul x = m := ⟨Additive.toMul m, rfl⟩
      obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective x
      have hu : u ∈ Subgroup.zpowers q := (tateCurvePoint_eq_zero_iff q hq).mp hm
      simpa [← QuotientGroup.eq_one_iff] using hu,
    fun P ↦ by
      obtain ⟨u, hu⟩ := exists_tateCurvePoint_eq q hq P
      exact ⟨Additive.ofMul (QuotientGroup.mk u), hu⟩⟩

variable [DecidableEq k] in
/-- `tateCurveEquiv` sends the class of a unit `u` to `tateCurvePoint q hq u`. -/
theorem WeierstrassCurve.tateCurveEquiv_ofMul_mk (q : kˣ) (hq : valuation k (q : k) < 1)
    (u : kˣ) :
    tateCurveEquiv q hq (Additive.ofMul (↑u : kˣ ⧸ Subgroup.zpowers q)) =
      tateCurvePoint q hq u :=
  rfl

-- `tateParameter` — the inverse of `q ↦ j(q)` of Silverman, ATAEC V.5.2, by which the
-- Tate parameter is *defined* below, choice-freely — is constructed in
-- `FLT.KnownIn1980s.EllipticCurves.TateParameter` (imported above) as the evaluation at
-- `j⁻¹` of an explicit integral power series. Here we state its interaction with the
-- valuation.

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] in
lemma WeierstrassCurve.tateParameter_eq {j : k} : WeierstrassCurve.tateParameter j =
    TateCurve.evalInt j⁻¹ TateCurve.jInvReverse := by
  rfl

/-- The Tate parameter of `j` has valuation exactly `|j|⁻¹`: the leading term `j⁻¹` of
the inverse series `q = j⁻¹ + 744j⁻² + ⋯` dominates ultrametrically. -/
theorem WeierstrassCurve.valuation_tateParameter_eq {j : k} (hj : 1 < valuation k j) :
    valuation k (tateParameter j) = (valuation k j)⁻¹ := by
  have hj0 : j ≠ 0 := by
    rintro rfl
    simp [map_zero] at hj
  have h := TateCurve.valuation_evalInt_eq j⁻¹ (inv_ne_zero hj0)
    (by simpa [map_inv₀] using inv_lt_one_of_one_lt₀ hj) TateCurve.constantCoeff_jInvReverse
    TateCurve.coeff_one_jInvReverse
  rw [WeierstrassCurve.tateParameter_eq, h, map_inv₀]

theorem WeierstrassCurve.tateParameter_ne_zero {j : k} (hj : 1 < valuation k j) :
    tateParameter j ≠ 0 := by
  intro h
  have heq := valuation_tateParameter_eq hj
  rw [h, map_zero] at heq
  exact inv_ne_zero (ne_of_gt (lt_trans zero_lt_one hj)) heq.symm

theorem WeierstrassCurve.valuation_tateParameter_lt_one {j : k} (hj : 1 < valuation k j) :
    valuation k (tateParameter j) < 1 := by
  simpa [valuation_tateParameter_eq hj] using inv_lt_one_of_one_lt₀ hj

-- The next few lemmas transfer `mathlib`'s reduction-theoretic facts (stated for the adic
-- valuation of the discrete valuation ring `𝒪[k]`) to the canonical valuation of `k`,
-- through unit and maximal-ideal membership in `𝒪[k]`.

/-- An elliptic curve over `k` with bad (here multiplicative) reduction has discriminant of
valuation less than `1`: the discriminant of the integral model lies in the maximal ideal. -/
theorem WeierstrassCurve.valuation_Δ_lt_one (E : WeierstrassCurve k)
    [E.HasMultiplicativeReduction 𝒪[k]] :
    valuation k E.Δ < 1 := by
  have hbad := HasMultiplicativeReduction.badReduction (R := 𝒪[k]) (W := E)
  rw [← integralModel_Δ_eq 𝒪[k] E] at hbad ⊢
  exact adicValuation_lt_one_iff.mp hbad

/-- An elliptic curve over `k` with multiplicative reduction has `c₄` of valuation exactly
`1`: `c₄` of the integral model is a unit of `𝒪[k]`. -/
theorem WeierstrassCurve.valuation_c₄_eq_one (E : WeierstrassCurve k)
    [E.HasMultiplicativeReduction 𝒪[k]] :
    valuation k E.c₄ = 1 := by
  have hmul := HasMultiplicativeReduction.multiplicativeReduction (R := 𝒪[k]) (W := E)
  rw [← integralModel_c₄_eq 𝒪[k] E] at hmul ⊢
  exact adicValuation_eq_one_iff.mp hmul

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
/-- The discriminant of an elliptic curve has nonzero valuation. -/
theorem WeierstrassCurve.valuation_Δ_ne_zero (E : WeierstrassCurve k) [E.IsElliptic] :
    valuation k E.Δ ≠ 0 := by
  rw [(valuation k).ne_zero_iff, ← E.coe_Δ']
  exact Units.ne_zero _

/-- An elliptic curve over `k` with multiplicative reduction has `|j| = |c₄|³/|Δ| = |Δ|⁻¹`. -/
theorem WeierstrassCurve.valuation_j_eq (E : WeierstrassCurve k) [E.IsElliptic]
    [E.HasMultiplicativeReduction 𝒪[k]] :
    valuation k E.j = (valuation k E.Δ)⁻¹ := by
  rw [show E.j = (↑(E.Δ'⁻¹) : k) * E.c₄ ^ 3 from rfl, map_mul, map_pow,
    E.valuation_c₄_eq_one, one_pow, mul_one, Units.val_inv_eq_inv_val, map_inv₀, E.coe_Δ']

/-- An elliptic curve over `k` with split multiplicative reduction has non-integral
`j`-invariant, `|j(E)| > 1`: indeed `v(j) = -v(Δ_min) < 0`, since `c₄` is a unit when the
reduction is multiplicative. -/
theorem WeierstrassCurve.one_lt_valuation_j (E : WeierstrassCurve k) [E.IsElliptic]
    [E.HasSplitMultiplicativeReduction 𝒪[k]] :
    1 < valuation k E.j := by
  rw [E.valuation_j_eq]
  exact (one_lt_inv₀ (zero_lt_iff.mpr E.valuation_Δ_ne_zero)).mpr E.valuation_Δ_lt_one

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
/-- An elliptic curve with non-integral `j`-invariant has `c₄ ≠ 0`: otherwise `j = 0`. -/
theorem WeierstrassCurve.c₄_ne_zero_of_one_lt_valuation_j (W : WeierstrassCurve k)
    [W.IsElliptic] (hj : 1 < valuation k W.j) :
    W.c₄ ≠ 0 := by
  intro h0
  rw [show W.j = (↑(W.Δ'⁻¹) : k) * W.c₄ ^ 3 from rfl, h0] at hj
  simp at hj

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
/-- An elliptic curve with non-integral `j`-invariant has `c₆ ≠ 0`: otherwise
`c₄³ = 1728Δ` by the relation `1728Δ = c₄³ - c₆²`, so `j = 1728`, which is integral. -/
theorem WeierstrassCurve.c₆_ne_zero_of_one_lt_valuation_j (W : WeierstrassCurve k)
    [W.IsElliptic] (hj : 1 < valuation k W.j) :
    W.c₆ ≠ 0 := by
  intro h0
  have hc₄ : W.c₄ ^ 3 = 1728 * W.Δ := by linear_combination -W.c_relation + W.c₆ * h0
  have hj1728 : W.j = 1728 := by
    rw [show W.j = (↑(W.Δ'⁻¹) : k) * W.c₄ ^ 3 from rfl, hc₄, ← W.coe_Δ', mul_left_comm,
      Units.inv_mul, mul_one]
  rw [hj1728] at hj
  have h1728 : valuation k (1728 : k) ≤ 1 := by
    simpa using ValuativeRel.valuation_natCast_le_one (R := k) 1728
  exact absurd hj (not_lt.mpr h1728)

/-- The Tate parameter of an elliptic curve `E`, given by a minimal Weierstrass equation with
split multiplicative reduction over a nonarchimedean local field `k`: the unique element
`q` of `k` with `0 < |q| < 1` such that `j(E) = j(q) = q⁻¹ + 744 + 196884q + ⋯`, defined
directly (with no appeal to choice) as `tateParameter E.j`, the inverse `j`-series
evaluated at `j(E)`. Equivalently, the unique `q` such that `E(k̄)` is Galois-equivariantly
isomorphic to `k̄ˣ/q^ℤ`. (The bare existence of an abstract isomorphism `E(k) ≅ kˣ/q^ℤ`
would not pin down `q`: already over `ℚ_p` the groups `ℚ_pˣ/p^ℤ` and `ℚ_pˣ/(p(1+p))^ℤ`
are isomorphic, even topologically.) -/
noncomputable def WeierstrassCurve.q (E : WeierstrassCurve k) [E.IsElliptic] : k :=
  tateParameter E.j

-- Let E/k be an elliptic curve, given by a minimal Weierstrass equation,
-- with split multiplicative reduction
variable (E : WeierstrassCurve k) [E.IsElliptic] [E.HasSplitMultiplicativeReduction 𝒪[k]]
  [E.IsMinimal 𝒪[k]]

omit [E.IsMinimal 𝒪[k]] in
theorem WeierstrassCurve.q_ne_zero : E.q ≠ 0 :=
  tateParameter_ne_zero E.one_lt_valuation_j

omit [E.IsMinimal 𝒪[k]] in
/-- The Tate parameter has norm less than `1`. -/
theorem WeierstrassCurve.valuation_q_lt_one : valuation k E.q < 1 :=
  valuation_tateParameter_lt_one E.one_lt_valuation_j

/-- The Tate parameter as an element of `kˣ`. -/
noncomputable def WeierstrassCurve.qUnit : kˣ :=
  Units.mk0 E.q E.q_ne_zero

-- Tate's theorem (Silverman, ATAEC V.5.3): an elliptic curve with split multiplicative
-- reduction is isomorphic, by a change of Weierstrass coordinates, to the Tate curve of its
-- Tate parameter. Since `j(E)` is non-integral, `Aut` of the curve is `{±1}` and there are
-- exactly *two* such `C`, differing by negation. `tateEquiv` is `tateCurveEquiv` transported
-- along a choice of one of them; this binary choice, for each `E`, is the only choice in
-- the whole theory, and it cannot be made functorially in `E` — see `tateEquiv_baseChange`.
theorem WeierstrassCurve.exists_variableChange_tateCurve :
    ∃ C : VariableChange k, C • tateCurve E.q = E :=
  sorry

/-- A choice of change of Weierstrass coordinates taking the Tate curve `E_{q(E)}` to
`E` (Silverman, ATAEC V.5.3). There are exactly two, differing by negation
(`WeierstrassCurve.smul_eq_self_iff`); this fixed choice, for each `E`, is the only
choice in the whole theory. -/
noncomputable def WeierstrassCurve.tateVariableChange : VariableChange k :=
  E.exists_variableChange_tateCurve.choose

theorem WeierstrassCurve.tateVariableChange_smul :
    E.tateVariableChange • tateCurve E.q = E :=
  E.exists_variableChange_tateCurve.choose_spec

theorem WeierstrassCurve.tateVariableChange_inv_smul :
    E.tateVariableChange⁻¹ • E = tateCurve E.q :=
  inv_smul_eq_iff.mpr E.tateVariableChange_smul.symm

-- `DecidableEq k` is needed for the group law on `(E⁄k).Point`
variable [DecidableEq k] in
/-- Tate's uniformization theorem: if `E/k` is an elliptic curve with split multiplicative
reduction then `E(k)` is isomorphic to `kˣ/⟨q⟩`.
-/
noncomputable def WeierstrassCurve.tateEquiv :
    Additive (kˣ ⧸ Subgroup.zpowers E.qUnit) ≃+ (E⁄k).Point :=
  (WeierstrassCurve.tateCurveEquiv E.qUnit (by
      simpa [WeierstrassCurve.qUnit] using E.valuation_q_lt_one)).trans <| by
    change (WeierstrassCurve.tateCurve E.q).toAffine.Point ≃+ E.toAffine.Point
    exact (E.tateVariableChange.pointAddEquiv (tateCurve E.q)).symm.trans
      (Affine.Point.congr E.tateVariableChange_smul)

/-- The coordinates of the point of `E` attached by `tateEquiv` to a unit `u ∉ qᶻ` are
nonsingular: they are the transport along `E.tateVariableChange` of the point
`(X(u, q), Y(u, q))` of the Tate curve. -/
theorem WeierstrassCurve.nonsingular_tateVariableChange_inv {u : kˣ}
    (hu : u ∉ Subgroup.zpowers E.qUnit) :
    E.toAffine.Nonsingular (E.tateVariableChange⁻¹.mapX (tateX (u : k) E.q))
      (E.tateVariableChange⁻¹.mapY (tateX (u : k) E.q) (tateY (u : k) E.q)) := by
  have hq : valuation k ((E.qUnit : kˣ) : k) < 1 := by
    simpa [WeierstrassCurve.qUnit] using E.valuation_q_lt_one
  refine (E.tateVariableChange⁻¹.nonsingular_iff E _ _).mp ?_
  rw [E.tateVariableChange_inv_smul]
  exact tateCurve_nonsingular E.qUnit hq u hu

variable [DecidableEq k] in
/-- Tate's uniformisation `tateEquiv` sends the class of a unit `u ∈ qᶻ` to the point at
infinity. -/
theorem WeierstrassCurve.tateEquiv_ofMul_of_mem {u : kˣ}
    (hu : u ∈ Subgroup.zpowers E.qUnit) :
    E.tateEquiv (Additive.ofMul (↑u : kˣ ⧸ Subgroup.zpowers E.qUnit)) = 0 := by
  simp only [tateEquiv, AddEquiv.trans_apply, tateCurveEquiv_ofMul_mk]
  rw [show tateCurvePoint E.qUnit _ u = 0 from by rw [tateCurvePoint, dif_pos hu]; rfl,
    map_zero]

variable [DecidableEq k] in
/-- Tate's uniformisation `tateEquiv` in coordinates: the class of a unit `u ∉ qᶻ` is
sent to the image of the point `(X(u, q), Y(u, q))` of the Tate curve under the chosen
change of variables `E.tateVariableChange`. This is the characterisation through which
all functoriality statements about `tateEquiv` are proved. -/
theorem WeierstrassCurve.tateEquiv_ofMul_of_notMem {u : kˣ}
    (hu : u ∉ Subgroup.zpowers E.qUnit) :
    E.tateEquiv (Additive.ofMul (↑u : kˣ ⧸ Subgroup.zpowers E.qUnit)) =
      .some (E.tateVariableChange⁻¹.mapX (tateX (u : k) E.q))
        (E.tateVariableChange⁻¹.mapY (tateX (u : k) E.q) (tateY (u : k) E.q))
        (E.nonsingular_tateVariableChange_inv hu) := by
  have hq : valuation k ((E.qUnit : kˣ) : k) < 1 := by
    simpa [WeierstrassCurve.qUnit] using E.valuation_q_lt_one
  have hns' : (E.tateVariableChange • tateCurve E.q).toAffine.Nonsingular
      (E.tateVariableChange⁻¹.mapX (tateX (u : k) E.q))
      (E.tateVariableChange⁻¹.mapY (tateX (u : k) E.q) (tateY (u : k) E.q)) := by
    rw [E.tateVariableChange_smul]
    exact E.nonsingular_tateVariableChange_inv hu
  have hns0 : (tateCurve E.q).toAffine.Nonsingular (tateX (u : k) E.q) (tateY (u : k) E.q) :=
    tateCurve_nonsingular E.qUnit hq u hu
  have key : ((E.tateVariableChange.pointAddEquiv (tateCurve E.q)).symm.trans
      (Affine.Point.congr E.tateVariableChange_smul))
        (Affine.Point.some (tateX (u : k) E.q) (tateY (u : k) E.q) hns0) =
      Affine.Point.some (E.tateVariableChange⁻¹.mapX (tateX (u : k) E.q))
        (E.tateVariableChange⁻¹.mapY (tateX (u : k) E.q) (tateY (u : k) E.q))
        (E.nonsingular_tateVariableChange_inv hu) := by
    rw [AddEquiv.trans_apply, VariableChange.pointAddEquiv_symm_apply,
      E.tateVariableChange.pointEquiv_symm_some (tateCurve E.q) hns0 hns']
    exact Affine.Point.congr_some E.tateVariableChange_smul hns'
      (E.nonsingular_tateVariableChange_inv hu)
  simp only [tateEquiv, AddEquiv.trans_apply, tateCurveEquiv_ofMul_mk, id_eq]
  rw [show tateCurvePoint E.qUnit hq u = Affine.Point.some (tateX (u : k) E.q)
      (tateY (u : k) E.q) hns0 from by rw [tateCurvePoint, dif_neg hu]; rfl]
  exact key

/-! ### Functoriality

Now let `l` be a second nonarchimedean local field and let `k → l` be a morphism of fields
inducing the valuative relation on `k` from the one on `l` (the `ValuativeExtension`
hypothesis). The compatibility hypothesis is what makes the morphism continuous, hence
commute with the power series defining Tate's theory; it is automatic for `k`-embeddings
between algebraic extensions of `k` (by uniqueness of extensions of valuations over the
complete field `k`), but not for arbitrary abstract field morphisms.
-/

variable {l : Type*} [Field l] [ValuativeRel l] [TopologicalSpace l]
  [IsNonarchimedeanLocalField l] [Algebra k l] [ValuativeExtension k l]

-- The base change of E is elliptic. (Mathlib has this instance for `E.map f`, but
-- `WeierstrassCurve.baseChange` is a non-reducible `def`, so instance search cannot
-- see through it.)
instance : (E.baseChange l).IsElliptic :=
  inferInstanceAs (E.map (algebraMap k l)).IsElliptic

/-- The construction of the Tate curve commutes on the nose with any valuative morphism:
its coefficients are power series in `q` with *integer* coefficients, and the partial
sums converge at matching rates on both sides (`TateCurve.evalInt_map`). The same is true
of the uniformisation `tateCurveEquiv` (a statement we defer, as it needs transport along
this equality).

On the hypothesis `|q| < 1`: the coefficient series `tateA₄`, `tateA₆` are `tsum`s, which
take *junk values* outside the open unit disc (the `tsum` of a non-summable family is
`0`, and terms with vanishing denominators `1 - qⁿ = 0` are the junk `x/0 = 0`). Without
the hypothesis this lemma would be a statement about the alignment of junk values across
two different fields: for `|q| > 1` it would hold by accident — each term of `tateA₄` has
size `|(n+1)³|`, which does not tend to `0`, so both sides are non-summable and both junk
to `0` — but for `|q| = 1` summability hinges on how well `qⁿ` approximates `1`, a
Diophantine condition on `q`, and transferring (non-)summability along `k → l` would
further require the image of `ValuativeExtension.mapValueGroupWithZero` to be cofinal in
the value group of `l` (true for local fields, by finiteness of ramification, but yet
another argument). None of this buys anything: every consumer feeds this lemma a Tate
parameter, which lies strictly inside the disc (`valuation_q_lt_one`). So the hypothesis
is free in practice, and keeps the statement the honest identity of convergent series
that it is in Silverman. -/
theorem WeierstrassCurve.tateCurve_baseChange (q : k) (hq : valuation k q < 1) :
    (tateCurve q)⁄l = tateCurve (algebraMap k l q) := by
  have hq' : valuation l (algebraMap k l q) < 1 := TateCurve.valuation_algebraMap_lt_one hq
  have h4 : algebraMap k l (tateA₄ q) = tateA₄ (algebraMap k l q) := by
    rw [tateA₄_eq_evalInt q hq, tateA₄_eq_evalInt _ hq', TateCurve.evalInt_map q hq]
  have h6 : algebraMap k l (tateA₆ q) = tateA₆ (algebraMap k l q) := by
    rw [tateA₆_eq_evalInt q hq, tateA₆_eq_evalInt _ hq', TateCurve.evalInt_map q hq]
  ext <;> simp [WeierstrassCurve.baseChange, tateCurve, h4, h6]

-- The base change of `E` to `l` is still given by a minimal Weierstrass equation. This uses the
-- multiplicative reduction hypothesis (which makes `c₄` a unit): minimality by itself is not
-- preserved by ramified base change — `y² = x³ + p` is minimal over `ℚ_p` but not over
-- `ℚ_p(p^{1/6})`. See `WeierstrassCurve.isMinimal_baseChange` in `ReductionBaseChange`.
instance : (E.baseChange l).IsMinimal 𝒪[l] :=
  E.isMinimal_baseChange

-- and it still has split multiplicative reduction, via
-- `WeierstrassCurve.hasSplitMultiplicativeReduction_baseChange` in `ReductionBaseChange`
-- (from which the preceding `IsMinimal` also follows by class-parent projection).
instance : (E.baseChange l).HasSplitMultiplicativeReduction 𝒪[l] :=
  E.hasSplitMultiplicativeReduction_baseChange

/-- The Tate parameter series commutes with valuative extensions: it is the evaluation of
an integral power series at `j⁻¹`, so this is a direct instance of `evalInt_map`. -/
theorem WeierstrassCurve.tateParameter_map {j : k} (hj : 1 < valuation k j) :
    tateParameter (algebraMap k l j) = algebraMap k l (tateParameter j) := by
  have hjinv : valuation k j⁻¹ < 1 := by
    simpa [map_inv₀] using inv_lt_one_of_one_lt₀ hj
  simp_rw [WeierstrassCurve.tateParameter_eq, TateCurve.evalInt_map j⁻¹ hjinv, map_inv₀]

omit [E.IsMinimal 𝒪[k]] in
theorem WeierstrassCurve.q_baseChange : (E.baseChange l).q = algebraMap k l E.q := by
  rw [show (E.baseChange l).q = tateParameter (E.baseChange l).j from rfl,
    show E.q = tateParameter E.j from rfl,
    show (E.baseChange l).j = algebraMap k l E.j from E.map_j (algebraMap k l),
    tateParameter_map E.one_lt_valuation_j]

omit [E.IsMinimal 𝒪[k]] in
/-- The Tate parameter of the base change, as a unit, is the image of the Tate
parameter. -/
theorem WeierstrassCurve.qUnit_baseChange :
    (E.baseChange l).qUnit = Units.map (algebraMap k l).toMonoidHom E.qUnit := by
  ext
  simp [WeierstrassCurve.qUnit, E.q_baseChange (l := l)]

-- the transported `k`-choice of variable change is a valid `l`-choice
private theorem WeierstrassCurve.baseChange_tateVariableChange_smul :
    E.tateVariableChange.map (algebraMap k l) • tateCurve (E.baseChange l).q =
      E.baseChange l := by
  have h := congrArg (fun W ↦ WeierstrassCurve.map W (algebraMap k l))
    E.tateVariableChange_smul
  rwa [← map_variableChange,
    show (tateCurve E.q).map (algebraMap k l) = tateCurve (E.baseChange l).q from by
      rw [E.q_baseChange]; exact tateCurve_baseChange E.q E.valuation_q_lt_one] at h

omit [E.IsMinimal 𝒪[k]] in
private theorem WeierstrassCurve.isElliptic_tateCurve_baseChange :
    (tateCurve (E.baseChange l).q).IsElliptic := by
  rw [← (E.baseChange l).tateVariableChange_inv_smul]
  infer_instance

-- `tateCurve q_l` has non-integral `j`, so its `c₄`, `c₆` are nonzero
omit [E.IsMinimal 𝒪[k]] in
private theorem WeierstrassCurve.one_lt_valuation_j_tateCurve
    [(tateCurve (E.baseChange l).q).IsElliptic] :
    1 < valuation l (tateCurve (E.baseChange l).q).j := by
  have h := (E.baseChange l).one_lt_valuation_j
  rw [← variableChange_j (W := E.baseChange l)
    (C := (E.baseChange l).tateVariableChange⁻¹)] at h
  simpa only [(E.baseChange l).tateVariableChange_inv_smul] using h

-- the chosen `l`-variable-change is the transported `k`-choice, possibly composed with
-- the negation automorphism of the Tate curve: this is the dichotomy behind the sign `ε`
private theorem WeierstrassCurve.tateVariableChange_map_dichotomy :
    (E.baseChange l).tateVariableChange = E.tateVariableChange.map (algebraMap k l) ∨
      (E.baseChange l).tateVariableChange = E.tateVariableChange.map (algebraMap k l) *
        (tateCurve (E.baseChange l).q).negVariableChange := by
  haveI := E.isElliptic_tateCurve_baseChange (l := l)
  have hjT := E.one_lt_valuation_j_tateCurve (l := l)
  have hD : ((E.tateVariableChange.map (algebraMap k l))⁻¹ *
      (E.baseChange l).tateVariableChange) • tateCurve (E.baseChange l).q =
      tateCurve (E.baseChange l).q := by
    rw [mul_smul, (E.baseChange l).tateVariableChange_smul,
      inv_smul_eq_iff.mpr E.baseChange_tateVariableChange_smul.symm]
  rcases (smul_eq_self_iff (c₄_ne_zero_of_one_lt_valuation_j _ hjT)
      (c₆_ne_zero_of_one_lt_valuation_j _ hjT)).mp hD with h1 | hneg
  · exact Or.inl (inv_mul_eq_one.mp h1).symm
  · exact Or.inr (by rw [← hneg, mul_inv_cancel_left])

-- The uniformisations of `E` and of its base change fit into a commutative diagram, but only
-- up to a sign `ε` which cannot in general be removed, whatever choices are made in
-- `tateEquiv`. It is tempting to think the diagrams must commute on the nose because the
-- theory is given by universal power series — and for the curves `tateCurve q` themselves
-- they do. But `tateEquiv` for a general `E` also involves the choice of one of the two
-- isomorphisms `C : tateCurve E.q ≅ E`, whose scaling parameter is a square root
-- `u₀ = ±√(c₆(E_q)c₄(E)/(c₆(E)c₄(E_q)))`, and no choice of square roots is Galois-natural.
-- Concretely: let `E₀/ℚ_p` have *non-split* multiplicative reduction, let `k := ℚ_{p²}`
-- (the unramified quadratic extension, which splits the reduction), `E := (E₀)_k`, and let
-- `σ ∈ Gal(k/ℚ_p)` be Frobenius. Take `l := k` with the `Algebra k l` structure given by
-- `σ` (legal: `σ` is valuative). Then `E.baseChange l = E` and both routes around the
-- diagram use the *same* uniformisation `E.tateEquiv` — no choice can distinguish them —
-- while `u₀² ∈ ℚ_p` is a nonsquare (otherwise `E₀` would be split), so `σ(u₀) = -u₀` and
-- the diagram anticommutes: `ε = -1` is forced.
-- (When the morphism is `k`-linear the sign disappears: see `tateEquiv_galois` below.)
variable [DecidableEq k] [DecidableEq l] in
theorem WeierstrassCurve.tateEquiv_baseChange :
    ∃ ε : ℤˣ, ∀ u : kˣ,
      Affine.Point.baseChange (W' := E) k l (E.tateEquiv (Additive.ofMul ↑u)) =
        (ε : ℤ) • (E.baseChange l).tateEquiv
          (Additive.ofMul
            (Units.map (algebraMap k l).toMonoidHom u :
              lˣ ⧸ Subgroup.zpowers (E.baseChange l).qUnit)) := by
  have hφc : Continuous (algebraMap k l) := ValuativeExtension.continuous_algebraMap k l
  have hq : valuation k E.q < 1 := E.valuation_q_lt_one
  have hq' : valuation l (algebraMap k l E.q) < 1 := TateCurve.valuation_algebraMap_lt_one hq
  have hql : algebraMap k l E.q = (E.baseChange l).q := E.q_baseChange.symm
  -- the transported `k`-choice is a valid `l`-choice
  have hC₁' : E.tateVariableChange.map (algebraMap k l) • tateCurve (E.baseChange l).q =
      E.baseChange l := by
    have h := congrArg (fun W ↦ WeierstrassCurve.map W (algebraMap k l))
      E.tateVariableChange_smul
    rwa [← map_variableChange,
      show (tateCurve E.q).map (algebraMap k l) = tateCurve (E.baseChange l).q from by
        rw [← hql]; exact tateCurve_baseChange E.q hq] at h
  -- `tateCurve q_l` is elliptic with non-integral `j`, so its `c₄`, `c₆` are nonzero
  have hTE : (E.baseChange l).tateVariableChange⁻¹ • E.baseChange l =
      tateCurve (E.baseChange l).q :=
    inv_smul_eq_iff.mpr (E.baseChange l).tateVariableChange_smul.symm
  haveI : (tateCurve (E.baseChange l).q).IsElliptic := by
    rw [← hTE]; infer_instance
  have hjT : 1 < valuation l (tateCurve (E.baseChange l).q).j := by
    have h := (E.baseChange l).one_lt_valuation_j
    rw [← variableChange_j (W := E.baseChange l)
      (C := (E.baseChange l).tateVariableChange⁻¹)] at h
    simpa only [hTE] using h
  -- the two choices differ by the negation automorphism or agree
  have hD : ((E.baseChange l).tateVariableChange⁻¹ *
      E.tateVariableChange.map (algebraMap k l)) • tateCurve (E.baseChange l).q =
      tateCurve (E.baseChange l).q := by
    rw [mul_smul, hC₁', hTE]
  -- membership in `qᶻ` transfers along the (injective) base-change map
  have hu_iff : ∀ u : kˣ, Units.map (algebraMap k l).toMonoidHom u ∈
      Subgroup.zpowers (E.baseChange l).qUnit ↔ u ∈ Subgroup.zpowers E.qUnit := by
    intro u
    rw [E.qUnit_baseChange]
    exact MonoidHom.map_mem_zpowers_iff (Units.map_injective (algebraMap k l).injective)
  -- the coordinate series transport on the nose
  have hXmap : ∀ u : kˣ, algebraMap k l (tateX (u : k) E.q) =
      tateX ((Units.map (algebraMap k l).toMonoidHom u : lˣ) : l) (E.baseChange l).q := by
    intro u
    rw [show ((Units.map (algebraMap k l).toMonoidHom u : lˣ) : l) =
      algebraMap k l (u : k) from rfl, ← hql]
    exact tateX_map_of_continuous (algebraMap k l) hφc E.qUnit u hq hq'
  have hYmap : ∀ u : kˣ, algebraMap k l (tateY (u : k) E.q) =
      tateY ((Units.map (algebraMap k l).toMonoidHom u : lˣ) : l) (E.baseChange l).q := by
    intro u
    rw [show ((Units.map (algebraMap k l).toMonoidHom u : lˣ) : l) =
      algebraMap k l (u : k) from rfl, ← hql]
    exact tateY_map_of_continuous (algebraMap k l) hφc E.qUnit u hq hq'
  rcases (smul_eq_self_iff (c₄_ne_zero_of_one_lt_valuation_j _ hjT)
      (c₆_ne_zero_of_one_lt_valuation_j _ hjT)).mp hD with h1 | hneg
  · -- the choices agree: the diagram commutes on the nose, `ε = 1`
    have hC12 : (E.baseChange l).tateVariableChange =
        E.tateVariableChange.map (algebraMap k l) := inv_mul_eq_one.mp h1
    refine ⟨1, fun u ↦ ?_⟩
    by_cases hu : u ∈ Subgroup.zpowers E.qUnit
    · simp only [E.tateEquiv_ofMul_of_mem hu, map_zero,
        (E.baseChange l).tateEquiv_ofMul_of_mem ((hu_iff u).mpr hu), smul_zero]
      rfl
    · rw [E.tateEquiv_ofMul_of_notMem hu,
        (E.baseChange l).tateEquiv_ofMul_of_notMem (fun h ↦ hu ((hu_iff u).mp h)),
        Affine.Point.map_some]
      have hX : (Algebra.ofId k l) (E.tateVariableChange⁻¹.mapX (tateX (u : k) E.q)) =
          (E.baseChange l).tateVariableChange⁻¹.mapX
            (tateX ((Units.map (algebraMap k l).toMonoidHom u : lˣ) : l)
              (E.baseChange l).q) := by
        rw [show ((Algebra.ofId k l) : k → l) = ⇑(algebraMap k l) from rfl, map_mapX,
          hXmap u, show E.tateVariableChange⁻¹.map (algebraMap k l) =
            (E.baseChange l).tateVariableChange⁻¹ from by
              rw [hC12]; exact map_inv (VariableChange.mapHom (algebraMap k l)) _]
      have hY : (Algebra.ofId k l) (E.tateVariableChange⁻¹.mapY (tateX (u : k) E.q)
          (tateY (u : k) E.q)) =
          (E.baseChange l).tateVariableChange⁻¹.mapY
            (tateX ((Units.map (algebraMap k l).toMonoidHom u : lˣ) : l)
              (E.baseChange l).q)
            (tateY ((Units.map (algebraMap k l).toMonoidHom u : lˣ) : l)
              (E.baseChange l).q) := by
        rw [show ((Algebra.ofId k l) : k → l) = ⇑(algebraMap k l) from rfl, map_mapY,
          hXmap u, hYmap u, show E.tateVariableChange⁻¹.map (algebraMap k l) =
            (E.baseChange l).tateVariableChange⁻¹ from by
              rw [hC12]; exact map_inv (VariableChange.mapHom (algebraMap k l)) _]
      simp only [hX, hY, show ((1 : ℤˣ) : ℤ) = 1 from rfl, one_zsmul]
      rfl
  · -- the choices differ by negation: the diagram anticommutes, `ε = -1`
    have hC12 : E.tateVariableChange.map (algebraMap k l) =
        (E.baseChange l).tateVariableChange *
          (tateCurve (E.baseChange l).q).negVariableChange := by
      rw [← hneg, mul_inv_cancel_left]
    refine ⟨-1, fun u ↦ ?_⟩
    by_cases hu : u ∈ Subgroup.zpowers E.qUnit
    · simp only [E.tateEquiv_ofMul_of_mem hu, map_zero,
        (E.baseChange l).tateEquiv_ofMul_of_mem ((hu_iff u).mpr hu), smul_zero]
      rfl
    · have hul : Units.map (algebraMap k l).toMonoidHom u ∉
          Subgroup.zpowers (E.baseChange l).qUnit := fun h ↦ hu ((hu_iff u).mp h)
      rw [E.tateEquiv_ofMul_of_notMem hu,
        (E.baseChange l).tateEquiv_ofMul_of_notMem hul, Affine.Point.map_some]
      have hCinv : E.tateVariableChange⁻¹.map (algebraMap k l) =
          (tateCurve (E.baseChange l).q).negVariableChange *
            (E.baseChange l).tateVariableChange⁻¹ := by
        rw [show E.tateVariableChange⁻¹.map (algebraMap k l) =
            (E.tateVariableChange.map (algebraMap k l))⁻¹ from
              map_inv (VariableChange.mapHom (algebraMap k l)) _, hC12, mul_inv_rev,
          inv_negVariableChange]
      have hX : (Algebra.ofId k l) (E.tateVariableChange⁻¹.mapX (tateX (u : k) E.q)) =
          (E.baseChange l).tateVariableChange⁻¹.mapX
            (tateX ((Units.map (algebraMap k l).toMonoidHom u : lˣ) : l)
              (E.baseChange l).q) := by
        rw [show ((Algebra.ofId k l) : k → l) = ⇑(algebraMap k l) from rfl, map_mapX,
          hXmap u, hCinv, VariableChange.mul_mapX, negVariableChange_mapX]
      have hY : (Algebra.ofId k l) (E.tateVariableChange⁻¹.mapY (tateX (u : k) E.q)
          (tateY (u : k) E.q)) =
          (E.baseChange l).tateVariableChange⁻¹.mapY
            (tateX ((Units.map (algebraMap k l).toMonoidHom u : lˣ) : l)
              (E.baseChange l).q)
            ((tateCurve (E.baseChange l).q).toAffine.negY
              (tateX ((Units.map (algebraMap k l).toMonoidHom u : lˣ) : l)
                (E.baseChange l).q)
              (tateY ((Units.map (algebraMap k l).toMonoidHom u : lˣ) : l)
                (E.baseChange l).q)) := by
        rw [show ((Algebra.ofId k l) : k → l) = ⇑(algebraMap k l) from rfl, map_mapY,
          hXmap u, hYmap u, hCinv, VariableChange.mul_mapY, negVariableChange_mapX,
          negVariableChange_mapY]
      have hnegY : (E.baseChange l).toAffine.negY
          ((E.baseChange l).tateVariableChange⁻¹.mapX
            (tateX ((Units.map (algebraMap k l).toMonoidHom u : lˣ) : l)
              (E.baseChange l).q))
          ((E.baseChange l).tateVariableChange⁻¹.mapY
            (tateX ((Units.map (algebraMap k l).toMonoidHom u : lˣ) : l)
              (E.baseChange l).q)
            (tateY ((Units.map (algebraMap k l).toMonoidHom u : lˣ) : l)
              (E.baseChange l).q)) =
          (E.baseChange l).tateVariableChange⁻¹.mapY
            (tateX ((Units.map (algebraMap k l).toMonoidHom u : lˣ) : l)
              (E.baseChange l).q)
            ((tateCurve (E.baseChange l).q).toAffine.negY
              (tateX ((Units.map (algebraMap k l).toMonoidHom u : lˣ) : l)
                (E.baseChange l).q)
              (tateY ((Units.map (algebraMap k l).toMonoidHom u : lˣ) : l)
                (E.baseChange l).q)) := by
        rw [VariableChange.negY_apply, hTE]
      simp only [hX, hY, show ((-1 : ℤˣ) : ℤ) = -1 from rfl, neg_one_zsmul,
        Affine.Point.neg_some]
      congr 1
      exact hnegY.symm

-- Galois equivariance: for a `k`-*algebra* automorphism `σ` of `l` the diagram commutes
-- with no sign, because `E` and a choice of uniformisation for it already live over `k`,
-- and `σ` fixes `k`. This is the statement needed to compute the Galois action on the
-- torsion of `E`. The continuity hypothesis on `σ` is automatic when `l/k` is algebraic
-- (e.g. a finite extension), by uniqueness of extensions of valuations.
variable [DecidableEq l] in
theorem WeierstrassCurve.tateEquiv_galois (σ : l ≃ₐ[k] l) (hσ : Continuous σ) (u : lˣ) :
    Affine.Point.map (W' := E) σ.toAlgHom
        ((E.baseChange l).tateEquiv (Additive.ofMul ↑u) : (E⁄l).Point) =
      (E.baseChange l).tateEquiv
        (Additive.ofMul ↑(Units.map σ.toAlgHom.toRingHom.toMonoidHom u)) := by
  have hq : valuation l (E.baseChange l).q < 1 := (E.baseChange l).valuation_q_lt_one
  have hσq : σ.toAlgHom.toRingHom (E.baseChange l).q = (E.baseChange l).q := by
    rw [E.q_baseChange (l := l)]
    exact σ.commutes E.q
  have hqσ : valuation l (σ.toAlgHom.toRingHom (E.baseChange l).q) < 1 := by
    rw [hσq]; exact hq
  -- `σ` fixes the Tate curve over `l` and the base change of `E`
  have hσT : (tateCurve (E.baseChange l).q).map σ.toAlgHom.toRingHom =
      tateCurve (E.baseChange l).q := by
    rw [tateCurve_map_of_continuous σ.toAlgHom.toRingHom hσ hq hqσ, hσq]
  have hσE : (E.baseChange l).map σ.toAlgHom.toRingHom = E.baseChange l := by
    rw [show E.baseChange l = E.map (algebraMap k l) from rfl, WeierstrassCurve.map_map,
      show σ.toAlgHom.toRingHom.comp (algebraMap k l) = algebraMap k l from
        AlgHom.comp_algebraMap σ.toAlgHom]
  -- the transported `k`-choice is a valid, `σ`-fixed `l`-choice
  have hq_k : valuation k E.q < 1 := E.valuation_q_lt_one
  have hql : algebraMap k l E.q = (E.baseChange l).q := E.q_baseChange.symm
  have hC₁' : E.tateVariableChange.map (algebraMap k l) • tateCurve (E.baseChange l).q =
      E.baseChange l := by
    have h := congrArg (fun W ↦ WeierstrassCurve.map W (algebraMap k l))
      E.tateVariableChange_smul
    rwa [← map_variableChange,
      show (tateCurve E.q).map (algebraMap k l) = tateCurve (E.baseChange l).q from by
        rw [← hql]; exact tateCurve_baseChange E.q hq_k] at h
  -- the dichotomy between the two `l`-choices
  have hTE : (E.baseChange l).tateVariableChange⁻¹ • E.baseChange l =
      tateCurve (E.baseChange l).q :=
    inv_smul_eq_iff.mpr (E.baseChange l).tateVariableChange_smul.symm
  haveI : (tateCurve (E.baseChange l).q).IsElliptic := by
    rw [← hTE]; infer_instance
  have hjT : 1 < valuation l (tateCurve (E.baseChange l).q).j := by
    have h := (E.baseChange l).one_lt_valuation_j
    rw [← variableChange_j (W := E.baseChange l)
      (C := (E.baseChange l).tateVariableChange⁻¹)] at h
    simpa only [hTE] using h
  have hD : ((E.tateVariableChange.map (algebraMap k l))⁻¹ *
      (E.baseChange l).tateVariableChange) • tateCurve (E.baseChange l).q =
      tateCurve (E.baseChange l).q := by
    rw [mul_smul, (E.baseChange l).tateVariableChange_smul,
      inv_smul_eq_iff.mpr hC₁'.symm]
  -- `σ` fixes the chosen `l`-variable-change, since both dichotomy factors are `σ`-fixed
  have hσC₂ : (E.baseChange l).tateVariableChange.map σ.toAlgHom.toRingHom =
      (E.baseChange l).tateVariableChange := by
    have hσC₁' : (E.tateVariableChange.map (algebraMap k l)).map σ.toAlgHom.toRingHom =
        E.tateVariableChange.map (algebraMap k l) := by
      rw [VariableChange.map_map,
        show σ.toAlgHom.toRingHom.comp (algebraMap k l) = algebraMap k l from
          AlgHom.comp_algebraMap σ.toAlgHom]
    rcases (smul_eq_self_iff (c₄_ne_zero_of_one_lt_valuation_j _ hjT)
        (c₆_ne_zero_of_one_lt_valuation_j _ hjT)).mp hD with h1 | hneg
    · rw [show (E.baseChange l).tateVariableChange =
        E.tateVariableChange.map (algebraMap k l) from (inv_mul_eq_one.mp h1).symm, hσC₁']
    · rw [show (E.baseChange l).tateVariableChange =
          E.tateVariableChange.map (algebraMap k l) *
            (tateCurve (E.baseChange l).q).negVariableChange from by
            rw [← hneg, mul_inv_cancel_left],
        show (E.tateVariableChange.map (algebraMap k l) *
            (tateCurve (E.baseChange l).q).negVariableChange).map σ.toAlgHom.toRingHom =
          (E.tateVariableChange.map (algebraMap k l)).map σ.toAlgHom.toRingHom *
            (tateCurve (E.baseChange l).q).negVariableChange.map σ.toAlgHom.toRingHom from
          map_mul (VariableChange.mapHom σ.toAlgHom.toRingHom) _ _,
        hσC₁', map_negVariableChange, hσT]
  -- `σ` fixes `qᶻ` and its membership
  have hσqUnit : Units.map σ.toAlgHom.toRingHom.toMonoidHom (E.baseChange l).qUnit =
      (E.baseChange l).qUnit := by
    ext
    simpa [WeierstrassCurve.qUnit] using hσq
  have hu_iff : Units.map σ.toAlgHom.toRingHom.toMonoidHom u ∈
      Subgroup.zpowers (E.baseChange l).qUnit ↔ u ∈ Subgroup.zpowers (E.baseChange l).qUnit := by
    conv_lhs => rw [← hσqUnit]
    exact MonoidHom.map_mem_zpowers_iff
      (Units.map_injective σ.toAlgHom.toRingHom.injective)
  by_cases hu : u ∈ Subgroup.zpowers (E.baseChange l).qUnit
  · rw [show ((E.baseChange l).tateEquiv (Additive.ofMul (↑u : lˣ ⧸ Subgroup.zpowers
        (E.baseChange l).qUnit)) : (E⁄l).Point) = 0 from
        (E.baseChange l).tateEquiv_ofMul_of_mem hu,
      (E.baseChange l).tateEquiv_ofMul_of_mem (hu_iff.mpr hu)]
    exact map_zero _
  · -- the coordinate chase, with no sign
    have hXσ : σ.toAlgHom.toRingHom (tateX (u : l) (E.baseChange l).q) =
        tateX ((Units.map σ.toAlgHom.toRingHom.toMonoidHom u : lˣ) : l)
          (E.baseChange l).q := by
      have h := tateX_map_of_continuous σ.toAlgHom.toRingHom hσ (E.baseChange l).qUnit u
        hq hqσ
      rwa [show σ.toAlgHom.toRingHom (((E.baseChange l).qUnit : lˣ) : l) =
        (E.baseChange l).q from hσq] at h
    have hYσ : σ.toAlgHom.toRingHom (tateY (u : l) (E.baseChange l).q) =
        tateY ((Units.map σ.toAlgHom.toRingHom.toMonoidHom u : lˣ) : l)
          (E.baseChange l).q := by
      have h := tateY_map_of_continuous σ.toAlgHom.toRingHom hσ (E.baseChange l).qUnit u
        hq hqσ
      rwa [show σ.toAlgHom.toRingHom (((E.baseChange l).qUnit : lˣ) : l) =
        (E.baseChange l).q from hσq] at h
    have hCinvσ : (E.baseChange l).tateVariableChange⁻¹.map σ.toAlgHom.toRingHom =
        (E.baseChange l).tateVariableChange⁻¹ := by
      rw [show (E.baseChange l).tateVariableChange⁻¹.map σ.toAlgHom.toRingHom =
          ((E.baseChange l).tateVariableChange.map σ.toAlgHom.toRingHom)⁻¹ from
          map_inv (VariableChange.mapHom σ.toAlgHom.toRingHom) _, hσC₂]
    have hX : σ.toAlgHom ((E.baseChange l).tateVariableChange⁻¹.mapX
        (tateX (u : l) (E.baseChange l).q)) =
        (E.baseChange l).tateVariableChange⁻¹.mapX
          (tateX ((Units.map σ.toAlgHom.toRingHom.toMonoidHom u : lˣ) : l)
            (E.baseChange l).q) := by
      rw [show (⇑σ.toAlgHom : l → l) = ⇑σ.toAlgHom.toRingHom from rfl, map_mapX, hXσ,
        hCinvσ]
    have hY : σ.toAlgHom ((E.baseChange l).tateVariableChange⁻¹.mapY
        (tateX (u : l) (E.baseChange l).q) (tateY (u : l) (E.baseChange l).q)) =
        (E.baseChange l).tateVariableChange⁻¹.mapY
          (tateX ((Units.map σ.toAlgHom.toRingHom.toMonoidHom u : lˣ) : l)
            (E.baseChange l).q)
          (tateY ((Units.map σ.toAlgHom.toRingHom.toMonoidHom u : lˣ) : l)
            (E.baseChange l).q) := by
      rw [show (⇑σ.toAlgHom : l → l) = ⇑σ.toAlgHom.toRingHom from rfl, map_mapY, hXσ,
        hYσ, hCinvσ]
    rw [show ((E.baseChange l).tateEquiv (Additive.ofMul (↑u : lˣ ⧸ Subgroup.zpowers
        (E.baseChange l).qUnit)) : (E⁄l).Point) =
        .some ((E.baseChange l).tateVariableChange⁻¹.mapX
          (tateX (u : l) (E.baseChange l).q))
        ((E.baseChange l).tateVariableChange⁻¹.mapY (tateX (u : l) (E.baseChange l).q)
          (tateY (u : l) (E.baseChange l).q))
        ((E.baseChange l).nonsingular_tateVariableChange_inv hu) from
        (E.baseChange l).tateEquiv_ofMul_of_notMem hu,
      (E.baseChange l).tateEquiv_ofMul_of_notMem (fun h ↦ hu (hu_iff.mp h))]
    exact (Affine.Point.map_some σ.toAlgHom _).trans (by simp only [hX, hY]; rfl)

/-! ### Torsion and the Weil pairing

Passing to the limit over the finite subextensions of a separable closure `Ω` of `k`, the
uniformisations above glue to a Galois-equivariant uniformisation `E(Ω) ≅ Ωˣ/qᶻ`. The
`N`-torsion of `Ωˣ/qᶻ` is generated by the `N`-th roots of unity and (the classes of) the
`N`-th roots of `q`, so the uniformisation identifies the `N`-torsion of `E` explicitly:
this is how one computes the Galois representations attached to `E`.

The identification is compatible with the Weil pairing: with a suitable sign convention in
the definition of the Weil pairing `e_N`, we have `e_N(ζ, q^{1/N}) = ζ` for every `N`-th
root of unity `ζ` and every `N`-th root `q^{1/N}` of `q`, where on the left-hand side units
are identified with points of `E` via the uniformisation. This is the content of
`weilPairing_tatePoint` below; see the comment there for exactly what this does and
does not pin down.
-/

-- Now let `Ω` be a separable closure of `k`. It is not itself a nonarchimedean local field
-- (it is not complete), so it does not fit the framework above; but `E(Ω)` is the union of
-- the `E(l)` over the finite subextensions `l/k` of `Ω`, and Tate's theory applies to each.
variable (Ω : Type*) [Field Ω] [Algebra k Ω] [IsSepClosed Ω] [Algebra.IsSeparable k Ω]

-- the base change of E to Ω is elliptic (same remark as for `l` above)
instance : (E.baseChange Ω).IsElliptic :=
  inferInstanceAs (E.map (algebraMap k Ω)).IsElliptic

/-- The image of the Tate parameter in a separable closure `Ω` of `k`, as a unit. (`Ω` is
not a nonarchimedean local field, so this is not literally `(E.baseChange Ω).qUnit`.) -/
noncomputable def WeierstrassCurve.qUnitSepClosure : Ωˣ :=
  Units.map (algebraMap k Ω).toMonoidHom E.qUnit

-- `DecidableEq Ω` is needed for the group law on `(E⁄Ω).Point`
variable [DecidableEq Ω]

/-- Tate's uniformisation over a separable closure `Ω` of `k`: the union of the
uniformisations of the `E(l)` over the finite subextensions `l/k` of `Ω`. Its sign is
pinned to that of `tateEquiv` by `tatePoint_baseChange`. -/
noncomputable def WeierstrassCurve.tateEquivSepClosure :
    Additive (Ωˣ ⧸ Subgroup.zpowers (E.qUnitSepClosure Ω)) ≃+ (E⁄Ω).Point :=
  sorry

/-- The point of `E(Ω)` corresponding to a unit `x ∈ Ωˣ` under Tate's uniformisation. -/
noncomputable def WeierstrassCurve.tatePoint (x : Ωˣ) : (E⁄Ω).Point :=
  E.tateEquivSepClosure Ω (Additive.ofMul ↑x)

-- The uniformisations over `k` and over `Ω` commute on the nose, not merely up to sign:
-- the inclusion `k → Ω` is a `k`-algebra map, so this is an instance of the same
-- phenomenon as `tateEquiv_galois`, not of `tateEquiv_baseChange`. This statement is what
-- pins the sign of `tateEquivSepClosure` to the sign of `tateEquiv`.
variable [DecidableEq k] in
theorem WeierstrassCurve.tatePoint_baseChange (u : kˣ) :
    Affine.Point.baseChange (W' := E) k Ω (E.tateEquiv (Additive.ofMul ↑u)) =
      E.tatePoint Ω (Units.map (algebraMap k Ω).toMonoidHom u) :=
  sorry

-- Galois equivariance of the uniformisation over `Ω`: no continuity hypothesis is needed
-- this time, since `Ω/k` is algebraic.
theorem WeierstrassCurve.tatePoint_galois (σ : Ω ≃ₐ[k] Ω) (u : Ωˣ) :
    Affine.Point.map (W' := E) σ.toAlgHom (E.tatePoint Ω u) =
      E.tatePoint Ω (Units.map σ.toAlgHom.toRingHom.toMonoidHom u) :=
  sorry

/-- `N`-th roots of unity give `N`-torsion points of `E` under Tate's uniformisation. -/
theorem WeierstrassCurve.tatePoint_mem_torsionBy_of_mem_rootsOfUnity {N : ℕ} {ζ : Ωˣ}
    (hζ : ζ ∈ rootsOfUnity N Ω) :
    E.tatePoint Ω ζ ∈ AddSubgroup.torsionBy (E⁄Ω).Point (N : ℤ) :=
  sorry

/-- `N`-th roots of the Tate parameter give `N`-torsion points of `E` under Tate's
uniformisation. -/
theorem WeierstrassCurve.tatePoint_mem_torsionBy_of_pow_eq {N : ℕ} {r : Ωˣ}
    (hr : r ^ N = E.qUnitSepClosure Ω) :
    E.tatePoint Ω r ∈ AddSubgroup.torsionBy (E⁄Ω).Point (N : ℤ) :=
  sorry

-- `weilPairing` and `tateEquiv`/`tateEquivSepClosure` are all currently `sorry`ed data,
-- each pinned down mathematically only up to a sign. The following compatibility, due to
-- Tate, is the demand that these signs be chosen coherently. Note that it constrains the
-- sign convention in the *Weil pairing* (about which the literature does not agree) in
-- terms of the uniformisation, and not vice versa: by bilinearity `e_N(-P, -Q) = e_N(P, Q)`,
-- so the demand is insensitive to negating `tateEquivSepClosure`.
theorem WeierstrassCurve.weilPairing_tatePoint (N : ℕ) [NeZero (N : Ω)] {ζ r : Ωˣ}
    (hζ : ζ ∈ rootsOfUnity N Ω) (hr : r ^ N = E.qUnitSepClosure Ω) :
    (E⁄Ω).weilPairing Ω N
      ⟨E.tatePoint Ω ζ, E.tatePoint_mem_torsionBy_of_mem_rootsOfUnity Ω hζ⟩
      ⟨E.tatePoint Ω r, E.tatePoint_mem_torsionBy_of_pow_eq Ω hr⟩ =
    Additive.ofMul (⟨ζ, hζ⟩ : rootsOfUnity N Ω) :=
  sorry
