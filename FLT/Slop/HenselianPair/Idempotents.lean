/-
Copyright (c) 2026 Akhil Mathew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Akhil Mathew
-/
module

public import FLT.Slop.HenselianPair.Defs
public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.Idempotents

/-!
# Lifting idempotents along a Henselian pair

For a Henselian pair `(R, I)` idempotents of `R ⧸ I` lift uniquely to idempotents of `R`, and
likewise for orthogonal and complete orthogonal systems of idempotents. This is one of the
equivalent conditions in the Henselian-pair TFAE (Stacks Tag 09XI(2)).

Conversely, bijectivity of the idempotent-reduction map for all finite (or integral) algebras
already forces `I ≤ Jac(R)`, which isolates the first paragraph of the converse direction.

## Main definitions

* `IsHenselianPair.idempotentQuotientEquiv` — idempotents of `R` are equivalent to idempotents
  of `R ⧸ I`.
* `IsHenselianPair.orthogonalIdempotentsQuotientEquiv`,
  `IsHenselianPair.completeOrthogonalIdempotentsQuotientEquiv` — the same for systems.

## Main results

* `IsHenselianPair.existsUnique_isIdempotentElem_lift` — idempotents lift uniquely.
* `IsHenselianPair.le_jacobson_of_idempotentQuotientMap_bijective_of_finite` and the integral
  variant — the idempotent-bijection criteria imply `I ≤ Jac(R)`.

## References

* [Stacks Project, Tag 09XI](https://stacks.math.columbia.edu/tag/09XI)
-/

@[expose] public section

open Polynomial

variable {R : Type*} [CommRing R]

namespace IsHenselianPair

/-- **Idempotents lift along `R → R ⧸ I`** for a Henselian pair `(R, I)`.
This is one of the equivalent conditions in the pair TFAE (Stacks Tag 09XI). -/
theorem exists_isIdempotentElem_lift {I : Ideal R} (h : IsHenselianPair R I) {ε : R ⧸ I}
    (hε : IsIdempotentElem ε) : ∃ e : R, IsIdempotentElem e ∧ Ideal.Quotient.mk I e = ε := by
  obtain ⟨a₀, ha₀⟩ := Ideal.Quotient.mk_surjective ε
  -- `ε` is a simple root of `f = X² - X` mod `I`; its Henselian lift is the idempotent.
  set f : R[X] := X ^ 2 - X with hf
  have hfmonic : f.Monic := by
    rw [hf]
    exact monic_X_pow_sub (n := 2) (lt_of_le_of_lt degree_X_le (by decide))
  have heval : f.eval a₀ = a₀ ^ 2 - a₀ := by simp [hf]
  -- `a₀² - a₀ ∈ I` because `ε` is idempotent.
  have hmem : a₀ ^ 2 - a₀ ∈ I := by
    rwa [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_pow, ha₀, sub_eq_zero, sq]
  -- the derivative `2X - 1` evaluates to a unit modulo `I` (it is its own inverse).
  have hderiv : IsUnit (Ideal.Quotient.mk I (f.derivative.eval a₀)) := by
    have hde : f.derivative.eval a₀ = 2 * a₀ - 1 := by
      simp only [hf, derivative_sub, derivative_X_pow, derivative_X, Nat.cast_ofNat,
        eval_sub, eval_mul, eval_C, eval_pow, eval_X, eval_one]
      ring
    rw [hde]
    refine IsUnit.of_mul_eq_one (Ideal.Quotient.mk I (2 * a₀ - 1)) ?_
    rw [← map_mul, ← map_one (Ideal.Quotient.mk I), Ideal.Quotient.eq,
      show (2 * a₀ - 1) * (2 * a₀ - 1) - 1 = 4 * (a₀ ^ 2 - a₀) by ring]
    exact I.mul_mem_left 4 hmem
  obtain ⟨e, he_root, he_sub⟩ :=
    h.henselianRing.is_henselian f hfmonic a₀ (heval ▸ hmem) hderiv
  have he_eval : e ^ 2 - e = 0 := by
    have : f.eval e = 0 := he_root
    rwa [hf, eval_sub, eval_pow, eval_X] at this
  refine ⟨e, ?_, ?_⟩
  · change e * e = e
    linear_combination he_eval
  · rwa [← ha₀, ← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]

/-- An idempotent element in the Jacobson radical is zero. -/
theorem isIdempotentElem_eq_zero_of_mem_jacobson {e : R} (he : IsIdempotentElem e)
    (hejac : e ∈ Ideal.jacobson (⊥ : Ideal R)) : e = 0 := by
  rw [Ideal.mem_jacobson_bot] at hejac
  have hunit : IsUnit (1 - e) := by
    convert hejac (-1) using 1
    ring
  exact hunit.mul_right_eq_zero.mp he.one_sub_mul_self

/-- Two idempotents congruent modulo the Jacobson radical are equal. -/
theorem isIdempotentElem_eq_of_sub_mem_jacobson {e₁ e₂ : R} (he₁ : IsIdempotentElem e₁)
    (he₂ : IsIdempotentElem e₂) (hdiff : e₁ - e₂ ∈ Ideal.jacobson (⊥ : Ideal R)) : e₁ = e₂ := by
  let J : Ideal R := Ideal.jacobson (⊥ : Ideal R)
  have hleft_mem : e₁ * (1 - e₂) ∈ J := by
    have hrewrite : e₁ * (1 - e₂) = e₁ * (e₁ - e₂) := by
      rw [mul_sub, mul_sub, mul_one, he₁.eq]
    rw [hrewrite]
    exact J.mul_mem_left e₁ hdiff
  have hleft_zero : e₁ * (1 - e₂) = 0 :=
    isIdempotentElem_eq_zero_of_mem_jacobson (he₁.mul he₂.one_sub) hleft_mem
  have hdiff' : e₂ - e₁ ∈ J := by
    simpa only [neg_sub] using J.neg_mem hdiff
  have hright_mem : (1 - e₁) * e₂ ∈ J := by
    have hrewrite : (1 - e₁) * e₂ = (1 - e₁) * (e₂ - e₁) := by
      rw [mul_sub, he₁.one_sub_mul_self, sub_zero]
    rw [hrewrite]
    exact J.mul_mem_left (1 - e₁) hdiff'
  have hright_zero : (1 - e₁) * e₂ = 0 :=
    isIdempotentElem_eq_zero_of_mem_jacobson (he₁.one_sub.mul he₂) hright_mem
  linear_combination hleft_zero - hright_zero

/-- If `I` is contained in the Jacobson radical, idempotent lifts along
`R → R ⧸ I` are unique. -/
theorem isIdempotentElem_lift_unique_of_le_jacobson {I : Ideal R}
    (hIjac : I ≤ Ideal.jacobson (⊥ : Ideal R)) {e₁ e₂ : R}
    (he₁ : IsIdempotentElem e₁) (he₂ : IsIdempotentElem e₂)
    (hmod : Ideal.Quotient.mk I e₁ = Ideal.Quotient.mk I e₂) : e₁ = e₂ :=
  isIdempotentElem_eq_of_sub_mem_jacobson he₁ he₂ (hIjac (Ideal.Quotient.eq.mp hmod))

/-- In a henselian pair, idempotent lifts along `R → R ⧸ I` are unique. -/
theorem isIdempotentElem_lift_unique {I : Ideal R} (h : IsHenselianPair R I)
    {e₁ e₂ : R} (he₁ : IsIdempotentElem e₁) (he₂ : IsIdempotentElem e₂)
    (hmod : Ideal.Quotient.mk I e₁ = Ideal.Quotient.mk I e₂) : e₁ = e₂ :=
  isIdempotentElem_lift_unique_of_le_jacobson h.le_jacobson he₁ he₂ hmod

/-- **Idempotents lift uniquely along `R → R ⧸ I`** for a Henselian pair.
This packages the idempotent-lifting clause of Stacks Tag 09XI as an `∃!`
statement. -/
@[stacks 09XI "(2)"]
theorem existsUnique_isIdempotentElem_lift {I : Ideal R} (h : IsHenselianPair R I) {ε : R ⧸ I}
    (hε : IsIdempotentElem ε) : ∃! e : R, IsIdempotentElem e ∧ Ideal.Quotient.mk I e = ε :=
  existsUnique_of_exists_of_unique (h.exists_isIdempotentElem_lift hε)
    fun _ _ hy₁ hy₂ ↦ h.isIdempotentElem_lift_unique hy₁.1 hy₂.1 (hy₁.2.trans hy₂.2.symm)

/-- The quotient map on idempotent elements induced by `R → R ⧸ I`. -/
def idempotentQuotientMap {I : Ideal R} :
    {e : R // IsIdempotentElem e} → {ε : R ⧸ I // IsIdempotentElem ε} :=
  fun e => ⟨Ideal.Quotient.mk I e.1, e.2.map (Ideal.Quotient.mk I)⟩

/-- `simp`-normal form for `idempotentQuotientMap`: it reduces `e` componentwise via
`Ideal.Quotient.mk I`. -/
@[simp]
theorem idempotentQuotientMap_apply {I : Ideal R} (e : {e : R // IsIdempotentElem e}) :
    idempotentQuotientMap (R := R) (I := I) e =
      (⟨Ideal.Quotient.mk I e.1, e.2.map (Ideal.Quotient.mk I)⟩ :
        {ε : R ⧸ I // IsIdempotentElem ε}) :=
  rfl

/-- For a Henselian pair `(R, I)`, the quotient map induces a bijection on
idempotent elements. This is the subtype form of the idempotent clause in
Stacks Tag 09XI/Raynaud XI, §1. -/
@[stacks 09XI "(2)"]
theorem idempotentQuotientMap_bijective {I : Ideal R} (h : IsHenselianPair R I) :
    Function.Bijective (idempotentQuotientMap (R := R) (I := I)) := by
  constructor
  · intro e₁ e₂ hmap
    exact Subtype.ext (h.isIdempotentElem_lift_unique e₁.2 e₂.2 (congrArg Subtype.val hmap))
  · intro ε
    obtain ⟨e, he, heq⟩ := h.exists_isIdempotentElem_lift ε.2
    exact ⟨⟨e, he⟩, Subtype.ext heq⟩

/-- For a Henselian pair `(R, I)`, reduction modulo `I` gives an equivalence on
idempotent elements. -/
noncomputable def idempotentQuotientEquiv {I : Ideal R} (h : IsHenselianPair R I) :
    {e : R // IsIdempotentElem e} ≃ {ε : R ⧸ I // IsIdempotentElem ε} :=
  Equiv.ofBijective (idempotentQuotientMap (R := R) (I := I))
    h.idempotentQuotientMap_bijective

@[simp]
theorem idempotentQuotientEquiv_apply {I : Ideal R} (h : IsHenselianPair R I)
    (e : {e : R // IsIdempotentElem e}) :
    h.idempotentQuotientEquiv e = idempotentQuotientMap (R := R) (I := I) e :=
  Equiv.ofBijective_apply _ _ e

/-- Orthogonal systems of idempotents lift along `R → R ⧸ I` for a Henselian
pair. Orthogonality is recovered from uniqueness: the product of two distinct
coordinate lifts is an idempotent reducing to zero. -/
theorem exists_orthogonalIdempotents_lift {I : Ideal R} (h : IsHenselianPair R I) {ι : Type*}
    {ε : ι → R ⧸ I} (hε : OrthogonalIdempotents ε) :
    ∃ e : ι → R, OrthogonalIdempotents e ∧ Ideal.Quotient.mk I ∘ e = ε := by
  classical
  choose e he hmap using fun i => h.exists_isIdempotentElem_lift (hε.idem i)
  refine ⟨e, ⟨he, fun i j hij => ?_⟩, funext hmap⟩
  refine h.isIdempotentElem_lift_unique ((he i).mul (he j)) IsIdempotentElem.zero ?_
  simp [map_mul, hmap i, hmap j, hε.ortho hij]

/-- Orthogonal systems of idempotents lift uniquely along `R → R ⧸ I` for a
Henselian pair. -/
theorem orthogonalIdempotents_lift_unique {I : Ideal R} (h : IsHenselianPair R I) {ι : Type*}
    {e₁ e₂ : ι → R} (he₁ : OrthogonalIdempotents e₁) (he₂ : OrthogonalIdempotents e₂)
    (hmod : Ideal.Quotient.mk I ∘ e₁ = Ideal.Quotient.mk I ∘ e₂) : e₁ = e₂ := by
  funext i
  exact h.isIdempotentElem_lift_unique (he₁.idem i) (he₂.idem i) (congrFun hmod i)

/-- Orthogonal systems of idempotents have unique lifts along `R → R ⧸ I` for a
Henselian pair, packaged as an `∃!`. -/
theorem existsUnique_orthogonalIdempotents_lift {I : Ideal R} (h : IsHenselianPair R I) {ι : Type*}
    {ε : ι → R ⧸ I} (hε : OrthogonalIdempotents ε) :
    ∃! e : ι → R, OrthogonalIdempotents e ∧ Ideal.Quotient.mk I ∘ e = ε := by
  obtain ⟨e, he, hmap⟩ := h.exists_orthogonalIdempotents_lift hε
  refine ⟨e, ⟨he, hmap⟩, fun y hy => ?_⟩
  exact h.orthogonalIdempotents_lift_unique hy.1 he (hy.2.trans hmap.symm)

/-- The quotient map on orthogonal systems of idempotents induced by `R → R ⧸ I`. -/
def orthogonalIdempotentsQuotientMap {I : Ideal R} {ι : Type*} :
    {e : ι → R // OrthogonalIdempotents e} →
      {ε : ι → R ⧸ I // OrthogonalIdempotents ε} :=
  fun e => ⟨Ideal.Quotient.mk I ∘ e.1, e.2.map (Ideal.Quotient.mk I)⟩

@[simp]
theorem orthogonalIdempotentsQuotientMap_apply {I : Ideal R} {ι : Type*}
    (e : {e : ι → R // OrthogonalIdempotents e}) :
    orthogonalIdempotentsQuotientMap (R := R) (I := I) e =
      (⟨Ideal.Quotient.mk I ∘ e.1, e.2.map (Ideal.Quotient.mk I)⟩ :
        {ε : ι → R ⧸ I // OrthogonalIdempotents ε}) :=
  rfl

/-- The quotient map of a Henselian pair induces a bijection on orthogonal
systems of idempotents. -/
theorem orthogonalIdempotentsQuotientMap_bijective {I : Ideal R} (h : IsHenselianPair R I)
    {ι : Type*} :
    Function.Bijective (orthogonalIdempotentsQuotientMap (R := R) (I := I) (ι := ι)) := by
  constructor
  · intro e₁ e₂ hmap
    exact Subtype.ext (h.orthogonalIdempotents_lift_unique e₁.2 e₂.2 (congrArg Subtype.val hmap))
  · intro ε
    obtain ⟨e, he, hmap⟩ := h.exists_orthogonalIdempotents_lift ε.2
    exact ⟨⟨e, he⟩, Subtype.ext hmap⟩

/-- For a Henselian pair `(R, I)`, reduction modulo `I` gives an equivalence on
orthogonal systems of idempotents. -/
noncomputable def orthogonalIdempotentsQuotientEquiv {I : Ideal R} (h : IsHenselianPair R I)
    {ι : Type*} :
    {e : ι → R // OrthogonalIdempotents e} ≃ {ε : ι → R ⧸ I // OrthogonalIdempotents ε} :=
  Equiv.ofBijective (orthogonalIdempotentsQuotientMap (R := R) (I := I) (ι := ι))
    h.orthogonalIdempotentsQuotientMap_bijective

@[simp]
theorem orthogonalIdempotentsQuotientEquiv_apply {I : Ideal R} (h : IsHenselianPair R I) {ι : Type*}
    (e : {e : ι → R // OrthogonalIdempotents e}) :
    h.orthogonalIdempotentsQuotientEquiv e = orthogonalIdempotentsQuotientMap (R := R) (I := I) e :=
  Equiv.ofBijective_apply _ _ e

/-- Complete orthogonal systems of idempotents lift along `R → R ⧸ I` for a
Henselian pair. Completeness is recovered from uniqueness by comparing the sum
of the lifted orthogonal system with `1`. -/
theorem exists_completeOrthogonalIdempotents_lift {I : Ideal R} (h : IsHenselianPair R I)
    {ι : Type*} [Fintype ι] {ε : ι → R ⧸ I} (hε : CompleteOrthogonalIdempotents ε) :
    ∃ e : ι → R, CompleteOrthogonalIdempotents e ∧ Ideal.Quotient.mk I ∘ e = ε := by
  obtain ⟨e, he, hmap⟩ := h.exists_orthogonalIdempotents_lift hε.toOrthogonalIdempotents
  have hmap_apply : ∀ i, Ideal.Quotient.mk I (e i) = ε i := fun i => congrFun hmap i
  have hsum_mod : Ideal.Quotient.mk I (∑ i, e i) = Ideal.Quotient.mk I (1 : R) := by
    simp [map_sum, hmap_apply, hε.complete]
  have hcomplete : ∑ i, e i = 1 :=
    h.isIdempotentElem_lift_unique
      (he.isIdempotentElem_sum (s := Finset.univ)) IsIdempotentElem.one hsum_mod
  exact ⟨e, ⟨he, hcomplete⟩, hmap⟩

/-- Complete orthogonal systems of idempotents lift uniquely along `R → R ⧸ I`
for a Henselian pair. -/
theorem completeOrthogonalIdempotents_lift_unique {I : Ideal R} (h : IsHenselianPair R I)
    {ι : Type*} [Fintype ι] {e₁ e₂ : ι → R}
    (he₁ : CompleteOrthogonalIdempotents e₁) (he₂ : CompleteOrthogonalIdempotents e₂)
    (hmod : Ideal.Quotient.mk I ∘ e₁ = Ideal.Quotient.mk I ∘ e₂) : e₁ = e₂ :=
  h.orthogonalIdempotents_lift_unique he₁.toOrthogonalIdempotents
    he₂.toOrthogonalIdempotents hmod

/-- Complete orthogonal systems of idempotents have unique lifts along
`R → R ⧸ I` for a Henselian pair, packaged as an `∃!`. -/
theorem existsUnique_completeOrthogonalIdempotents_lift {I : Ideal R}
    (h : IsHenselianPair R I) {ι : Type*} [Fintype ι] {ε : ι → R ⧸ I}
    (hε : CompleteOrthogonalIdempotents ε) :
    ∃! e : ι → R, CompleteOrthogonalIdempotents e ∧ Ideal.Quotient.mk I ∘ e = ε := by
  obtain ⟨e, he, hmap⟩ := h.exists_completeOrthogonalIdempotents_lift hε
  exact ⟨e, ⟨he, hmap⟩, fun y hy =>
    h.completeOrthogonalIdempotents_lift_unique hy.1 he (hy.2.trans hmap.symm)⟩

/-- The quotient map on finite complete orthogonal systems of idempotents induced by
`R → R ⧸ I`. -/
def completeOrthogonalIdempotentsQuotientMap {I : Ideal R} {ι : Type*} [Fintype ι] :
    {e : ι → R // CompleteOrthogonalIdempotents e} →
      {ε : ι → R ⧸ I // CompleteOrthogonalIdempotents ε} :=
  fun e => ⟨Ideal.Quotient.mk I ∘ e.1, e.2.map (Ideal.Quotient.mk I)⟩

@[simp]
theorem completeOrthogonalIdempotentsQuotientMap_apply {I : Ideal R} {ι : Type*} [Fintype ι]
    (e : {e : ι → R // CompleteOrthogonalIdempotents e}) :
    completeOrthogonalIdempotentsQuotientMap (R := R) (I := I) e =
      (⟨Ideal.Quotient.mk I ∘ e.1, e.2.map (Ideal.Quotient.mk I)⟩ :
        {ε : ι → R ⧸ I // CompleteOrthogonalIdempotents ε}) :=
  rfl

/-- The quotient map of a Henselian pair induces a bijection on finite complete
orthogonal systems of idempotents. -/
theorem completeOrthogonalIdempotentsQuotientMap_bijective {I : Ideal R} (h : IsHenselianPair R I)
    {ι : Type*} [Fintype ι] :
    Function.Bijective (completeOrthogonalIdempotentsQuotientMap (R := R) (I := I) (ι := ι)) := by
  constructor
  · intro e₁ e₂ hmap
    apply Subtype.ext
    exact h.completeOrthogonalIdempotents_lift_unique e₁.2 e₂.2 (congrArg Subtype.val hmap)
  · intro ε
    obtain ⟨e, he, hmap⟩ := h.exists_completeOrthogonalIdempotents_lift ε.2
    exact ⟨⟨e, he⟩, Subtype.ext hmap⟩

/-- For a Henselian pair `(R, I)`, reduction modulo `I` gives an equivalence on
finite complete orthogonal systems of idempotents. -/
noncomputable def completeOrthogonalIdempotentsQuotientEquiv {I : Ideal R} (h : IsHenselianPair R I)
    {ι : Type*} [Fintype ι] :
    {e : ι → R // CompleteOrthogonalIdempotents e} ≃
      {ε : ι → R ⧸ I // CompleteOrthogonalIdempotents ε} :=
  Equiv.ofBijective (completeOrthogonalIdempotentsQuotientMap (R := R) (I := I) (ι := ι))
    h.completeOrthogonalIdempotentsQuotientMap_bijective

@[simp]
theorem completeOrthogonalIdempotentsQuotientEquiv_apply {I : Ideal R}
    (h : IsHenselianPair R I) {ι : Type*} [Fintype ι]
    (e : {e : ι → R // CompleteOrthogonalIdempotents e}) :
    h.completeOrthogonalIdempotentsQuotientEquiv e =
      completeOrthogonalIdempotentsQuotientMap (R := R) (I := I) e :=
  Equiv.ofBijective_apply _ _ e

/-- Integral extensions carry ideals contained in the Jacobson radical into the
Jacobson radical after extension of scalars. -/
theorem map_le_jacobson_of_isIntegral {S : Type*} [CommRing S] [Algebra R S]
    [Algebra.IsIntegral R S] {I : Ideal R} (hIjac : I ≤ Ideal.jacobson (⊥ : Ideal R)) :
    I.map (algebraMap R S) ≤ Ideal.jacobson (⊥ : Ideal S) := by
  intro x hx
  rw [Ideal.jacobson, Ideal.mem_sInf]
  intro M hM
  have : M.IsMaximal := hM.2
  have hcomap_max : (M.comap (algebraMap R S)).IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := R) (S := S) M
  have hI_le_comap : I ≤ M.comap (algebraMap R S) := by
    intro r hr
    have hrjac : r ∈ Ideal.jacobson (⊥ : Ideal R) := hIjac hr
    rw [Ideal.jacobson, Ideal.mem_sInf] at hrjac
    exact hrjac (I := M.comap (algebraMap R S)) ⟨bot_le, hcomap_max⟩
  exact (Ideal.map_le_iff_le_comap.mpr hI_le_comap) hx

/-- The quotient map on idempotents in an `R`-algebra `S`, induced by
`S → S ⧸ I·S`. -/
def idempotentQuotientMapOfAlgebra {S : Type*} [CommRing S] [Algebra R S] {I : Ideal R} :
    {e : S // IsIdempotentElem e} →
      {ε : S ⧸ I.map (algebraMap R S) // IsIdempotentElem ε} :=
  fun e => ⟨Ideal.Quotient.mk (I.map (algebraMap R S)) e.1,
    e.2.map (Ideal.Quotient.mk (I.map (algebraMap R S)))⟩

/-- `simp`-normal form for `idempotentQuotientMapOfAlgebra`: it reduces `e` via
`Ideal.Quotient.mk (I.map (algebraMap R S))`. -/
@[simp]
theorem idempotentQuotientMapOfAlgebra_apply {S : Type*} [CommRing S] [Algebra R S] {I : Ideal R}
    (e : {e : S // IsIdempotentElem e}) :
    idempotentQuotientMapOfAlgebra (R := R) (S := S) (I := I) e =
      (⟨Ideal.Quotient.mk (I.map (algebraMap R S)) e.1,
        e.2.map (Ideal.Quotient.mk (I.map (algebraMap R S)))⟩ :
        {ε : S ⧸ I.map (algebraMap R S) // IsIdempotentElem ε}) :=
  rfl

/-- The quotient map on orthogonal systems of idempotents in an `R`-algebra `S`,
induced by `S → S ⧸ I·S`. -/
def orthogonalIdempotentsQuotientMapOfAlgebra {S : Type*} [CommRing S] [Algebra R S]
    {I : Ideal R} {ι : Type*} :
    {e : ι → S // OrthogonalIdempotents e} →
      {ε : ι → S ⧸ I.map (algebraMap R S) // OrthogonalIdempotents ε} :=
  fun e => ⟨Ideal.Quotient.mk (I.map (algebraMap R S)) ∘ e.1,
    e.2.map (Ideal.Quotient.mk (I.map (algebraMap R S)))⟩

/-- `simp`-normal form for `orthogonalIdempotentsQuotientMapOfAlgebra`: it reduces `e`
componentwise via `Ideal.Quotient.mk (I.map (algebraMap R S))`. -/
@[simp]
theorem orthogonalIdempotentsQuotientMapOfAlgebra_apply {S : Type*} [CommRing S] [Algebra R S]
    {I : Ideal R} {ι : Type*} (e : {e : ι → S // OrthogonalIdempotents e}) :
    orthogonalIdempotentsQuotientMapOfAlgebra (R := R) (S := S) (I := I) e =
      (⟨Ideal.Quotient.mk (I.map (algebraMap R S)) ∘ e.1,
        e.2.map (Ideal.Quotient.mk (I.map (algebraMap R S)))⟩ :
        {ε : ι → S ⧸ I.map (algebraMap R S) // OrthogonalIdempotents ε}) :=
  rfl

/-- The quotient map on finite complete orthogonal systems of idempotents in an
`R`-algebra `S`, induced by `S → S ⧸ I·S`. -/
def completeOrthogonalIdempotentsQuotientMapOfAlgebra {S : Type*} [CommRing S] [Algebra R S]
    {I : Ideal R} {ι : Type*} [Fintype ι] :
    {e : ι → S // CompleteOrthogonalIdempotents e} →
      {ε : ι → S ⧸ I.map (algebraMap R S) // CompleteOrthogonalIdempotents ε} :=
  fun e => ⟨Ideal.Quotient.mk (I.map (algebraMap R S)) ∘ e.1,
    e.2.map (Ideal.Quotient.mk (I.map (algebraMap R S)))⟩

@[simp]
theorem completeOrthogonalIdempotentsQuotientMapOfAlgebra_apply {S : Type*} [CommRing S]
    [Algebra R S] {I : Ideal R} {ι : Type*} [Fintype ι]
    (e : {e : ι → S // CompleteOrthogonalIdempotents e}) :
    completeOrthogonalIdempotentsQuotientMapOfAlgebra (R := R) (S := S) (I := I) e =
      (⟨Ideal.Quotient.mk (I.map (algebraMap R S)) ∘ e.1,
        e.2.map (Ideal.Quotient.mk (I.map (algebraMap R S)))⟩ :
        {ε : ι → S ⧸ I.map (algebraMap R S) // CompleteOrthogonalIdempotents ε}) :=
  rfl

universe u

/-- The finite-algebra injectivity condition on idempotents forces the base ideal
to lie in the Jacobson radical. This is the Jacobson-radical part of the
finite-idempotent converse in Stacks Tag 09XI. -/
theorem le_jacobson_of_idempotentQuotientMap_injective_of_finite {R : Type u} [CommRing R]
    {I : Ideal R} (hfinite : ∀ (S : Type u) [CommRing S] [Algebra R S] [Module.Finite R S],
      Function.Injective (idempotentQuotientMapOfAlgebra (R := R) (S := S) (I := I))) :
    I ≤ Ideal.jacobson (⊥ : Ideal R) := by
  intro x hxI
  -- test `x ∈ Jac(⊥)` against each maximal ideal `M`.
  rw [Ideal.jacobson, Ideal.mem_sInf]
  intro M hM
  have hMmax : M.IsMaximal := hM.2
  -- suppose `x ∉ M`; as `x ∈ I` and `M` is maximal, `I` and `M` are comaximal.
  by_contra hxM
  obtain ⟨y, m, hm, hym⟩ := hMmax.exists_inv hxM
  have hIMtop : I ⊔ M = ⊤ := by
    rw [Ideal.eq_top_iff_one, ← hym]
    exact Submodule.mem_sup.mpr ⟨y * x, I.mul_mem_left y hxI, m, hm, rfl⟩
  -- CRT: `S := R ⧸ (I ⊓ M)` is isomorphic to `(R ⧸ I) × (R ⧸ M)`.
  let J : Ideal R := I ⊓ M
  let S : Type u := R ⧸ J
  have hcop : IsCoprime I M := Ideal.isCoprime_iff_sup_eq.mpr hIMtop
  let e : S ≃+* (R ⧸ I) × R ⧸ M :=
    Ideal.quotientInfEquivQuotientProd I M hcop
  have : Nontrivial (R ⧸ M) := Ideal.Quotient.nontrivial_iff.mpr hMmax.ne_top
  -- the CRT-preimages of `(1, 0)` and `(1, 1)`: two idempotents of `S`, distinct as `0 ≠ 1`.
  let a : S := e.symm (1, 0)
  let b : S := e.symm (1, 1)
  have ha : IsIdempotentElem a := by
    change a * a = a
    apply e.injective
    simp [a]
  have hb : IsIdempotentElem b := by
    change b * b = b
    apply e.injective
    simp [b]
  have hne : a ≠ b := by
    intro hab
    have hprod : ((1 : R ⧸ I), (0 : R ⧸ M)) = ((1 : R ⧸ I), (1 : R ⧸ M)) := by
      simpa [a, b] using congrArg e hab
    have hzero_one : (0 : R ⧸ M) = 1 := congrArg Prod.snd hprod
    exact zero_ne_one hzero_one
  let q : S →+* S ⧸ I.map (algebraMap R S) :=
    Ideal.Quotient.mk (I.map (algebraMap R S))
  have hJI : J ≤ I := inf_le_left
  let d : (S ⧸ I.map (algebraMap R S)) ≃+* R ⧸ I :=
    DoubleQuot.quotQuotEquivQuotOfLE hJI
  have hd_eq_fst (z : S) : d (q z) = (e z).fst := by
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective z
    change d (DoubleQuot.quotQuotMk J I r) =
      (Ideal.quotientInfEquivQuotientProd I M hcop (Ideal.Quotient.mk (I ⊓ M) r)).fst
    rw [Ideal.quotientInfEquivQuotientProd_fst]
    change d (DoubleQuot.quotQuotMk J I r) = Ideal.Quotient.mk I r
    exact DoubleQuot.quotQuotEquivQuotOfLE_quotQuotMk r hJI
  -- yet `a` and `b` have the same reduction modulo `I·S`.
  have hq : q a = q b := by
    apply d.injective
    rw [hd_eq_fst a, hd_eq_fst b]
    simp [a, b]
  -- `S` is module-finite over `R`, so injectivity of the idempotent map forces `a = b`.
  have : Module.Finite R S :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ R J).toLinearMap
      Ideal.Quotient.mk_surjective
  have hsub :
      idempotentQuotientMapOfAlgebra (R := R) (S := S) (I := I) ⟨a, ha⟩ =
        idempotentQuotientMapOfAlgebra (R := R) (S := S) (I := I) ⟨b, hb⟩ :=
    Subtype.ext hq
  exact hne (congrArg Subtype.val (hfinite S hsub))

/-- The finite-algebra bijectivity condition on idempotents forces the base
ideal to lie in the Jacobson radical. This is the formulation closest to the
finite-idempotent condition in Stacks Tag 09XI. -/
theorem le_jacobson_of_idempotentQuotientMap_bijective_of_finite {R : Type u} [CommRing R]
    {I : Ideal R} (hfinite : ∀ (S : Type u) [CommRing S] [Algebra R S] [Module.Finite R S],
      Function.Bijective (idempotentQuotientMapOfAlgebra (R := R) (S := S) (I := I))) :
    I ≤ Ideal.jacobson (⊥ : Ideal R) :=
  le_jacobson_of_idempotentQuotientMap_injective_of_finite fun S _ _ _ ↦ (hfinite S).1

/-- The integral-algebra injectivity condition on idempotents forces the base
ideal to lie in the Jacobson radical. This is the integral-algebra variant of
`le_jacobson_of_idempotentQuotientMap_injective_of_finite`; it reduces to the
finite case because finite algebras are integral. -/
theorem le_jacobson_of_idempotentQuotientMap_injective_of_isIntegral {R : Type u} [CommRing R]
    {I : Ideal R} (hintegral : ∀ (S : Type u) [CommRing S] [Algebra R S] [Algebra.IsIntegral R S],
      Function.Injective (idempotentQuotientMapOfAlgebra (R := R) (S := S) (I := I))) :
    I ≤ Ideal.jacobson (⊥ : Ideal R) :=
  le_jacobson_of_idempotentQuotientMap_injective_of_finite fun S _ _ _ ↦ hintegral S

/-- The integral-algebra bijectivity condition on idempotents forces the base
ideal to lie in the Jacobson radical. This is the formulation matching the
integral-idempotent condition in Stacks Tag 09XI. -/
theorem le_jacobson_of_idempotentQuotientMap_bijective_of_isIntegral {R : Type u} [CommRing R]
    {I : Ideal R} (hintegral : ∀ (S : Type u) [CommRing S] [Algebra R S] [Algebra.IsIntegral R S],
      Function.Bijective (idempotentQuotientMapOfAlgebra (R := R) (S := S) (I := I))) :
    I ≤ Ideal.jacobson (⊥ : Ideal R) :=
  le_jacobson_of_idempotentQuotientMap_injective_of_isIntegral fun S _ _ _ ↦ (hintegral S).1

/-- In an integral `R`-algebra `S`, idempotent lifts modulo `I·S` are unique
whenever `I ≤ Jac(R)`. -/
theorem isIdempotentElem_lift_unique_map_of_isIntegral {S : Type*} [CommRing S] [Algebra R S]
    [Algebra.IsIntegral R S] {I : Ideal R} (hIjac : I ≤ Ideal.jacobson (⊥ : Ideal R)) {e₁ e₂ : S}
    (he₁ : IsIdempotentElem e₁) (he₂ : IsIdempotentElem e₂)
    (hmod : Ideal.Quotient.mk (I.map (algebraMap R S)) e₁ =
      Ideal.Quotient.mk (I.map (algebraMap R S)) e₂) : e₁ = e₂ :=
  isIdempotentElem_lift_unique_of_le_jacobson (map_le_jacobson_of_isIntegral hIjac) he₁ he₂ hmod

/-- If `I ≤ Jac(R)` and `S` is integral over `R`, the quotient map
`S → S/IS` is injective on idempotents. -/
theorem idempotentQuotientMap_injective_of_isIntegral_of_le_jacobson {S : Type*}
    [CommRing S] [Algebra R S] [Algebra.IsIntegral R S] {I : Ideal R}
    (hIjac : I ≤ Ideal.jacobson (⊥ : Ideal R)) :
    Function.Injective (idempotentQuotientMapOfAlgebra (R := R) (S := S) (I := I)) := by
  intro e₁ e₂ hmap
  exact Subtype.ext (isIdempotentElem_lift_unique_map_of_isIntegral hIjac e₁.2 e₂.2
    (congrArg Subtype.val hmap))

/-- If `I ≤ Jac(R)` and `S` is integral over `R`, the quotient map
`S → S/IS` is injective on orthogonal systems of idempotents. -/
theorem orthogonalIdempotentsQuotientMap_injective_of_isIntegral_of_le_jacobson
    {S : Type*} [CommRing S] [Algebra R S] [Algebra.IsIntegral R S] {I : Ideal R}
    (hIjac : I ≤ Ideal.jacobson (⊥ : Ideal R)) {ι : Type*} :
    Function.Injective
      (orthogonalIdempotentsQuotientMapOfAlgebra (R := R) (S := S) (I := I) (ι := ι)) := by
  intro e₁ e₂ hmap
  apply Subtype.ext
  funext i
  exact isIdempotentElem_lift_unique_map_of_isIntegral hIjac (e₁.2.idem i) (e₂.2.idem i)
    (congrFun (congrArg Subtype.val hmap) i)

/-- If `I ≤ Jac(R)` and `S` is integral over `R`, the quotient map
`S → S/IS` is injective on finite complete orthogonal systems of idempotents. -/
theorem completeOrthogonalIdempotentsQuotientMap_injective_of_isIntegral_of_le_jacobson
    {S : Type*} [CommRing S] [Algebra R S] [Algebra.IsIntegral R S] {I : Ideal R}
    (hIjac : I ≤ Ideal.jacobson (⊥ : Ideal R)) {ι : Type*} [Fintype ι] :
    Function.Injective
      (completeOrthogonalIdempotentsQuotientMapOfAlgebra (R := R) (S := S) (I := I) (ι := ι)) := by
  intro e₁ e₂ hmap
  apply Subtype.ext
  funext i
  exact isIdempotentElem_lift_unique_map_of_isIntegral hIjac (e₁.2.idem i) (e₂.2.idem i)
    (congrFun (congrArg Subtype.val hmap) i)

/-- In an integral algebra over a Henselian pair `(R, I)`, idempotent lifts
modulo `I·S` are unique. Existence for finite étale algebras is the remaining
hard 09XI/Raynaud section-lifting input; this theorem supplies the uniqueness
half for all integral algebras. -/
theorem isIdempotentElem_lift_unique_map_of_pair {S : Type*} [CommRing S] [Algebra R S]
    [Algebra.IsIntegral R S] {I : Ideal R} (h : IsHenselianPair R I)
    {e₁ e₂ : S} (he₁ : IsIdempotentElem e₁) (he₂ : IsIdempotentElem e₂)
    (hmod : Ideal.Quotient.mk (I.map (algebraMap R S)) e₁ =
      Ideal.Quotient.mk (I.map (algebraMap R S)) e₂) : e₁ = e₂ :=
  isIdempotentElem_lift_unique_map_of_isIntegral h.le_jacobson he₁ he₂ hmod

/-- Finite algebras are integral, so idempotent lifts modulo `I·S` are unique
over a Henselian pair. -/
theorem isIdempotentElem_lift_unique_map_of_finite {S : Type*} [CommRing S] [Algebra R S]
    [Module.Finite R S] {I : Ideal R} (h : IsHenselianPair R I)
    {e₁ e₂ : S} (he₁ : IsIdempotentElem e₁) (he₂ : IsIdempotentElem e₂)
    (hmod : Ideal.Quotient.mk (I.map (algebraMap R S)) e₁ =
      Ideal.Quotient.mk (I.map (algebraMap R S)) e₂) : e₁ = e₂ :=
  isIdempotentElem_lift_unique_map_of_pair h he₁ he₂ hmod

/-- For an integral algebra over a Henselian pair, the quotient map on
idempotents is injective. This is the uniqueness half of the idempotent lifting
criterion in Raynaud XI, §1 / Stacks Tag 09XI, and is the part that only uses
the Jacobson-radical condition. -/
theorem idempotentQuotientMap_injective_of_isIntegral {S : Type*} [CommRing S] [Algebra R S]
    [Algebra.IsIntegral R S] {I : Ideal R} (h : IsHenselianPair R I) :
    Function.Injective (idempotentQuotientMapOfAlgebra (R := R) (S := S) (I := I)) :=
  idempotentQuotientMap_injective_of_isIntegral_of_le_jacobson h.le_jacobson

/-- For an integral algebra over a Henselian pair, the quotient map is injective
on orthogonal systems of idempotents. -/
theorem orthogonalIdempotentsQuotientMap_injective_of_isIntegral {S : Type*}
    [CommRing S] [Algebra R S] [Algebra.IsIntegral R S] {I : Ideal R}
    (h : IsHenselianPair R I) {ι : Type*} :
    Function.Injective
      (orthogonalIdempotentsQuotientMapOfAlgebra (R := R) (S := S) (I := I) (ι := ι)) :=
  orthogonalIdempotentsQuotientMap_injective_of_isIntegral_of_le_jacobson h.le_jacobson

/-- For an integral algebra over a Henselian pair, the quotient map is injective
on finite complete orthogonal systems of idempotents. -/
theorem completeOrthogonalIdempotentsQuotientMap_injective_of_isIntegral {S : Type*}
    [CommRing S] [Algebra R S] [Algebra.IsIntegral R S] {I : Ideal R}
    (h : IsHenselianPair R I) {ι : Type*} [Fintype ι] :
    Function.Injective
      (completeOrthogonalIdempotentsQuotientMapOfAlgebra (R := R) (S := S) (I := I) (ι := ι)) :=
  completeOrthogonalIdempotentsQuotientMap_injective_of_isIntegral_of_le_jacobson h.le_jacobson

/-- For a finite algebra over a Henselian pair, the quotient map on idempotents
is injective. This is the finite-algebra specialization of the integral
uniqueness half of Raynaud XI, §1 / Stacks Tag 09XI. -/
theorem idempotentQuotientMap_injective_of_finite {S : Type*} [CommRing S] [Algebra R S]
    [Module.Finite R S] {I : Ideal R} (h : IsHenselianPair R I) :
    Function.Injective (idempotentQuotientMapOfAlgebra (R := R) (S := S) (I := I)) :=
  idempotentQuotientMap_injective_of_isIntegral h

/-- For a finite algebra over a Henselian pair, the quotient map is injective on
orthogonal systems of idempotents. -/
theorem orthogonalIdempotentsQuotientMap_injective_of_finite {S : Type*} [CommRing S] [Algebra R S]
    [Module.Finite R S] {I : Ideal R} (h : IsHenselianPair R I) {ι : Type*} :
    Function.Injective
      (orthogonalIdempotentsQuotientMapOfAlgebra (R := R) (S := S) (I := I) (ι := ι)) :=
  orthogonalIdempotentsQuotientMap_injective_of_isIntegral h

/-- For a finite algebra over a Henselian pair, the quotient map is injective on
finite complete orthogonal systems of idempotents. -/
theorem completeOrthogonalIdempotentsQuotientMap_injective_of_finite {S : Type*}
    [CommRing S] [Algebra R S] [Module.Finite R S] {I : Ideal R}
    (h : IsHenselianPair R I) {ι : Type*} [Fintype ι] :
    Function.Injective
      (completeOrthogonalIdempotentsQuotientMapOfAlgebra
        (R := R) (S := S) (I := I) (ι := ι)) :=
  completeOrthogonalIdempotentsQuotientMap_injective_of_isIntegral h

end IsHenselianPair
