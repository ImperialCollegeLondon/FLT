/-
Copyright (c) 2026 Duxing Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Duxing Yang
-/
module

public import Mathlib.LinearAlgebra.Matrix.Action
public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.GroupTheory.Sylow
public import Mathlib.LinearAlgebra.Matrix.CharP
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup
public import Mathlib.LinearAlgebra.Projectivization.Action

/-!
# Basic theory of `PGL₂` over the algebraic closure of `𝔽_p`

This file sets up the basic objects used in the proof of Dickson's classification
of the finite subgroups of `PGL₂(𝔽̄_p)` for `p` an odd prime.

We define `K p` to be an algebraic closure of `𝔽_p`, the group `PGL p := PGL₂(K p)`
(as the quotient of `GL₂(K p)` by its centre), the group `PSL p := PSL₂(K p)`, and the
projective line `ProjectiveLine p := ℙ¹(K p)` together with its natural `PGL p`-action.

The main results are:
* `Dickson.pgl_mulEquiv_psl`: over the algebraically closed field `K p`, the natural
  map `PSL₂(K p) → PGL₂(K p)` is an isomorphism.
* `Dickson.exists_finite_subfield_conjugate`: every finite subgroup of `PGL p` can be
  conjugated into the image of `PGL₂(F)` for some finite subfield `F` of `K p`.
* `Dickson.card_eigenvalues` and `Dickson.fixedPoints_card`: a nontrivial element of
  `PGL p` fixes either one or two points of the projective line, according to whether
  its lift to `GL₂` has one or two eigenvalues.
-/

/- The code in this file was ported from Duxing Yang's `DicksonClassification` project
and does not yet follow the mathlib style conventions enforced by the linters below. -/
set_option linter.style.longLine false
set_option linter.style.emptyLine false
set_option linter.style.whitespace false
set_option linter.style.show false
set_option linter.style.openClassical false
set_option linter.style.cdot false
set_option linter.style.multiGoal false
set_option linter.style.refine false
set_option linter.style.induction false
set_option linter.unusedFintypeInType false

@[expose] public section

open scoped Classical

namespace Dickson

scoped instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
scoped instance : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
scoped instance : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

noncomputable section lemmata

/-- The `Sylow p`-subgroups of a finite group form a `Fintype`. -/
scoped instance instFintypeSylow {p : ℕ} {G : Type*} [Group G] [Finite G] :
    Fintype (Sylow p G) := Fintype.ofFinite _
/-- A finite Galois field `GF(pᵐ)` is a `Fintype`. -/
scoped instance instFintypeGaloisField {p m : ℕ} [Fact p.Prime] :
    Fintype (GaloisField p m) := Fintype.ofFinite _

lemma Nat.factorization_eq_one {n m p : ℕ}
    (h_eq : n = m * p)
    (hp : p.Prime)
    (h_ndvd : ¬ p ∣ m) :
    n.factorization p = 1 := by
  rw [h_eq, Nat.factorization_mul (by rintro rfl; exact h_ndvd (dvd_zero p)) hp.ne_zero,
      Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd h_ndvd,
      hp.factorization, Finsupp.single_eq_same, zero_add]

lemma Nat.factorization_eq_two {n m p : ℕ}
    (h_eq : n = m * p * p)
    (hp : p.Prime)
    (h_ndvd : ¬ p ∣ m) :
    n.factorization p = 2 := by
  rw [h_eq,
      Nat.factorization_mul (mul_ne_zero
          (by rintro rfl; exact h_ndvd (dvd_zero p)) hp.ne_zero) hp.ne_zero,
      Finsupp.add_apply,
      hp.factorization, Finsupp.single_eq_same,
      Nat.factorization_mul (by rintro rfl; exact h_ndvd (dvd_zero p)) hp.ne_zero,
      Finsupp.add_apply,
      hp.factorization, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd h_ndvd]


variable (p : ℕ) [Fact (Nat.Prime p)]

/-- The algebraic closure `K p` of the finite field `𝔽_p = ZMod p`. -/
noncomputable abbrev K : Type := AlgebraicClosure (ZMod p)

/-- The projective general linear group `PGL₂(K p)`, i.e. `GL₂(K p)` modulo its centre. -/
abbrev PGL : Type := GL (Fin 2) (K p) ⧸ Subgroup.center (GL (Fin 2) (K p))

/-- The projective special linear group `PSL₂(K p)`. -/
abbrev PSL : Type := Matrix.ProjectiveSpecialLinearGroup (Fin 2) (K p)

theorem pgl_mulEquiv_psl : Nonempty (PGL p ≃* PSL p) := by
  have h_sqrt : ∀ x : K p, ∃ c : K p, c ^ 2 = x := fun x ↦
    let ⟨y, hy⟩ := IsAlgClosed.exists_root (Polynomial.X ^ 2 - Polynomial.C x) (fun h ↦ by rw [Polynomial.degree_X_pow_sub_C (by norm_num)] at h; norm_num at h)
    ⟨y, by rw [Polynomial.IsRoot.def, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C, sub_eq_zero] at hy; exact hy⟩

  let f : PSL p →* PGL p := QuotientGroup.lift (Subgroup.center _)
    (MonoidHom.comp (QuotientGroup.mk' _) Matrix.SpecialLinearGroup.toGL) (by
      intro x hx
      change QuotientGroup.mk (Matrix.SpecialLinearGroup.toGL x) = 1
      rw [QuotientGroup.eq_one_iff, Subgroup.mem_center_iff]
      intro g
      obtain ⟨c, hc⟩ := h_sqrt g.val.det
      have hc_ne : c ≠ 0 := fun h ↦ g.det_ne_zero (by rw [← hc, h, zero_pow (by norm_num)])
      let g' : Matrix.SpecialLinearGroup (Fin 2) (K p) :=
        ⟨c⁻¹ • g.val, by rw [Matrix.det_smul, Fintype.card_fin, ← hc, ← mul_pow, inv_mul_cancel₀ hc_ne, one_pow]⟩
      apply Units.ext
      change g.val * (Matrix.SpecialLinearGroup.toGL x).val = (Matrix.SpecialLinearGroup.toGL x).val * g.val
      rw [show g.val = c • g'.val by change g.val = c • (c⁻¹ • g.val); rw [smul_smul, mul_inv_cancel₀ hc_ne, one_smul]]
      rw [Matrix.smul_mul, Matrix.mul_smul]
      exact congr_arg (c • ·) (congr_arg Subtype.val (Subgroup.mem_center_iff.mp hx g')))

  have h_inj : Function.Injective f := fun x y ↦ by
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective y
    intro h
    change QuotientGroup.mk (Matrix.SpecialLinearGroup.toGL a) = QuotientGroup.mk (Matrix.SpecialLinearGroup.toGL b) at h
    rw [QuotientGroup.eq, Subgroup.mem_center_iff] at h ⊢
    exact fun g ↦ Subtype.ext <| congr_arg Units.val (h (Matrix.SpecialLinearGroup.toGL g))

  have h_surj : Function.Surjective f := fun x ↦ by
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨c, hc⟩ := h_sqrt y.val.det
    have hc_ne : c ≠ 0 := fun h ↦ y.det_ne_zero (by rw [← hc, h, zero_pow (by norm_num)])
    let z : Matrix.SpecialLinearGroup (Fin 2) (K p) :=
      ⟨c⁻¹ • y.val, by rw [Matrix.det_smul, Fintype.card_fin, ← hc, ← mul_pow, inv_mul_cancel₀ hc_ne, one_pow]⟩
    use QuotientGroup.mk z
    change QuotientGroup.mk (Matrix.SpecialLinearGroup.toGL z) = QuotientGroup.mk y
    rw [QuotientGroup.eq, Subgroup.mem_center_iff]
    intro g
    apply Units.ext
    change g.val * ((Matrix.SpecialLinearGroup.toGL z)⁻¹ * y).val = ((Matrix.SpecialLinearGroup.toGL z)⁻¹ * y).val * g.val
    have hy_eq : y.val = (Matrix.SpecialLinearGroup.toGL z).val * Matrix.diagonal ![c, c] := by
      ext i j
      rw [Matrix.mul_apply, Fin.sum_univ_two]
      match i, j with
      | 0, 0 => change y.val 0 0 = (c⁻¹ * y.val 0 0) * c + (c⁻¹ * y.val 0 1) * 0; rw [mul_zero, add_zero, mul_comm c⁻¹, mul_assoc, inv_mul_cancel₀ hc_ne, mul_one]
      | 0, 1 => change y.val 0 1 = (c⁻¹ * y.val 0 0) * 0 + (c⁻¹ * y.val 0 1) * c; rw [mul_zero, zero_add, mul_comm c⁻¹, mul_assoc, inv_mul_cancel₀ hc_ne, mul_one]
      | 1, 0 => change y.val 1 0 = (c⁻¹ * y.val 1 0) * c + (c⁻¹ * y.val 1 1) * 0; rw [mul_zero, add_zero, mul_comm c⁻¹, mul_assoc, inv_mul_cancel₀ hc_ne, mul_one]
      | 1, 1 => change y.val 1 1 = (c⁻¹ * y.val 1 0) * 0 + (c⁻¹ * y.val 1 1) * c; rw [mul_zero, zero_add, mul_comm c⁻¹, mul_assoc, inv_mul_cancel₀ hc_ne, mul_one]
    rw [show ((Matrix.SpecialLinearGroup.toGL z)⁻¹ * y).val = Matrix.diagonal ![c, c] by
      rw [Units.val_mul, hy_eq, ← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]]
    ext i j
    rw [Matrix.mul_apply, Fin.sum_univ_two, Matrix.mul_apply, Fin.sum_univ_two]
    match i, j with
    | 0, 0 =>
      change (g : Matrix (Fin 2) (Fin 2) (K p)) 0 0 * c + (g : Matrix (Fin 2) (Fin 2) (K p)) 0 1 * 0 = c * (g : Matrix (Fin 2) (Fin 2) (K p)) 0 0 + 0 * (g : Matrix (Fin 2) (Fin 2) (K p)) 1 0
      rw [mul_zero, add_zero, zero_mul, add_zero, mul_comm]
    | 0, 1 =>
      change (g : Matrix (Fin 2) (Fin 2) (K p)) 0 0 * 0 + (g : Matrix (Fin 2) (Fin 2) (K p)) 0 1 * c = c * (g : Matrix (Fin 2) (Fin 2) (K p)) 0 1 + 0 * (g : Matrix (Fin 2) (Fin 2) (K p)) 1 1
      rw [mul_zero, zero_add, zero_mul, add_zero, mul_comm]
    | 1, 0 =>
      change (g : Matrix (Fin 2) (Fin 2) (K p)) 1 0 * c + (g : Matrix (Fin 2) (Fin 2) (K p)) 1 1 * 0 = 0 * (g : Matrix (Fin 2) (Fin 2) (K p)) 0 0 + c * (g : Matrix (Fin 2) (Fin 2) (K p)) 1 0
      rw [mul_zero, add_zero, zero_mul, zero_add, mul_comm]
    | 1, 1 =>
      change (g : Matrix (Fin 2) (Fin 2) (K p)) 1 0 * 0 + (g : Matrix (Fin 2) (Fin 2) (K p)) 1 1 * c = 0 * (g : Matrix (Fin 2) (Fin 2) (K p)) 0 1 + c * (g : Matrix (Fin 2) (Fin 2) (K p)) 1 1
      rw [mul_zero, zero_add, zero_mul, zero_add, mul_comm]
  exact ⟨(MulEquiv.ofBijective f ⟨h_inj, h_surj⟩).symm⟩

/-- The projective line `ℙ¹(K p)` over `K p`. -/
abbrev ProjectiveLine : Type := Projectivization (K p) (Fin 2 → K p)

/-- The natural `GL₂(K p)`-action on the projective line `ℙ¹(K p)`. -/
@[reducible] def glActionProjectiveLine : MulAction (GL (Fin 2) (K p)) (ProjectiveLine p) :=
  Projectivization.instMulAction

instance : SMul (PGL p) (ProjectiveLine p) where
  smul := Quotient.lift (fun g x ↦ g • x) (by
    intro g₁ g₂ h
    funext x
    have hz : g₁⁻¹ * g₂ ∈ Subgroup.center (GL (Fin 2) (K p)) := QuotientGroup.leftRel_apply.mp h
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hz
    obtain ⟨u, hu⟩ := hz
    induction x using Projectivization.ind with
    | h v hv =>
      show g₁ • Projectivization.mk (K p) v hv = g₂ • Projectivization.mk (K p) v hv
      rw [show g₂ = g₁ * (g₁⁻¹ * g₂) by rw [← mul_assoc, mul_inv_cancel, one_mul], mul_smul]
      congr 1
      rw [Projectivization.smul_mk, eq_comm, Projectivization.mk_eq_mk_iff]
      refine ⟨u, ?_⟩
      change (↑u : K p) • v = Matrix.mulVec (g₁⁻¹ * g₂).val v
      rw [show (g₁⁻¹ * g₂).val = algebraMap (K p) (Matrix (Fin 2) (Fin 2) (K p)) (↑u : K p) from congr_arg Units.val hu.symm]
      rw [Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec, Matrix.one_mulVec])

instance : MulAction (PGL p) (ProjectiveLine p) where
  one_smul x := (glActionProjectiveLine p).one_smul x
  mul_smul g₁ g₂ x := by
    induction g₁ using QuotientGroup.induction_on
    induction g₂ using QuotientGroup.induction_on
    exact (glActionProjectiveLine p).mul_smul _ _ x

/-- The projective general linear group `PGL₂(F)` over a field `F`, i.e. `GL₂(F)` modulo its
centre. -/
abbrev PGLOf (F : Type*) [Field F] := GL (Fin 2) F ⧸ Subgroup.center (GL (Fin 2) F)


/-- The group homomorphism `PGL₂(F) → PGL₂(L)` induced by a ring homomorphism `f : F →+* L`. -/
def pglMap {F L : Type*} [Field F] [Field L] (f : F →+* L) : PGLOf F →* PGLOf L :=
  QuotientGroup.map (Subgroup.center (GL (Fin 2) F)) (Subgroup.center (GL (Fin 2) L))
    (Matrix.GeneralLinearGroup.map f) (by
      intro x hx
      apply Subgroup.mem_center_iff.mpr
      let E1 := Matrix.GeneralLinearGroup.mkOfDetNeZero (!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) F) (by norm_num [Matrix.det_fin_two])
      have h1 : (!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) F) * x.val = x.val * !![1, 1; 0, 1] := by
        have h := congr_arg Units.val (Subgroup.mem_center_iff.mp hx E1)
        rw [Units.val_mul, Units.val_mul] at h
        exact h
      have h10 : x.val 1 0 = 0 := add_right_cancel (by
        have h_eq := congr_fun (congr_fun h1.symm 1) 1
        rw [Matrix.mul_apply, Fin.sum_univ_two, Matrix.mul_apply, Fin.sum_univ_two] at h_eq
        change x.val 1 0 * 1 + x.val 1 1 * 1 = 0 * x.val 0 1 + 1 * x.val 1 1 at h_eq
        rw [mul_one, mul_one, zero_mul, one_mul] at h_eq
        exact h_eq)
      let E2 := Matrix.GeneralLinearGroup.mkOfDetNeZero (!![1, 0; 1, 1] : Matrix (Fin 2) (Fin 2) F) (by norm_num [Matrix.det_fin_two])
      have h2 : (!![1, 0; 1, 1] : Matrix (Fin 2) (Fin 2) F) * x.val = x.val * !![1, 0; 1, 1] := by
        have h := congr_arg Units.val (Subgroup.mem_center_iff.mp hx E2)
        rw [Units.val_mul, Units.val_mul] at h
        exact h
      have h01 : x.val 0 1 = 0 := Eq.symm (add_left_cancel (by
        have h_eq := congr_fun (congr_fun h2 0) 0
        rw [Matrix.mul_apply, Fin.sum_univ_two, Matrix.mul_apply, Fin.sum_univ_two] at h_eq
        change 1 * x.val 0 0 + 0 * x.val 1 0 = x.val 0 0 * 1 + x.val 0 1 * 1 at h_eq
        rw [one_mul, zero_mul, mul_one, mul_one] at h_eq
        exact h_eq))
      have h00 : x.val 0 0 = x.val 1 1 := by
        have h_eq := congr_fun (congr_fun h1.symm 0) 1
        rw [Matrix.mul_apply, Fin.sum_univ_two, Matrix.mul_apply, Fin.sum_univ_two] at h_eq
        change x.val 0 0 * 1 + x.val 0 1 * 1 = 1 * x.val 0 1 + 1 * x.val 1 1 at h_eq
        rw [h01, mul_one, zero_mul, mul_zero, one_mul, add_zero, zero_add] at h_eq
        exact h_eq
      intro g
      apply Units.ext
      change g.val * (Matrix.GeneralLinearGroup.map f x).val = (Matrix.GeneralLinearGroup.map f x).val * g.val
      ext i j
      rw [Matrix.mul_apply, Fin.sum_univ_two, Matrix.mul_apply, Fin.sum_univ_two]
      match i, j with
      | 0, 0 =>
        change g.val 0 0 * f (x.val 0 0) + g.val 0 1 * f (x.val 1 0) = f (x.val 0 0) * g.val 0 0 + f (x.val 0 1) * g.val 1 0
        rw [h10, h01, map_zero, mul_zero, zero_mul, add_zero, add_zero, mul_comm]
      | 0, 1 =>
        change g.val 0 0 * f (x.val 0 1) + g.val 0 1 * f (x.val 1 1) = f (x.val 0 0) * g.val 0 1 + f (x.val 0 1) * g.val 1 1
        rw [h01, map_zero, mul_zero, zero_mul, zero_add, add_zero, h00, mul_comm]
      | 1, 0 =>
        change g.val 1 0 * f (x.val 0 0) + g.val 1 1 * f (x.val 1 0) = f (x.val 1 0) * g.val 0 0 + f (x.val 1 1) * g.val 1 0
        rw [h10, map_zero, mul_zero, zero_mul, add_zero, zero_add, h00, mul_comm]
      | 1, 1 =>
        change g.val 1 0 * f (x.val 0 1) + g.val 1 1 * f (x.val 1 1) = f (x.val 1 0) * g.val 0 1 + f (x.val 1 1) * g.val 1 1
        rw [h01, h10, map_zero, mul_zero, zero_mul, zero_add, zero_add, mul_comm])

theorem finite_of_closure_finite (S : Set (K p)) (hS : S.Finite) : Finite (Subfield.closure S) := by
  obtain ⟨s, rfl⟩ := hS.exists_finset_coe
  haveI : Finite (IntermediateField.adjoin (ZMod p) (s : Set (K p))) :=
    Module.finite_iff_finite.mp (IntermediateField.finiteDimensional_adjoin
      (fun x _ ↦ isAlgebraic_iff_isIntegral.mp ((AlgebraicClosure.isAlgebraic (ZMod p)).isAlgebraic x)))
  let f : Subfield.closure (s : Set (K p)) → IntermediateField.adjoin (ZMod p) (s : Set (K p)) :=
    fun x ↦ ⟨x.val, Subfield.closure_le.mpr (fun _ hx ↦ IntermediateField.subset_adjoin (ZMod p) (s : Set (K p)) hx) x.property⟩
  exact Finite.of_injective f (fun x y h ↦ Subtype.ext (show x.val = y.val by
    change (f x).val = (f y).val
    rw [h]))

theorem exists_finite_subfield_conjugate (G : Subgroup (PGL p)) [Finite G] :
    ∃ (L : Subfield (K p)) (g : PGL p),
      Subgroup.map (MulAut.conj g) G ≤ (pglMap (Subfield.subtype L)).range := by
  choose f hf using fun g : PGL p ↦ QuotientGroup.mk_surjective g
  haveI : Fintype G := Fintype.ofFinite G
  let S : Finset (GL (Fin 2) (K p)) := Finset.univ.image (fun x : G ↦ f x.val)

  let L : Subfield (K p) := Subfield.closure (⋃ g ∈ S, Set.range (fun ij : Fin 2 × Fin 2 ↦ g.val ij.1 ij.2))

  have hL_fin : Finite L := by
    apply finite_of_closure_finite
    exact Set.Finite.biUnion (Finset.finite_toSet S) (fun _ _ ↦ Set.finite_range _)

  have hL_mem : ∀ g ∈ S, ∀ i j, g.val i j ∈ L := fun g hg i j ↦
    Subfield.subset_closure (Set.mem_iUnion₂.mpr ⟨g, hg, Set.mem_range_self (i, j)⟩)

  refine ⟨L, (1 : PGL p), ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  erw [show (MulAut.conj (1 : PGL p)) x = x by rw [MulAut.conj_apply, inv_one, mul_one, one_mul]]

  have h_range : f x ∈ (Matrix.GeneralLinearGroup.map (Subfield.subtype L)).range := by
    have hf_in : f x ∈ S := Finset.mem_image.mpr ⟨⟨x, hx⟩, Finset.mem_univ _, rfl⟩
    let y_val : Matrix (Fin 2) (Fin 2) L := Matrix.of fun i j ↦ ⟨(f x).val i j, hL_mem (f x) hf_in i j⟩
    have h_det : y_val.det ≠ 0 := fun hd ↦ by
      have h_eq : (Subfield.subtype L) y_val.det = (f x).val.det := by
        rw [Matrix.det_fin_two, Matrix.det_fin_two, map_sub, map_mul, map_mul]
        rfl
      have h_mul := congr_arg Matrix.det (f x).mul_inv
      rw [Matrix.det_mul, ← h_eq, hd, map_zero, zero_mul, Matrix.det_one] at h_mul
      exact zero_ne_one h_mul
    exact ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero y_val h_det, Units.ext rfl⟩

  obtain ⟨y', hy'⟩ := h_range
  exact ⟨QuotientGroup.mk y', (congr_arg QuotientGroup.mk hy').trans (hf x)⟩

/-- The set of fixed points of the action of `g : PGL p` on the projective line `ℙ¹(K p)`. -/
def fixedPoints (g : PGL p) : Set (ProjectiveLine p) := Function.fixedPoints (fun x ↦ g • x)

theorem fixedPoints_lift (g : GL (Fin 2) (K p)) (x : ProjectiveLine p) :
    x ∈ fixedPoints p (QuotientGroup.mk g) ↔ ∃ c : K p, g.val.mulVec x.rep = c • x.rep := by
  constructor
  · intro h
    change g • x = x at h
    rw [← Projectivization.mk_rep x] at h
    change Projectivization.mk (K p) (g.val.mulVec x.rep) _ = Projectivization.mk (K p) x.rep _ at h
    rw [Projectivization.mk_eq_mk_iff] at h
    exact let ⟨u, hu⟩ := h; ⟨(u : K p), hu.symm⟩

  · rintro ⟨c, hc⟩
    change g • x = x
    rw [← Projectivization.mk_rep x]
    change Projectivization.mk (K p) (g.val.mulVec x.rep) _ = Projectivization.mk (K p) x.rep _
    rw [Projectivization.mk_eq_mk_iff]
    have hc_ne : c ≠ 0 := fun h ↦ x.rep_nonzero <| by
      calc x.rep = (g⁻¹.val * g.val).mulVec x.rep := by
            rw [← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
        _ = g⁻¹.val.mulVec (g.val.mulVec x.rep) := by rw [Matrix.mulVec_mulVec]
        _ = 0 := by rw [hc, h, zero_smul, Matrix.mulVec_zero]
    exact ⟨Units.mk0 c hc_ne, hc.symm⟩

theorem card_eigenvalues (g : GL (Fin 2) (K p)) :
    Set.ncard {x : K p | (g.val - x • 1).det = 0} = if (g.val.trace)^2 = 4 * g.val.det then 1 else 2 := by
  let T := g.val.trace
  let D := g.val.det

  have h_det : ∀ x : K p, (g.val - x • 1).det = x^2 - T * x + D := fun x ↦ by
    rw [Matrix.det_fin_two]
    change (g.val - x • 1) 0 0 * (g.val - x • 1) 1 1 - (g.val - x • 1) 0 1 * (g.val - x • 1) 1 0 = x^2 - g.val.trace * x + g.val.det
    rw [Matrix.trace_fin_two, Matrix.det_fin_two]
    change (g.val 0 0 - x * 1) * (g.val 1 1 - x * 1) - (g.val 0 1 - x * 0) * (g.val 1 0 - x * 0) = x^2 - (g.val 0 0 + g.val 1 1) * x + (g.val 0 0 * g.val 1 1 - g.val 0 1 * g.val 1 0)
    ring

  rw [show {x : K p | (g.val - x • 1).det = 0} = {x | x^2 - T * x + D = 0} from Set.ext (fun z ↦ by change (g.val - z • 1).det = 0 ↔ z^2 - T * z + D = 0; rw [h_det z])]

  obtain ⟨x, hx⟩ : ∃ x : K p, x^2 - T * x + D = 0 := by
    let f : Polynomial (K p) := Polynomial.X^2 - Polynomial.C T * Polynomial.X + Polynomial.C D
    have h_deg : f.degree ≠ 0 := fun h ↦ by
      have h1 : f.coeff 2 = 1 := by
        change (Polynomial.X^2 - Polynomial.C T * Polynomial.X + Polynomial.C D).coeff 2 = 1
        simp only [Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_X_pow, Polynomial.coeff_C_mul, Polynomial.coeff_X, Polynomial.coeff_C]
        change (1 : K p) - T * 0 + 0 = 1
        ring
      have h2 : f.coeff 2 = 0 := by
        rw [Polynomial.eq_C_of_degree_eq_zero h, Polynomial.coeff_C, if_neg (by norm_num : 2 ≠ 0)]
      exact one_ne_zero (h1.symm.trans h2)
    obtain ⟨root, h_root⟩ := IsAlgClosed.exists_root f h_deg
    exact ⟨root, by
      have h_eval : f.eval root = root^2 - T * root + D := by
        change (Polynomial.X^2 - Polynomial.C T * Polynomial.X + Polynomial.C D).eval root = root^2 - T * root + D
        simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_C]
      rw [← h_eval]
      exact h_root⟩

  let y := -x + T

  rw [show {z : K p | z^2 - T * z + D = 0} = {x, y} from Set.ext (fun z ↦ by
    change z^2 - T * z + D = 0 ↔ z = x ∨ z = y
    have h_id : (z - x) * (z - y) = z^2 - T * z + D := by
      change (z - x) * (z - (-x + T)) = z^2 - T * z + D
      calc (z - x) * (z - (-x + T)) = (z^2 - T * z + D) - (x^2 - T * x + D) := by ring
        _ = z^2 - T * z + D := by rw [hx, sub_zero]
    rw [← h_id, mul_eq_zero, sub_eq_zero, sub_eq_zero])]

  have hxy : x = y ↔ (g.val.trace)^2 = 4 * g.val.det := by
    change x = y ↔ T^2 = 4 * D
    constructor <;> intro h
    · apply sub_eq_zero.mp
      change x = -x + T at h
      calc T^2 - 4 * D = ((-x + T) - x)^2 - 4 * (x^2 - T * x + D) := by ring
        _ = (x - x)^2 - 4 * 0 := by rw [hx, ← h]
        _ = 0 := by ring
    · change x = -x + T
      have h_sq : (2 * x - T)^2 = 0 := by
        calc (2 * x - T)^2 = 4 * (x^2 - T * x + D) + (T^2 - 4 * D) := by ring
          _ = 4 * 0 + 0 := by rw [hx, sub_eq_zero.mpr h]
          _ = 0 := by ring
      calc x = x - (2 * x - T) := by rw [sq_eq_zero_iff.mp h_sq]; ring
        _ = -x + T := by ring

  split_ifs with h_disc
  · rw [hxy.mpr h_disc, Set.pair_eq_singleton, Set.ncard_singleton]
  · exact Set.ncard_pair (mt hxy.mp h_disc)

theorem eigenvectors_linearIndependent (g : GL (Fin 2) (K p)) (x y : K p) (v w : Fin 2 → K p)
    (h_ne : x ≠ y) (hv : v ≠ 0) (hw : w ≠ 0)
    (hvx : g.val.mulVec v = x • v) (hwy : g.val.mulVec w = y • w) :
    LinearIndependent (K p) ![v, w] := by
  refine linearIndependent_fin2.mpr ⟨hw, fun a ha ↦ hv ?_⟩
  change a • w = v at ha

  have h_eq : x • v = y • v := by
    calc x • v = g.val.mulVec v := hvx.symm
      _ = g.val.mulVec (a • w) := by rw [ha]
      _ = a • g.val.mulVec w := by rw [Matrix.mulVec_smul]
      _ = a • (y • w) := by rw [hwy]
      _ = y • (a • w) := by rw [smul_comm]
      _ = y • v := by rw [ha]

  have h_zero : (x - y) • v = 0 := by rw [sub_smul, h_eq, sub_self]
  exact (smul_eq_zero.mp h_zero).resolve_left (sub_ne_zero.mpr h_ne)

theorem eigenvector_isMultiple_of_basis (g : GL (Fin 2) (K p)) (x y : K p) (v w u : Fin 2 → K p)
    (h_ne : x ≠ y) (hv : v ≠ 0) (hw : w ≠ 0)
    (hvx : g.val.mulVec v = x • v) (hwy : g.val.mulVec w = y • w)
    (hu_eigen : ∃ z : K p, g.val.mulVec u = z • u) :
    (∃ c : K p, u = c • v) ∨ (∃ c : K p, u = c • w) := by
  have h_lin := eigenvectors_linearIndependent p g x y v w h_ne hv hw hvx hwy

  obtain ⟨c, hc_eq⟩ := (Submodule.mem_span_range_iff_exists_fun (K p)).mp <|
    (Submodule.eq_top_of_finrank_eq (by rw [finrank_span_eq_card h_lin, Module.finrank_pi])).symm ▸ Submodule.mem_top

  let a := c 0; let b := c 1
  have h_comb : u = a • v + b • w := by
    calc u = ∑ i : Fin 2, c i • ![v, w] i := hc_eq.symm
         _ = a • v + b • w := by rw [Fin.sum_univ_two]; rfl

  obtain ⟨z, hz⟩ := hu_eigen
  have h_zero : (a * (x - z)) • v + (b * (y - z)) • w = 0 := by
    ext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    calc a * (x - z) * v i + b * (y - z) * w i
      _ = a * (x * v i) + b * (y * w i) - z * (a * v i + b * w i) := by ring
      _ = (a • (x • v) + b • (y • w)) i - z * (a • v + b • w) i := rfl
      _ = (a • (g.val.mulVec v) + b • (g.val.mulVec w)) i - z * (a • v + b • w) i := by rw [← hvx, ← hwy]
      _ = (g.val.mulVec (a • v) + g.val.mulVec (b • w)) i - z * (a • v + b • w) i := by rw [← Matrix.mulVec_smul, ← Matrix.mulVec_smul]
      _ = (g.val.mulVec (a • v + b • w)) i - z * (a • v + b • w) i := by rw [← Matrix.mulVec_add]
      _ = (g.val.mulVec u) i - z * u i := by rw [← h_comb]
      _ = 0 := by rw [congr_fun hz i]; exact sub_self _

  have h_c_zero := Fintype.linearIndependent_iff.mp h_lin ![a * (x - z), b * (y - z)] (by rw [Fin.sum_univ_two]; exact h_zero)

  rcases mul_eq_zero.mp (h_c_zero 0) with ha0 | hxz
  · right
    exact ⟨b, by rw [h_comb, ha0, zero_smul, zero_add]⟩
  · rcases mul_eq_zero.mp (h_c_zero 1) with hb0 | hyz
    · left
      exact ⟨a, by rw [h_comb, hb0, zero_smul, add_zero]⟩
    · exfalso; exact h_ne <| by rw [sub_eq_zero.mp hxz, sub_eq_zero.mp hyz]

theorem fixedPoints_eq_pair (g : GL (Fin 2) (K p)) (x y : K p) (v w : Fin 2 → K p)
    (h_ne : x ≠ y) (hv : v ≠ 0) (hw : w ≠ 0)
    (hvx : g.val.mulVec v = x • v) (hwy : g.val.mulVec w = y • w) :
    fixedPoints p (QuotientGroup.mk g) = {Projectivization.mk (K p) v hv,
        Projectivization.mk (K p) w hw} := by
  ext P
  rw [Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · intro hP
    rcases eigenvector_isMultiple_of_basis p g x y v w P.rep h_ne hv hw hvx hwy ((fixedPoints_lift p g P).mp hP) with ⟨c, hc⟩ | ⟨c, hc⟩
    · left
      rw [← Projectivization.mk_rep P]
      exact (Projectivization.mk_eq_mk_iff' (K p) _ _ _ _).mpr ⟨c, hc.symm⟩
    · right
      rw [← Projectivization.mk_rep P]
      exact (Projectivization.mk_eq_mk_iff' (K p) _ _ _ _).mpr ⟨c, hc.symm⟩

  · rintro (rfl | rfl)
    · change Projectivization.mk (K p) (g.val.mulVec v) _ = Projectivization.mk (K p) v hv
      exact (Projectivization.mk_eq_mk_iff' (K p) _ _ _ _).mpr ⟨x, hvx.symm⟩
    · change Projectivization.mk (K p) (g.val.mulVec w) _ = Projectivization.mk (K p) w hw
      exact (Projectivization.mk_eq_mk_iff' (K p) _ _ _ _).mpr ⟨y, hwy.symm⟩

theorem ncard_fixedPoints_eq_two_of_ne_eigenvalues (g : GL (Fin 2) (K p)) (x y : K p)
    (h_ne : x ≠ y) (hx : (g.val - x • 1).det = 0) (hy : (g.val - y • 1).det = 0) :
    Set.ncard (fixedPoints p (QuotientGroup.mk g)) = 2 := by
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hx
  obtain ⟨w, hw0, hw⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hy
  rw [Matrix.sub_mulVec, sub_eq_zero, Matrix.smul_mulVec, Matrix.one_mulVec] at hv hw
  rw [fixedPoints_eq_pair p g x y v w h_ne hv0 hw0 hv hw, Set.ncard_pair]

  intro heq
  rw [Projectivization.mk_eq_mk_iff] at heq
  obtain ⟨c, hc⟩ := heq
  have h_contra : x • v = y • v := by
    rw [Units.smul_def] at hc; rw [← hv, ← hc, Matrix.mulVec_smul, hw, smul_comm, hc]

  rw [← sub_eq_zero, ← sub_smul, smul_eq_zero, sub_eq_zero] at h_contra
  exact h_contra.elim h_ne hv0

theorem ncard_fixedPoints_eq_two_of_discrim_ne_zero (g : GL (Fin 2) (K p))
    (h_discr : (g.val.trace)^2 ≠ 4 * g.val.det) :
    Set.ncard (fixedPoints p (QuotientGroup.mk g)) = 2 := by

  let f : Polynomial (K p) :=
    Polynomial.X^2 - Polynomial.C g.val.trace * Polynomial.X + Polynomial.C g.val.det
  have hf_ne_zero : f.degree ≠ 0 := fun h ↦ by
    have h1 : f.coeff 2 = 1 := by
      change (Polynomial.X^2 - Polynomial.C g.val.trace * Polynomial.X + Polynomial.C g.val.det).coeff 2 = 1
      simp only [Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_X_pow, Polynomial.coeff_C_mul, Polynomial.coeff_X, Polynomial.coeff_C]
      change (1 : K p) - g.val.trace * 0 + 0 = 1
      ring
    have h2 : f.coeff 2 = 0 := by
      rw [Polynomial.eq_C_of_degree_eq_zero h, Polynomial.coeff_C, if_neg (by norm_num : 2 ≠ 0)]
    exact one_ne_zero (h1.symm.trans h2)

  obtain ⟨x, hx_root⟩ := IsAlgClosed.exists_root f hf_ne_zero
  have hx : x^2 - g.val.trace * x + g.val.det = 0 := by
    have h_eval : f.eval x = x^2 - g.val.trace * x + g.val.det := by
      change (Polynomial.X^2 - Polynomial.C g.val.trace * Polynomial.X + Polynomial.C g.val.det).eval x = x^2 - g.val.trace * x + g.val.det
      simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_C]
    rw [← h_eval]
    exact hx_root

  let y := g.val.trace - x

  have h_ne : x ≠ y := fun h_eq ↦ h_discr <| by
    have ht : g.val.trace = 2 * x := by
      calc g.val.trace = (g.val.trace - x) + x := by rw [sub_add_cancel]
        _ = y + x := rfl
        _ = x + x := by rw [h_eq]
        _ = 2 * x := by ring
    have hd : g.val.det = x^2 := by
      calc g.val.det = (x^2 - g.val.trace * x + g.val.det) + x * g.val.trace - x^2 := by ring
        _ = 0 + x * g.val.trace - x^2 := by rw [hx]
        _ = x * (2 * x) - x^2 := by rw [zero_add, ht]
        _ = x^2 := by ring
    rw [ht, hd]; ring

  have hy : y^2 - g.val.trace * y + g.val.det = 0 := by
    calc y^2 - g.val.trace * y + g.val.det
      _ = (g.val.trace - x)^2 - g.val.trace * (g.val.trace - x) + g.val.det := rfl
      _ = x^2 - g.val.trace * x + g.val.det := by ring
      _ = 0 := hx

  have expand (t : K p) : (g.val - t • 1).det = t^2 - g.val.trace * t + g.val.det := by
    rw [Matrix.det_fin_two, Matrix.trace_fin_two, Matrix.det_fin_two]
    change (g.val 0 0 - t * 1) * (g.val 1 1 - t * 1) - (g.val 0 1 - t * 0) * (g.val 1 0 - t * 0) = t^2 - (g.val 0 0 + g.val 1 1) * t + (g.val 0 0 * g.val 1 1 - g.val 0 1 * g.val 1 0)
    ring

  exact ncard_fixedPoints_eq_two_of_ne_eigenvalues p g x y h_ne (by rw [expand, hx]) (by rw [expand, hy])

theorem ncard_fixedPoints_eq_one_of_discrim_zero (g : GL (Fin 2) (K p)) (hg : ¬ ∃ c : K p,
    g.val = c • 1) (h_discr : (g.val.trace)^2 = 4 * g.val.det) :
    Set.ncard (fixedPoints p (QuotientGroup.mk g)) = 1 := by

  have h_eigen : Set.ncard {x : K p | (g.val - x • 1).det = 0} = 1 := by
    rw [card_eigenvalues, if_pos h_discr]
  obtain ⟨lambda, hl⟩ := Set.ncard_eq_one.mp h_eigen
  have hlambda : ∀ x : K p, (g.val - x • 1).det = 0 ↔ x = lambda := by
    intro x
    change x ∈ {y : K p | (g.val - y • 1).det = 0} ↔ x ∈ ({lambda} : Set (K p))
    rw [hl]

  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr ((hlambda lambda).mpr rfl)
  have hv_eq : g.val.mulVec v = lambda • v := by
    rw [Matrix.sub_mulVec, sub_eq_zero, Matrix.smul_mulVec, Matrix.one_mulVec] at hv
    exact hv

  let A := g.val - lambda • 1
  let ker := LinearMap.ker (Matrix.mulVecLin A)

  have h_span_le : Submodule.span (K p) {v} ≤ ker := by
    rw [Submodule.span_le, Set.singleton_subset_iff, SetLike.mem_coe, LinearMap.mem_ker]
    exact hv

  have h_ker_lt : Module.finrank (K p) ker < 2 := by
    by_contra! h2
    have h_top : ker = ⊤ := by
      refine Submodule.eq_top_of_finrank_eq ?_
      have h_dim : Module.finrank (K p) (Fin 2 → K p) = 2 := by rw [Module.finrank_pi, Fintype.card_fin]
      have h_le := Submodule.finrank_le ker
      omega
    have hA_zero : A = 0 := by
      ext i j
      have h_mem := Submodule.eq_top_iff'.mp h_top (Pi.single j 1 : Fin 2 → K p)
      rw [LinearMap.mem_ker] at h_mem
      have h_eval := congr_fun h_mem i
      change ∑ k, A i k * (Pi.single j 1 : Fin 2 → K p) k = 0 at h_eval
      rw [Fin.sum_univ_two] at h_eval
      match i, j with
      | 0, 0 => change A 0 0 * (1 : K p) + A 0 1 * (0 : K p) = 0 at h_eval; rw [mul_zero, add_zero, mul_one] at h_eval; exact h_eval
      | 0, 1 => change A 0 0 * (0 : K p) + A 0 1 * (1 : K p) = 0 at h_eval; rw [mul_zero, zero_add, mul_one] at h_eval; exact h_eval
      | 1, 0 => change A 1 0 * (1 : K p) + A 1 1 * (0 : K p) = 0 at h_eval; rw [mul_zero, add_zero, mul_one] at h_eval; exact h_eval
      | 1, 1 => change A 1 0 * (0 : K p) + A 1 1 * (1 : K p) = 0 at h_eval; rw [mul_zero, zero_add, mul_one] at h_eval; exact h_eval
    exact hg ⟨lambda, sub_eq_zero.mp hA_zero⟩

  have h_ker_eq : Submodule.span (K p) {v} = ker := by
    have h_span_dim : Module.finrank (K p) (Submodule.span (K p) {v}) = 1 :=
      finrank_span_singleton hv0
    refine Submodule.eq_of_le_of_finrank_eq h_span_le ?_
    have h_le_span := Submodule.finrank_mono h_span_le
    omega

  have h_kernel : ∀ w : Fin 2 → K p, g.val.mulVec w = lambda • w → ∃ c : K p, w = c • v := by
    intro w hw
    have hw_ker : w ∈ ker := by
      rw [LinearMap.mem_ker]
      change A.mulVec w = 0
      rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, hw, sub_self]
    rw [← h_ker_eq] at hw_ker
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hw_ker
    exact ⟨c, hc.symm⟩

  rw [show fixedPoints p (QuotientGroup.mk g) = {Projectivization.mk (K p) v hv0} from ?_]
  · exact Set.ncard_singleton _
  apply Set.ext
  intro P
  change P ∈ fixedPoints p (QuotientGroup.mk g) ↔ P = Projectivization.mk (K p) v hv0
  constructor
  · intro hP
    have h_eigen : ∃ c : K p, g.val.mulVec P.rep = c • P.rep := (fixedPoints_lift p g P).mp hP
    obtain ⟨c, hc⟩ := h_eigen
    have h_det_c : (g.val - c • 1).det = 0 := by
      rw [← Matrix.exists_mulVec_eq_zero_iff]
      exact ⟨P.rep, P.rep_nonzero, by rw [Matrix.sub_mulVec, sub_eq_zero, Matrix.smul_mulVec,
          Matrix.one_mulVec, hc]⟩
    rw [hlambda c] at h_det_c
    rw [h_det_c] at hc
    obtain ⟨k, hk⟩ := h_kernel P.rep hc
    have hk0 : k ≠ 0 := by
      intro h_zero
      rw [h_zero, zero_smul] at hk
      exact P.rep_nonzero hk
    rw [← Projectivization.mk_rep P, Projectivization.mk_eq_mk_iff]
    exact ⟨Units.mk0 k hk0, hk.symm⟩
  · rintro rfl
    rw [fixedPoints_lift p]
    have h_mk := Projectivization.mk_rep (Projectivization.mk (K p) v hv0)
    rw [Projectivization.mk_eq_mk_iff] at h_mk
    obtain ⟨c, hc⟩ := h_mk
    exact ⟨lambda, by rw [← hc, Matrix.mulVec_smul, hv_eq, smul_comm]⟩

theorem orderOf_coprime_of_discrim_ne_zero (g : GL (Fin 2) (K p))
    (h_discr : (g.val.trace)^2 ≠ 4 * g.val.det)
        (h_fin : IsOfFinOrder (QuotientGroup.mk g : PGL p)) :
    p.Coprime (orderOf (QuotientGroup.mk g : PGL p)) := by
  let f : Polynomial (K p) := Polynomial.X^2 - Polynomial.C g.val.trace * Polynomial.X + Polynomial.C g.val.det
  have h_deg : f.degree ≠ 0 := fun h ↦ by
    have h1 : f.coeff 2 = 1 := by
      change (Polynomial.X^2 - Polynomial.C g.val.trace * Polynomial.X + Polynomial.C g.val.det).coeff 2 = 1
      simp only [Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_X_pow, Polynomial.coeff_C_mul, Polynomial.coeff_X, Polynomial.coeff_C]
      change (1 : K p) - g.val.trace * 0 + 0 = 1
      ring
    have h2 : f.coeff 2 = 0 := by rw [Polynomial.eq_C_of_degree_eq_zero h, Polynomial.coeff_C, if_neg (by norm_num : 2 ≠ 0)]
    exact one_ne_zero (h1.symm.trans h2)

  obtain ⟨lambda1, h_root⟩ := IsAlgClosed.exists_root f h_deg
  have hlambda1 : lambda1^2 - g.val.trace * lambda1 + g.val.det = 0 := by
    have h_eval : f.eval lambda1 = lambda1^2 - g.val.trace * lambda1 + g.val.det := by
      change (Polynomial.X^2 - Polynomial.C g.val.trace * Polynomial.X + Polynomial.C g.val.det).eval lambda1 = lambda1^2 - g.val.trace * lambda1 + g.val.det
      simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_C]
    rw [← h_eval]
    exact h_root

  let lambda2 := g.val.trace - lambda1
  have hlambda2 : lambda1 + lambda2 = g.val.trace ∧ lambda1 * lambda2 = g.val.det :=
    ⟨by ring, by linear_combination -hlambda1⟩

  have h_ne : lambda1 ≠ lambda2 := fun h ↦ h_discr <| by
    calc (g.val.trace)^2 = (2 * lambda1)^2 := by rw [← hlambda2.1, h]; ring
      _ = 4 * g.val.det := by rw [← hlambda2.2, h]; ring

  have expand (t : K p) : (g.val - t • 1).det = t^2 - g.val.trace * t + g.val.det := by
    rw [Matrix.det_fin_two, Matrix.trace_fin_two, Matrix.det_fin_two]
    change (g.val 0 0 - t * 1) * (g.val 1 1 - t * 1) - (g.val 0 1 - t * 0) * (g.val 1 0 - t * 0) = t^2 - (g.val 0 0 + g.val 1 1) * t + (g.val 0 0 * g.val 1 1 - g.val 0 1 * g.val 1 0)
    ring

  obtain ⟨v1, hv1_ne, hv1⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr <|
    show (g.val - lambda1 • 1).det = 0 by rw [expand lambda1, hlambda1]

  have hv1_eq : g.val.mulVec v1 = lambda1 • v1 := by
    apply sub_eq_zero.mp
    calc g.val.mulVec v1 - lambda1 • v1 = g.val.mulVec v1 - (lambda1 • 1 : Matrix _ _ _).mulVec v1 := by rw [Matrix.smul_mulVec, Matrix.one_mulVec]
      _ = (g.val - lambda1 • 1).mulVec v1 := by rw [Matrix.sub_mulVec]
      _ = 0 := hv1

  obtain ⟨v2, hv2_ne, hv2⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr <|
    show (g.val - lambda2 • 1).det = 0 by
      have hlambda2_eq_zero : lambda2^2 - g.val.trace * lambda2 + g.val.det = 0 := by
        calc lambda2^2 - g.val.trace * lambda2 + g.val.det = (g.val.trace - lambda1)^2 - g.val.trace * (g.val.trace - lambda1) + g.val.det := rfl
          _ = lambda1^2 - g.val.trace * lambda1 + g.val.det := by ring
          _ = 0 := hlambda1
      rw [expand lambda2, hlambda2_eq_zero]

  have hv2_eq : g.val.mulVec v2 = lambda2 • v2 := by
    apply sub_eq_zero.mp
    calc g.val.mulVec v2 - lambda2 • v2 = g.val.mulVec v2 - (lambda2 • 1 : Matrix _ _ _).mulVec v2 := by rw [Matrix.smul_mulVec, Matrix.one_mulVec]
      _ = (g.val - lambda2 • 1).mulVec v2 := by rw [Matrix.sub_mulVec]
      _ = 0 := hv2

  have h_lin_indep : LinearIndependent (K p) ![v1, v2] :=
    eigenvectors_linearIndependent p g lambda1 lambda2 v1 v2 h_ne hv1_ne hv2_ne hv1_eq hv2_eq

  have h_P_det_ne_zero : (Matrix.of fun i (j : Fin 2) ↦ if j = 0 then v1 i else v2 i).det ≠ 0 := by
    rw [Fintype.linearIndependent_iff] at h_lin_indep
    contrapose! h_lin_indep
    have h_det : v1 0 * v2 1 - v2 0 * v1 1 = 0 := by
      have h_det_fin : (Matrix.of fun i (j : Fin 2) ↦ if j = 0 then v1 i else v2 i).det = v1 0 * v2 1 - v2 0 * v1 1 := by
        rw [Matrix.det_fin_two]
        change (if (0 : Fin 2) = 0 then v1 0 else v2 0) * (if (1 : Fin 2) = 0 then v1 1 else v2 1) - (if (1 : Fin 2) = 0 then v1 0 else v2 0) * (if (0 : Fin 2) = 0 then v1 1 else v2 1) = _
        rw [if_pos rfl, if_neg (by norm_num : (1 : Fin 2) ≠ 0), if_neg (by norm_num : (1 : Fin 2) ≠ 0), if_pos rfl]
      rw [h_det_fin] at h_lin_indep
      exact h_lin_indep
    by_cases h : v1 0 = 0 <;> by_cases h' : v2 0 = 0
    · refine ⟨fun i ↦ if i = 0 then v2 1 else -v1 1, ?_, ?_⟩
      · ext j
        match j with
        | 0 =>
          change ∑ i : Fin 2, (if i = 0 then v2 1 else -v1 1) * (![v1, v2] i 0) = 0
          rw [Fin.sum_univ_two]
          change (if (0 : Fin 2) = 0 then v2 1 else -v1 1) * v1 0 + (if (1 : Fin 2) = 0 then v2 1 else -v1 1) * v2 0 = 0
          rw [if_pos rfl, if_neg (by norm_num : (1 : Fin 2) ≠ 0), h, h', mul_zero, mul_zero, add_zero]
        | 1 =>
          change ∑ i : Fin 2, (if i = 0 then v2 1 else -v1 1) * (![v1, v2] i 1) = 0
          rw [Fin.sum_univ_two]
          change (if (0 : Fin 2) = 0 then v2 1 else -v1 1) * v1 1 + (if (1 : Fin 2) = 0 then v2 1 else -v1 1) * v2 1 = 0
          rw [if_pos rfl, if_neg (by norm_num : (1 : Fin 2) ≠ 0)]
          ring
      · use 1; intro c1; apply hv1_ne; ext i
        match i with
        | 0 => exact h
        | 1 => change -v1 1 = 0 at c1; exact neg_eq_zero.mp c1
    · exfalso; apply hv1_ne; ext i
      match i with
      | 0 => exact h
      | 1 => exact (mul_eq_zero.mp <|
          by calc v2 0 * v1 1 = -(v1 0 * v2 1 - v2 0 * v1 1) + v1 0 * v2 1 := by ring
                                     _ = -0 + 0 * v2 1 := by rw [h_det, h]
                                     _ = 0 := by ring).resolve_left h'
    · exfalso; apply hv2_ne; ext i
      match i with
      | 0 => exact h'
      | 1 => exact (mul_eq_zero.mp <| by
          calc v1 0 * v2 1
              = (v1 0 * v2 1 - v2 0 * v1 1) + v2 0 * v1 1 := by
                ring
            _ = 0 + 0 * v1 1 := by rw [h_det, h']
            _ = 0 := by ring).resolve_left h
    · refine ⟨fun i ↦ if i = 0 then -v2 0 else v1 0, ?_, ?_⟩
      · ext j
        match j with
        | 0 =>
          change ∑ i : Fin 2, (if i = 0 then -v2 0 else v1 0) * (![v1, v2] i 0) = 0
          rw [Fin.sum_univ_two]
          change (if (0 : Fin 2) = 0 then -v2 0 else v1 0) * v1 0 + (if (1 : Fin 2) = 0 then -v2 0 else v1 0) * v2 0 = 0
          rw [if_pos rfl, if_neg (by norm_num : (1 : Fin 2) ≠ 0)]
          ring
        | 1 =>
          change ∑ i : Fin 2, (if i = 0 then -v2 0 else v1 0) * (![v1, v2] i 1) = 0
          rw [Fin.sum_univ_two]
          change (if (0 : Fin 2) = 0 then -v2 0 else v1 0) * v1 1 + (if (1 : Fin 2) = 0 then -v2 0 else v1 0) * v2 1 = 0
          rw [if_pos rfl, if_neg (by norm_num : (1 : Fin 2) ≠ 0)]
          calc (-v2 0) * v1 1 + v1 0 * v2 1 = v1 0 * v2 1 - v2 0 * v1 1 := by ring
            _ = 0 := h_det
      · use 0; intro c0; apply h'; change -v2 0 = 0 at c0; exact neg_eq_zero.mp c0

  have h_diag_det_ne_zero : (Matrix.diagonal ![lambda1, lambda2]).det ≠ 0 := by
    intro hz
    have hd1 : (Matrix.diagonal ![lambda1, lambda2]).det = lambda1 * lambda2 := by
      rw [Matrix.det_fin_two]
      change (Matrix.diagonal ![lambda1, lambda2] 0 0) * (Matrix.diagonal ![lambda1, lambda2] 1 1) - (Matrix.diagonal ![lambda1, lambda2] 0 1) * (Matrix.diagonal ![lambda1, lambda2] 1 0) = lambda1 * lambda2
      change lambda1 * lambda2 - 0 * 0 = lambda1 * lambda2
      ring
    rw [hd1] at hz
    rw [hlambda2.2] at hz
    exact g.isUnit.map Matrix.detMonoidHom |>.ne_zero hz

  let Y := Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.diagonal ![lambda1, lambda2]) h_diag_det_ne_zero
  obtain ⟨P, hP⟩ : ∃ P : GL (Fin 2) (K p), g = P * Y * P⁻¹ := by
    let P_mat := Matrix.of fun i (j : Fin 2) ↦ if j = 0 then v1 i else v2 i
    let P := Matrix.GeneralLinearGroup.mkOfDetNeZero P_mat h_P_det_ne_zero
    refine ⟨P, Units.ext ?_⟩
    have h_diag : g.val * P.val = P.val * Y.val := by
      ext i j
      match j with
      | 0 =>
        calc (g.val * P.val) i 0 = (g.val.mulVec v1) i := rfl
          _ = (lambda1 • v1) i := congr_fun hv1_eq i
          _ = (P.val * Y.val) i 0 := by
            change lambda1 * v1 i = ∑ k : Fin 2, P.val i k * Y.val k 0
            rw [Fin.sum_univ_two]; change lambda1 * v1 i = v1 i * lambda1 + v2 i * 0; ring
      | 1 =>
        calc (g.val * P.val) i 1 = (g.val.mulVec v2) i := rfl
          _ = (lambda2 • v2) i := congr_fun hv2_eq i
          _ = (P.val * Y.val) i 1 := by
            change lambda2 * v2 i = ∑ k : Fin 2, P.val i k * Y.val k 1
            rw [Fin.sum_univ_two]; change lambda2 * v2 i = v1 i * 0 + v2 i * lambda2; ring
    have h_g : g.val * P.val * (P⁻¹).val = g.val := by rw [Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel P, Units.val_one, Matrix.mul_one]
    calc g.val = (g.val * P.val) * (P⁻¹).val := h_g.symm
      _ = (P.val * Y.val) * (P⁻¹).val := by rw [h_diag]
      _ = (P * Y * P⁻¹).val := rfl

  have h_order_eq : orderOf (QuotientGroup.mk g : PGL p) = orderOf (QuotientGroup.mk Y : PGL p) := by
    have h_semi : SemiconjBy (QuotientGroup.mk P : PGL p) (QuotientGroup.mk Y : PGL p) (QuotientGroup.mk g : PGL p) := by
      change (QuotientGroup.mk (P * Y) : PGL p) = QuotientGroup.mk (g * P)
      have h_eq : P * Y = g * P := by
        calc P * Y = P * Y * 1 := by rw [mul_one]
          _ = P * Y * (P⁻¹ * P) := by rw [inv_mul_cancel]
          _ = (P * Y * P⁻¹) * P := by rw [← mul_assoc (P * Y)]
          _ = g * P := by rw [← hP]
      rw [h_eq]
    exact h_semi.orderOf_eq.symm

  have h_order_eq2 : orderOf (QuotientGroup.mk Y : PGL p) = orderOf (lambda1 / lambda2 : K p) := by
    rw [orderOf_eq_orderOf_iff]
    intro n
    rw [show (QuotientGroup.mk Y : PGL p) ^ n = QuotientGroup.mk (Y ^ n) from rfl, QuotientGroup.eq_one_iff, Subgroup.mem_center_iff]
    have hl2_ne : lambda2 ≠ 0 := by
      intro hc
      exact g.isUnit.map Matrix.detMonoidHom |>.ne_zero (show g.val.det = 0 by rw [← hlambda2.2, hc, mul_zero])
    constructor
    · intro h
      let E := Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.of fun (i j : Fin 2) ↦ if i = 0 then if j = 0 then (1 : K p) else 0 else if j = 0 then 1 else 1) (by
        intro hE
        have h_det : (Matrix.of fun (i j : Fin 2) ↦ if i = 0 then if j = 0 then (1 : K p) else 0 else if j = 0 then 1 else 1).det = 1 := by
          rw [Matrix.det_fin_two]
          change (1 : K p) * 1 - 0 * 1 = 1
          ring
        rw [h_det] at hE
        exact one_ne_zero hE)
      have hl_eq : lambda1^n = lambda2^n := by
        have hE := congr_arg (fun M : GL _ _ ↦ M.val 1 0) (h E)
        change (E.val * (Matrix.diagonal ![lambda1, lambda2])^n) 1 0 = ((Matrix.diagonal ![lambda1, lambda2])^n * E.val) 1 0 at hE
        rw [Matrix.diagonal_pow] at hE
        change (E.val * Matrix.diagonal ![lambda1^n, lambda2^n]) 1 0 = (Matrix.diagonal ![lambda1^n, lambda2^n] * E.val) 1 0 at hE
        have h_left : (E.val * Matrix.diagonal ![lambda1^n, lambda2^n]) 1 0 = lambda1^n := by
          change ∑ k : Fin 2, E.val 1 k * Matrix.diagonal ![lambda1^n, lambda2^n] k 0 = lambda1^n
          rw [Fin.sum_univ_two]
          change 1 * lambda1^n + 1 * 0 = lambda1^n
          ring
        have h_right : (Matrix.diagonal ![lambda1^n, lambda2^n] * E.val) 1 0 = lambda2^n := by
          change ∑ k : Fin 2, Matrix.diagonal ![lambda1^n, lambda2^n] 1 k * E.val k 0 = lambda2^n
          rw [Fin.sum_univ_two]
          change 0 * 1 + lambda2^n * 1 = lambda2^n
          ring
        rw [h_left, h_right] at hE
        exact hE
      rw [div_pow, hl_eq, div_self (pow_ne_zero n hl2_ne)]
    · intro h
      have hl_eq : lambda1^n = lambda2^n := by
        rw [div_pow] at h; exact div_eq_one_iff_eq (pow_ne_zero n hl2_ne) |>.mp h
      intro E
      apply Units.ext
      change E.val * (Matrix.diagonal ![lambda1, lambda2])^n = (Matrix.diagonal ![lambda1, lambda2])^n * E.val
      rw [Matrix.diagonal_pow]
      ext i j
      match i, j with
      | 0, 0 =>
        change ∑ k : Fin 2, E.val 0 k * Matrix.diagonal ![lambda1^n, lambda2^n] k 0 = ∑ k : Fin 2, Matrix.diagonal ![lambda1^n, lambda2^n] 0 k * E.val k 0
        rw [Fin.sum_univ_two, Fin.sum_univ_two]
        change E.val 0 0 * lambda1^n + E.val 0 1 * 0 = lambda1^n * E.val 0 0 + 0 * E.val 1 0
        ring
      | 0, 1 =>
        change ∑ k : Fin 2, E.val 0 k * Matrix.diagonal ![lambda1^n, lambda2^n] k 1 = ∑ k : Fin 2, Matrix.diagonal ![lambda1^n, lambda2^n] 0 k * E.val k 1
        rw [Fin.sum_univ_two, Fin.sum_univ_two]
        change E.val 0 0 * 0 + E.val 0 1 * lambda2^n = lambda1^n * E.val 0 1 + 0 * E.val 1 1
        rw [hl_eq]; ring
      | 1, 0 =>
        change ∑ k : Fin 2, E.val 1 k * Matrix.diagonal ![lambda1^n, lambda2^n] k 0 = ∑ k : Fin 2, Matrix.diagonal ![lambda1^n, lambda2^n] 1 k * E.val k 0
        rw [Fin.sum_univ_two, Fin.sum_univ_two]
        change E.val 1 0 * lambda1^n + E.val 1 1 * 0 = 0 * E.val 0 0 + lambda2^n * E.val 1 0
        rw [hl_eq]; ring
      | 1, 1 =>
        change ∑ k : Fin 2, E.val 1 k * Matrix.diagonal ![lambda1^n, lambda2^n] k 1 = ∑ k : Fin 2, Matrix.diagonal ![lambda1^n, lambda2^n] 1 k * E.val k 1
        rw [Fin.sum_univ_two, Fin.sum_univ_two]
        change E.val 1 0 * 0 + E.val 1 1 * lambda2^n = 0 * E.val 0 1 + lambda2^n * E.val 1 1
        ring

  have h_coprime : ¬(p ∣ orderOf (lambda1 / lambda2 : K p)) := by
    rintro ⟨k, hk⟩
    have hdvd : p * k ∣ k := by
      rw [← hk]
      exact orderOf_dvd_iff_pow_eq_one.mpr <| sub_eq_zero.mp <| eq_zero_of_pow_eq_zero <|
        show ((lambda1 / lambda2 : K p) ^ k - 1) ^ p = 0 by
          rw [sub_pow_char, one_pow, ← pow_mul', sub_eq_zero, ← hk, pow_orderOf_eq_one]
    have hk_pos : 0 < k := by
      have h_opos: 0 < orderOf (lambda1 / lambda2 : K p) := h_order_eq2 ▸ h_order_eq ▸ h_fin.orderOf_pos
      by_contra h_k0
      rw [show k = 0 by exact Nat.eq_zero_of_not_pos h_k0, mul_zero] at hk
      rw [hk] at h_opos
      exact Nat.lt_irrefl 0 h_opos
    have hle : p * k ≤ k := Nat.le_of_dvd hk_pos hdvd
    have hp1 : 1 < p := (inferInstance : Fact (Nat.Prime p)).out.one_lt
    nlinarith only [hk_pos, hp1, hle]

  rw [h_order_eq, h_order_eq2]
  exact (Nat.Prime.coprime_iff_not_dvd Fact.out).mpr h_coprime

variable [h_odd : Fact (p > 2)]

theorem orderOf_eq_prime_of_discrim_zero (g : GL (Fin 2) (K p)) (hg : ¬ ∃ c : K p, g.val = c • 1)
    (h_discr : (g.val.trace)^2 = 4 * g.val.det) : orderOf (QuotientGroup.mk g : PGL p) = p := by
  let eig := g.val.trace / 2
  let N := g.val - eig • 1

  have h_two_ne : (2 : K p) ≠ 0 :=
    (NeZero.of_not_dvd (R := K p) (fun h ↦ absurd (Nat.le_of_dvd (by norm_num) h) (not_le.mpr h_odd.out))).out

  have h_four_ne : (4 : K p) ≠ 0 := by
    intro h4
    have h22 : (2 * 2 : K p) = 0 := by
      calc (2 * 2 : K p) = 4 := by ring
        _ = 0 := h4
    exact h_two_ne (mul_self_eq_zero.mp h22)

  have h_d : (g.val 0 0 + g.val 1 1) ^ 2 = 4 * (g.val 0 0 * g.val 1 1 - g.val 0 1 * g.val 1 0) := by
    rw [← Matrix.trace_fin_two, ← Matrix.det_fin_two]
    exact h_discr

  have h2_eig : 2 * eig = g.val 0 0 + g.val 1 1 := by
    calc 2 * eig = 2 * (g.val.trace / 2) := rfl
      _ = 2 * (g.val.trace * (2 : K p)⁻¹) := by rw [div_eq_mul_inv]
      _ = g.val.trace * (2 * (2 : K p)⁻¹) := by ring
      _ = g.val.trace * 1 := by rw [mul_inv_cancel₀ h_two_ne]
      _ = g.val 0 0 + g.val 1 1 := by rw [mul_one, Matrix.trace_fin_two]

  have h_N_entry (i j : Fin 2) : 2 * N i j = 2 * g.val i j - (g.val 0 0 + g.val 1 1) * (1 : Matrix (Fin 2) (Fin 2) (K p)) i j := by
    simp only [N, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    calc 2 * (g.val i j - eig * (1 : Matrix (Fin 2) (Fin 2) (K p)) i j) = 2 * g.val i j - (2 * eig) * (1 : Matrix (Fin 2) (Fin 2) (K p)) i j := by ring
      _ = 2 * g.val i j - (g.val 0 0 + g.val 1 1) * (1 : Matrix (Fin 2) (Fin 2) (K p)) i j := by rw [h2_eig]

  have hN2 : N ^ 2 = 0 := by
    ext i j
    simp only [sq, Matrix.mul_apply, Fin.sum_univ_two, Matrix.zero_apply]
    have hX : 4 * (N i 0 * N 0 j + N i 1 * N 1 j) = 0 := by
      match i, j with
      | 0, 0 =>
        calc 4 * (N 0 0 * N 0 0 + N 0 1 * N 1 0)
          _ = (2 * N 0 0) * (2 * N 0 0) + (2 * N 0 1) * (2 * N 1 0) := by ring
          _ = (2 * g.val 0 0 - (g.val 0 0 + g.val 1 1) * (1 : Matrix (Fin 2) (Fin 2) (K p)) 0 0) *
                (2 * g.val 0 0 - (g.val 0 0 + g.val 1 1) * (1 : Matrix (Fin 2) (Fin 2) (K p)) 0 0) +
              (2 * g.val 0 1 - (g.val 0 0 + g.val 1 1) * (1 : Matrix (Fin 2) (Fin 2) (K p)) 0 1) *
                (2 * g.val 1 0 - (g.val 0 0 + g.val 1 1) * (1 : Matrix (Fin 2) (Fin 2) (K p)) 1 0) := by
            rw [h_N_entry 0 0, h_N_entry 0 1, h_N_entry 1 0]
          _ = (2 * g.val 0 0 - (g.val 0 0 + g.val 1 1) * 1) * (2 * g.val 0 0 - (g.val 0 0 + g.val 1 1) * 1) +
              (2 * g.val 0 1 - (g.val 0 0 + g.val 1 1) * 0) * (2 * g.val 1 0 - (g.val 0 0 + g.val 1 1) * 0) := rfl
          _ = (g.val 0 0 + g.val 1 1)^2 - 4 * (g.val 0 0 * g.val 1 1 - g.val 0 1 * g.val 1 0) := by ring
          _ = 4 * (g.val 0 0 * g.val 1 1 - g.val 0 1 * g.val 1 0) - 4 * (g.val 0 0 * g.val 1 1 - g.val 0 1 * g.val 1 0) := by rw [h_d]
          _ = 0 := by ring
      | 0, 1 =>
        calc 4 * (N 0 0 * N 0 1 + N 0 1 * N 1 1)
          _ = (2 * N 0 0) * (2 * N 0 1) + (2 * N 0 1) * (2 * N 1 1) := by ring
          _ = (2 * g.val 0 0 - (g.val 0 0 + g.val 1 1) * (1 : Matrix (Fin 2) (Fin 2) (K p)) 0 0) *
                (2 * g.val 0 1 - (g.val 0 0 + g.val 1 1) * (1 : Matrix (Fin 2) (Fin 2) (K p)) 0 1) +
              (2 * g.val 0 1 - (g.val 0 0 + g.val 1 1) * (1 : Matrix (Fin 2) (Fin 2) (K p)) 0 1) *
                (2 * g.val 1 1 - (g.val 0 0 + g.val 1 1) * (1 : Matrix (Fin 2) (Fin 2) (K p)) 1 1) := by
            rw [h_N_entry 0 0, h_N_entry 0 1, h_N_entry 1 1]
          _ = (2 * g.val 0 0 - (g.val 0 0 + g.val 1 1) * 1) * (2 * g.val 0 1 - (g.val 0 0 + g.val 1 1) * 0) +
              (2 * g.val 0 1 - (g.val 0 0 + g.val 1 1) * 0) * (2 * g.val 1 1 - (g.val 0 0 + g.val 1 1) * 1) := rfl
          _ = 0 := by ring
      | 1, 0 =>
        calc 4 * (N 1 0 * N 0 0 + N 1 1 * N 1 0)
          _ = (2 * N 1 0) * (2 * N 0 0) + (2 * N 1 1) * (2 * N 1 0) := by ring
          _ = (2 * g.val 1 0 - (g.val 0 0 + g.val 1 1) * (1 : Matrix (Fin 2) (Fin 2) (K p)) 1 0) *
                (2 * g.val 0 0 - (g.val 0 0 + g.val 1 1) * (1 : Matrix (Fin 2) (Fin 2) (K p)) 0 0) +
              (2 * g.val 1 1 - (g.val 0 0 + g.val 1 1) * (1 : Matrix (Fin 2) (Fin 2) (K p)) 1 1) *
                (2 * g.val 1 0 - (g.val 0 0 + g.val 1 1) * (1 : Matrix (Fin 2) (Fin 2) (K p)) 1 0) := by
            rw [h_N_entry 1 0, h_N_entry 0 0, h_N_entry 1 1]
          _ = (2 * g.val 1 0 - (g.val 0 0 + g.val 1 1) * 0) * (2 * g.val 0 0 - (g.val 0 0 + g.val 1 1) * 1) +
              (2 * g.val 1 1 - (g.val 0 0 + g.val 1 1) * 1) * (2 * g.val 1 0 - (g.val 0 0 + g.val 1 1) * 0) := rfl
          _ = 0 := by ring
      | 1, 1 =>
        calc 4 * (N 1 0 * N 0 1 + N 1 1 * N 1 1)
          _ = (2 * N 1 0) * (2 * N 0 1) + (2 * N 1 1) * (2 * N 1 1) := by ring
          _ = (2 * g.val 1 0 - (g.val 0 0 + g.val 1 1) * (1 : Matrix (Fin 2) (Fin 2) (K p)) 1 0) *
                (2 * g.val 0 1 - (g.val 0 0 + g.val 1 1) * (1 : Matrix (Fin 2) (Fin 2) (K p)) 0 1) +
              (2 * g.val 1 1 - (g.val 0 0 + g.val 1 1) * (1 : Matrix (Fin 2) (Fin 2) (K p)) 1 1) *
                (2 * g.val 1 1 - (g.val 0 0 + g.val 1 1) * (1 : Matrix (Fin 2) (Fin 2) (K p)) 1 1) := by
            rw [h_N_entry 1 0, h_N_entry 0 1, h_N_entry 1 1]
          _ = (2 * g.val 1 0 - (g.val 0 0 + g.val 1 1) * 0) * (2 * g.val 0 1 - (g.val 0 0 + g.val 1 1) * 0) +
              (2 * g.val 1 1 - (g.val 0 0 + g.val 1 1) * 1) * (2 * g.val 1 1 - (g.val 0 0 + g.val 1 1) * 1) := rfl
          _ = (g.val 0 0 + g.val 1 1)^2 - 4 * (g.val 0 0 * g.val 1 1 - g.val 0 1 * g.val 1 0) := by ring
          _ = 4 * (g.val 0 0 * g.val 1 1 - g.val 0 1 * g.val 1 0) - 4 * (g.val 0 0 * g.val 1 1 - g.val 0 1 * g.val 1 0) := by rw [h_d]
          _ = 0 := by ring
    cases mul_eq_zero.mp hX with
    | inl h4 => exact absurd h4 h_four_ne
    | inr hX_eq => exact hX_eq

  have h_char : g.val ^ p = eig ^ p • 1 := by
    have hgN : g.val = eig • 1 + N := by
      ext i j
      change g.val i j = (eig • (1 : Matrix (Fin 2) (Fin 2) (K p))) i j + (g.val i j - (eig • (1 : Matrix (Fin 2) (Fin 2) (K p))) i j)
      ring
    rw [hgN, add_pow_char_of_commute]
    · rw [smul_pow, one_pow, pow_eq_zero_of_le (Fact.out : p.Prime).two_le hN2, add_zero]
    · rw [← Algebra.algebraMap_eq_smul_one]
      exact Algebra.commute_algebraMap_left eig N
  have h_ne_one : (QuotientGroup.mk g : PGL p) ≠ 1 := by
    rw [Ne, QuotientGroup.eq_one_iff, Subgroup.mem_center_iff]
    contrapose! hg; refine ⟨g.val 0 0, Matrix.ext fun i j ↦ ?_⟩
    let E1 := Matrix.GeneralLinearGroup.mkOfDetNeZero (!![1, 1; 0,
        1] : Matrix (Fin 2) (Fin 2) (K p)) (by norm_num)
    let E2 := Matrix.GeneralLinearGroup.mkOfDetNeZero (!![1, 0; 1,
        1] : Matrix (Fin 2) (Fin 2) (K p)) (by norm_num)
    have hE1 := congr_arg Units.val (hg E1); rw [Units.val_mul, Units.val_mul] at hE1
    have hE2 := congr_arg Units.val (hg E2); rw [Units.val_mul, Units.val_mul] at hE2

    have h10 : g.val 1 0 = 0 := by
      have h := congr_fun (congr_fun hE1 1) 1
      change ∑ k : Fin 2, E1.val 1 k * g.val k 1 = ∑ k : Fin 2, g.val 1 k * E1.val k 1 at h
      rw [Fin.sum_univ_two, Fin.sum_univ_two] at h
      change 0 * g.val 0 1 + 1 * g.val 1 1 = g.val 1 0 * 1 + g.val 1 1 * 1 at h
      simp only [zero_mul, zero_add, one_mul, mul_one] at h
      calc g.val 1 0 = (g.val 1 0 + g.val 1 1) - g.val 1 1 := by ring
        _ = g.val 1 1 - g.val 1 1 := by rw [← h]
        _ = 0 := by ring

    have h00_11 : g.val 1 1 = g.val 0 0 := by
      have h := congr_fun (congr_fun hE1 0) 1
      change ∑ k : Fin 2, E1.val 0 k * g.val k 1 = ∑ k : Fin 2, g.val 0 k * E1.val k 1 at h
      rw [Fin.sum_univ_two, Fin.sum_univ_two] at h
      change 1 * g.val 0 1 + 1 * g.val 1 1 = g.val 0 0 * 1 + g.val 0 1 * 1 at h
      simp only [one_mul, mul_one] at h
      calc g.val 1 1 = (g.val 0 1 + g.val 1 1) - g.val 0 1 := by ring
        _ = (g.val 0 0 + g.val 0 1) - g.val 0 1 := by rw [h]
        _ = g.val 0 0 := by ring

    have h01 : g.val 0 1 = 0 := by
      have h := congr_fun (congr_fun hE2 0) 0
      change ∑ k : Fin 2, E2.val 0 k * g.val k 0 = ∑ k : Fin 2, g.val 0 k * E2.val k 0 at h
      rw [Fin.sum_univ_two, Fin.sum_univ_two] at h
      change 1 * g.val 0 0 + 0 * g.val 1 0 = g.val 0 0 * 1 + g.val 0 1 * 1 at h
      simp only [one_mul, zero_mul, add_zero, mul_one] at h
      calc g.val 0 1 = (g.val 0 0 + g.val 0 1) - g.val 0 0 := by ring
        _ = g.val 0 0 - g.val 0 0 := by rw [← h]
        _ = 0 := by ring

    rw [Matrix.smul_apply, smul_eq_mul]
    match i, j with
    | 0, 0 =>
      calc g.val 0 0 = g.val 0 0 * 1 := by ring
        _ = g.val 0 0 * (1 : Matrix (Fin 2) (Fin 2) (K p)) 0 0 := rfl
    | 0, 1 =>
      calc g.val 0 1 = 0 := h01
        _ = g.val 0 0 * 0 := by ring
        _ = g.val 0 0 * (1 : Matrix (Fin 2) (Fin 2) (K p)) 0 1 := rfl
    | 1, 0 =>
      calc g.val 1 0 = 0 := h10
        _ = g.val 0 0 * 0 := by ring
        _ = g.val 0 0 * (1 : Matrix (Fin 2) (Fin 2) (K p)) 1 0 := rfl
    | 1, 1 =>
      calc g.val 1 1 = g.val 0 0 := h00_11
        _ = g.val 0 0 * 1 := by ring
        _ = g.val 0 0 * (1 : Matrix (Fin 2) (Fin 2) (K p)) 1 1 := rfl
  have h_pow_one : (QuotientGroup.mk g : PGL p) ^ p = 1 := by
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_center_iff]
    intro x
    apply Units.ext
    change x.val * (g ^ p).val = (g ^ p).val * x.val
    rw [Units.val_pow_eq_pow_val, h_char, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul]

  exact orderOf_eq_prime h_pow_one h_ne_one

theorem fixedPoints_dichotomy (s : PGL p) (hs_ne_one : s ≠ 1) (hs_fin : IsOfFinOrder s) :
    (Set.ncard (fixedPoints p s) = 1 ↔ orderOf s = p) ∧
    (Set.ncard (fixedPoints p s) = 2 ↔ p.Coprime (orderOf s)) := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective s
  have hg_not_scalar : ¬∃ c : K p, g.val = c • 1 := by
    rintro ⟨c, hc⟩
    apply hs_ne_one
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_center_iff]
    intro x
    apply Units.ext
    change x.val * g.val = g.val * x.val
    rw [hc, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul]

  have h_not_coprime : ¬ p.Coprime p :=
    fun h ↦ (Nat.Prime.coprime_iff_not_dvd Fact.out).mp h (dvd_refl p)

  by_cases h_discr : (g.val.trace)^2 = 4 * g.val.det
  · have hc1 := ncard_fixedPoints_eq_one_of_discrim_zero p g hg_not_scalar h_discr
    have ho := orderOf_eq_prime_of_discrim_zero p g hg_not_scalar h_discr
    refine ⟨iff_of_true hc1 ho, iff_of_false ?_ ?_⟩
    · intro h
      rw [hc1] at h
      exact Nat.zero_ne_one (Nat.succ.inj h)
    · intro h
      rw [ho] at h
      exact h_not_coprime h
  · have hc2 := ncard_fixedPoints_eq_two_of_discrim_ne_zero p g h_discr
    have ho := orderOf_coprime_of_discrim_ne_zero p g h_discr hs_fin
    refine ⟨iff_of_false ?_ ?_, iff_of_true hc2 ho⟩
    · intro h
      rw [hc2] at h
      exact Nat.zero_ne_one (Nat.succ.inj h).symm
    · intro h
      rw [h] at ho
      exact h_not_coprime ho

omit h_odd in
theorem fixedPoint_of_center_unique (P : Subgroup (PGL p)) (z : P) (x : ProjectiveLine p)
    (hz_center : z ∈ Subgroup.center P) (hz_fix : z • x = x)
    (hz_unique : ∀ y : ProjectiveLine p, z • y = y → y = x) :
    ∀ g : P, g • x = x := fun g ↦
  hz_unique _ <| by rw [← mul_smul, ← Subgroup.mem_center_iff.mp hz_center g, mul_smul, hz_fix]

theorem isPGroup_exists_common_fixedPoint (P : Subgroup (PGL p)) (hP_fin : Finite P)
    (hP_p : IsPGroup p P) :
    ∃ x : ProjectiveLine p, ∀ g ∈ P, g • x = x := by
  by_cases h_trivial : ∀ g ∈ P, g = (1 : PGL p)
  · exact ⟨Classical.arbitrary _, fun g hg ↦ by rw [h_trivial g hg, one_smul]⟩
  · push Not at h_trivial
    obtain ⟨g_ne, hg_mem, hg_ne_one⟩ := h_trivial
    haveI : Nontrivial P := ⟨⟨⟨g_ne, hg_mem⟩, 1, Subtype.ext_iff.not.mpr hg_ne_one⟩⟩
    haveI : Nontrivial (Subgroup.center P) := IsPGroup.center_nontrivial hP_p

    obtain ⟨⟨z, hz_center⟩, hz_ne_one⟩ := exists_ne (1 : Subgroup.center P)
    obtain ⟨k_orig, hk_orig⟩ := hP_p z
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Fact.out).mp (orderOf_dvd_iff_pow_eq_one.mpr hk_orig)

    obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := Nat.exists_eq_succ_of_ne_zero (by
      rintro rfl
      rw [pow_zero, orderOf_eq_one_iff] at hk
      exact hz_ne_one (Subtype.ext hk))

    let z_p : P := z ^ p ^ m
    have hz_p_order : orderOf z_p = p := by
      rw [orderOf_pow, hk, Nat.gcd_eq_right (pow_dvd_pow p (Nat.le_succ m)), pow_add, pow_one]
      exact Nat.mul_div_cancel_left _ (pow_pos (Nat.Prime.pos Fact.out) m)

    have hz_val_order : orderOf (z_p : PGL p) = p :=
      (Subgroup.orderOf_coe z_p).trans hz_p_order

    have hz_ne_one_val : (z_p : PGL p) ≠ 1 := fun h ↦
      (Fact.out : Nat.Prime p).ne_one <| by
        rw [h, orderOf_one] at hz_val_order
        exact hz_val_order.symm

    have hz_fin_order : IsOfFinOrder (z_p : PGL p) :=
      orderOf_pos_iff.mp <| by
        rw [hz_val_order]
        exact (Fact.out : Nat.Prime p).pos

    obtain ⟨x, hx_eq⟩ := Set.ncard_eq_one.mp <|
      (fixedPoints_dichotomy p (z_p : PGL p) hz_ne_one_val hz_fin_order).1.mpr hz_val_order

    exact ⟨x, fun g hg ↦
      fixedPoint_of_center_unique p P z_p x
        (Subgroup.pow_mem _ hz_center _)
        (hx_eq.symm ▸ Set.mem_singleton x : x ∈ fixedPoints p (z_p : PGL p))
        (fun y hy ↦ Set.mem_singleton_iff.mp (hx_eq ▸ (hy : y ∈ fixedPoints p (z_p : PGL p))))
        ⟨g, hg⟩⟩

theorem orderOf_eq_prime_of_prime_pow (g : PGL p) (k : ℕ) (hk : k ≥ 1)
    (hg : orderOf g = p ^ k) : orderOf g = p := by
  obtain ⟨g', rfl⟩ := QuotientGroup.mk_surjective g

  have h_non_scalar : ¬∃ c : K p, g'.val = c • 1 := by
    rintro ⟨c, hc⟩
    have h_one : (QuotientGroup.mk g' : PGL p) = 1 := (QuotientGroup.eq_one_iff g').mpr
      (Subgroup.mem_center_iff.mpr fun x ↦ Units.ext <| by
        change x.val * g'.val = g'.val * x.val
        rw [hc, mul_smul_comm, smul_mul_assoc, mul_one, one_mul])
    have h_p_eq_one : p = 1 := Nat.eq_one_of_dvd_one
      ⟨p ^ (k - 1), by rw [mul_comm, ← pow_succ, Nat.sub_add_cancel hk, ← hg, h_one, orderOf_one]⟩
    exact (Fact.out : Nat.Prime p).ne_one h_p_eq_one

  by_cases h_discr : (g'.val.trace)^2 = 4 * g'.val.det
  · exact orderOf_eq_prime_of_discrim_zero p g' h_non_scalar h_discr
  · have h_coprime := orderOf_coprime_of_discrim_ne_zero p g' h_discr
      (orderOf_pos_iff.mp (by rw [hg]; exact pow_pos (Fact.out : Nat.Prime p).pos k))
    have h_gcd_eq_p : Nat.gcd p (p ^ k) = p := Nat.gcd_eq_left (dvd_pow_self p (by exact ne_of_gt hk))
    exact absurd (h_gcd_eq_p.symm.trans <| hg ▸ h_coprime) (Fact.out : Nat.Prime p).ne_one

@[nolint unusedArguments]
theorem isPGroup_orderOf_eq_prime (P : Subgroup (PGL p)) [Finite P] (hP_p : IsPGroup p P) (g : P)
    (hg : g ≠ 1) : orderOf (g : PGL p) = p := by
  obtain ⟨_, hk_orig⟩ := hP_p g
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Fact.out).mp (orderOf_dvd_iff_pow_eq_one.mpr hk_orig)

  have hk_pos : k ≥ 1 := by
    apply Nat.pos_of_ne_zero
    intro h_zero
    rw [h_zero, pow_zero] at hk
    exact hg (orderOf_eq_one_iff.mp hk)

  have hg_val_order : orderOf (g : PGL p) = p ^ k := by
    rw [Subgroup.orderOf_coe]
    exact hk

  exact orderOf_eq_prime_of_prime_pow p (g : PGL p) k hk_pos hg_val_order

theorem isPGroup_exponent_dvd_prime (P : Subgroup (PGL p)) [Finite P] (hP_p : IsPGroup p P) :
    Monoid.exponent P ∣ p := by
  refine Monoid.exponent_dvd_of_forall_pow_eq_one fun g ↦ ?_
  by_cases hg : g = 1
  · rw [hg, one_pow]
  · have h_order_p : orderOf g = p := by
      rw [← Subgroup.orderOf_coe]
      exact isPGroup_orderOf_eq_prime p P hP_p g hg
    have h_pow : g ^ orderOf g = 1 := pow_orderOf_eq_one g
    rw [h_order_p] at h_pow
    exact h_pow



/-- The point `∞ = [1 : 0]` of the projective line `ℙ¹(K p)`. -/
def infinity : ProjectiveLine p := Projectivization.mk (K p) ![1,
    0] (fun h ↦ one_ne_zero (congr_fun h 0))

omit h_odd in
theorem fixesInfinity_iff_upperTriangular (g : PGL p) :
    g • (infinity p) = (infinity p) ↔ ∃ (a b d : K p) (h : a * d ≠ 0),
        g = QuotientGroup.mk (Matrix.GeneralLinearGroup.mkOfDetNeZero !![a, b; 0,
            d] (by rw [Matrix.det_fin_two]; change a * d - b * 0 ≠ 0; rw [mul_zero, sub_zero]; exact h)) := by
  have hz_one : (![1, 0] : Fin 2 → K p) ≠ 0 := fun h ↦ one_ne_zero (congr_fun h 0)
  constructor
  · intro h
    obtain ⟨M, rfl⟩ := QuotientGroup.mk_surjective g
    have h_det_ne : M.val.det ≠ 0 := Matrix.det_ne_zero_of_left_inverse M.inv_mul
    have hz : M.val.mulVec ![1, 0] ≠ 0 := fun h_zero ↦
      h_det_ne (Matrix.exists_mulVec_eq_zero_iff.mp ⟨![1, 0], hz_one, h_zero⟩)
    change Projectivization.mk (K p) (M.val.mulVec ![1, 0]) hz = Projectivization.mk (K p) ![1,
        0] hz_one at h
    have h_iff := Projectivization.mk_eq_mk_iff (K p) (M.val.mulVec ![1, 0]) ![1, 0] hz hz_one
    obtain ⟨c, hc⟩ := h_iff.mp h
    use M.val 0 0, M.val 0 1, M.val 1 1
    have h10 : M.val 1 0 = 0 := by
      have hc1 := congr_fun hc 1
      rw [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at hc1
      calc M.val 1 0 = M.val 1 0 * 1 + M.val 1 1 * 0 := by ring
        _ = (c : K p) * 0 := hc1.symm
        _ = 0 := by ring
    have h_det_eq : M.val.det = M.val 0 0 * M.val 1 1 := by
      rw [Matrix.det_fin_two, h10, mul_zero, sub_zero]
    use h_det_eq ▸ h_det_ne
    congr 1
    apply Units.ext
    ext i j
    match i, j with
    | 0, 0 => rfl
    | 0, 1 => rfl
    | 1, 0 => exact h10
    | 1, 1 => rfl
  · rintro ⟨a, b, d, h_det, rfl⟩
    have hz_mul : (Matrix.GeneralLinearGroup.mkOfDetNeZero !![a, b; 0,
        d] (by rw [Matrix.det_fin_two]; change a * d - b * 0 ≠ 0; rw [mul_zero, sub_zero]; exact h_det)).val.mulVec ![1, 0] ≠ 0 := by
      intro h_zero
      have hM_det : !![a, b; 0, d].det = 0 := Matrix.exists_mulVec_eq_zero_iff.mp ⟨![1, 0], hz_one, h_zero⟩
      rw [Matrix.det_fin_two] at hM_det
      change a * d - b * 0 = 0 at hM_det
      rw [mul_zero, sub_zero] at hM_det
      exact h_det hM_det
    change Projectivization.mk (K p) _ hz_mul = Projectivization.mk (K p) ![1, 0] hz_one
    rw [Projectivization.mk_eq_mk_iff (K p) _ _ hz_mul hz_one]
    use Units.mk0 a (fun h_a ↦ h_det (by rw [h_a, zero_mul]))
    ext i
    rw [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    match i with
    | 0 => change a * 1 = a * 1 + b * 0; simp only [mul_one, mul_zero, add_zero]
    | 1 => change a * 0 = 0 * 1 + d * 0; simp only [zero_mul, mul_zero, add_zero]

omit h_odd in
theorem upper_triangular_ratio_unique
    (a₁ b₁ d₁ a₂ b₂ d₂ : K p) (h₁ : a₁ * d₁ ≠ 0) (h₂ : a₂ * d₂ ≠ 0)
    (heq : (QuotientGroup.mk (Matrix.GeneralLinearGroup.mkOfDetNeZero !![a₁, b₁; 0, d₁]
      (by rw [Matrix.det_fin_two]; change a₁ * d₁ - b₁ * 0 ≠ 0; rw [mul_zero, sub_zero]; exact h₁)) : PGL p) =
     QuotientGroup.mk (Matrix.GeneralLinearGroup.mkOfDetNeZero !![a₂, b₂; 0, d₂]
      (by rw [Matrix.det_fin_two]; change a₂ * d₂ - b₂ * 0 ≠ 0; rw [mul_zero, sub_zero]; exact h₂))) :
    a₁ * d₁⁻¹ = a₂ * d₂⁻¹ := by
  let A := Matrix.GeneralLinearGroup.mkOfDetNeZero !![a₁, b₁; 0, d₁] (by
    rw [Matrix.det_fin_two]
    change a₁ * d₁ - b₁ * 0 ≠ 0
    rw [mul_zero, sub_zero]
    exact h₁)
  let B := Matrix.GeneralLinearGroup.mkOfDetNeZero !![a₂, b₂; 0, d₂] (by
    rw [Matrix.det_fin_two]
    change a₂ * d₂ - b₂ * 0 ≠ 0
    rw [mul_zero, sub_zero]
    exact h₂)
  obtain ⟨c, hc⟩ := Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.mp (QuotientGroup.eq.mp heq)
  have hB : B.val = A.val * Matrix.scalar (Fin 2) c := by rw [hc, ← Units.val_mul, mul_inv_cancel_left]
  have ha2 : a₂ = a₁ * c := by
    refine Eq.trans (congr_fun (congr_fun hB 0) 0) ?_
    rw [Matrix.mul_apply, Fin.sum_univ_two]
    change a₁ * c + b₁ * 0 = a₁ * c
    rw [mul_zero, add_zero]
  have hd2 : d₂ = d₁ * c := by
    refine Eq.trans (congr_fun (congr_fun hB 1) 1) ?_
    rw [Matrix.mul_apply, Fin.sum_univ_two]
    change 0 * 0 + d₁ * c = d₁ * c
    rw [zero_mul, zero_add]
  calc a₁ * d₁⁻¹
    _ = a₁ * d₁⁻¹ * (c * c⁻¹) := by rw [mul_inv_cancel₀ (fun hc ↦ h₂ (by rw [ha2, hc, mul_zero, zero_mul])), mul_one]
    _ = (a₁ * c) * (d₁⁻¹ * c⁻¹) := by ring
    _ = (a₁ * c) * (d₁ * c)⁻¹ := by rw [← mul_inv]
    _ = a₂ * d₂⁻¹ := by rw [← ha2, ← hd2]

omit h_odd in
theorem upper_triangular_mul_ratio
    (a₁ b₁ d₁ a₂ b₂ d₂ : K p) (h₁ : a₁ * d₁ ≠ 0) (h₂ : a₂ * d₂ ≠ 0) :
    (QuotientGroup.mk (Matrix.GeneralLinearGroup.mkOfDetNeZero !![a₁, b₁; 0, d₁]
      (by rw [Matrix.det_fin_two]; change a₁ * d₁ - b₁ * 0 ≠ 0; rw [mul_zero, sub_zero]; exact h₁)) : PGL p) *
     QuotientGroup.mk (Matrix.GeneralLinearGroup.mkOfDetNeZero !![a₂, b₂; 0, d₂]
      (by rw [Matrix.det_fin_two]; change a₂ * d₂ - b₂ * 0 ≠ 0; rw [mul_zero, sub_zero]; exact h₂)) =
     QuotientGroup.mk (Matrix.GeneralLinearGroup.mkOfDetNeZero !![a₁ * a₂, a₁ * b₂ + b₁ * d₂; 0, d₁ * d₂]
      (by rw [Matrix.det_fin_two]; change (a₁ * a₂) * (d₁ * d₂) - (a₁ * b₂ + b₁ * d₂) * 0 ≠ 0; rw [mul_zero, sub_zero]; rw [show (a₁ * a₂) * (d₁ * d₂) = (a₁ * d₁) * (a₂ * d₂) by ring]; exact mul_ne_zero h₁ h₂)) := by
  refine congr_arg (fun x ↦ (QuotientGroup.mk x : PGL p)) ?_
  ext i j
  change ( !![a₁, b₁; 0, d₁] * !![a₂, b₂; 0, d₂] ) i j = _
  rw [Matrix.mul_apply, Fin.sum_univ_two]
  match i, j with
  | 0, 0 => change a₁ * a₂ + b₁ * 0 = a₁ * a₂; rw [mul_zero, add_zero]
  | 0, 1 => change a₁ * b₂ + b₁ * d₂ = a₁ * b₂ + b₁ * d₂; rfl
  | 1, 0 => change 0 * a₂ + d₁ * 0 = 0; rw [zero_mul, mul_zero, add_zero]
  | 1, 1 => change 0 * b₂ + d₁ * d₂ = d₁ * d₂; rw [zero_mul, zero_add]


theorem ratio_one_imp_unipotent
    (a b d : K p) (h : a * d ≠ 0) (hr : a * d⁻¹ = 1) :
    orderOf (QuotientGroup.mk (Matrix.GeneralLinearGroup.mkOfDetNeZero !![a, b; 0, d]
      (by rw [Matrix.det_fin_two]; change a * d - b * 0 ≠ 0; rw [mul_zero, sub_zero]; exact h)) : PGL p) = 1 ∨
    orderOf (QuotientGroup.mk (Matrix.GeneralLinearGroup.mkOfDetNeZero !![a, b; 0, d]
      (by rw [Matrix.det_fin_two]; change a * d - b * 0 ≠ 0; rw [mul_zero, sub_zero]; exact h)) : PGL p) = p := by
  have ha : a ≠ 0 := fun ha_eq ↦ h (by rw [ha_eq, zero_mul])
  have h_eq : a = d := eq_of_div_eq_one hr
  let Y := Matrix.GeneralLinearGroup.mkOfDetNeZero !![a, b; 0, d] (by rw [Matrix.det_fin_two]; change a * d - b * 0 ≠ 0; rw [mul_zero, sub_zero]; exact h)
  let X := Matrix.GeneralLinearGroup.mkOfDetNeZero !![1, b * a⁻¹; 0, 1] (by rw [Matrix.det_fin_two]; change 1 * 1 - (b * a⁻¹) * 0 ≠ 0; rw [mul_zero, sub_zero, mul_one]; exact one_ne_zero)
  have h_simplified : (QuotientGroup.mk Y : PGL p) = QuotientGroup.mk X := by
    rw [QuotientGroup.eq, Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar]
    use a⁻¹
    have h_mat : X.val = Y.val * Matrix.scalar (Fin 2) a⁻¹ := by
      ext i j
      rw [Matrix.mul_apply, Fin.sum_univ_two]
      match i, j with
      | 0, 0 => change 1 = a * a⁻¹ + b * 0; rw [mul_zero, add_zero, mul_inv_cancel₀ ha]
      | 0, 1 => change b * a⁻¹ = a * 0 + b * a⁻¹; rw [mul_zero, zero_add]
      | 1, 0 => change 0 = 0 * a⁻¹ + d * 0; rw [mul_zero, zero_mul, add_zero]
      | 1, 1 => change 1 = 0 * 0 + d * a⁻¹; rw [zero_mul, zero_add, ← h_eq, mul_inv_cancel₀ ha]
    rw [Units.val_mul, h_mat, ← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]
  rw [h_simplified]
  by_cases hb : b * a⁻¹ = 0
  · left
    have hX_one : X = 1 := by
      ext i j
      match i, j with
      | 0, 0 => rfl
      | 0, 1 => exact hb
      | 1, 0 => rfl
      | 1, 1 => rfl
    rw [hX_one]
    exact orderOf_one
  · right
    refine orderOf_eq_prime_of_discrim_zero p X ?_ ?_
    · rintro ⟨c, hc⟩
      have h01 : X.val 0 1 = (c • (1 : Matrix (Fin 2) (Fin 2) (K p))) 0 1 := congr_fun (congr_fun hc 0) 1
      rw [Matrix.smul_apply, Matrix.one_apply_ne Fin.zero_ne_one, smul_zero] at h01
      exact hb h01
    · rw [Matrix.trace_fin_two, Matrix.det_fin_two]
      change (1 + 1 : K p)^2 = 4 * (1 * 1 - (b * a⁻¹) * 0)
      ring

theorem isUnipotent_of_fixesInfinity_orderOf (g : PGL p) (h_fix : g • (infinity p) = (infinity p))
    (h_order : orderOf g = p) :
  ∃ x : K p, g = QuotientGroup.mk (Matrix.GeneralLinearGroup.mkOfDetNeZero !![1, x; 0,
      1] (by rw [Matrix.det_fin_two]; change (1 : K p) * 1 - x * 0 ≠ 0; rw [mul_one, mul_zero,
          sub_zero]; exact one_ne_zero)) := by
  obtain ⟨a, b, d, h_det, hg⟩ := (fixesInfinity_iff_upperTriangular p g).mp h_fix
  by_cases ha : a = d
  · use b / a
    rw [hg]
    symm
    rw [QuotientGroup.eq]
    simp only [Subgroup.mem_center_iff]
    intro x
    apply Units.ext
    let A := Matrix.GeneralLinearGroup.mkOfDetNeZero
      !![a, b; 0, d] (by
        rw [Matrix.det_fin_two]
        change a * d - b * 0 ≠ 0
        rw [mul_zero, sub_zero]; exact h_det)
    let B := Matrix.GeneralLinearGroup.mkOfDetNeZero
      !![1, b / a; 0, 1] (by
        rw [Matrix.det_fin_two]
        change (1 : K p) * 1 - b / a * 0 ≠ 0
        rw [mul_one, mul_zero, sub_zero]; exact one_ne_zero)
    have hAB : A.val = a • B.val := by
      ext i j
      match i, j with
      | 0, 0 => exact (mul_one a).symm
      | 0, 1 =>
        change b = a * (b * a⁻¹)
        rw [← mul_assoc, mul_comm a b, mul_assoc, mul_inv_cancel₀ (mul_ne_zero_iff.mp h_det).1, mul_one]
      | 1, 0 => exact (mul_zero a).symm
      | 1, 1 => exact ha.symm.trans (mul_one a).symm
    have h_center : (B⁻¹ * A).val = a • 1 :=
      calc (B⁻¹ * A).val = (B⁻¹).val * A.val := rfl
        _ = (B⁻¹).val * (a • B.val) := by rw [hAB]
        _ = a • ((B⁻¹).val * B.val) := by rw [Matrix.mul_smul]
        _ = a • 1 := by rw [show (B⁻¹).val * B.val = 1 from congr_arg Units.val (inv_mul_cancel B)]
    change x.val * (B⁻¹ * A).val = (B⁻¹ * A).val * x.val
    rw [h_center]
    simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul]
  · let A := Matrix.GeneralLinearGroup.mkOfDetNeZero
      !![a, b; 0, d] (by
        rw [Matrix.det_fin_two]
        change a * d - b * 0 ≠ 0
        rw [mul_zero, sub_zero]; exact h_det)
    have h_two_fixed_points : Set.ncard (fixedPoints p (QuotientGroup.mk A)) = 2 := by
      apply ncard_fixedPoints_eq_two_of_discrim_ne_zero p A
      have h_trace : A.val.trace = a + d := by
        change ∑ i : Fin 2, A.val i i = a + d
        rw [Fin.sum_univ_two]; rfl
      have h_det_val : A.val.det = a * d := by
        rw [Matrix.det_fin_two]
        change a * d - b * 0 = a * d
        rw [mul_zero, sub_zero]
      rw [h_trace, h_det_val]
      intro hc
      have h_eq : (a - d) * (a - d) = 0 :=
        calc (a - d) * (a - d) = (a + d)^2 - 4 * (a * d) := by ring
          _ = 0 := sub_eq_zero.mpr hc
      exact ha (eq_of_sub_eq_zero (mul_self_eq_zero.mp h_eq))

    have hg_ne_one : g ≠ 1 := fun hc ↦
      (Fact.out : Nat.Prime p).ne_one (h_order.symm.trans ((congr_arg orderOf hc).trans orderOf_one))

    have hg_fin : IsOfFinOrder g :=
      isOfFinOrder_iff_pow_eq_one.mpr ⟨p, (Fact.out : Nat.Prime p).pos, by
        calc g ^ p = g ^ orderOf g := by rw [h_order]
          _ = 1 := pow_orderOf_eq_one g⟩

    have h_coprime : p.Coprime (orderOf g) :=
      (fixedPoints_dichotomy p g hg_ne_one hg_fin).2.mp (hg.symm ▸ h_two_fixed_points)

    have h_gcd_eq_one : Nat.gcd p p = 1 := by
      calc Nat.gcd p p = Nat.gcd p (orderOf g) := by rw [h_order]
        _ = 1 := h_coprime

    exact absurd ((Nat.gcd_self p).symm.trans h_gcd_eq_one) (Fact.out : Nat.Prime p).ne_one

omit h_odd in
theorem exists_smul_eq_infinity (x : ProjectiveLine p) :
    ∃ k : PGL p, k • x = infinity p := by
  set v := x.rep
  obtain ⟨A, hAdet, hAv⟩ : ∃ A : Matrix (Fin 2) (Fin 2) (K p), A.det ≠ 0 ∧ A.mulVec v = ![1, 0] := by
    by_cases hv0 : v 0 = 0
    · have hv1 : v 1 ≠ 0 := fun h ↦ x.rep_nonzero (funext fun i ↦ match i with | 0 => hv0 | 1 => h)
      refine ⟨!![0, (v 1)⁻¹; 1, 0], ?_, ?_⟩
      · rw [Matrix.det_fin_two]
        change 0 * 0 - (v 1)⁻¹ * 1 ≠ 0
        rw [mul_zero, mul_one, zero_sub, neg_ne_zero]
        exact inv_ne_zero hv1
      · ext i
        rw [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
        match i with
        | 0 =>
          change 0 * v 0 + (v 1)⁻¹ * v 1 = 1
          rw [zero_mul, zero_add, inv_mul_cancel₀ hv1]
        | 1 =>
          change 1 * v 0 + 0 * v 1 = 0
          rw [one_mul, zero_mul, add_zero, hv0]
    · refine ⟨!![(v 0)⁻¹, 0; -(v 1) * (v 0)⁻¹, 1], ?_, ?_⟩
      · rw [Matrix.det_fin_two]
        change (v 0)⁻¹ * 1 - 0 * (-(v 1) * (v 0)⁻¹) ≠ 0
        rw [mul_one, zero_mul, sub_zero]
        exact inv_ne_zero hv0
      · ext i
        rw [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
        match i with
        | 0 =>
          change (v 0)⁻¹ * v 0 + 0 * v 1 = 1
          rw [zero_mul, add_zero, inv_mul_cancel₀ hv0]
        | 1 =>
          change (-(v 1) * (v 0)⁻¹) * v 0 + 1 * v 1 = 0
          rw [neg_mul, neg_mul, one_mul]
          change -(v 1 * (v 0)⁻¹ * v 0) + v 1 = 0
          rw [mul_assoc, inv_mul_cancel₀ hv0, mul_one, neg_add_cancel]
  refine ⟨QuotientGroup.mk (Matrix.GeneralLinearGroup.mkOfDetNeZero A hAdet), ?_⟩
  rw [← Projectivization.mk_rep x]
  exact (Projectivization.mk_eq_mk_iff (K p) _ _ _ _).mpr ⟨1, by rw [one_smul]; exact hAv.symm⟩

theorem commute_of_orderOf_prime_fixesInfinity (g h : PGL p) (hg_order : orderOf g = p)
    (hh_order : orderOf h = p) (hg_fix : g • (infinity p) = (infinity p))
        (hh_fix : h • (infinity p) = (infinity p)) :
    g * h = h * g := by
  obtain ⟨x, hx⟩ := isUnipotent_of_fixesInfinity_orderOf p g hg_fix hg_order
  obtain ⟨y, hy⟩ := isUnipotent_of_fixesInfinity_orderOf p h hh_fix hh_order
  rw [hx, hy]
  change QuotientGroup.mk (_ * _) = QuotientGroup.mk (_ * _)
  congr 1
  apply Units.ext
  change (!![1, x; 0, 1] * !![1, y; 0, 1] : Matrix (Fin 2) (Fin 2) _) = (!![1, y; 0, 1] * !![1,
      x; 0, 1] : Matrix (Fin 2) (Fin 2) _)
  ext i j
  rw [Matrix.mul_apply, Fin.sum_univ_two, Matrix.mul_apply, Fin.sum_univ_two]
  match i, j with
  | 0, 0 => change (1 * 1 + x * 0 : K p) = 1 * 1 + y * 0; ring
  | 0, 1 => change (1 * y + x * 1 : K p) = 1 * x + y * 1; ring
  | 1, 0 => change (0 * 1 + 1 * 0 : K p) = 0 * 1 + 1 * 0; ring
  | 1, 1 => change (0 * y + 1 * 1 : K p) = 0 * x + 1 * 1; ring

theorem commute_of_orderOf_prime_common_fixedPoint (g h : PGL p) (x : ProjectiveLine p)
    (hg_order : orderOf g = p) (hh_order : orderOf h = p) (hg_fix : g • x = x)
        (hh_fix : h • x = x) :
    g * h = h * g := by
  obtain ⟨k, hk⟩ := exists_smul_eq_infinity p x
  have order_conj_eq : ∀ y : PGL p, orderOf (k * y * k⁻¹) = orderOf y := fun y ↦
    SemiconjBy.orderOf_eq k⁻¹
        (show SemiconjBy k⁻¹ (k * y * k⁻¹) y by change k⁻¹ * (k * y * k⁻¹) = y * k⁻¹; group)
  have h_comm := commute_of_orderOf_prime_fixesInfinity p (k * g * k⁻¹) (k * h * k⁻¹)
    (Eq.trans (order_conj_eq g) hg_order)
    (Eq.trans (order_conj_eq h) hh_order)
    (by rw [← hk, mul_smul, mul_smul, inv_smul_smul, hg_fix])
    (by rw [← hk, mul_smul, mul_smul, inv_smul_smul, hh_fix])
  calc g * h = k⁻¹ * ((k * g * k⁻¹) * (k * h * k⁻¹)) * k := by group
    _ = k⁻¹ * ((k * h * k⁻¹) * (k * g * k⁻¹)) * k := by rw [h_comm]
    _ = h * g := by group

theorem isPGroup_comm_exponent_fixedPoint (P : Subgroup (PGL p)) [Finite P] (hP_p : IsPGroup p P)
    (hP_nontriv : Nontrivial P) :
    (∀ g h : P, g * h = h * g) ∧
    (Monoid.exponent P ∣ p) ∧
    (∃! x : ProjectiveLine p, ∀ g ∈ P, g • x = x) := by
  obtain ⟨x, hx⟩ := isPGroup_exists_common_fixedPoint p P ‹_› hP_p
  refine ⟨?_, isPGroup_exponent_dvd_prime p P hP_p, x, hx, ?_⟩
  · intro g h
    ext
    by_cases hg : g = 1; · rw [hg, one_mul, mul_one]
    by_cases hh : h = 1; · rw [hh, mul_one, one_mul]
    exact commute_of_orderOf_prime_common_fixedPoint p g.val h.val x
      (isPGroup_orderOf_eq_prime p P hP_p g hg)
      (isPGroup_orderOf_eq_prime p P hP_p h hh)
      (hx g.val g.prop) (hx h.val h.prop)
  · intro y hy
    obtain ⟨z, hz⟩ := exists_ne (1 : P)
    have hz_order := isPGroup_orderOf_eq_prime p P hP_p z hz
    have hz_ne_one : z.val ≠ 1 := fun hc ↦ hz (Subtype.ext hc)
    have hz_fin : IsOfFinOrder z.val :=
      isOfFinOrder_iff_pow_eq_one.mpr ⟨p, (Fact.out : Nat.Prime p).pos, by
        calc z.val ^ p = z.val ^ orderOf z.val := by rw [hz_order]
          _ = 1 := pow_orderOf_eq_one z.val⟩
    obtain ⟨a, ha⟩ := Set.ncard_eq_one.mp <|
      (fixedPoints_dichotomy p z.val hz_ne_one hz_fin).1.mpr hz_order
    have hx_mem : x ∈ fixedPoints p z.val := hx z.val z.prop
    have hy_mem : y ∈ fixedPoints p z.val := hy z.val z.prop
    rw [ha, Set.mem_singleton_iff] at hx_mem hy_mem
    exact hy_mem.trans hx_mem.symm

end lemmata

noncomputable section CardPGL

variable {F : Type*} [Field F] [Fintype F]


theorem card_center_GL2 :
    Nat.card (Subgroup.center (GL (Fin 2) F)) = Fintype.card F - 1 := by
  have h_center : ∀ g : GL (Fin 2) F, g ∈ Subgroup.center (GL (Fin 2) F) ↔ ∃ c : F, c ≠ 0 ∧ (g : Matrix (Fin 2) (Fin 2) F) = Matrix.diagonal ![c, c] := by
    intro g
    constructor
    · intro hg
      have h_comm : ∀ h : Matrix (Fin 2) (Fin 2) F, h.det ≠ 0 → (g : Matrix (Fin 2) (Fin 2) F) * h = h * (g : Matrix (Fin 2) (Fin 2) F) := fun h hh ↦
        congrArg Units.val (Subgroup.mem_center_iff.mp hg (Matrix.GeneralLinearGroup.mkOfDetNeZero h hh)).symm
      have eq_01 : (g : Matrix (Fin 2) (Fin 2) F) 0 1 = 0 := by
        have h := congrFun (congrFun (h_comm !![1, 0; 1, 1] (by
          rw [Matrix.det_fin_two]
          change (1 * 1 - 0 * 1 : F) ≠ 0
          simp only [mul_one, sub_zero]
          exact one_ne_zero)) 0) 0
        simp only [Matrix.mul_apply, Fin.sum_univ_two] at h
        change (g : Matrix (Fin 2) (Fin 2) F) 0 0 * 1 + (g : Matrix (Fin 2) (Fin 2) F) 0 1 * 1 = 1 * (g : Matrix (Fin 2) (Fin 2) F) 0 0 + 0 * (g : Matrix (Fin 2) (Fin 2) F) 1 0 at h
        simp only [mul_one, one_mul, zero_mul] at h
        exact add_left_cancel h

      have eq_10 : (g : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by
        have h := congrFun (congrFun (h_comm !![1, 1; 0, 1] (by
          rw [Matrix.det_fin_two]
          change (1 * 1 - 1 * 0 : F) ≠ 0
          simp only [mul_one, mul_zero, sub_zero]
          exact one_ne_zero)) 1) 1
        simp only [Matrix.mul_apply, Fin.sum_univ_two] at h
        change (g : Matrix (Fin 2) (Fin 2) F) 1 0 * 1 + (g : Matrix (Fin 2) (Fin 2) F) 1 1 * 1 = 0 * (g : Matrix (Fin 2) (Fin 2) F) 0 1 + 1 * (g : Matrix (Fin 2) (Fin 2) F) 1 1 at h
        simp only [mul_one, one_mul, zero_mul] at h
        exact add_right_cancel h

      have eq_11 : (g : Matrix (Fin 2) (Fin 2) F) 1 1 = (g : Matrix (Fin 2) (Fin 2) F) 0 0 := by
        have h := congrFun (congrFun (h_comm !![1, 0; 1, 1] (by
          rw [Matrix.det_fin_two]
          change (1 * 1 - 0 * 1 : F) ≠ 0
          simp only [mul_one, sub_zero]
          exact one_ne_zero)) 1) 0
        simp only [Matrix.mul_apply, Fin.sum_univ_two] at h
        change (g : Matrix (Fin 2) (Fin 2) F) 1 0 * 1 + (g : Matrix (Fin 2) (Fin 2) F) 1 1 * 1 = 1 * (g : Matrix (Fin 2) (Fin 2) F) 0 0 + 1 * (g : Matrix (Fin 2) (Fin 2) F) 1 0 at h
        simp only [mul_one, one_mul, eq_10, zero_add, add_zero] at h
        exact h
      use (g : Matrix (Fin 2) (Fin 2) F) 0 0
      refine ⟨?_, ?_⟩
      · intro hc
        have hdet : IsUnit (g : Matrix (Fin 2) (Fin 2) F) := ⟨g, rfl⟩
        rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_fin_two, eq_01, eq_10, eq_11, hc] at hdet
        simp only [mul_zero, sub_zero] at hdet
        exact not_isUnit_zero hdet
      · ext i j
        match i, j with
        | 0, 0 => rfl
        | 0, 1 => exact eq_01
        | 1, 0 => exact eq_10
        | 1, 1 => exact eq_11
    · rintro ⟨c, _, hg⟩
      rw [Subgroup.mem_center_iff]
      intro h
      apply Units.ext
      rw [Units.val_mul, Units.val_mul, hg]
      ext i j
      rw [Matrix.mul_apply, Fin.sum_univ_two, Matrix.mul_apply, Fin.sum_univ_two]
      match i, j with
      | 0, 0 =>
        change (h : Matrix (Fin 2) (Fin 2) F) 0 0 * c + (h : Matrix (Fin 2) (Fin 2) F) 0 1 * 0 = c * (h : Matrix (Fin 2) (Fin 2) F) 0 0 + 0 * (h : Matrix (Fin 2) (Fin 2) F) 1 0
        rw [mul_zero, add_zero, zero_mul, add_zero, mul_comm]
      | 0, 1 =>
        change (h : Matrix (Fin 2) (Fin 2) F) 0 0 * 0 + (h : Matrix (Fin 2) (Fin 2) F) 0 1 * c = c * (h : Matrix (Fin 2) (Fin 2) F) 0 1 + 0 * (h : Matrix (Fin 2) (Fin 2) F) 1 1
        rw [mul_zero, zero_add, zero_mul, add_zero, mul_comm]
      | 1, 0 =>
        change (h : Matrix (Fin 2) (Fin 2) F) 1 0 * c + (h : Matrix (Fin 2) (Fin 2) F) 1 1 * 0 = 0 * (h : Matrix (Fin 2) (Fin 2) F) 0 0 + c * (h : Matrix (Fin 2) (Fin 2) F) 1 0
        rw [mul_zero, add_zero, zero_mul, zero_add, mul_comm]
      | 1, 1 =>
        change (h : Matrix (Fin 2) (Fin 2) F) 1 0 * 0 + (h : Matrix (Fin 2) (Fin 2) F) 1 1 * c = 0 * (h : Matrix (Fin 2) (Fin 2) F) 0 1 + c * (h : Matrix (Fin 2) (Fin 2) F) 1 1
        rw [mul_zero, zero_add, zero_mul, zero_add, mul_comm]
  let e : Subgroup.center (GL (Fin 2) F) ≃ {c : F // c ≠ 0} := {
    toFun := fun g ↦ ⟨(g.1 : Matrix (Fin 2) (Fin 2) F) 0 0, by
      obtain ⟨c, hc, hg⟩ := h_center g.1 |>.mp g.2
      rw [hg]
      exact hc⟩
    invFun := fun c ↦ ⟨
      Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.diagonal ![c.val, c.val]) (by
        rw [Matrix.det_fin_two]
        change c.val * c.val - 0 * 0 ≠ 0
        simp only [mul_zero, sub_zero, ne_eq]
        exact mul_ne_zero c.property c.property),
      (h_center _).mpr ⟨c.val, c.property, rfl⟩⟩
    left_inv := fun g ↦ Subtype.ext (Units.ext (by
      obtain ⟨c, _, hg⟩ := h_center g.1 |>.mp g.2
      change Matrix.diagonal ![(g.1 : Matrix (Fin 2) (Fin 2) F) 0 0, (g.1 : Matrix (Fin 2) (Fin 2) F) 0 0] = _
      rw [hg]
      rfl))
    right_inv := fun _ ↦ Subtype.ext rfl
  }
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.filter_ne', Finset.card_erase_of_mem (Finset.mem_univ 0), Finset.card_univ]


theorem card_PGL2 :
    Nat.card (GL (Fin 2) F ⧸ Subgroup.center (GL (Fin 2) F)) =
    Fintype.card F * (Fintype.card F ^ 2 - 1) := by
  refine mul_right_cancel₀ (Nat.sub_ne_zero_of_lt (Fintype.one_lt_card (α := F))) ?_
  rw [← card_center_GL2, ← Subgroup.card_eq_card_quotient_mul_card_subgroup,
      Matrix.card_GL_field 2, Fin.prod_univ_two, Fin.val_zero, Fin.val_one,
      pow_zero, pow_one]
  rw [show Fintype.card F ^ 2 - Fintype.card F = Fintype.card F * (Fintype.card F - 1) by
        rw [Nat.pow_two, Nat.mul_sub_left_distrib, Nat.mul_one]]
  rw [← mul_assoc, mul_comm (Fintype.card F ^ 2 - 1), card_center_GL2]

end CardPGL

end Dickson
