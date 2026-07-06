/-
Copyright (c) 2026 Duxing Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Duxing Yang
-/
module

public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.Module.ZMod
public import FLT.Slop.PGL2.FiniteSubgroups.CyclicPartition
public import FLT.Slop.PGL2.FiniteSubgroups.NatClassEquation
public import FLT.Slop.PGL2.FiniteSubgroups.PGLBasic

/-!
# Dickson's classification: the tame case

This file classifies the finite subgroups `G` of `PGL p = PGL₂(𝔽̄_p)` of order coprime
to `p` (the *tame* case): the main theorem `Dickson.classification_tame_slop` shows any
such `G` is cyclic, dihedral, or isomorphic to `A₄`, `S₄` or `A₅`.

The proof is via the class equation. Every nontrivial element of `G` fixes exactly two
points of `ℙ¹(𝔽̄_p)` (`Dickson.tame_ncard_fixedPoints_eq_two`), and the stabilizers
`Dickson.pairStabilizer` of the resulting pairs are cyclic with normalizers of index at
most 2. Counting elements (`Dickson.orbitPartitionData`) yields the classical
constraint `∑ i, (1 - 1/dᵢ) ≤ 2 (1 - 1/n)` on at most three "partition types", whose
solutions (`r1Solution`, `r2Solutions`, `r3SolutionsUnsorted`) correspond exactly to
the cyclic, dihedral, `A₄`, `S₄` and `A₅` cases, recognised via the cyclic-partition
machinery of `FLT.Slop.PGL2.FiniteSubgroups.CyclicPartition`.
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

open scoped BigOperators Nat Pointwise

noncomputable section

variable (p : ℕ) [Fact (Nat.Prime p)] [h_odd : Fact (p > 2)]

theorem tame_ncard_fixedPoints_eq_two (G : Subgroup (PGL p)) [Fintype G]
    (hG_tame : ¬ (p : ℕ) ∣ Nat.card G)
    (g : PGL p) (hg : g ∈ G) (hg_ne : g ≠ 1) :
    Set.ncard (fixedPoints p g) = 2 := by

  have h_coprime : p.Coprime (orderOf g) := by
    rw [Nat.Prime.coprime_iff_not_dvd Fact.out]
    refine mt (fun h ↦ h.trans ?_) hG_tame
    rw [Subgroup.orderOf_coe ⟨g, hg⟩]
    exact orderOf_dvd_natCard (⟨g, hg⟩ : G)

  have h_fin : IsOfFinOrder g := by
    obtain ⟨n, hpos, hn⟩ := isOfFinOrder_iff_pow_eq_one.mp (isOfFinOrder_of_finite (⟨g, hg⟩ : G))
    exact isOfFinOrder_iff_pow_eq_one.mpr ⟨n, hpos, Subtype.ext_iff.mp hn⟩
  exact (fixedPoints_dichotomy p g hg_ne h_fin).2.mpr h_coprime

/-- The subgroup of `G` consisting of the elements that fix both `x` and `y` on the
projective line. -/
def pairStabilizer (G : Subgroup (PGL p)) (x y : ProjectiveLine p) : Subgroup G where
  carrier := {g : G | (g : PGL p) • x = x ∧ (g : PGL p) • y = y}
  mul_mem' {a b} ha hb :=
    ⟨by rw [Subgroup.coe_mul, mul_smul, hb.1, ha.1],
     by rw [Subgroup.coe_mul, mul_smul, hb.2, ha.2]⟩
  one_mem' := ⟨one_smul _ _, one_smul _ _⟩
  inv_mem' {g} hg :=
    ⟨by rw [Subgroup.coe_inv, inv_smul_eq_iff, hg.1],
     by rw [Subgroup.coe_inv, inv_smul_eq_iff, hg.2]⟩

lemma fixedPoints_determined (G : Subgroup (PGL p)) [Fintype G]
    (hG_tame : ¬ (p : ℕ) ∣ Nat.card G)
    (g : PGL p) (hg : g ∈ G) (hg_ne : g ≠ 1)
    (x y : ProjectiveLine p) (hxy : x ≠ y) (hfx : g • x = x) (hfy : g • y = y) :
    fixedPoints p g = {x, y} := by
  have hcard : (fixedPoints p g).ncard = 2 := tame_ncard_fixedPoints_eq_two p G hG_tame g hg hg_ne
  obtain ⟨a, b, _, hS⟩ := Set.ncard_eq_two.mp hcard
  have hx_in : x ∈ ({a, b} : Set (ProjectiveLine p)) := by rw [← hS]; exact hfx
  have hy_in : y ∈ ({a, b} : Set (ProjectiveLine p)) := by rw [← hS]; exact hfy
  rw [hS]
  rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hx_in hy_in
  rcases hx_in with rfl | rfl

  · rcases hy_in with rfl | rfl
    · exfalso; exact hxy rfl

    · rfl

  · rcases hy_in with rfl | rfl
    · exact Set.pair_comm y x

    · exfalso; exact hxy rfl

omit h_odd in
@[nolint unusedArguments]
lemma commute_of_fixedPair (G_sub : Subgroup (PGL p)) [Fintype G_sub]
    (g h : PGL p) (hg : g ∈ G_sub) (hh : h ∈ G_sub)
    (x y : ProjectiveLine p) (hxy : x ≠ y)
    (hgx : g • x = x) (hgy : g • y = y)
    (hhx : h • x = x) (hhy : h • y = y) :
    Commute g h := by
  obtain ⟨G, rfl⟩ := QuotientGroup.mk_surjective g
  obtain ⟨H, rfl⟩ := QuotientGroup.mk_surjective h
  obtain ⟨v, hv⟩ := x
  obtain ⟨w, hw⟩ := y

  have extract_eigen : ∀ {M : GL (Fin 2) (K p)} {u : Fin 2 → K p} {hu : u ≠ 0},
      (QuotientGroup.mk M : PGL p) • Projectivization.mk (K p) u hu = Projectivization.mk (K p) u
          hu →
      ∃ c : K p, M.val.mulVec u = c • u := by
    intro M u hu h_fix
    change Projectivization.mk (K p) (M • u) _ = _ at h_fix
    rw [Projectivization.mk_eq_mk_iff] at h_fix
    obtain ⟨c, hc⟩ := h_fix
    exact ⟨(c : K p), hc.symm⟩
  obtain ⟨c, hc⟩ := extract_eigen hgx
  obtain ⟨d, hd⟩ := extract_eigen hhx
  obtain ⟨e, he⟩ := extract_eigen hgy
  obtain ⟨f, hf⟩ := extract_eigen hhy

  have h_indep : LinearIndependent (K p) ![v, w] := by
    rw [linearIndependent_fin2]
    refine ⟨hw, fun a ha ↦ hxy ?_⟩
    change Projectivization.mk (K p) v hv = Projectivization.mk (K p) w hw
    rw [Projectivization.mk_eq_mk_iff]
    exact ⟨Units.mk0 a (fun ha0 ↦ hv (by rw [ha0, zero_smul] at ha; exact ha.symm)), ha⟩

  have h_basis : ∀ u : Fin 2 → K p, ∃ a b : K p, u = a • v + b • w := fun u ↦ by
    have h_span : Submodule.span (K p) (Set.range ![v, w]) = ⊤ := by
      apply Submodule.eq_top_of_finrank_eq
      rw [finrank_span_eq_card h_indep, Module.finrank_pi]
    have hu : u ∈ Submodule.span (K p) (Set.range ![v, w]) := by rw [h_span]; trivial
    obtain ⟨coeff, hu_eq⟩ := (Submodule.mem_span_range_iff_exists_fun (K p)).mp hu
    exact ⟨coeff 0, coeff 1, by rw [← hu_eq, Fin.sum_univ_two]; rfl⟩

  have h_comm_u : ∀ u : Fin 2 → K p,
      (G.val * H.val).mulVec u = (H.val * G.val).mulVec u := fun u ↦ by
    obtain ⟨a, b, rfl⟩ := h_basis u
    simp only [← Matrix.mulVec_mulVec, Matrix.mulVec_add, Matrix.mulVec_smul, hc, hd, he, hf,
        smul_smul]
    congr 1 <;> { congr 1; ring }
  rw [Commute, SemiconjBy]
  change QuotientGroup.mk (G * H) = QuotientGroup.mk (H * G)
  congr 1
  exact Units.ext (Matrix.toLin'.injective (LinearMap.ext h_comm_u))
omit h_odd in

lemma scalar_eq_one_in_PGL (g : GL (Fin 2) (K p)) (c : K p)
    (x y : ProjectiveLine p) (hxy : x ≠ y)
    (hgx : g.val.mulVec x.rep = c • x.rep) (hgy : g.val.mulVec y.rep = c • y.rep) :
    (QuotientGroup.mk g : PGL p) = 1 := by
  rw [QuotientGroup.eq_one_iff, Subgroup.mem_center_iff]

  have h_g_eq : g.val = c • (1 : Matrix (Fin 2) (Fin 2) (K p)) := by
    apply Matrix.toLin'.injective
    rw [LinearMap.ext_iff]
    intro v

    have h_span : Submodule.span (K p) (Set.range ![x.rep, y.rep]) = ⊤ := by
      apply Submodule.eq_top_of_finrank_eq
      rw [finrank_span_eq_card (by
        rw [linearIndependent_fin2]
        refine ⟨y.rep_nonzero, fun a ha ↦ hxy ?_⟩
        change a • y.rep = x.rep at ha
        rw [← Projectivization.mk_rep x, ← Projectivization.mk_rep y, Projectivization.mk_eq_mk_iff]
        exact ⟨Units.mk0 a (fun ha0 ↦ x.rep_nonzero (by rw [ha0, zero_smul] at ha; exact ha.symm)),
            ha⟩
      ), Module.finrank_pi]

    have hv : v ∈ Submodule.span (K p) (Set.range ![x.rep, y.rep]) := by
      rw [h_span]; exact Submodule.mem_top
    obtain ⟨coeff, hu_eq⟩ := (Submodule.mem_span_range_iff_exists_fun (K p)).mp hv

    have v_eq : v = coeff 0 • x.rep + coeff 1 • y.rep := by
      rw [← hu_eq, Fin.sum_univ_two]
      rfl
    change g.val.mulVec v = (c • 1 : Matrix (Fin 2) (Fin 2) (K p)).mulVec v
    rw [v_eq, Matrix.smul_mulVec, Matrix.one_mulVec]
    simp only [Matrix.mulVec_add, Matrix.mulVec_smul, hgx, hgy, smul_add]
    rw [smul_comm c (coeff 0), smul_comm c (coeff 1)]
  intro h
  exact Units.ext (by simp only [Units.val_mul, h_g_eq, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_one, Matrix.one_mul])
omit h_odd in

lemma exists_unique_normalizedLift (g : PGL p) (y : ProjectiveLine p)
    (hgy : g • y = y) :
    ∃! (g' : GL (Fin 2) (K p)),
      (QuotientGroup.mk g' : PGL p) = g ∧ g'.val.mulVec y.rep = y.rep := by

  have h_z_scalar : ∀ z : GL (Fin 2) (K p), (QuotientGroup.mk z : PGL p) = 1 → ∃ c : K p,
      z.val = c • 1 := by
    intro z hz

    have h_comm (M_mat : Matrix (Fin 2) (Fin 2) (K p))
        (hM : M_mat.det = 1) : z.val * M_mat = M_mat * z.val := by
      let M := Matrix.GeneralLinearGroup.mkOfDetNeZero M_mat (by rw [hM]; exact one_ne_zero)
      have hz_mem : z ∈ Subgroup.center (GL (Fin 2) (K p)) := by rwa [← QuotientGroup.eq_one_iff]
      have h_center := Subgroup.mem_center_iff.mp hz_mem M
      calc z.val * M_mat = z.val * M.val := rfl
      _ = (z * M).val := (Units.val_mul z M).symm
      _ = (M * z).val := by rw [h_center]
      _ = M.val * z.val := Units.val_mul M z
      _ = M_mat * z.val := rfl

    have hz1 := h_comm ![![1, 1], ![0,
        1]] (by rw [Matrix.det_fin_two]; change (1:K p)*1 - 1*0 = 1; ring)

    have hz2 := h_comm ![![1, 0], ![1,
        1]] (by rw [Matrix.det_fin_two]; change (1:K p)*1 - 0*1 = 1; ring)
    have eq1_11 := congr_fun (congr_fun hz1 1) 1
    have eq1_01 := congr_fun (congr_fun hz1 0) 1
    have eq2_00 := congr_fun (congr_fun hz2 0) 0
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
        mul_one, one_mul, zero_mul, zero_add, add_zero] at eq1_11 eq1_01 eq2_00

    have hz_01 : z.val 0 1 = 0 := by
      calc z.val 0 1 = (z.val 0 0 + z.val 0 1) - z.val 0 0 := by ring
      _ = z.val 0 0 - z.val 0 0 := by rw [eq2_00]
      _ = 0 := by ring

    have hz_10 : z.val 1 0 = 0 := by
      calc z.val 1 0 = (z.val 1 0 + z.val 1 1) - z.val 1 1 := by ring
      _ = z.val 1 1 - z.val 1 1 := by rw [eq1_11]
      _ = 0 := by ring

    have hz_11 : z.val 1 1 = z.val 0 0 := by
      calc z.val 1 1 = (z.val 0 1 + z.val 1 1) - z.val 0 1 := by ring
      _ = (z.val 0 0 + z.val 0 1) - z.val 0 1 := by rw [← eq1_01]
      _ = z.val 0 0 := by ring
    use z.val 0 0
    ext i j
    match i, j with
    | 0, 0 => change z.val 0 0 = z.val 0 0 * 1; exact (mul_one _).symm
    | 0, 1 => change z.val 0 1 = z.val 0 0 * 0; rw [mul_zero, hz_01]
    | 1, 0 => change z.val 1 0 = z.val 0 0 * 0; rw [mul_zero, hz_10]
    | 1, 1 => change z.val 1 1 = z.val 0 0 * 1; rw [mul_one, hz_11]
  obtain ⟨g₀, hg₀⟩ := QuotientGroup.mk_surjective g

  obtain ⟨d, hd_ne_zero, hd⟩ : ∃ d : K p, d ≠ 0 ∧ g₀.val.mulVec y.rep = d • y.rep := by
    have h_fix : (QuotientGroup.mk g₀ : PGL p) • Projectivization.mk (K p) y.rep y.rep_nonzero =
        Projectivization.mk (K p) y.rep y.rep_nonzero := by
      rw [Projectivization.mk_rep y, hg₀, hgy]
    change Projectivization.mk (K p)
        (g₀.val.mulVec y.rep) _ = Projectivization.mk (K p) y.rep y.rep_nonzero at h_fix
    rw [Projectivization.mk_eq_mk_iff] at h_fix
    obtain ⟨c, hc⟩ := h_fix
    exact ⟨(c : K p), c.ne_zero, hc.symm⟩

  let g' : GL (Fin 2) (K p) :=
    { val := d⁻¹ • g₀.val
      inv := d • g₀.inv
      val_inv := by
        rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ hd_ne_zero, one_smul,
            g₀.val_inv]
      inv_val := by
        rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ hd_ne_zero, one_smul,
            g₀.inv_val] }

  have hg'_mk : (QuotientGroup.mk g' : PGL p) = g := by
    rw [← hg₀, QuotientGroup.eq, Subgroup.mem_center_iff]
    intro M
    apply Units.ext
    have h_LHS : (M * (g'⁻¹ * g₀)).val = M.val * (g'⁻¹ * g₀).val := Units.val_mul M _
    have h_RHS : ((g'⁻¹ * g₀) * M).val = (g'⁻¹ * g₀).val * M.val := Units.val_mul _ M
    rw [h_LHS, h_RHS]

    have h_diff : (g'⁻¹ * g₀).val = d • 1 := by
      calc (g'⁻¹ * g₀).val = (g'⁻¹).val * g₀.val := Units.val_mul _ _
      _ = (d • g₀.inv) * g₀.val := rfl
      _ = d • (g₀.inv * g₀.val) := Matrix.smul_mul d g₀.inv g₀.val
      _ = d • 1 := by rw [g₀.inv_val]
    rw [h_diff, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul]

  have hg'_y : g'.val.mulVec y.rep = y.rep := by
    change (d⁻¹ • g₀.val).mulVec y.rep = y.rep
    rw [Matrix.smul_mulVec, hd, smul_smul, inv_mul_cancel₀ hd_ne_zero, one_smul]
  use g'
  refine ⟨⟨hg'_mk, hg'_y⟩, ?_⟩
  rintro g'' ⟨hg''_mk, hg''_y⟩
  let z := g'' * g'⁻¹

  have hz_mk : (QuotientGroup.mk z : PGL p) = 1 := by
    change (QuotientGroup.mk g'' : PGL p) * (QuotientGroup.mk g' : PGL p)⁻¹ = 1
    rw [hg''_mk, hg'_mk, mul_inv_cancel]
  obtain ⟨c, hz_val⟩ := h_z_scalar z hz_mk

  have h_g''_val : g''.val = c • g'.val := by
    calc g''.val = (g'' * 1).val := by rw [mul_one]
    _ = (g'' * (g'⁻¹ * g')).val := by rw [inv_mul_cancel]
    _ = ((g'' * g'⁻¹) * g').val := by rw [mul_assoc]
    _ = z.val * g'.val := Units.val_mul z g'
    _ = (c • 1) * g'.val := by rw [hz_val]
    _ = c • g'.val := by rw [Matrix.smul_mul, Matrix.one_mul]

  have hc1 : c = 1 := by
    have h_sub : (1 - c) • y.rep = 0 := by
      calc (1 - c) • y.rep = y.rep - c • y.rep := by rw [sub_smul, one_smul]
      _ = g''.val.mulVec y.rep - c • (g'.val.mulVec y.rep) := by rw [hg''_y, hg'_y]
      _ = (c • g'.val).mulVec y.rep - c • (g'.val.mulVec y.rep) := by rw [h_g''_val]
      _ = 0 := by rw [Matrix.smul_mulVec, sub_self]
    rcases smul_eq_zero.mp h_sub with hc_eq | hy

    · exact (sub_eq_zero.mp hc_eq).symm

    · exact absurd hy y.rep_nonzero
  apply Units.ext
  calc g''.val = c • g'.val := h_g''_val
  _ = (1 : K p) • g'.val := by rw [hc1]
  _ = g'.val := one_smul _ _
omit h_odd in

lemma pairStabilizer_isCyclic (G : Subgroup (PGL p)) [Fintype G]
    (x y : ProjectiveLine p) (hxy : x ≠ y) :
    IsCyclic (pairStabilizer p G x y) := by

  have h_norm : ∀ g : pairStabilizer p G x y, ∃ g' : GL (Fin 2) (K p),
      (QuotientGroup.mk g' : PGL p) = (g : PGL p) ∧ g'.val.mulVec y.rep = y.rep ∧
      ∀ g'',
          (QuotientGroup.mk g'' : PGL p) = (g : PGL p) → g''.val.mulVec y.rep = y.rep → g'' = g' :=
            by
    intro g
    obtain ⟨g', ⟨h1, h2⟩, h3⟩ := exists_unique_normalizedLift p (g : PGL p) y g.2.2
    exact ⟨g', h1, h2, fun g'' h1' h2' ↦ h3 g'' ⟨h1', h2'⟩⟩
  choose f hf_mk hf_y hf_uniq using h_norm

  have extract_c : ∀ g : pairStabilizer p G x y, ∃ c : K p,
      c ≠ 0 ∧ (f g).val.mulVec x.rep = c • x.rep := by
    intro g

    have h_fix : (QuotientGroup.mk (f g) : PGL p) • Projectivization.mk (K p) x.rep x.rep_nonzero =
        Projectivization.mk (K p) x.rep x.rep_nonzero := by
      rw [Projectivization.mk_rep x, hf_mk, g.2.1]
    change Projectivization.mk (K p)
        ((f g).val.mulVec x.rep) _ = Projectivization.mk (K p) x.rep x.rep_nonzero at h_fix
    rw [Projectivization.mk_eq_mk_iff] at h_fix
    obtain ⟨c, hc⟩ := h_fix
    exact ⟨c, c.ne_zero, hc.symm⟩
  choose c hc_ne_zero hc_x using extract_c

  have hf_mul : ∀ g₁ g₂ : pairStabilizer p G x y, f (g₁ * g₂) = f g₁ * f g₂ := by
    intro g₁ g₂
    symm
    apply hf_uniq (g₁ * g₂)

    · change (QuotientGroup.mk (f g₁) : PGL p) * (QuotientGroup.mk (f g₂) : PGL p) = (g₁ : PGL p) *
        (g₂ : PGL p)
      rw [hf_mk, hf_mk]

    · rw [Units.val_mul, ← Matrix.mulVec_mulVec, hf_y, hf_y]

  have hc_mul : ∀ g₁ g₂ : pairStabilizer p G x y, c (g₁ * g₂) = c g₁ * c g₂ := by
    intro g₁ g₂

    have h : (c (g₁ * g₂) - c g₁ * c g₂) • x.rep = 0 := by
      rw [sub_smul, sub_eq_zero, ← hc_x, hf_mul, Units.val_mul, ← Matrix.mulVec_mulVec,
      hc_x, Matrix.mulVec_smul, hc_x, ← mul_smul, mul_comm]
    exact sub_eq_zero.mp (Or.resolve_right (smul_eq_zero.mp h) x.rep_nonzero)

  have hf_one : f 1 = 1 := by
    symm
    apply hf_uniq 1

    · change (QuotientGroup.mk 1 : PGL p) = 1; rfl

    · rw [Units.val_one, Matrix.one_mulVec]

  have h_c_one : c 1 = 1 := by
    have hx_one : x.rep = c 1 • x.rep := by
      simpa [hf_one] using hc_x (1 : pairStabilizer p G x y)
    have h : (1 - c 1) • x.rep = 0 := by
      rw [sub_smul, one_smul]
      exact sub_eq_zero.mpr hx_one
    exact Eq.symm (sub_eq_zero.mp (Or.resolve_right (smul_eq_zero.mp h) x.rep_nonzero))
  let hom : pairStabilizer p G x y →* K p := { toFun := c, map_one' := h_c_one, map_mul' := hc_mul }

  have hom_inj : Function.Injective hom := by
    intro g₁ g₂ h_eq
    apply mul_inv_eq_one.mp
    apply Subtype.ext; apply Subtype.ext

    have h_div : c (g₁ * g₂⁻¹) = 1 := by
      rw [hc_mul, show c g₁ = c g₂ from h_eq, ← hc_mul, mul_inv_cancel, h_c_one]
    exact (hf_mk (g₁ * g₂⁻¹)).symm.trans <|
      scalar_eq_one_in_PGL p (f (g₁ * g₂⁻¹)) 1 x y hxy
        (by rw [hc_x, h_div, one_smul]) (by rw [hf_y, one_smul])
  exact isCyclic_of_injective_ringHom hom hom_inj

lemma disjoint_fixedPairs (G : Subgroup (PGL p)) [Fintype G]
    (hG_tame : ¬ (p : ℕ) ∣ Nat.card G)
    (x y x' y' : ProjectiveLine p) (hxy : x ≠ y) (hx'y' : x' ≠ y')
    (hpairs : ({x, y} : Set (ProjectiveLine p)) ≠ {x', y'})
    (g : PGL p) (hg : g ∈ G) (hg_ne : g ≠ 1)
    (hfx : g • x = x) (hfy : g • y = y) (hfx' : g • x' = x') (hfy' : g • y' = y') :
    False := by
  let S := Function.fixedPoints (HSMul.hSMul g : ProjectiveLine p → ProjectiveLine p)
  have h2 := tame_ncard_fixedPoints_eq_two p G hG_tame g hg hg_ne

  have h_eq : ∀ {u v : ProjectiveLine p}, u ≠ v → u ∈ S → v ∈ S → S = {u, v} := by
    intro u v huv hu hv
    obtain ⟨a, b, _, hS⟩ : ∃ a b, a ≠ b ∧ S = {a, b} := Set.ncard_eq_two.mp h2
    rw [hS] at hu hv ⊢
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hu hv
    rcases hu with rfl | rfl

    · rcases hv with rfl | rfl
      · exact absurd rfl huv

      · rfl

    · rcases hv with rfl | rfl
      · ext z
        rw [Set.mem_insert_iff, Set.mem_singleton_iff]
        exact ⟨Or.symm, Or.symm⟩

      · exact absurd rfl huv
  exact hpairs ((h_eq hxy hfx hfy).symm.trans (h_eq hx'y' hfx' hfy'))

lemma normalizer_permutes_pair (G : Subgroup (PGL p)) [Fintype G]
    (hG_tame : ¬ (p : ℕ) ∣ Nat.card G)
    (x y : ProjectiveLine p) (hxy : x ≠ y)
    (n : (Subgroup.normalizer (SetLike.coe (pairStabilizer p G x y))))
    (hne : ∃ g : pairStabilizer p G x y, g ≠ 1) :
    ((n : G).val • x = x ∧ (n : G).val • y = y) ∨
    ((n : G).val • x = y ∧ (n : G).val • y = x) := by
  obtain ⟨g, hg_ne⟩ := hne

  have h_fix_set : fixedPoints p (g : G).val = {x, y} :=
    fixedPoints_determined p G hG_tame (g : G).val (g : G).property
      (fun h ↦ hg_ne (Subtype.ext (Subtype.ext h))) x y hxy g.2.1 g.2.2
  have hn_mem := (Subgroup.mem_normalizer_iff.mp n.property (g : G)).mp g.property

  have h_prop {z : ProjectiveLine p} (hz : (((n : G) * (g : G) * (n : G)⁻¹ : G) : PGL p) • z = z) :
      (n : G).val⁻¹ • z ∈ ({x, y} : Set (ProjectiveLine p)) := by
    rw [← h_fix_set]
    change (g : G).val • ((n : G).val⁻¹ • z) = (n : G).val⁻¹ • z
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, mul_smul, mul_smul] at hz
    rw [← one_smul (PGL p) ((g : G).val • ((n : G).val⁻¹ • z)), ← inv_mul_cancel (n : G).val,
        mul_smul, hz]
  have hnx := h_prop hn_mem.1
  have hny := h_prop hn_mem.2
  rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hnx hny

  have h_eq_smul {z w : ProjectiveLine p} (h : (n : G).val⁻¹ • z = w) : (n : G).val • w = z := by
    rw [← h, ← mul_smul, mul_inv_cancel (n : G).val, one_smul]
  rcases hnx with hnx_x | hnx_y

  · rcases hny with hny_x | hny_y
    · exact absurd (by rw [← h_eq_smul hnx_x, h_eq_smul hny_x]) hxy

    · exact Or.inl ⟨h_eq_smul hnx_x, h_eq_smul hny_y⟩

  · rcases hny with hny_x | hny_y
    · exact Or.inr ⟨h_eq_smul hny_x, h_eq_smul hnx_y⟩

    · exact absurd (by rw [← h_eq_smul hnx_y, h_eq_smul hny_y]) hxy

lemma normalizer_pairStabilizer_index_le_two (G : Subgroup (PGL p)) [Fintype G]
    (hG_tame : ¬ (p : ℕ) ∣ Nat.card G)
    (x y : ProjectiveLine p) (hxy : x ≠ y)
    (hne : ∃ g : pairStabilizer p G x y, g ≠ 1) :
    ((pairStabilizer p G x y).subgroupOf (Subgroup.normalizer (SetLike.coe (pairStabilizer p G x y)))).index ≤ 2 := by
  let N := (Subgroup.normalizer (SetLike.coe (pairStabilizer p G x y)))
  let H_sub := (pairStabilizer p G x y).subgroupOf N

  have h_perm (n : N) : ((n : G).val • x = x ∧ (n : G).val • y = y) ∨ ((n : G).val • x = y ∧ (n :
      G).val • y = x) :=
    normalizer_permutes_pair p G hG_tame x y hxy n hne
  by_cases hk : ∃ k : N, ((k : G).val • x = y ∧ (k : G).val • y = x)

  · obtain ⟨k, hk_swap⟩ := hk
    let Q := N ⧸ H_sub

    have h_all : ∀ q : Q, q = 1 ∨ q = QuotientGroup.mk k := by
      rintro ⟨n⟩
      rcases h_perm n with h_fix | h_swap

      · exact Or.inl (QuotientGroup.eq_one_iff n |>.mpr h_fix)

      · apply Or.inr
        apply QuotientGroup.eq.mpr
        rw [Subgroup.mem_subgroupOf]
        change ((n : G).val⁻¹ * (k : G).val) • x = x ∧ ((n : G).val⁻¹ * (k : G).val) • y = y
        exact ⟨by rw [mul_smul, hk_swap.1, ← h_swap.1, inv_smul_smul], by rw [mul_smul, hk_swap.2,
            ← h_swap.2, inv_smul_smul]⟩
    let S : Finset Q := {1, QuotientGroup.mk k}

    have h_univ : (Finset.univ : Finset Q) ⊆ S := fun q _ ↦ by
      rw [Finset.mem_insert, Finset.mem_singleton]
      exact h_all q
    change Nat.card Q ≤ 2
    rw [Nat.card_eq_fintype_card]
    exact (Finset.card_le_card h_univ).trans ((Finset.card_insert_le 1 _).trans_eq
        (by rw [Finset.card_singleton]))

  · push Not at hk
    have H_top : H_sub = ⊤ := by
      apply eq_top_iff.mpr
      intro n _
      rw [Subgroup.mem_subgroupOf]
      rcases h_perm n with h_fix | h_swap

      · exact h_fix

      · exact absurd h_swap.2 (hk n h_swap.1)
    change H_sub.index ≤ 2
    rw [H_top, Subgroup.index_top]
    omega

lemma mem_pairStabilizer_of_ne_one (G : Subgroup (PGL p)) [Fintype G]
    (hG_tame : ¬ (p : ℕ) ∣ Nat.card G)
    (g : G) (hg_ne : g ≠ 1) :
    ∃ (x y : ProjectiveLine p), x ≠ y ∧ g ∈ pairStabilizer p G x y := by

  obtain ⟨x, y, hxy, hfp⟩ := Set.ncard_eq_two.mp <|
    tame_ncard_fixedPoints_eq_two p G hG_tame (g : PGL p) g.property (fun h ↦ hg_ne (Subtype.ext h))
  exact ⟨x, y, hxy,
    show x ∈ fixedPoints p ↑g by rw [hfp]; exact Set.mem_insert x _,
    show y ∈ fixedPoints p ↑g by rw [hfp]; exact Set.mem_insert_of_mem x (Set.mem_singleton y)⟩
omit h_odd in

@[nolint unusedArguments]
lemma pairStabilizer_conj (G : Subgroup (PGL p)) [Fintype G]
    (x y : ProjectiveLine p) (h : G) :
    (pairStabilizer p G x y).map (MulAut.conj h).toMonoidHom =
    pairStabilizer p G ((h : PGL p) • x) ((h : PGL p) • y) := by
  ext g
  constructor

  · rintro ⟨g', hg', rfl⟩
    have h_eq (z : ProjectiveLine p)
        (hz : (g' : PGL p) • z = z) : ((h * g' * h⁻¹ : G) : PGL p) • ((h : PGL p) • z) = (h : PGL
            p) • z := by
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, mul_smul, inv_smul_smul, mul_smul,
          hz]
    exact ⟨h_eq x hg'.1, h_eq y hg'.2⟩

  · intro hg
    have h_eq (z : ProjectiveLine p)
        (hz : (g : PGL p) • ((h : PGL p) • z) = (h : PGL p) • z) : ((h⁻¹ * (g * h) : G) : PGL p) •
            z = z := by
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, mul_smul, mul_smul, hz,
          inv_smul_smul]
    exact ⟨h⁻¹ * (g * h), ⟨h_eq x hg.1, h_eq y hg.2⟩,
      show h * (h⁻¹ * (g * h)) * h⁻¹ = g by rw [← mul_assoc h h⁻¹, mul_inv_cancel, one_mul,
          mul_assoc, mul_inv_cancel, mul_one]⟩

lemma conjugate_pairStabilizer_disjoint (G : Subgroup (PGL p)) [Fintype G]
    (hG_tame : ¬ (p : ℕ) ∣ Nat.card G)
    (H₁ H₂ : Subgroup G)
    (hH₁ : ∃ x y : ProjectiveLine p, x ≠ y ∧ H₁ = pairStabilizer p G x y)
    (hH₂ : ∃ x y : ProjectiveLine p, x ≠ y ∧ H₂ = pairStabilizer p G x y)
    (g₁ g₂ : G)
    (hne : H₁.map (MulAut.conj g₁).toMonoidHom ≠ H₂.map (MulAut.conj g₂).toMonoidHom) :
    H₁.map (MulAut.conj g₁).toMonoidHom ⊓ H₂.map (MulAut.conj g₂).toMonoidHom = ⊥ := by
  obtain ⟨x₁, y₁, hxy₁, rfl⟩ := hH₁
  obtain ⟨x₂, y₂, hxy₂, rfl⟩ := hH₂
  let x₁' := (g₁ : PGL p) • x₁
  let y₁' := (g₁ : PGL p) • y₁
  let x₂' := (g₂ : PGL p) • x₂
  let y₂' := (g₂ : PGL p) • y₂

  have h_inj (g : G) (x y : ProjectiveLine p) (hxy : x ≠ y) : (g : PGL p) • x ≠ (g : PGL p) • y :=
    fun h ↦ hxy <| by rw [← inv_smul_smul (g : PGL p) x, h, inv_smul_smul]
  rw [pairStabilizer_conj, pairStabilizer_conj] at hne ⊢
  by_contra h_not_bot

  obtain ⟨g, ⟨hg1, hg2⟩, hg_ne⟩ : ∃ g : G,
      g ∈ pairStabilizer p G x₁' y₁' ⊓ pairStabilizer p G x₂' y₂' ∧ g ≠ 1 := by
    by_contra h_none
    apply h_not_bot
    ext z
    exact ⟨fun hz ↦ by_contra fun hz_ne ↦ h_none ⟨z, hz, hz_ne⟩, fun h ↦ h ▸ Subgroup.one_mem _⟩

  have h_set_eq : ({x₁', y₁'} : Set (ProjectiveLine p)) = {x₂', y₂'} := by
    have hg_ne_val : (g : PGL p) ≠ 1 := fun h ↦ hg_ne (Subtype.ext h)
    exact (fixedPoints_determined p G hG_tame g g.property hg_ne_val x₁' y₁'
      (h_inj g₁ x₁ y₁ hxy₁) hg1.1 hg1.2).symm.trans
      (fixedPoints_determined p G hG_tame g g.property hg_ne_val x₂' y₂'
      (h_inj g₂ x₂ y₂ hxy₂) hg2.1 hg2.2)
  have hx1 : x₁' ∈ ({x₂', y₂'} : Set (ProjectiveLine p)) := h_set_eq ▸ Set.mem_insert x₁' {y₁'}

  have hy1 : y₁' ∈ ({x₂',
      y₂'} : Set (ProjectiveLine p)) := h_set_eq ▸ Set.mem_insert_of_mem x₁' (Set.mem_singleton y₁')
  rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hx1 hy1
  rcases hx1 with hx_x | hx_y

  · rcases hy1 with hy_x | hy_y
    · exact h_inj g₁ x₁ y₁ hxy₁ (hx_x.trans hy_x.symm)

    · exact hne (by change pairStabilizer p G x₁' y₁' = pairStabilizer p G x₂' y₂'; rw [hx_x, hy_y])

  · rcases hy1 with hy_x | hy_y
    · exact hne <| by
        change pairStabilizer p G x₁' y₁' = pairStabilizer p G x₂' y₂'
        rw [hx_y, hy_x]
        ext z
        exact ⟨fun h ↦ ⟨h.2, h.1⟩, fun h ↦ ⟨h.2, h.1⟩⟩

    · exact h_inj g₁ x₁ y₁ hxy₁ (hx_y.trans hy_y.symm)

lemma classEquation_nat_to_rat (n r : ℕ) (d f : Fin r → ℕ)
    (hn : n ≥ 2) (hd : ∀ i, d i ≥ 2) (hf : ∀ i, f i ≥ 1)
    (hdiv : ∀ i, f i * d i ∣ n)
    (hnat : n - 1 = ∑ i : Fin r, (n / (f i * d i)) * (d i - 1)) :
    (∑ i : Fin r, (1 : ℚ) / (f i) * (1 - 1 / (d i))) = 1 - 1 / ↑n := by
  have hn0 : (n : ℚ) ≠ 0 := by positivity
  have h1 : 1 - 1 / (n : ℚ) = ((n : ℚ) - 1) / n := by rw [sub_div, div_self hn0]
  rw [h1, ← Nat.cast_one, ← Nat.cast_sub (by omega), hnat, Nat.cast_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  have hdi := hd i
  have hfi := hf i
  have hd0 : (d i : ℚ) ≠ 0 := by positivity
  have h2 : 1 - 1 / (d i : ℚ) = ((d i : ℚ) - 1) / d i := by rw [sub_div, div_self hd0]
  rw [Nat.cast_mul, Nat.cast_sub (by omega), Nat.cast_one, Nat.cast_div (hdiv i),
      Nat.cast_mul, h2, one_div, inv_mul_eq_div, div_div, mul_comm (d i : ℚ) (f i : ℚ),
      div_mul_eq_mul_div, div_div, mul_comm (f i * d i : ℚ) n, mul_div_mul_left _ _ hn0, ← div_div]
  exact ne_of_gt (by positivity)

@[nolint unusedArguments]
lemma normalizer_card_eq_index_mul {G : Type*} [Group G] [Fintype G]
    (H : Subgroup G) :
    Nat.card (Subgroup.normalizer (SetLike.coe H)) = (H.subgroupOf (Subgroup.normalizer (SetLike.coe H))).index * Nat.card H := by

  have h_congr : Nat.card (H.subgroupOf (Subgroup.normalizer (SetLike.coe H))) = Nat.card H := Nat.card_congr
    { toFun := fun x ↦ ⟨x.val.val, x.property⟩
      invFun := fun x ↦ ⟨⟨x.val, Subgroup.le_normalizer x.property⟩, x.property⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  rw [← h_congr]
  exact (Subgroup.index_mul_card _).symm

lemma finQuotientReps {α : Type*} [Fintype α] (s : Setoid α) :
    ∃ (r : ℕ) (reps : Fin r → α),
      (∀ x : α, ∃ i, s.r x (reps i)) ∧
      (∀ i j, s.r (reps i) (reps j) → i = j) := by
  let e := Fintype.equivFin (Quotient s)
  refine ⟨Fintype.card (Quotient s), fun i ↦ Quotient.out (e.symm i),
    fun x ↦ ⟨e (Quotient.mk s x), ?_⟩,
    fun i j hij ↦ e.symm.injective ?_⟩

  · change s.r x (Quotient.out (e.symm (e (Quotient.mk s x))))
    rw [e.symm_apply_apply]
    exact Setoid.symm (Quotient.exact (Quotient.out_eq (Quotient.mk s x)))

  · exact (Quotient.out_eq (e.symm i)).symm.trans ((Quotient.sound hij).trans (Quotient.out_eq
      (e.symm j)))

omit h_odd in
lemma orbitPartitionConstruction (G : Subgroup (PGL p)) [Fintype G]
    (_hG_tame : ¬ (p : ℕ) ∣ Nat.card G)
    (_hG_nontrivial : Nontrivial G) :
    ∃ (r : ℕ) (xrep yrep : Fin r → ProjectiveLine p),
      (∀ i, xrep i ≠ yrep i) ∧
      (∀ i, Nontrivial (pairStabilizer p G (xrep i) (yrep i))) ∧
      (∀ (a b : ProjectiveLine p), a ≠ b → Nontrivial (pairStabilizer p G a b) →
        ∃ (i : Fin r) (g : G),
          pairStabilizer p G a b =
            (pairStabilizer p G (xrep i) (yrep i)).map (MulAut.conj g).toMonoidHom) ∧
      (∀ i j : Fin r, (∃ g : G,
          (pairStabilizer p G (xrep i) (yrep i)).map (MulAut.conj g).toMonoidHom =
            pairStabilizer p G (xrep j) (yrep j)) → i = j) := by

  let StabType := {H : Subgroup G // ∃ x y : ProjectiveLine p,
      x ≠ y ∧ H = pairStabilizer p G x y ∧ Nontrivial H}
  let R (A B : StabType) : Prop := ∃ g : G, B.val = A.val.map (MulAut.conj g).toMonoidHom

  have h_refl : ∀ A : StabType, R A A := fun A ↦ ⟨1, by
    have h_id : (MulAut.conj (1 : G)).toMonoidHom = MonoidHom.id G := by
      ext x; have hx : (((MulAut.conj (1 : G)).toMonoidHom) x : G) = 1 * x * 1⁻¹ := rfl
      rw [hx, inv_one, one_mul, mul_one]; rfl
    rw [h_id, Subgroup.map_id]⟩

  have h_symm : ∀ {A B : StabType}, R A B → R B A := fun {A B} ⟨g, hg⟩ ↦ ⟨g⁻¹, by
    rw [hg, Subgroup.map_map]

    have h_comp_id : (MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom = MonoidHom.id
        G := by
      ext x; have hx : (((MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom) x : G) =
          g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ := rfl
      rw [hx, inv_inv, ← mul_assoc g⁻¹ (g * x) g⁻¹, ← mul_assoc g⁻¹ g x, inv_mul_cancel, one_mul,
          mul_assoc, inv_mul_cancel, mul_one]; rfl
    rw [h_comp_id, Subgroup.map_id]⟩

  have h_trans : ∀ {A B C : StabType}, R A B → R B C → R A C := fun {A B C} ⟨g1, hg1⟩ ⟨g2,
      hg2⟩ ↦ ⟨g2 * g1, by
    rw [hg2, hg1, Subgroup.map_map]

    have h_comp : (MulAut.conj g2).toMonoidHom.comp (MulAut.conj g1).toMonoidHom = (MulAut.conj (g2
        * g1)).toMonoidHom := by
      ext x

      have h1 : (((MulAut.conj g2).toMonoidHom.comp (MulAut.conj g1).toMonoidHom) x : G) = g2 * (g1
          * x * g1⁻¹) * g2⁻¹ := rfl
      have h2 : (((MulAut.conj (g2 * g1)).toMonoidHom) x : G) = (g2 * g1) * x * (g2 * g1)⁻¹ := rfl
      rw [h1, h2, ← mul_assoc g2 (g1 * x) g1⁻¹, ← mul_assoc g2 g1 x,
          mul_assoc ((g2 * g1) * x) g1⁻¹ g2⁻¹, ← mul_inv_rev]
    rw [h_comp]⟩
  let s : Setoid StabType := { r := R, iseqv := ⟨h_refl, h_symm, h_trans⟩ }
  obtain ⟨r, reps, h_cover, h_inj⟩ := finQuotientReps s
  choose xrep yrep hxy_rep heq_rep hnontriv_rep using fun i ↦ (reps i).property
  exact ⟨r, xrep, yrep, hxy_rep,
    fun i ↦ by rw [← heq_rep i]; exact hnontriv_rep i,
    fun a b hab hnontriv ↦ by
      obtain ⟨i, hi⟩ := h_cover ⟨pairStabilizer p G a b, a, b, hab, rfl, hnontriv⟩
      obtain ⟨g, hg⟩ := h_symm hi
      exact ⟨i, g, by rw [heq_rep i] at hg; exact hg⟩,
    fun i j ⟨g, hg⟩ ↦ h_inj i j ⟨g, by rw [← heq_rep i, ← heq_rep j] at hg; exact hg.symm⟩⟩

lemma orbitPartitionData (G : Subgroup (PGL p)) [Fintype G]
    (hG_tame : ¬ (p : ℕ) ∣ Nat.card G)
    (hG_nontrivial : Nontrivial G) :
    ∃ (r : ℕ) (d f : Fin r → ℕ)
      (H : Fin r → Subgroup ↥G),
      (∀ i, IsCyclic (H i)) ∧
      (∀ i, Nat.card (H i) = d i) ∧
      (∀ i, d i ≥ 2) ∧
      (∀ i, f i = 1 ∨ f i = 2) ∧
      (∀ i, f i * d i ∣ Nat.card ↥G) ∧
      (∀ i, Nat.card ((Subgroup.normalizer (SetLike.coe (H i)))) = f i * d i) ∧
      (∀ K L : Subgroup ↥G,
        (∃ (i : Fin r) (g : ↥G), K = (H i).map (MulAut.conj g).toMonoidHom) →
        (∃ (j : Fin r) (h : ↥G), L = (H j).map (MulAut.conj h).toMonoidHom) →
        K ≠ L → K ⊓ L = ⊥) ∧
      (∀ x : ↥G, x ≠ 1 →
        ∃ K : Subgroup ↥G, (∃ (i : Fin r) (g : ↥G),
          K = (H i).map (MulAut.conj g).toMonoidHom) ∧ x ∈ K) ∧
      (∑ i : Fin r, (1 : ℚ) / (f i) * (1 - 1 / (d i))) =
        1 - 1 / (Nat.card ↥G) := by

  obtain ⟨r, xrep, yrep, hxy, hnt, horbit, hinj⟩ :=
    orbitPartitionConstruction p G hG_tame hG_nontrivial
  let H : Fin r → Subgroup ↥G := fun i ↦ pairStabilizer p G (xrep i) (yrep i)
  let d : Fin r → ℕ := fun i ↦ Nat.card (H i)
  let f : Fin r → ℕ := fun i ↦ (H i).subgroupOf (Subgroup.normalizer (SetLike.coe (H i))) |>.index

  have hd_ge : ∀ i, d i ≥ 2 := by
    intro i
    change Nat.card (H i) ≥ 2
    rw [Nat.card_eq_fintype_card]
    exact Fintype.one_lt_card

  have hdisjoint : ∀ K L : Subgroup ↥G,
      (∃ (i : Fin r) (g : ↥G), K = (H i).map (MulAut.conj g).toMonoidHom) →
      (∃ (j : Fin r) (h : ↥G), L = (H j).map (MulAut.conj h).toMonoidHom) →
      K ≠ L → K ⊓ L = ⊥ := by
    rintro K L ⟨i, g, rfl⟩ ⟨j, h, rfl⟩ hne
    exact conjugate_pairStabilizer_disjoint p G hG_tame _ _ ⟨xrep i, yrep i, hxy i, rfl⟩ ⟨xrep j,
        yrep j, hxy j, rfl⟩ _ _ hne

  have hcover : ∀ x : ↥G, x ≠ 1 →
      ∃ K : Subgroup ↥G, (∃ (i : Fin r) (g : ↥G),
          K = (H i).map (MulAut.conj g).toMonoidHom) ∧ x ∈ K := fun x hx ↦ by
    obtain ⟨a, b, hab, hstab⟩ := mem_pairStabilizer_of_ne_one p G hG_tame x hx

    obtain ⟨i, g, hig⟩ := horbit a b hab (nontrivial_of_ne ⟨x,
        hstab⟩ 1 (fun h ↦ hx (congrArg Subtype.val h)))
    exact ⟨pairStabilizer p G a b, ⟨i, g, hig⟩, hstab⟩
  refine ⟨r, d, f, H,
    fun i ↦ pairStabilizer_isCyclic p G (xrep i) (yrep i) (hxy i),
    fun i ↦ rfl,
    hd_ge,
    fun i ↦ by
      obtain ⟨g, hg⟩ := exists_ne (1 : H i)

      have h1 : f i ≤ 2 :=
        normalizer_pairStabilizer_index_le_two p G hG_tame (xrep i) (yrep i) (hxy i) ⟨g, hg⟩
      have hz : f i ≠ 0 := Subgroup.index_ne_zero_of_finite (H := (H i).subgroupOf (Subgroup.normalizer (SetLike.coe (H i))))
      omega,
    fun i ↦ by
      rw [← normalizer_card_eq_index_mul (H i)]
      exact Subgroup.card_subgroup_dvd_card _,
    fun i ↦ normalizer_card_eq_index_mul (H i),
    hdisjoint,
    hcover,
    ?_⟩

  have hnat' : Nat.card ↥G - 1 = ∑ i : Fin r, (Nat.card ↥G / (f i * d i)) * (d i - 1) := by
    rw [natClassEquation r H hd_ge hdisjoint hcover (fun i j ⟨g, hg⟩ ↦ hinj i j ⟨g, hg⟩)]
    congr 1; ext i; congr 1
    have h_idx := Subgroup.index_mul_card (Subgroup.normalizer (SetLike.coe (H i)))
    rw [normalizer_card_eq_index_mul (H i)] at h_idx
    have hf_pos : f i > 0 := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
    have hd_pos : d i > 0 := by have := hd_ge i; omega
    rw [← h_idx, Nat.mul_div_cancel _ (Nat.mul_pos hf_pos hd_pos)]
  exact classEquation_nat_to_rat (Nat.card ↥G) r d f
    (by rw [Nat.card_eq_fintype_card]; exact Fintype.one_lt_card)
    hd_ge
    (fun i ↦ Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite)
    (fun i ↦ by rw [← normalizer_card_eq_index_mul (H i)]; exact Subgroup.card_subgroup_dvd_card _)
    hnat'

lemma r1Solution (d₁ f₁ n : ℕ) (hn : n ≥ 2) (hd : d₁ ≥ 2) (hf : f₁ = 1 ∨ f₁ = 2)
    (hfdn : f₁ * d₁ ∣ n)
    (hsum : (1 : ℚ) / f₁ * (1 - 1 / d₁) = 1 - 1 / n) :
    d₁ = n ∧ f₁ = 1 := by
  rcases hf with rfl | rfl

  · refine ⟨(Nat.cast_inj (R := ℚ)).mp ?_, rfl⟩
    have h : (1 : ℚ) / d₁ = 1 / n := by linarith only [hsum]
    rw [div_eq_div_iff (by positivity : (d₁ : ℚ) ≠ 0) (by positivity : (n : ℚ) ≠ 0)] at h
    linarith only [h]

  · have h_cross : 2 * d₁ = n * (d₁ + 1) := (Nat.cast_inj (R := ℚ)).mp (by
      calc ((2 * d₁ : ℕ) : ℚ) = 2 * (d₁ : ℚ) := by push_cast; ring
        _ = 2 * (d₁ : ℚ) * ((1 : ℚ) / n * n) := by
          rw [div_mul_cancel₀ 1 (by positivity : (n : ℚ) ≠ 0), mul_one]
        _ = 2 * (d₁ : ℚ) * ((1 / 2 + 1 / 2 * (1 / (d₁ : ℚ))) * n) := by
          rw [show (1 : ℚ) / n = 1 / 2 + 1 / 2 * (1 / (d₁ : ℚ)) by linarith only [hsum]]
        _ = n * ((d₁ : ℚ) + ((1 : ℚ) / (d₁ : ℚ)) * (d₁ : ℚ)) := by ring
        _ = n * ((d₁ : ℚ) + 1) := by
          rw [div_mul_cancel₀ 1 (by positivity : (d₁ : ℚ) ≠ 0)]
        _ = ((n * (d₁ + 1) : ℕ) : ℚ) := by push_cast; ring)

    have : d₁ + 1 ≤ 1 := Nat.le_of_mul_le_mul_left
      (calc 2 * d₁ * (d₁ + 1) ≤ n * (d₁ + 1) :=
            Nat.mul_le_mul_right _ (Nat.le_of_dvd (by omega) hfdn)
        _ = 2 * d₁ * 1 := by omega) (by omega)
    omega

lemma r2Solutions (d f : Fin 2 → ℕ) (n : ℕ) (hn : n ≥ 2)
    (hd : ∀ i, d i ≥ 2) (hf : ∀ i, f i = 1 ∨ f i = 2)
    (hdn : ∀ i, f i * d i ∣ n)
    (hsum : (∑ i : Fin 2, (1 : ℚ) / (f i) * (1 - 1 / (d i))) = 1 - 1 / n) :
    (∃ (a b : Fin 2), a ≠ b ∧ f a = 2 ∧ f b = 1 ∧ d b = 2 ∧ n = 2 * d a) ∨
    (∃ (a b : Fin 2), a ≠ b ∧ f a = 2 ∧ d a = 2 ∧ f b = 1 ∧ d b = 3 ∧ n = 12) := by

  have hsum' : (1 : ℚ) / f 0 * (1 - 1 / d 0) + (1 : ℚ) / f 1 * (1 - 1 / d 1) = 1 - 1 / n := by
    rwa [Fin.sum_univ_two] at hsum
  have hn0 : (n : ℚ) ≠ 0 := by positivity

  have h_n_of (c : ℚ) (hc : c ≠ 0) (h : (1 : ℚ) / n = 1 / c) : (n : ℚ) = c := by
    rw [div_eq_div_iff hn0 hc] at h; linarith only [h]
  rcases hf 0 with hf0 | hf0 <;> rcases hf 1 with hf1 | hf1

  ·
    rw [hf0, hf1] at hsum'; simp only [Nat.cast_one, div_one, one_mul] at hsum'

    have h_leq : (1 : ℚ) / d 0 + 1 / d 1 ≤ 1 :=
      calc _ ≤ 1 / (2 : ℚ) + 1 / 2 := by gcongr; exact Nat.cast_le.mpr (hd 0); exact Nat.cast_le.mpr (hd 1)
        _ = 1 := by norm_num
    linarith only [hsum', h_leq, div_pos (by norm_num : (0:ℚ) < 1) (by positivity : (0:ℚ) < n)]

  ·
    rw [hf0, hf1] at hsum'; simp only [Nat.cast_one, Nat.cast_two, div_one, one_mul] at hsum'

    have h_inv_sum : (1 : ℚ) / n + 1 / 2 = 1 / d 0 + 1 / (2 * (d 1 : ℚ)) := by
      calc (1 : ℚ) / n + 1 / 2 = (1 - (1 - 1 / (n : ℚ))) + 1 / 2 := by ring
        _ = (1 - ((1 : ℚ) - 1 / d 0 + 1 / 2 * (1 - 1 / d 1))) + 1 / 2 := by rw [hsum']
        _ = 1 / d 0 + 1 / (2 * (d 1 : ℚ)) := by ring

    have h_d0_le : d 0 ≤ 3 := by
      by_contra! h

      have h_leq : (1 : ℚ) / d 0 + 1 / (2 * (d 1 : ℚ)) ≤ 1 / 2 := by
        calc (1 : ℚ) / d 0 + 1 / (2 * (d 1 : ℚ)) ≤ 1 / 4 + 1 / 4 := by
              gcongr; exact_mod_cast show d 0 ≥ 4 by omega
              exact_mod_cast show 2 * d 1 ≥ 4 by have := hd 1; omega
          _ = 1 / 2 := by norm_num
      linarith only [h_inv_sum, h_leq, div_pos (by norm_num : (0:ℚ) < 1) (by positivity : (0:ℚ) < n)]
    have hd0_ge : d 0 ≥ 2 := hd 0
    interval_cases h0 : d 0

    · left; refine ⟨1, 0, by norm_num, hf1, hf0, h0, ?_⟩
      exact_mod_cast h_n_of (2 * (d 1 : ℚ)) (by have := hd 1; positivity) (by linarith only [h_inv_sum])

    · have h1 : d 1 = 2 := by
        have : d 1 ≤ 2 := by
          by_contra! h

          have h_leq: (1 : ℚ) / (2 * (d 1 : ℚ)) ≤ 1 / 6 := by
            gcongr; exact_mod_cast show 2 * d 1 ≥ 6 by omega
          linarith only [h_inv_sum, h_leq, div_pos (by norm_num : (0:ℚ) < 1) (by positivity : (0:ℚ) < n)]
        have := hd 1; omega
      right; refine ⟨1, 0, by norm_num, hf1, h1, hf0, h0, ?_⟩
      have h1_q : (d 1 : ℚ) = 2 := by norm_cast
      exact_mod_cast h_n_of 12 (by norm_num) (by rw [h1_q] at h_inv_sum; linarith only [h_inv_sum])

  ·
    rw [hf0, hf1] at hsum'; simp only [Nat.cast_one, Nat.cast_two, div_one, one_mul] at hsum'

    have h_inv_sum : (1 : ℚ) / n + 1 / 2 = 1 / (2 * (d 0 : ℚ)) + 1 / d 1 := by
      calc (1 : ℚ) / n + 1 / 2 = (1 - (1 - 1 / (n : ℚ))) + 1 / 2 := by ring
        _ = (1 - (1 / 2 * (1 - 1 / d 0) + ((1 : ℚ) - 1 / d 1))) + 1 / 2 := by rw [hsum']
        _ = 1 / (2 * (d 0 : ℚ)) + 1 / d 1 := by ring

    have h_d1_le : d 1 ≤ 3 := by
      by_contra! h

      have h_leq : (1 : ℚ) / (2 * (d 0 : ℚ)) + 1 / d 1 ≤ 1 / 2 := by
        calc (1 : ℚ) / (2 * (d 0 : ℚ)) + 1 / d 1 ≤ 1 / 4 + 1 / 4 := by
              gcongr; exact_mod_cast show 2 * d 0 ≥ 4 by have := hd 0; omega
              exact_mod_cast show d 1 ≥ 4 by omega
          _ = 1 / 2 := by norm_num
      linarith only [h_inv_sum, h_leq, div_pos (by norm_num : (0:ℚ) < 1) (by positivity : (0:ℚ) < n)]
    have hd1_ge : d 1 ≥ 2 := hd 1
    interval_cases h1 : d 1

    · left; refine ⟨0, 1, by norm_num, hf0, hf1, h1, ?_⟩
      exact_mod_cast h_n_of (2 * (d 0 : ℚ)) (by have := hd 0; positivity) (by linarith only [h_inv_sum])

    · have h0 : d 0 = 2 := by
        have : d 0 ≤ 2 := by
          by_contra! h

          have h_leq : (1 : ℚ) / (2 * (d 0 : ℚ)) ≤ 1 / 6 := by
            gcongr; exact_mod_cast show 2 * d 0 ≥ 6 by omega
          linarith only [h_inv_sum, h_leq, div_pos (by norm_num : (0:ℚ) < 1) (by positivity : (0:ℚ) < n)]
        have := hd 0; omega
      right; refine ⟨0, 1, by norm_num, hf0, h0, hf1, h1, ?_⟩
      have h0_q : (d 0 : ℚ) = 2 := by norm_cast
      exact_mod_cast h_n_of 12 (by norm_num) (by rw [h0_q] at h_inv_sum; linarith only [h_inv_sum])

  ·
    rw [hf0, hf1] at hsum'; simp only [Nat.cast_two] at hsum'

    have h_inv_sum : (1 : ℚ) / n = 1 / (2 * (d 0 : ℚ)) + 1 / (2 * (d 1 : ℚ)) := by
      calc (1 : ℚ) / n = 1 - (1 - 1 / (n : ℚ)) := by ring
        _ = 1 - (1 / 2 * (1 - 1 / d 0) + 1 / 2 * (1 - 1 / d 1)) := by rw [hsum']
        _ = 1 / (2 * (d 0 : ℚ)) + 1 / (2 * (d 1 : ℚ)) := by ring
    have hd0_nz : 2 * (d 0 : ℚ) ≠ 0 := by norm_cast; have := hd 0; omega
    have hd1_nz : 2 * (d 1 : ℚ) ≠ 0 := by norm_cast; have := hd 1; omega

    have h_cross : (((2 * d 0) * (2 * d 1) : ℕ) : ℚ) =
        (n : ℚ) * (2 * (d 1 : ℚ)) + (n : ℚ) * (2 * (d 0 : ℚ)) := by
      calc (((2 * d 0) * (2 * d 1) : ℕ) : ℚ)
        _ = (2 * (d 0 : ℚ)) * (2 * (d 1 : ℚ)) * ((1 : ℚ) / n * n) := by
          rw [div_mul_cancel₀ 1 hn0]; push_cast; ring
        _ = (2 * (d 0 : ℚ)) * (2 * (d 1 : ℚ)) *
            ((1 / (2 * (d 0 : ℚ)) + 1 / (2 * (d 1 : ℚ))) * n) := by rw [← h_inv_sum]
        _ = (n : ℚ) * ((2 * (d 1 : ℚ)) * ((1 : ℚ) / (2 * (d 0 : ℚ)) * (2 * (d 0 : ℚ))) +
            (2 * (d 0 : ℚ)) * ((1 : ℚ) / (2 * (d 1 : ℚ)) * (2 * (d 1 : ℚ)))) := by ring
        _ = (n : ℚ) * (2 * (d 1 : ℚ)) + (n : ℚ) * (2 * (d 0 : ℚ)) := by
          rw [div_mul_cancel₀ 1 hd0_nz, div_mul_cancel₀ 1 hd1_nz]; ring

    have h_cross_nat : (2 * d 0) * (2 * d 1) = n * (2 * d 1) + n * (2 * d 0) := by
      exact_mod_cast h_cross
    have h_leq : 2 * d 0 ≤ n := Nat.le_of_dvd (by omega) (by have h := hdn 0; rwa [hf0] at h)
    nlinarith only [h_cross_nat, Nat.mul_le_mul_right (2 * d 1) h_leq,
      Nat.mul_pos (by omega : 0 < n) (by have := hd 0; omega : 0 < 2 * d 0)]

lemma r3SolutionsUnsorted (d : Fin 3 → ℕ) (n : ℕ) (hn : n ≥ 2) (hd : ∀ i, d i ≥ 2)
    (hsum : (∑ i : Fin 3, (1 : ℚ) / (d i)) = 1 + 2 / n) :
    (∃ σ : Equiv.Perm (Fin 3),
      d (σ 0) = 2 ∧ d (σ 1) = 2 ∧ ∃ k, k ≥ 2 ∧ d (σ 2) = k ∧ n = 2 * k) ∨
    (∃ σ : Equiv.Perm (Fin 3),
      d (σ 0) = 2 ∧ d (σ 1) = 3 ∧ d (σ 2) = 3 ∧ n = 12) ∨
    (∃ σ : Equiv.Perm (Fin 3),
      d (σ 0) = 2 ∧ d (σ 1) = 3 ∧ d (σ 2) = 4 ∧ n = 24) ∨
    (∃ σ : Equiv.Perm (Fin 3),
      d (σ 0) = 2 ∧ d (σ 1) = 3 ∧ d (σ 2) = 5 ∧ n = 60) := by

  obtain ⟨σ, hσ⟩ : ∃ σ : Equiv.Perm (Fin 3), d (σ 0) ≤ d (σ 1) ∧ d (σ 1) ≤ d (σ 2) := by
    rcases le_total (d 0) (d 1) with h01 | h10

    · rcases le_total (d 1) (d 2) with h12 | h21
      · exact ⟨1, h01, h12⟩

      · rcases le_total (d 0) (d 2) with h02 | h20
        · refine ⟨Equiv.swap 1 2, ?_⟩; change d 0 ≤ d 2 ∧ d 2 ≤ d 1; exact ⟨h02, h21⟩

        · refine ⟨Equiv.swap 1 2 * Equiv.swap 0 1, ?_⟩
          change d 2 ≤ d 0 ∧ d 0 ≤ d 1; exact ⟨h20, h01⟩

    · rcases le_total (d 0) (d 2) with h02 | h20
      · refine ⟨Equiv.swap 0 1, ?_⟩; change d 1 ≤ d 0 ∧ d 0 ≤ d 2; exact ⟨h10, h02⟩

      · rcases le_total (d 1) (d 2) with h12 | h21
        · refine ⟨Equiv.swap 0 1 * Equiv.swap 1 2, ?_⟩
          change d 1 ≤ d 2 ∧ d 2 ≤ d 0; exact ⟨h12, h20⟩

        · refine ⟨Equiv.swap 0 2, ?_⟩; change d 2 ≤ d 1 ∧ d 1 ≤ d 0; exact ⟨h21, h10⟩

  have hsum' : (1 : ℚ) / d (σ 0) + 1 / d (σ 1) + 1 / d (σ 2) = 1 + 2 / n := by
    have := Equiv.sum_comp σ (fun i ↦ (1 : ℚ) / d i)
    rw [Fin.sum_univ_three] at this; exact this.trans hsum

  have hd₀ : d (σ 0) = 2 := by
    refine le_antisymm (by_contra (fun (h : ¬(d (σ 0) ≤ 2)) ↦ ?_)) (hd (σ 0))
    push Not at h

    have h_leq : (1 : ℚ) / d (σ 0) + 1 / d (σ 1) + 1 / d (σ 2) ≤ 1 :=
      calc (1 : ℚ) / d (σ 0) + 1 / d (σ 1) + 1 / d (σ 2)
        _ ≤ 1 / (d (σ 0) : ℚ) + 1 / (d (σ 0) : ℚ) + 1 / (d (σ 0) : ℚ) := by
          gcongr; exact Nat.cast_le.mpr hσ.1; exact Nat.cast_le.mpr (hσ.1.trans hσ.2)
        _ = 3 / (d (σ 0) : ℚ) := by ring
        _ ≤ 1 := by rw [div_le_one (by positivity)]; exact Nat.cast_le.mpr h
    linarith only [hsum', h_leq, div_pos (by positivity : (0 : ℚ) < 2) (by positivity : (0:ℚ) < n)]

  have hd₁_le : d (σ 1) ≤ 3 := by
    by_contra! h

    have h_leq : (1 : ℚ) / d (σ 1) + 1 / d (σ 2) ≤ 1 / 2 :=
      calc (1 : ℚ) / d (σ 1) + 1 / d (σ 2)
        _ ≤ 1 / (d (σ 1) : ℚ) + 1 / (d (σ 1) : ℚ) := by gcongr; exact Nat.cast_le.mpr hσ.2
        _ = 2 / (d (σ 1) : ℚ) := by ring
        _ ≤ 2 / 4 := by gcongr; exact Nat.cast_le.mpr h
        _ = 1 / 2 := by norm_num
    linarith only [hsum', h_leq, show (1 : ℚ) / d (σ 0) = 1 / 2 by rw [hd₀]; norm_num,
      div_pos (by positivity : (0 : ℚ) < 2) (by positivity : (0:ℚ) < n)]

  have h_n_eq (x : ℕ) (hx : x ≠ 0) (h_inv : (2 : ℚ) / n = 1 / (x : ℚ)) : n = 2 * x :=
    (Nat.cast_inj (R := ℚ)).mp (by
      rw [div_eq_div_iff (by positivity : (n : ℚ) ≠ 0) (Nat.cast_ne_zero.mpr hx)] at h_inv
      push_cast; linarith only [h_inv])
  have := hd (σ 1)
  interval_cases h₁ : d (σ 1)

  · left; refine ⟨σ, hd₀, h₁, d (σ 2), hd (σ 2), rfl, ?_⟩
    revert hsum'; simp only [hd₀, Nat.cast_ofNat]; intro hsum'
    exact h_n_eq (d (σ 2)) (by have := hd (σ 2); omega) (by linarith only [hsum'])

  · have hd₂_le : d (σ 2) ≤ 5 := by
      by_contra! h
      linarith only [hsum', show (1 : ℚ) / d (σ 2) ≤ 1 / 6 by gcongr; exact Nat.cast_le.mpr h,
        show (1 : ℚ) / d (σ 0) = 1 / 2 by rw [hd₀]; norm_num,
        show (1 : ℚ) / d (σ 1) = 1 / 3 by rw [h₁]; norm_num,
        div_pos (by positivity : (0 : ℚ) < 2) (by positivity : (0:ℚ) < n)]
    have : d (σ 2) ≥ 3 := by omega
    interval_cases h₂ : d (σ 2)

    · right; left; refine ⟨σ, hd₀, h₁, h₂, ?_⟩
      revert hsum'; simp only [hd₀, Nat.cast_ofNat]; intro hsum'
      exact h_n_eq 6 (by norm_num) (by linarith only [hsum'])

    · right; right; left; refine ⟨σ, hd₀, h₁, h₂, ?_⟩
      revert hsum'; simp only [hd₀, Nat.cast_ofNat]; intro hsum'
      exact h_n_eq 12 (by norm_num) (by linarith only [hsum'])

    · right; right; right; refine ⟨σ, hd₀, h₁, h₂, ?_⟩
      revert hsum'; simp only [hd₀, Nat.cast_ofNat]; intro hsum'
      exact h_n_eq 30 (by norm_num) (by linarith only [hsum'])

lemma dihedral2_of_hasCyclicPartition (G : Type*) [Group G] [Fintype G]
    (hN : Nat.card G = 4)
    (h : HasCyclicPartition G [{d := 2, f := 2}, {d := 2, f := 2}, {d := 2, f := 2}]) :
    Nonempty (G ≃* DihedralGroup 2) := by
  obtain ⟨H_list, _, h_H_props, _, h_covers⟩ := h

  have h_sq : ∀ x : G, x * x = 1 := fun x ↦ by
    rcases eq_or_ne x 1 with rfl | hx

    · exact mul_one 1
    obtain ⟨K, ⟨i, g, Hi_sub, h_get_sub, rfl⟩, hxK⟩ := h_covers x hx
    obtain ⟨Hi, h_get_Hi, _, h_card, _⟩ := h_H_props i
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hxK

    have h_card_sub : Nat.card Hi_sub = 2 := by
      rw [← show Hi = Hi_sub from by injection (h_get_Hi.symm.trans h_get_sub)]
      revert h_card; fin_cases i <;> exact id

    have h_y_sq : y * y = 1 := Subtype.ext_iff.mp <|
      (sq (⟨y, hy⟩ : Hi_sub)).symm.trans <| orderOf_dvd_iff_pow_eq_one.mp <|
        h_card_sub ▸ orderOf_dvd_natCard (⟨y, hy⟩ : Hi_sub)
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc _ = g * (y * y) * g⁻¹ := by group
      _ = 1 := by rw [h_y_sq]; group

  have h_comm : ∀ a b : G, a * b = b * a := fun a b ↦ by
    have h_inv : ∀ g : G, g⁻¹ = g := fun g ↦ inv_eq_of_mul_eq_one_left (h_sq g)
    rw [← h_inv (a * b), mul_inv_rev, h_inv, h_inv]
  letI : CommGroup G := { ‹Group G› with mul_comm := h_comm }
  letI : CommGroup (DihedralGroup 2) := { (inferInstance : Group (DihedralGroup 2)) with
    mul_comm :=
      fun a b ↦
          by rcases a with ⟨a⟩ | ⟨a⟩ <;> rcases b with ⟨b⟩ | ⟨b⟩ <;> fin_cases a <;> fin_cases b
              <;> decide }
  letI : Module (ZMod 2) (Additive G) := AddCommGroup.zmodModule fun x ↦ by
    rw [two_nsmul]; show x.toMul * x.toMul = 1; exact h_sq x.toMul
  letI : Module (ZMod 2) (Additive (DihedralGroup 2)) := AddCommGroup.zmodModule fun x ↦ by
    rw [two_nsmul]; show x.toMul * x.toMul = 1
    rcases x.toMul with ⟨a⟩ | ⟨a⟩ <;> fin_cases a <;> decide

  have h_frG : Module.finrank (ZMod 2) (Additive G) = 2 := by
    have h1 := Module.card_eq_pow_finrank (K := ZMod 2) (V := Additive G)
    rw [ZMod.card] at h1
    rw [show Fintype.card (Additive G) = 4 from by rw [← Nat.card_eq_fintype_card]; exact hN] at h1
    exact Nat.pow_right_injective (by norm_num) (h1.symm.trans (by norm_num))

  have h_frD : Module.finrank (ZMod 2) (Additive (DihedralGroup 2)) = 2 := by
    have h1 := Module.card_eq_pow_finrank (K := ZMod 2) (V := Additive (DihedralGroup 2))
    rw [ZMod.card, show Fintype.card (Additive (DihedralGroup 2)) = 4 from rfl] at h1
    exact Nat.pow_right_injective (by norm_num) (h1.symm.trans (by norm_num))
  let e_add := (LinearEquiv.ofFinrankEq _ _ (h_frG.trans h_frD.symm)).toAddEquiv
  exact ⟨{
    toFun := fun x ↦ (e_add (Additive.ofMul x)).toMul
    invFun := fun x ↦ (e_add.symm (Additive.ofMul x)).toMul
    left_inv := fun x ↦ congr_arg Additive.toMul (e_add.left_inv (Additive.ofMul x))
    right_inv := fun x ↦ congr_arg Additive.toMul (e_add.right_inv (Additive.ofMul x))
    map_mul' :=
      fun x y ↦ congr_arg Additive.toMul (e_add.map_add (Additive.ofMul x) (Additive.ofMul y))
  }⟩

lemma r2CaseOdd (G : Type*) [Group G] [Fintype G]
    (d : ℕ) (hd : d ≥ 2) (hn : Nat.card G = 2 * d)
    (H_a H_b : Subgroup G)
    (hHa_cyc : IsCyclic H_a) (hHa_card : Nat.card H_a = d)
    (hHb_card : Nat.card H_b = 2)
    (hHb_norm : Nat.card (Subgroup.normalizer (SetLike.coe H_b)) = 2)
    (h_disj : H_a ⊓ H_b = ⊥) :
    Odd d := by
  by_contra hd_even

  obtain ⟨k, hk⟩ : ∃ k, d = 2 * k := by
    rw [Nat.odd_iff] at hd_even; exact ⟨d / 2, by omega⟩
  obtain ⟨g, hg_gen⟩ := hHa_cyc.exists_generator

  have h_zpowers_g : Subgroup.zpowers (g : G) = H_a := by
    ext y; exact ⟨fun h ↦ let ⟨n,
        hn⟩ := Subgroup.mem_zpowers_iff.mp h; hn ▸ Subgroup.zpow_mem H_a g.property n,
      fun hy ↦ let ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (hg_gen ⟨y, hy⟩)
        have : ((g : G) ^ n) = y := congr_arg Subtype.val hn; Subgroup.mem_zpowers_iff.mpr ⟨n,
            this⟩⟩

  have hg_ord : orderOf (g : G) = d := by
    calc orderOf (g : G) = orderOf g := orderOf_injective H_a.subtype Subtype.coe_injective g
      _ = Nat.card H_a := orderOf_eq_card_of_forall_mem_zpowers hg_gen
      _ = d := hHa_card
  have hk_pos : k > 0 := by omega
  let z := (g : G) ^ k
  have hz_mem : z ∈ H_a := Subgroup.pow_mem H_a g.property k

  have hz_ord : orderOf z = 2 := by
    calc orderOf z = orderOf (g : G) / Nat.gcd (orderOf (g : G)) k := orderOf_pow (g : G)
      _ = (2 * k) / Nat.gcd (2 * k) k := by rw [hg_ord, hk]
      _ = 2 := by rw [Nat.gcd_eq_right ⟨2, mul_comm 2 k⟩]; exact Nat.mul_div_cancel 2 hk_pos

  have hz_unique : ∀ x ∈ H_a, orderOf x = 2 → x = z := fun x _ hx_ord ↦ by
    obtain ⟨n, hn_eq⟩ := Subgroup.mem_zpowers_iff.mp (by rwa [h_zpowers_g])

    have h_g_2n : (g : G) ^ ((2 : ℤ) * n) = 1 :=
      calc (g : G) ^ ((2 : ℤ) * n)
          = ((g : G) ^ n) ^ (2 : ℤ) := by
            rw [mul_comm]; exact zpow_mul (g : G) n 2
        _ = x ^ (2 : ℤ) := by rw [hn_eq]
        _ = 1 := by
          rw [show x ^ (2 : ℤ) = x ^ 2 from zpow_natCast x 2]
          exact orderOf_dvd_iff_pow_eq_one.mp (by rw [hx_ord])

    obtain ⟨c, hc_eq⟩ : ∃ c : ℤ, n = k * c := by
      have hdvd : (d : ℤ) ∣ 2 * n := by rw [← hg_ord]; exact orderOf_dvd_iff_zpow_eq_one.mpr h_g_2n
      rw [show (d : ℤ) = 2 * k from congrArg Nat.cast hk] at hdvd
      obtain ⟨c, hc⟩ := hdvd; exact ⟨c, by linarith only [hc]⟩

    have h_x_zpow : x = z ^ c := calc x = (g : G) ^ n := hn_eq.symm
      _ = ((g : G) ^ (k : ℤ)) ^ c := by rw [hc_eq, zpow_mul]
      _ = z ^ c := by rw [zpow_natCast]

    have h_z_zsq : z ^ (2 : ℤ) = 1 := by
      rw [show z ^ (2 : ℤ) = z ^ 2 from zpow_natCast z 2]
      exact orderOf_dvd_iff_pow_eq_one.mp (by rw [hz_ord])
    obtain ⟨m, rfl | rfl⟩ : ∃ m : ℤ, c = 2 * m ∨ c = 2 * m + 1 := ⟨c / 2, by omega⟩

    · exfalso
      have : orderOf x = 1 := by
        rw [h_x_zpow, zpow_mul (z:G) 2 m, h_z_zsq, one_zpow, orderOf_one]
      rw [this] at hx_ord; exact absurd hx_ord (by norm_num)

    · calc x = z ^ (2 * m + 1) := h_x_zpow
        _ = (z ^ (2 : ℤ)) ^ m * z := by rw [zpow_add, zpow_mul, zpow_one]
        _ = z := by rw [h_z_zsq, one_zpow, one_mul]

  have h_norm : H_a.Normal := Subgroup.normal_of_index_eq_two <|
    Nat.eq_of_mul_eq_mul_right (show d > 0 from by omega) <|
        calc H_a.index * d = H_a.index * Nat.card H_a := by rw [hHa_card]
      _ = Nat.card G := Subgroup.index_mul_card H_a
      _ = 2 * d := hn

  have hz_center : z ∈ Subgroup.center G := Subgroup.mem_center_iff.mpr fun y ↦ by
    have h_conj_mem : y * z * y⁻¹ ∈ H_a := h_norm.conj_mem z hz_mem y

    have h_conj_ord : orderOf (y * z * y⁻¹) = 2 := by
      have hd : orderOf (y * z * y⁻¹) ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr <| by
        have hz2 : z * z = 1 := by rw [← sq]; exact orderOf_dvd_iff_pow_eq_one.mp (by rw [hz_ord])
        rw [sq]; calc (y * z * y⁻¹) * (y * z * y⁻¹) = y * (z * z) * y⁻¹ := by group
          _ = 1 := by rw [hz2]; group

      have hn1 : orderOf (y * z * y⁻¹) ≠ 1 := fun h ↦ by
        have hz_one : z = 1 := calc z = y⁻¹ * (y * z * y⁻¹) * y := by group
          _ = 1 := by rw [orderOf_eq_one_iff.mp h]; group
        rw [hz_one, orderOf_one] at hz_ord; exact absurd hz_ord (by norm_num)
      have hn0 : orderOf (y * z * y⁻¹) ≠ 0 := fun h ↦ by rw [h] at hd; revert hd; norm_num
      have hd2: orderOf (y * z * y⁻¹) ≤ 2 := Nat.le_of_dvd (by norm_num) hd
      omega
    calc y * z = (y * z * y⁻¹) * y := by group
      _ = z * y := by rw [hz_unique _ h_conj_mem h_conj_ord]

  have hz_in_b : z ∈ H_b := by
    by_contra hz_not_b

    obtain ⟨y_sub, hy_neq⟩ := Fintype.exists_ne_of_one_lt_card
      (by rw [← Nat.card_eq_fintype_card, hHb_card]; omega) (1 : H_b)

    have hy_not_one : (y_sub : G) ≠ 1 :=
      fun h ↦ hy_neq (Subtype.ext h)

    have hz_not_one : z ≠ 1 := fun h ↦ by
      rw [h, orderOf_one] at hz_ord
      exact absurd hz_ord (by norm_num)

    have hz_norm_b : z ∈ (Subgroup.normalizer (SetLike.coe H_b)) := Subgroup.mem_normalizer_iff.mpr fun w ↦ by
      have hw : w * z = z * w := Subgroup.mem_center_iff.mp hz_center w
      rw [show z * w * z⁻¹ = w by rw [← hw]; group]

    let S : Finset (Subgroup.normalizer (SetLike.coe H_b)) := insert ⟨1, Subgroup.one_mem _⟩ (insert ⟨y_sub,
        Subgroup.le_normalizer y_sub.property⟩ {⟨z, hz_norm_b⟩})

    have hs_card : S.card = 3 := by
      rw [Finset.card_insert_of_notMem (by
            rw [Finset.mem_insert, Finset.mem_singleton]
            rintro (h | h)

            · exact hy_not_one (Subtype.ext_iff.mp h).symm

            · exact hz_not_one (Subtype.ext_iff.mp h).symm),
        Finset.card_insert_of_notMem (by
            rw [Finset.mem_singleton]
            exact fun h ↦ hz_not_b <| by
              have h_eq : (y_sub : G) = z := Subtype.ext_iff.mp h
              rw [← h_eq]; exact y_sub.property),
        Finset.card_singleton]
    have h_bound : S.card ≤ Fintype.card (Subgroup.normalizer (SetLike.coe H_b)) := Finset.card_le_univ S
    rw [hs_card, ← Nat.card_eq_fintype_card, hHb_norm] at h_bound
    omega
  have hz_bot : z = 1 := Subgroup.mem_bot.mp (h_disj ▸ Subgroup.mem_inf.mpr ⟨hz_mem, hz_in_b⟩)
  rw [hz_bot, orderOf_one] at hz_ord; exact absurd hz_ord (by norm_num)

lemma r3D233Contradiction (G : Type*) [Group G] [Fintype G]
    (hn : Nat.card G = 12)
    (H : Subgroup G) (hH_card : Nat.card H = 3)
    (hH_norm : Nat.card (Subgroup.normalizer (SetLike.coe H)) = 6) : False := by

  obtain ⟨P, hP_le⟩ := (show IsPGroup 3 H from fun x ↦ ⟨1, by
    change x ^ 3 = 1
    rw [← hH_card, Nat.card_eq_fintype_card]
    exact pow_card_eq_one⟩).exists_le_sylow

  have h_eq : H = ↑P := SetLike.ext' <| Set.eq_of_subset_of_ncard_le hP_le <| by
    show Nat.card ↑P ≤ Nat.card H
    rw [hH_card, P.card_eq_multiplicity, hn,
        Nat.factorization_eq_one (m := 4) rfl Nat.prime_three (by norm_num), pow_one]

  have h_idx : (Subgroup.normalizer (SetLike.coe H)).index = 2 := by
    have h_mul := Subgroup.index_mul_card (Subgroup.normalizer (SetLike.coe H))
    rw [hH_norm, hn] at h_mul
    omega
  have h_sylow := card_sylow_modEq_one 3 G
  rw [P.card_eq_index_normalizer, ← Sylow.coe_coe, ← h_eq, h_idx] at h_sylow
  change 2 % 3 = 1 % 3 at h_sylow
  omega

lemma buildPartition_r1 (G : Type*) [Group G] [Fintype G]
    (H : Subgroup G)
    (hcyc : IsCyclic H) (hcard : Nat.card H = Nat.card G)
    (hnorm : Nat.card (Subgroup.normalizer (SetLike.coe H)) = 1 * Nat.card G)
    (hdisj : ∀ K L : Subgroup G,
      (∃ g : G, K = H.map (MulAut.conj g).toMonoidHom) →
      (∃ h : G, L = H.map (MulAut.conj h).toMonoidHom) →
      K ≠ L → K ⊓ L = ⊥)
    (hcover : ∀ x : G, x ≠ 1 →
      ∃ K : Subgroup G, (∃ g : G, K = H.map (MulAut.conj g).toMonoidHom) ∧ x ∈ K) :
    HasCyclicPartition G [{d := Nat.card G, f := 1}] := by
  refine ⟨[H], rfl, ?_, ?_, ?_⟩

  · intro i; fin_cases i; exact ⟨H, rfl, hcyc, hcard, hnorm⟩

  · rintro K L ⟨i, g, _, hK', rfl⟩ ⟨j, h, _, hL', rfl⟩ hKL
    fin_cases i; fin_cases j; cases hK'; cases hL'
    exact hdisj _ _ ⟨g, rfl⟩ ⟨h, rfl⟩ hKL

  · intro x hx
    obtain ⟨K, ⟨g, rfl⟩, hxK⟩ := hcover x hx
    exact ⟨_, ⟨⟨0, by exact one_pos⟩, g, H, rfl, rfl⟩, hxK⟩

lemma buildPartition_r2_dihedral (G : Type*) [Group G] [Fintype G]
    (Ha Hb : Subgroup G) (da : ℕ)
    (ha_cyc : IsCyclic Ha) (hb_cyc : IsCyclic Hb)
    (ha_card : Nat.card Ha = da) (hb_card : Nat.card Hb = 2)
    (ha_norm : Nat.card (Subgroup.normalizer (SetLike.coe Ha)) = 2 * da)
    (hb_norm : Nat.card (Subgroup.normalizer (SetLike.coe Hb)) = 1 * 2)
    (hdisj : ∀ K L : Subgroup G,
      (∃ (i : Fin 2) (g : G), K = (![Ha, Hb] i).map (MulAut.conj g).toMonoidHom) →
      (∃ (j : Fin 2) (h : G), L = (![Ha, Hb] j).map (MulAut.conj h).toMonoidHom) →
      K ≠ L → K ⊓ L = ⊥)
    (hcover : ∀ x : G, x ≠ 1 →
      ∃ K : Subgroup G, (∃ (i : Fin 2) (g : G),
        K = (![Ha, Hb] i).map (MulAut.conj g).toMonoidHom) ∧ x ∈ K) :
    HasCyclicPartition G [{d := da, f := 2}, {d := 2, f := 1}] := by
  refine ⟨[Ha, Hb], rfl, ?_, ?_, ?_⟩

  · exact fun (i : Fin 2) ↦ match i with
    | 0 => ⟨Ha, rfl, ha_cyc, ha_card, ha_norm⟩
    | 1 => ⟨Hb, rfl, hb_cyc, hb_card, hb_norm⟩

  · rintro K L ⟨i, g, Hi, hK, rfl⟩ ⟨j, h, Hj, hL, rfl⟩ hKL
    have ei : Hi = ![Ha, Hb] i := by fin_cases i <;> cases hK <;> rfl
    have ej : Hj = ![Ha, Hb] j := by fin_cases j <;> cases hL <;> rfl
    exact hdisj _ _ ⟨i, g, by rw [ei]⟩ ⟨j, h, by rw [ej]⟩ hKL

  · intro x hx
    obtain ⟨K_sub, ⟨i, g, rfl⟩, hxK⟩ := hcover x hx
    exact ⟨_, ⟨i, g, ![Ha, Hb] i, by fin_cases i <;> rfl, rfl⟩, hxK⟩

lemma buildPartition_r2_A4 (G : Type*) [Group G] [Fintype G]
    (Ha Hb : Subgroup G)
    (ha_cyc : IsCyclic Ha) (hb_cyc : IsCyclic Hb)
    (ha_card : Nat.card Ha = 2) (hb_card : Nat.card Hb = 3)
    (ha_norm : Nat.card (Subgroup.normalizer (SetLike.coe Ha)) = 4)
    (hb_norm : Nat.card (Subgroup.normalizer (SetLike.coe Hb)) = 3)
    (hdisj : ∀ K L : Subgroup G,
      (∃ (i : Fin 2) (g : G), K = (![Ha, Hb] i).map (MulAut.conj g).toMonoidHom) →
      (∃ (j : Fin 2) (h : G), L = (![Ha, Hb] j).map (MulAut.conj h).toMonoidHom) →
      K ≠ L → K ⊓ L = ⊥)
    (hcover : ∀ x : G, x ≠ 1 →
      ∃ K : Subgroup G, (∃ (i : Fin 2) (g : G),
        K = (![Ha, Hb] i).map (MulAut.conj g).toMonoidHom) ∧ x ∈ K) :
    HasCyclicPartition G [{d := 2, f := 2}, {d := 3, f := 1}] := by
  refine ⟨[Ha, Hb], rfl, ?_, ?_, ?_⟩

  · exact fun (i : Fin 2) ↦ match i with
    | 0 => ⟨Ha, rfl, ha_cyc, ha_card, ha_norm⟩
    | 1 => ⟨Hb, rfl, hb_cyc, hb_card, hb_norm⟩

  · rintro K_sub L_sub ⟨i, g, Hi, hK, rfl⟩ ⟨j, h, Hj, hL, rfl⟩ hKL
    have e_i : Hi = ![Ha, Hb] i := by fin_cases i <;> cases hK <;> rfl
    have e_j : Hj = ![Ha, Hb] j := by fin_cases j <;> cases hL <;> rfl
    exact hdisj _ _ ⟨i, g, by rw [e_i]⟩ ⟨j, h, by rw [e_j]⟩ hKL

  · intro x hx
    obtain ⟨K_sub, ⟨i, g, rfl⟩, hxK⟩ := hcover x hx
    exact ⟨_, ⟨i, g, ![Ha, Hb] i, by fin_cases i <;> rfl, rfl⟩, hxK⟩

lemma buildPartition_r3_evenDihedral (G : Type*) [Group G] [Fintype G]
    (H0 H1 H2 : Subgroup G) (k : ℕ)
    (h0_cyc : IsCyclic H0) (h1_cyc : IsCyclic H1) (h2_cyc : IsCyclic H2)
    (h0_card : Nat.card H0 = 2) (h1_card : Nat.card H1 = 2) (h2_card : Nat.card H2 = k)
    (h0_norm : Nat.card (Subgroup.normalizer (SetLike.coe H0)) = 4) (h1_norm : Nat.card (Subgroup.normalizer (SetLike.coe H1)) = 4)
    (h2_norm : Nat.card (Subgroup.normalizer (SetLike.coe H2)) = 2 * k)
    (hdisj : ∀ K L : Subgroup G,
      (∃ (i : Fin 3) (g : G), K = (![H0, H1, H2] i).map (MulAut.conj g).toMonoidHom) →
      (∃ (j : Fin 3) (h : G), L = (![H0, H1, H2] j).map (MulAut.conj h).toMonoidHom) →
      K ≠ L → K ⊓ L = ⊥)
    (hcover : ∀ x : G, x ≠ 1 →
      ∃ K : Subgroup G, (∃ (i : Fin 3) (g : G),
        K = (![H0, H1, H2] i).map (MulAut.conj g).toMonoidHom) ∧ x ∈ K) :
    HasCyclicPartition G [{d := k, f := 2}, {d := 2, f := 2}, {d := 2, f := 2}] := by
  refine ⟨[H2, H0, H1], rfl, ?_, ?_, ?_⟩

  · exact fun (i : Fin 3) ↦ match i with
    | 0 => ⟨H2, rfl, h2_cyc, h2_card, h2_norm⟩
    | 1 => ⟨H0, rfl, h0_cyc, h0_card, h0_norm⟩
    | 2 => ⟨H1, rfl, h1_cyc, h1_card, h1_norm⟩

  · rintro K_sub L_sub ⟨i, g, Hi, hK, rfl⟩ ⟨j, h, Hj, hL, rfl⟩ hKL
    have e_i : Hi = ![H0, H1, H2] (![2, 0, 1] i) := by fin_cases i <;> cases hK <;> rfl
    have e_j : Hj = ![H0, H1, H2] (![2, 0, 1] j) := by fin_cases j <;> cases hL <;> rfl
    exact hdisj _ _ ⟨![2, 0, 1] i, g, by rw [e_i]⟩ ⟨![2, 0, 1] j, h, by rw [e_j]⟩ hKL

  · intro x hx
    obtain ⟨K_sub, ⟨i, g, rfl⟩, hxK⟩ := hcover x hx
    match i with
    | 0 => exact ⟨_, ⟨⟨1, by show (1 : ℕ) < 3; omega⟩, g, H0, rfl, rfl⟩, hxK⟩
    | 1 => exact ⟨_, ⟨⟨2, by show (2 : ℕ) < 3; omega⟩, g, H1, rfl, rfl⟩, hxK⟩
    | 2 => exact ⟨_, ⟨⟨0, by show (0 : ℕ) < 3; omega⟩, g, H2, rfl, rfl⟩, hxK⟩

lemma buildPartition_r3_exceptional (G : Type*) [Group G] [Fintype G]
    (H0 H1 H2 : Subgroup G) (d0 d1 d2 : ℕ)
    (h0_cyc : IsCyclic H0) (h1_cyc : IsCyclic H1) (h2_cyc : IsCyclic H2)
    (h0_card : Nat.card H0 = d0) (h1_card : Nat.card H1 = d1) (h2_card : Nat.card H2 = d2)
    (h0_norm : Nat.card (Subgroup.normalizer (SetLike.coe H0)) = 2 * d0) (h1_norm : Nat.card (Subgroup.normalizer (SetLike.coe H1)) = 2 * d1)
    (h2_norm : Nat.card (Subgroup.normalizer (SetLike.coe H2)) = 2 * d2)
    (hdisj : ∀ K L : Subgroup G,
      (∃ (i : Fin 3) (g : G), K = (![H0, H1, H2] i).map (MulAut.conj g).toMonoidHom) →
      (∃ (j : Fin 3) (h : G), L = (![H0, H1, H2] j).map (MulAut.conj h).toMonoidHom) →
      K ≠ L → K ⊓ L = ⊥)
    (hcover : ∀ x : G, x ≠ 1 →
      ∃ K : Subgroup G, (∃ (i : Fin 3) (g : G),
        K = (![H0, H1, H2] i).map (MulAut.conj g).toMonoidHom) ∧ x ∈ K) :
    HasCyclicPartition G [{d := d0, f := 2}, {d := d1, f := 2}, {d := d2, f := 2}] := by
  refine ⟨[H0, H1, H2], rfl, ?_, ?_, ?_⟩

  · exact fun (i : Fin 3) ↦ match i with
    | 0 => ⟨H0, rfl, h0_cyc, h0_card, h0_norm⟩
    | 1 => ⟨H1, rfl, h1_cyc, h1_card, h1_norm⟩
    | 2 => ⟨H2, rfl, h2_cyc, h2_card, h2_norm⟩

  · rintro K_sub L_sub ⟨i, g, Hi, hK, rfl⟩ ⟨j, h, Hj, hL, rfl⟩ hKL
    have e_i : Hi = ![H0, H1, H2] i := by fin_cases i <;> cases hK <;> rfl
    have e_j : Hj = ![H0, H1, H2] j := by fin_cases j <;> cases hL <;> rfl
    exact hdisj _ _ ⟨i, g, by rw [e_i]⟩ ⟨j, h, by rw [e_j]⟩ hKL

  · intro x hx
    obtain ⟨K_sub, ⟨i, g, rfl⟩, hxK⟩ := hcover x hx
    exact ⟨_, ⟨i, g, ![H0, H1, H2] i, by fin_cases i <;> rfl, rfl⟩, hxK⟩

lemma termLowerBound (d f : ℕ) (hd : d ≥ 2) (hf : f = 1 ∨ f = 2) :
    (1 : ℚ) / 4 ≤ ((1 : ℚ) / f) * (1 - 1 / d) := by
  rcases hf with rfl | rfl

  · calc (1 : ℚ) / 4 ≤ (1 : ℚ) / 1 * (1 - 1 / 2) := by norm_num
      _ ≤ (1 : ℚ) / 1 * (1 - 1 / d) := by gcongr; exact Nat.cast_le.mpr hd

  · calc (1 : ℚ) / 4 ≤ (1 : ℚ) / 2 * (1 - 1 / 2) := by norm_num
      _ ≤ (1 : ℚ) / 2 * (1 - 1 / d) := by gcongr; exact Nat.cast_le.mpr hd

lemma numTerms_le_three (r : ℕ) (d f : Fin r → ℕ) (n : ℕ) (hn : n ≥ 2)
    (hd : ∀ i, d i ≥ 2) (hf : ∀ i, f i = 1 ∨ f i = 2)
    (hsum : (∑ i : Fin r, (1 : ℚ) / (f i) * (1 - 1 / (d i))) = 1 - 1 / n) :
    r ≤ 3 := by
  by_contra! h
  exact lt_irrefl (1 : ℚ) <| calc (1 : ℚ) = 4 * (1 / 4) := by norm_num
    _ ≤ (r : ℚ) * (1 / 4) := by gcongr; exact Nat.cast_le.mpr h
    _ = ∑ _i : Fin r, (1 : ℚ) / 4 := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ ≤ ∑ i : Fin r,
        (1 : ℚ) / (f i) * (1 - 1 / d i) :=
          Finset.sum_le_sum fun i _ ↦ termLowerBound (d i) (f i) (hd i) (hf i)
    _ = 1 - 1 / (n : ℚ) := hsum
    _ < 1 := sub_lt_self 1 (by positivity)

lemma r3_allF_eq_two (d f : Fin 3 → ℕ) (n : ℕ) (hn : n ≥ 2)
    (hd : ∀ i, d i ≥ 2) (hf : ∀ i, f i = 1 ∨ f i = 2)
    (hsum : (∑ i : Fin 3, (1 : ℚ) / (f i) * (1 - 1 / (d i))) = 1 - 1 / n) :
    ∀ i, f i = 2 := by
  intro i
  rcases hf i with hfi | hfi

  · exfalso; exact lt_irrefl (1 : ℚ) <|
      calc (1 : ℚ)
          = (1 : ℚ) / 1 * (1 - 1 / 2) + 2 * (1 / 4) := by
            norm_num
        _ = (1 : ℚ) / 1 * (1 - 1 / 2) +
            ((Finset.univ.erase i).card : ℚ) * (1 / 4) := by
          rw [Finset.card_erase_of_mem (Finset.mem_univ i),
            Finset.card_univ, Fintype.card_fin]; norm_num
        _ = (1 : ℚ) / 1 * (1 - 1 / 2) +
            ∑ _j ∈ Finset.univ.erase i, (1 : ℚ) / 4 := by
          rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ (1 : ℚ) / (f i) * (1 - 1 / (d i)) +
            ∑ j ∈ Finset.univ.erase i,
            (1 : ℚ) / (f j) * (1 - 1 / (d j)) :=
              add_le_add
                (by rw [hfi]; gcongr; norm_num; exact Nat.cast_le.mpr (hd i))
                (Finset.sum_le_sum fun j _ ↦
                  termLowerBound (d j) (f j) (hd j) (hf j))
        _ = ∑ j : Fin 3,
            (1 : ℚ) / (f j) * (1 - 1 / (d j)) :=
              Finset.add_sum_erase _
                (fun j ↦ (1 : ℚ) / (f j) * (1 - 1 / (d j)))
                (Finset.mem_univ i)
        _ = 1 - 1 / (n : ℚ) := hsum
        _ < 1 := sub_lt_self 1 (by positivity)

  · exact hfi

lemma tame_hasCyclicPartition (G : Subgroup (PGL p)) [Fintype G]
    (hG_tame : ¬ (p : ℕ) ∣ Nat.card G)
    (hG_nontrivial : Nontrivial G) :
    (∃ N : ℕ, Nat.card G = N ∧ HasCyclicPartition G [{d := N, f := 1}]) ∨
    (∃ n : ℕ, Odd n ∧ n ≥ 3 ∧ Nat.card G = 2 * n ∧
      HasCyclicPartition G [{d := n, f := 2}, {d := 2, f := 1}]) ∨
    (∃ n : ℕ, Even n ∧ n ≥ 2 ∧ Nat.card G = 2 * n ∧
      HasCyclicPartition G [{d := n, f := 2}, {d := 2, f := 2}, {d := 2, f := 2}]) ∨
    (Nat.card G = 12 ∧
      HasCyclicPartition G [{d := 2, f := 2}, {d := 3, f := 1}]) ∨
    (Nat.card G = 24 ∧
      HasCyclicPartition G [{d := 2, f := 2}, {d := 3, f := 2}, {d := 4, f := 2}]) ∨
    (Nat.card G = 60 ∧
      HasCyclicPartition G [{d := 2, f := 2}, {d := 3, f := 2}, {d := 5, f := 2}]) := by

  obtain ⟨r, d, f, H, hcyc, hcard, hge2, hf12, hdiv, hnorm, hdisj, hcover, heq⟩ :=
    orbitPartitionData p G hG_tame hG_nontrivial

  have hG2 : Nat.card (↥G) ≥ 2 := by
     rw [Nat.card_eq_fintype_card]; exact Fintype.one_lt_card_iff_nontrivial.mpr hG_nontrivial
  have hr3 : r ≤ 3 := numTerms_le_three r d f (Nat.card (↥G)) hG2 hge2 hf12 heq
  interval_cases r

  · simp only [Finset.univ_eq_empty, Finset.sum_empty] at heq
    linarith only [heq, show (0 : ℚ) < 1 - 1 / (Nat.card (↥G) : ℚ) from by
      rw [sub_pos, div_lt_one (by exact Nat.cast_pos.mpr (show Nat.card ↥G > 0 by omega))]
      exact Nat.cast_lt.mpr (show 1 < Nat.card ↥G by omega)]

  · have heq1 : (1 : ℚ) / (f ⟨0, by omega⟩) * (1 - 1 / (d ⟨0,
      by omega⟩)) = 1 - 1 / (Nat.card (↥G)) := by
      simp only [Fin.sum_univ_one] at heq
      exact heq

    have r1 := r1Solution (d ⟨0, by omega⟩) (f ⟨0, by omega⟩) (Nat.card (↥G)) hG2
      (hge2 ⟨0, by omega⟩) (hf12 ⟨0, by omega⟩)
      (hdiv ⟨0, by omega⟩) heq1
    left; refine ⟨Nat.card (↥G), rfl, ?_⟩
    apply buildPartition_r1 (↥G) (H ⟨0, by omega⟩)

    · exact hcyc ⟨0, by omega⟩

    · rw [hcard]; exact r1.1

    · rw [hnorm, r1.2, r1.1]

    · exact fun K L hK hL hKL ↦ hdisj K L ⟨⟨0, by omega⟩, hK.choose, hK.choose_spec⟩
        ⟨⟨0, by omega⟩, hL.choose, hL.choose_spec⟩ hKL

    · intro x hx
      obtain ⟨K, ⟨i, g, hK⟩, hxK⟩ := hcover x hx
      exact ⟨K, ⟨g, by rwa [show i = ⟨0, by omega⟩ from Fin.ext (by omega)] at hK⟩, hxK⟩

  · have h_fin2_disj (a b : Fin 2) : ∀ K L : Subgroup ↥G,
        (∃ (i : Fin 2) (g : ↥G), K = (![H a, H b] i).map (MulAut.conj g).toMonoidHom) →
        (∃ (j : Fin 2) (h : ↥G), L = (![H a, H b] j).map (MulAut.conj h).toMonoidHom) →
        K ≠ L → K ⊓ L = ⊥ := by
      rintro K L ⟨i, g, rfl⟩ ⟨j, h, rfl⟩ hKL
      exact hdisj _ _ ⟨![a, b] i, g, by fin_cases i <;> rfl⟩
        ⟨![a, b] j, h, by fin_cases j <;> rfl⟩ hKL

    have h_fin2_cover (a b : Fin 2) (hab : a ≠ b) : ∀ x : ↥G, x ≠ 1 →
        ∃ K : Subgroup ↥G, (∃ (i : Fin 2) (g : ↥G),
          K = (![H a, H b] i).map (MulAut.conj g).toMonoidHom) ∧ x ∈ K :=
      fun x hx ↦ by
        obtain ⟨_, ⟨i, g, rfl⟩, hxK⟩ := hcover x hx

        have : i = a ∨ i = b := by
          fin_cases i <;> fin_cases a <;> fin_cases b <;>
            first | exact absurd rfl hab | exact Or.inl rfl | exact Or.inr rfl
        rcases this with rfl | rfl

        · exact ⟨_, ⟨0, g, rfl⟩, hxK⟩

        · exact ⟨_, ⟨1, g, rfl⟩, hxK⟩

    rcases r2Solutions d f (Nat.card (↥G)) hG2 hge2 hf12 hdiv heq with
      ⟨a, b, hab, hfa, hfb, hdb, hn⟩ | ⟨a, b, hab, hfa, hda, hfb, hdb, hn⟩

    · have h_ne : H a ≠ H b := fun h_eq ↦ by
        have h1 := hnorm a; rw [hfa] at h1; have h2 := hnorm b; rw [hfb, hdb] at h2
        rw [h_eq] at h1; rw [h1] at h2; have := hge2 a; omega

      have h_map_one : ∀ K : Subgroup ↥G, K.map (MulAut.conj 1).toMonoidHom = K := fun K ↦ by
        have : (MulAut.conj (1 : ↥G)).toMonoidHom = MonoidHom.id ↥G := by
          ext x; simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_one, mul_one,
            one_mul, MonoidHom.id_apply]
        rw [this, Subgroup.map_id]

      have h_odd := r2CaseOdd G (d a) (hge2 a) hn (H a) (H b) (hcyc a) (hcard a)
        (by rw [hcard, hdb]) (by rw [hnorm, hfb, hdb, one_mul])
        (hdisj _ _ ⟨a, 1, (h_map_one _).symm⟩ ⟨b, 1, (h_map_one _).symm⟩ h_ne)
      refine Or.inr <| Or.inl ⟨d a, h_odd, ?_, hn, ?_⟩

      · obtain ⟨k, hk⟩ : ∃ k, d a = 2 * k + 1 := h_odd
        linarith only [hk, show k > 0 from Nat.pos_of_ne_zero fun h ↦ by subst h; have h_ge:= hge2 a; linarith only [hk, h_ge]]

      · exact buildPartition_r2_dihedral G (H a) (H b) (d a) (hcyc a) (hcyc b)
          (hcard a ▸ rfl) (hcard b ▸ hdb) (hnorm a ▸ hfa.symm ▸ rfl)
          (hnorm b ▸ hfb.symm ▸ hdb.symm ▸ rfl) (h_fin2_disj a b) (h_fin2_cover a b hab)

    · refine Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨hn, ?_⟩
      exact buildPartition_r2_A4 G (H a) (H b) (hcyc a) (hcyc b)
        (hcard a ▸ hda) (hcard b ▸ hdb) (hnorm a ▸ hfa.symm ▸ hda.symm ▸ rfl)
        (hnorm b ▸ hfb.symm ▸ hdb.symm ▸ rfl) (h_fin2_disj a b) (h_fin2_cover a b hab)

  ·
    have hf2 : ∀ i, f i = 2 := r3_allF_eq_two d f (Nat.card (↥G)) hG2 hge2 hf12 heq

    have hsum' : (∑ i : Fin 3, (1 : ℚ) / (d i)) = 1 + 2 / (Nat.card (↥G)) := by
      have h := heq; simp only [Fin.sum_univ_three] at h ⊢
      simp only [hf2] at h; field_simp at h ⊢; linarith only [h]

    have h_r3_disj (σ : Equiv.Perm (Fin 3)) : ∀ K L : Subgroup ↥G,
        (∃ (i : Fin 3) (g : ↥G), K = (![H (σ 0), H (σ 1),
            H (σ 2)] i).map (MulAut.conj g).toMonoidHom) →
        (∃ (j : Fin 3) (h : ↥G), L = (![H (σ 0), H (σ 1),
            H (σ 2)] j).map (MulAut.conj h).toMonoidHom) →
        K ≠ L → K ⊓ L = ⊥ := by
      rintro K L ⟨i, g, rfl⟩ ⟨j, h, rfl⟩ hKL
      exact hdisj _ _ ⟨σ i, g, by fin_cases i <;> rfl⟩ ⟨σ j, h, by fin_cases j <;> rfl⟩ hKL

    have h_r3_cover (σ : Equiv.Perm (Fin 3)) : ∀ x : ↥G, x ≠ 1 →
        ∃ K : Subgroup ↥G, (∃ (i : Fin 3) (g : ↥G),
          K = (![H (σ 0), H (σ 1), H (σ 2)] i).map (MulAut.conj g).toMonoidHom) ∧ x ∈ K :=
      fun x hx ↦ by
        obtain ⟨_, ⟨i, g, rfl⟩, hxK⟩ := hcover x hx
        refine ⟨_, ⟨σ.symm i, g, ?_⟩, hxK⟩

        have h_eval : ∀ x, ![H (σ 0), H (σ 1), H (σ 2)] x = H (σ x) :=
          fun x ↦ by fin_cases x <;> rfl
        rw [h_eval, Equiv.apply_symm_apply]
    obtain ⟨σ, hσ⟩ := r3SolutionsUnsorted d (Nat.card G) hG2 hge2 hsum'

    ·
      obtain ⟨k, hk_ge2, hk_d, hk_card⟩ := hσ.2.2

      have hk_even : Even k := by
        obtain ⟨m, hm⟩ := hdiv (σ 0); rw [hf2, hσ.1, hk_card] at hm
        exact even_iff_two_dvd.mpr ⟨m, by omega⟩
      refine Or.inr <| Or.inr <| Or.inl ⟨k, hk_even, hk_ge2, hk_card, ?_⟩
      exact buildPartition_r3_evenDihedral G (H (σ 0)) (H (σ 1)) (H (σ 2)) k
        (hcyc _) (hcyc _) (hcyc _)
        (by rw [hcard, hσ.1]) (by rw [hcard, hσ.2.1]) (by rw [hcard, hk_d])
        (by rw [hnorm, hf2, hσ.1]) (by rw [hnorm, hf2, hσ.2.1]) (by rw [hnorm, hf2, hk_d])
        (h_r3_disj σ) (h_r3_cover σ)

    · rcases ‹_› with ⟨σ, hσ₀, hσ₁, hσ₂, hσ₃⟩ | ⟨σ, hσ₀, hσ₁, hσ₂, hσ₃⟩ | ⟨σ, hσ₀, hσ₁, hσ₂, hσ₃⟩
      ·
        exfalso; exact r3D233Contradiction G hσ₃ (H (σ 1))
          (by rw [hcard, hσ₁]) (by rw [hnorm, hf2, hσ₁])

      ·
        refine Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨hσ₃, ?_⟩
        exact buildPartition_r3_exceptional G (H (σ 0)) (H (σ 1)) (H (σ 2)) 2 3 4
          (hcyc _) (hcyc _) (hcyc _)
          (by rw [hcard, hσ₀]) (by rw [hcard, hσ₁]) (by rw [hcard, hσ₂])
          (by rw [hnorm, hf2, hσ₀]) (by rw [hnorm, hf2, hσ₁]) (by rw [hnorm, hf2, hσ₂])
          (h_r3_disj σ) (h_r3_cover σ)

      ·
        refine Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr ⟨hσ₃, ?_⟩
        exact buildPartition_r3_exceptional G (H (σ 0)) (H (σ 1)) (H (σ 2)) 2 3 5
          (hcyc _) (hcyc _) (hcyc _)
          (by rw [hcard, hσ₀]) (by rw [hcard, hσ₁]) (by rw [hcard, hσ₂])
          (by rw [hnorm, hf2, hσ₀]) (by rw [hnorm, hf2, hσ₁]) (by rw [hnorm, hf2, hσ₂])
          (h_r3_disj σ) (h_r3_cover σ)

theorem classification_tame_slop (G : Subgroup (PGL p)) [Fintype G]
    (hG_tame : ¬ (p : ℕ) ∣ Nat.card G)
    (hG_nontrivial : Nontrivial G) :
    (IsCyclic G) ∨
    (∃ n : ℕ, n ≥ 2 ∧ Nonempty (G ≃* DihedralGroup n)) ∨
    (Nonempty (G ≃* alternatingGroup (Fin 4))) ∨
    (Nonempty (G ≃* Equiv.Perm (Fin 4))) ∨
    (Nonempty (G ≃* alternatingGroup (Fin 5))) := by

  rcases tame_hasCyclicPartition p G hG_tame hG_nontrivial with
    ⟨N, hN_card, hN_part⟩ | ⟨n, hn_odd, hn_ge, hn_card, hn_part⟩ |
    ⟨n, hn_even, hn_ge, hn_card, hn_part⟩ |
    ⟨h12_card, h12_part⟩ | ⟨h24_card, h24_part⟩ | ⟨h60_card, h60_part⟩

  · exact .inl (isCyclic_of_hasCyclicPartition G N hN_card hN_part)

  · exact .inr (.inl ⟨n, by omega, dihedral_of_hasCyclicPartition_odd G n hn_ge hn_card hn_part⟩)

  · rcases eq_or_ne n 2 with rfl | hn2
    · exact .inr (.inl ⟨2, by omega, dihedral2_of_hasCyclicPartition G hn_card hn_part⟩)

    · exact .inr (.inl ⟨n, by omega,
        dihedral_of_hasCyclicPartition_even G n
          (by obtain ⟨k, rfl⟩ := hn_even; omega)
          hn_card hn_part⟩)

  · exact .inr (.inr (.inl (iso_A4_of_hasCyclicPartition G h12_card h12_part)))

  · exact .inr (.inr (.inr (.inl (iso_S4_of_hasCyclicPartition G h24_card h24_part))))

  · exact .inr (.inr (.inr (.inr (iso_A5_of_hasCyclicPartition G h60_card h60_part))))
end

end Dickson
