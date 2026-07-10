/-
Copyright (c) 2026 Akhil Mathew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Akhil Mathew
-/
module

public import FLT.Slop.SpectralSequence.FilteredComplex
public import Mathlib.Algebra.Exact.Basic
public import Mathlib.Tactic.NormNum

/-!
# The five-term exact sequence of low-degree terms

For a **first-quadrant** filtered complex — the filtration is `⊥` strictly above
the diagonal and `⊤` at or below `0` (`FilteredComplex.IsFirstQuadrant`), which is
what the column/row filtrations of a first-quadrant double complex satisfy — the
spectral sequence yields the classical five-term exact sequence of low-degree
terms (FOAG §1.7)

`0 → E_2^{1,0} → H¹ → E_2^{0,1} →^{d₂} E_2^{2,0} → H²`.

The construction is entirely limit-free: each of the corner spots `(1,0)`,
`(0,1)`, `(2,0)` is reached from the convergence isomorphism
`FilteredComplex.pageEquivGrHOfBounded` plus the observation that in the first
quadrant the only differential touching these corners is the single
transgression `d₂ : E_2^{0,1} → E_2^{2,0}`.  Using concrete integer indices
`0, 1, 2` throughout lets the kernel discharge the index arithmetic
(`(0 + 2) - 2 = 0` etc.) definitionally, so no dependent-type transport is
needed to identify `d₂` with the abstract page differentials.

## Main definitions and results

* `FilteredComplex.IsFirstQuadrant` : the first-quadrant condition on a filtered
  complex.
* `FilteredComplex.d2` : the transgression `d₂ : E_2^{0,1} → E_2^{2,0}`.
* `FilteredComplex.f1`, `FilteredComplex.f2`, `FilteredComplex.f4` : the edge
  maps `E_2^{1,0} → H¹` and `H¹ → E_2^{0,1}`, and `E_2^{2,0} → H²`.
* `FilteredComplex.five_term_exact` : the five-term exact sequence — `f1` is
  injective and the sequence is exact at `H¹`, `E_2^{0,1}` and `E_2^{2,0}`.
* `FilteredComplex.pageSuccEquivOfStable`, `FilteredComplex.quotComapTopEquiv` :
  stabilization at a spot with vanishing differentials, and a quotient
  convenience used to peel off `⊤` filtration steps.
-/

@[expose] public section

open Submodule LinearMap

namespace FilteredComplex

variable {R : Type*} [Ring R] (K : FilteredComplex R)

section FiveTerm

/-- If `S = ⊤`, then `↥S ⧸ N.comap S.subtype ≅ M ⧸ N`.  (A convenience for pushing a
quotient through the identification `↥(⊤) ≅ M`.) -/
noncomputable def quotComapTopEquiv {M : Type*} [AddCommGroup M] [Module R M]
    {S : Submodule R M} (hS : S = ⊤) (N : Submodule R M) :
    (↥S ⧸ N.comap S.subtype) ≃ₗ[R] (M ⧸ N) := by
  refine Submodule.Quotient.equiv _ _
    ((LinearEquiv.ofEq S ⊤ hS).trans Submodule.topEquiv) ?_
  ext x
  simp only [Submodule.mem_map, Submodule.mem_comap, Submodule.coe_subtype]
  constructor
  · rintro ⟨y, hy, rfl⟩; exact hy
  · intro hx; exact ⟨⟨x, hS ▸ Submodule.mem_top⟩, hx, rfl⟩

/-- **Stabilization at a spot with vanishing differentials.**  If both the outgoing
differential `d_r : E_r^{p,n} → E_r^{p+r,n+1}` and the incoming differential
`d_r : E_r^{p-r,n-1} → E_r^{p,n}` vanish, then `E_{r+1}^{p,n} ≅ E_r^{p,n}`. -/
noncomputable def pageSuccEquivOfStable {r p n : ℤ}
    (hout : K.dPage r p n = 0) (hin : K.dPageFrom r p n = 0) :
    K.page (r + 1) p n ≃ₗ[R] K.page r p n := by
  refine (K.pageSuccEquiv r p n).trans
    ((Submodule.quotEquivOfEqBot _ ?_).trans
      ((LinearEquiv.ofEq _ _ ?_).trans Submodule.topEquiv))
  · rw [hin, LinearMap.range_zero, Submodule.comap_bot, Submodule.ker_subtype]
  · rw [hout, LinearMap.ker_zero]

/-- **First-quadrant condition** on a filtered complex: the filtration is `⊥`
strictly above the diagonal (`n < p`) and `⊤` at or below `0`.  The column and row
filtrations of a first-quadrant double complex both satisfy this. -/
structure IsFirstQuadrant : Prop where
  /-- The filtration vanishes strictly above the diagonal. -/
  bot : ∀ {p n : ℤ}, n < p → K.F p n = ⊥
  /-- The filtration is everything at or below filtration degree `0`. -/
  top : ∀ {p n : ℤ}, p ≤ 0 → K.F p n = ⊤

variable {K}

/-- If `F^p_n = ⊥` then the induced filtration piece `F^p H^n = ⊥`. -/
lemma FH_eq_bot {p n : ℤ} (hF : K.F p n = ⊥) : K.FH p n = ⊥ := by
  have hZ : K.abutmentZ p n = ⊥ := by unfold abutmentZ; rw [hF, bot_inf_eq]
  unfold FH
  rw [hZ, Submodule.comap_bot, Submodule.ker_subtype, Submodule.map_bot]

/-- If `F^p_n = ⊤` then the induced filtration piece `F^p H^n = ⊤`. -/
lemma FH_eq_top {p n : ℤ} (hF : K.F p n = ⊤) : K.FH p n = ⊤ := by
  have hZ : K.abutmentZ p n = ker (K.d n (n + 1)) := by unfold abutmentZ; rw [hF, top_inf_eq]
  unfold FH
  rw [hZ, Submodule.comap_subtype_self, Submodule.map_top, Submodule.range_mkQ]

/-! ### The middle map `d₂ : E_2^{0,1} → E_2^{2,0}` -/

/-- The transgression `d₂ : E_2^{0,1} → E_2^{2,0}` with clean literal indices. -/
noncomputable def d2 : K.page 2 0 1 →ₗ[R] K.page 2 2 2 :=
  K.dPageAux 2 0 2 1 2 (by norm_num) (by norm_num)

/-- `d₂` and the abstract outgoing differential at `(0,1)` have the same kernel
(they are definitionally the same map). -/
lemma ker_d2_eq : ker K.d2 = ker (K.dPage 2 0 1) := rfl

/-- `d₂` and the abstract incoming differential at `(2,2)` have the same range
(they are definitionally the same map). -/
lemma range_d2_eq : range K.d2 = range (K.dPageFrom 2 2 2) := rfl

/-! ### Left edge `f₁ : E_2^{1,0} → H¹` -/

/-- `E_2^{1,0} ≅ F^1 H^1`: the `(1,0)` spot already stabilizes at page 2 (no
differential touches it in the first quadrant), and its graded piece is the top of
the 2-step filtration on `H¹`. -/
noncomputable def e2Iso10 (hK : K.IsFirstQuadrant) :
    K.page 2 1 1 ≃ₗ[R] ↥(K.FH 1 1) := by
  have hb : K.F (1 + 2) (1 + 1) = ⊥ := hK.bot (by norm_num)
  have ht : K.F (1 - 2 + 1) (1 - 1) = ⊤ := hK.top (by norm_num)
  refine (K.pageEquivGrHOfBounded hb ht).trans (Submodule.quotEquivOfEqBot _ ?_)
  rw [FH_eq_bot (hK.bot (show (1:ℤ) < 1 + 1 by norm_num)),
    Submodule.comap_bot, Submodule.ker_subtype]

/-- The **left edge map** `f₁ : E_2^{1,0} → H^1`. -/
noncomputable def f1 (hK : K.IsFirstQuadrant) : K.page 2 1 1 →ₗ[R] K.homology 1 :=
  (K.FH 1 1).subtype.comp (e2Iso10 hK).toLinearMap

lemma f1_injective (hK : K.IsFirstQuadrant) : Function.Injective (f1 hK) :=
  (Subtype.val_injective).comp (e2Iso10 hK).injective

lemma range_f1 (hK : K.IsFirstQuadrant) : range (f1 hK) = K.FH 1 1 := by
  rw [f1, LinearMap.range_comp, LinearEquiv.range, Submodule.map_top,
    Submodule.range_subtype]

/-! ### Bottom edge `f₂ : H¹ → E_2^{0,1}` -/

/-- At `(0,1)`, the finite pages stabilize at the associated-graded target,
which is isomorphic to `ker(d₂)`: only the outgoing `d₂` survives. -/
noncomputable def associatedGradedHomologyIso01 (hK : K.IsFirstQuadrant) :
    K.associatedGradedHomology 0 1 ≃ₗ[R] ↥(ker (K.dPage 2 0 1)) := by
  have hb : K.F (0 + 3) (1 + 1) = ⊥ := hK.bot (by norm_num)
  have ht : K.F (0 - 3 + 1) (1 - 1) = ⊤ := hK.top (by norm_num)
  refine (K.pageEquivAssociatedGradedHomology hb ht).symm.trans
    ((K.pageSuccEquiv 2 0 1).trans (Submodule.quotEquivOfEqBot _ ?_))
  rw [K.dPageFrom_eq_zero (hK.top (show (0:ℤ) - 2 + 1 ≤ 0 by norm_num)),
    LinearMap.range_zero, Submodule.comap_bot, Submodule.ker_subtype]

/-- `H¹ ⧸ F^1 H^1` is isomorphic to the associated-graded target at `(0,1)`. -/
noncomputable def grH1Iso (hK : K.IsFirstQuadrant) :
    (K.homology 1 ⧸ K.FH 1 1) ≃ₗ[R] K.associatedGradedHomology 0 1 :=
  ((K.associatedGradedHomologyEquivGrH 0 1).trans
    (quotComapTopEquiv (FH_eq_top (hK.top (show (0:ℤ) ≤ 0 by norm_num) : K.F 0 1 = ⊤))
      (K.FH 1 1))).symm

/-- The **bottom edge map** `f₂ : H^1 → E_2^{0,1}`. -/
noncomputable def f2 (hK : K.IsFirstQuadrant) : K.homology 1 →ₗ[R] K.page 2 0 1 :=
  ((ker (K.dPage 2 0 1)).subtype.comp
    ((associatedGradedHomologyIso01 hK).toLinearMap.comp
      (grH1Iso hK).toLinearMap)).comp (K.FH 1 1).mkQ

lemma f2_aux_injective (hK : K.IsFirstQuadrant) :
    Function.Injective ((ker (K.dPage 2 0 1)).subtype.comp
      ((associatedGradedHomologyIso01 hK).toLinearMap.comp (grH1Iso hK).toLinearMap)) :=
  (Subtype.val_injective).comp
    ((associatedGradedHomologyIso01 hK).injective.comp (grH1Iso hK).injective)

lemma ker_f2 (hK : K.IsFirstQuadrant) : ker (f2 hK) = K.FH 1 1 := by
  rw [f2, LinearMap.ker_comp, LinearMap.ker_eq_bot.mpr (f2_aux_injective hK),
    Submodule.comap_bot, Submodule.ker_mkQ]

lemma range_f2 (hK : K.IsFirstQuadrant) : range (f2 hK) = ker (K.dPage 2 0 1) := by
  rw [f2, LinearMap.range_comp, Submodule.range_mkQ, Submodule.map_top,
    LinearMap.range_comp, LinearMap.range_comp, LinearEquiv.range, Submodule.map_top,
    LinearEquiv.range, Submodule.map_top, Submodule.range_subtype]

/-! ### Right edge `f₄ : E_2^{2,0} → H²` -/

/-- `E_2^{2,0} ⧸ im(d₂) ≅ F^2 H^2`: at `(2,0)` only the incoming `d₂`
survives, so the finite pages stabilize at the top graded piece of `H²`. -/
noncomputable def e2Iso20 (hK : K.IsFirstQuadrant) :
    (K.page 2 2 2 ⧸ range (K.dPageFrom 2 2 2)) ≃ₗ[R] ↥(K.FH 2 2) := by
  have hz : K.dPage 2 2 2 = 0 := K.dPage_eq_zero (hK.bot (show (2:ℤ) + 1 < 2 + 2 by norm_num))
  have hker : ker (K.dPage 2 2 2) = ⊤ := by rw [hz, LinearMap.ker_zero]
  have step2 : (K.page 2 2 2 ⧸ range (K.dPageFrom 2 2 2)) ≃ₗ[R] K.page 3 2 2 :=
    ((K.pageSuccEquiv 2 2 2).trans
      (quotComapTopEquiv hker (range (K.dPageFrom 2 2 2)))).symm
  have hb : K.F (2 + 3) (2 + 1) = ⊥ := hK.bot (by norm_num)
  have ht : K.F (2 - 3 + 1) (2 - 1) = ⊤ := hK.top (by norm_num)
  refine step2.trans ((K.pageEquivGrHOfBounded hb ht).trans (Submodule.quotEquivOfEqBot _ ?_))
  rw [FH_eq_bot (hK.bot (show (2:ℤ) < 2 + 1 by norm_num)),
    Submodule.comap_bot, Submodule.ker_subtype]

/-- The **right edge map** `f₄ : E_2^{2,0} → H^2`. -/
noncomputable def f4 (hK : K.IsFirstQuadrant) : K.page 2 2 2 →ₗ[R] K.homology 2 :=
  ((K.FH 2 2).subtype.comp (e2Iso20 hK).toLinearMap).comp
    (range (K.dPageFrom 2 2 2)).mkQ

lemma ker_f4 (hK : K.IsFirstQuadrant) : ker (f4 hK) = range (K.dPageFrom 2 2 2) := by
  rw [f4, LinearMap.ker_comp,
    LinearMap.ker_eq_bot.mpr ((Subtype.val_injective).comp (e2Iso20 hK).injective),
    Submodule.comap_bot, Submodule.ker_mkQ]

lemma range_f4 (hK : K.IsFirstQuadrant) : range (f4 hK) = K.FH 2 2 := by
  rw [f4, LinearMap.range_comp, Submodule.range_mkQ, Submodule.map_top,
    LinearMap.range_comp, LinearEquiv.range, Submodule.map_top, Submodule.range_subtype]

/-! ### The five-term exact sequence -/

/-- **The five-term exact sequence of a first-quadrant filtered complex** (FOAG §1.7,
the "exact sequence of low-degree terms"):

`0 → E_2^{1,0} → H¹ → E_2^{0,1} →^{d₂} E_2^{2,0} → H²`,

i.e. `f₁` is injective and the sequence is exact at `H¹`, `E_2^{0,1}`, and
`E_2^{2,0}`.  The middle map is the transgression `d₂`.  Applies to either spectral
sequence of a first-quadrant double complex (both filtrations satisfy
`IsFirstQuadrant`). -/
theorem five_term_exact (hK : K.IsFirstQuadrant) :
    Function.Injective (f1 hK) ∧
    Function.Exact (f1 hK) (f2 hK) ∧
    Function.Exact (f2 hK) K.d2 ∧
    Function.Exact K.d2 (f4 hK) := by
  refine ⟨f1_injective hK, ?_, ?_, ?_⟩
  · rw [LinearMap.exact_iff, ker_f2, range_f1]
  · rw [LinearMap.exact_iff, ker_d2_eq, range_f2]
  · rw [LinearMap.exact_iff, ker_f4, range_d2_eq]

end FiveTerm

end FilteredComplex
