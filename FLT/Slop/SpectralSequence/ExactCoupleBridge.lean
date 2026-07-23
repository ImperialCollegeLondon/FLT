/-
Copyright (c) 2026 Akhil Mathew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Akhil Mathew
-/
module

public import FLT.Slop.SpectralSequence.FilteredModule
public import FLT.Slop.ExactCouple.Graded

/-!
# The exact couple of a filtered differential module

Given a `FilteredDifferentialModule R M` we build its exact couple (Weibel §5.9.1):
* `D^p = H(F^p M) = (F^p ∩ ker d) / d(F^p)` — the homology of the subcomplex
  `F^p M`;
* `E^p = E_1^p = Z_1^p / B_1^p` — the first page;
* `i : D^{p+1} → D^p` induced by the inclusion `F^{p+1} ↪ F^p`;
* `j : D^p → E^p` induced by `(F^p ∩ ker d) ↪ Z_1^p`;
* `k : E^p → D^{p+1}` the connecting map `[x] ↦ [d x]`.

This file establishes the per-degree maps and the three exactness statements
(`range_iMap_eq_ker_jMap`, `range_jMap_eq_ker_kMap`, `range_kMap_eq_ker_iMap`)
and assembles them into a `GradedExactCouple` on the direct sums
`⨁ p, HF p` and `⨁ p, page 1 p`.
-/

@[expose] public section

namespace Slop

-- `_root_` is needed: this file's imports already populate the `Slop.DirectSum`
-- namespace, which would otherwise shadow mathlib's `DirectSum` here.
open scoped _root_.DirectSum
open Submodule LinearMap

namespace FilteredDifferentialModule

variable {R : Type*} {M : Type*} [Ring R] [AddCommGroup M] [Module R M]
variable (K : FilteredDifferentialModule R M)

/-! ## The homology of the subcomplex `F^p` -/

/-- The boundaries of the subcomplex `F^p`: `d(F^p) = im(d|_{F^p})`. -/
def dF (p : ℤ) : Submodule R M := (K.F p).map K.d

lemma dF_le_abutmentZ (p : ℤ) : K.dF p ≤ K.abutmentZ p := by
  rintro _ ⟨x, hx, rfl⟩
  refine Submodule.mem_inf.mpr ⟨K.d_mem_F p x hx, ?_⟩
  exact LinearMap.mem_ker.mpr (K.d_squared x)

lemma dF_mono {p q : ℤ} (h : p ≤ q) : K.dF q ≤ K.dF p :=
  Submodule.map_mono (K.F_mono h)

/-- `D^p = H(F^p) = (F^p ∩ ker d) / d(F^p)`, the homology of the subcomplex
`F^p`. Here `abutmentZ p` is the cycle submodule used to present this homology;
it is not the limit-term numerator `limitZ p`. -/
abbrev HF (p : ℤ) := ↥(K.abutmentZ p) ⧸ (K.dF p).comap (K.abutmentZ p).subtype

/-- Membership in `d(F^p)` for an element of `F^p ∩ ker d`, unfolded. -/
lemma mem_dF_comap {p : ℤ} (z : ↥(K.abutmentZ p)) :
    z ∈ (K.dF p).comap (K.abutmentZ p).subtype ↔ ∃ x ∈ K.F p, K.d x = z := by
  simp only [Submodule.mem_comap, Submodule.coe_subtype, dF, Submodule.mem_map]

/-! ## The map `i : D^{p+1} → D^p` -/

/-- The inclusion `F^{p+1} ∩ ker d → F^p ∩ ker d`. -/
def abutmentZIncl (p : ℤ) : ↥(K.abutmentZ (p + 1)) →ₗ[R] ↥(K.abutmentZ p) :=
  Submodule.inclusion (inf_le_inf_right _ (K.F_le p))

/-- `i : D^{p+1} → D^p`, induced by `F^{p+1} ↪ F^p`. -/
def iMap (p : ℤ) : K.HF (p + 1) →ₗ[R] K.HF p :=
  Submodule.mapQ _ _ (K.abutmentZIncl p) (by
    rintro z hz
    rw [Submodule.mem_comap] at hz ⊢
    obtain ⟨x, hx, hdx⟩ := (K.mem_dF_comap z).mp hz
    exact (K.mem_dF_comap _).mpr ⟨x, K.F_le p hx, hdx⟩)

@[simp] lemma iMap_mk (p : ℤ) (z : ↥(K.abutmentZ (p + 1))) :
    K.iMap p (Submodule.Quotient.mk z) = Submodule.Quotient.mk (K.abutmentZIncl p z) :=
  Submodule.mapQ_apply _ _ _ z

/-! ## The map `j : D^p → E^p` -/

lemma abutmentZ_le_Z_one (p : ℤ) : K.abutmentZ p ≤ K.Z 1 p := by
  intro z hz
  obtain ⟨hzF, hzk⟩ := Submodule.mem_inf.mp hz
  refine K.mem_Z.mpr ⟨hzF, ?_⟩
  rw [LinearMap.mem_ker.mp hzk]
  exact zero_mem _

lemma dF_le_B_one (p : ℤ) : K.dF p ≤ K.B 1 p := by
  rintro _ ⟨x, hx, rfl⟩
  refine K.mem_B_right ?_ (K.d_mem_F p x hx)
  rwa [show p - 1 + 1 = p by ring]

/-- The inclusion `F^p ∩ ker d → Z_1^p`. -/
def abutmentZToZOne (p : ℤ) : ↥(K.abutmentZ p) →ₗ[R] ↥(K.Z 1 p) :=
  Submodule.inclusion (K.abutmentZ_le_Z_one p)

/-- `j : D^p → E^p = E_1^p`, induced by `F^p ∩ ker d ↪ Z_1^p`. -/
def jMap (p : ℤ) : K.HF p →ₗ[R] K.page 1 p :=
  Submodule.mapQ _ _ (K.abutmentZToZOne p) (by
    rintro z hz
    rw [Submodule.mem_comap] at hz ⊢
    obtain ⟨x, hx, hdx⟩ := (K.mem_dF_comap z).mp hz
    simp only [Submodule.mem_comap, Submodule.coe_subtype, abutmentZToZOne,
      Submodule.coe_inclusion] at *
    rw [← hdx]
    exact K.dF_le_B_one p ⟨x, hx, rfl⟩)

@[simp] lemma jMap_mk (p : ℤ) (z : ↥(K.abutmentZ p)) :
    K.jMap p (Submodule.Quotient.mk z) = Submodule.Quotient.mk (K.abutmentZToZOne p z) :=
  Submodule.mapQ_apply _ _ _ z

/-! ## The map `k : E^p → D^{p+1}` -/

lemma d_mem_abutmentZ_succ {p : ℤ} {x : M} (hx : x ∈ K.Z 1 p) : K.d x ∈ K.abutmentZ (p + 1) :=
  Submodule.mem_inf.mpr ⟨(K.mem_Z.mp hx).2, LinearMap.mem_ker.mpr (K.d_squared x)⟩

/-- The connecting map `Z_1^p → F^{p+1} ∩ ker d`, `x ↦ d x`. -/
def zOneToAbutmentZ (p : ℤ) : ↥(K.Z 1 p) →ₗ[R] ↥(K.abutmentZ (p + 1)) :=
  K.d.restrict fun _ hx ↦ K.d_mem_abutmentZ_succ hx

@[simp] lemma zOneToAbutmentZ_coe (p : ℤ) (x : ↥(K.Z 1 p)) :
    (K.zOneToAbutmentZ p x : M) = K.d x := rfl

/-- `k : E^p → D^{p+1}`, the connecting map `[x] ↦ [d x]`. -/
def kMap (p : ℤ) : K.page 1 p →ₗ[R] K.HF (p + 1) :=
  Submodule.mapQ _ _ (K.zOneToAbutmentZ p) (by
    rintro x hx
    simp only [Submodule.mem_comap, Submodule.coe_subtype] at hx
    obtain ⟨u, v, hu1, hu2, hv, hdv, hxeq⟩ := K.B_cases hx
    rw [Submodule.mem_comap]
    change K.d (x : M) ∈ K.dF (p + 1)
    rw [hxeq, map_add, K.d_squared v, add_zero]
    exact Submodule.mem_map_of_mem hu1)

@[simp] lemma kMap_mk (p : ℤ) (x : ↥(K.Z 1 p)) :
    K.kMap p (Submodule.Quotient.mk x) = Submodule.Quotient.mk (K.zOneToAbutmentZ p x) :=
  Submodule.mapQ_apply _ _ _ x

/-- On the first page, the differential is the composite `j ∘ k` of the
exact-couple maps. -/
lemma jMap_comp_kMap (p : ℤ) :
    (K.jMap (p + 1)).comp (K.kMap p) = K.dPage 1 p := by
  apply Submodule.linearMap_qext
  ext x
  simp only [LinearMap.comp_apply, Submodule.mkQ_apply, kMap_mk, jMap_mk, dPageAux_mk]
  congr 1

@[simp] lemma abutmentZIncl_coe (p : ℤ) (z : ↥(K.abutmentZ (p + 1))) :
    (K.abutmentZIncl p z : M) = z := rfl

@[simp] lemma abutmentZToZOne_coe (p : ℤ) (z : ↥(K.abutmentZ p)) :
    (K.abutmentZToZOne p z : M) = z := rfl

/-! ## Zero-membership criteria in the quotients -/

lemma HF_mk_eq_zero {p : ℤ} (z : ↥(K.abutmentZ p)) :
    (Submodule.Quotient.mk z : K.HF p) = 0 ↔ (z : M) ∈ K.dF p := by
  rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.coe_subtype]

lemma page_one_mk_eq_zero {p : ℤ} (x : ↥(K.Z 1 p)) :
    (Submodule.Quotient.mk x : K.page 1 p) = 0 ↔ (x : M) ∈ K.B 1 p := by
  rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.coe_subtype]

/-! ## The three exactness conditions -/

/-- Exactness at `D` (`im i = ker j`): `range (iMap p) = ker (jMap p)`. -/
theorem range_iMap_eq_ker_jMap (p : ℤ) :
    range (K.iMap p) = ker (K.jMap p) := by
  apply le_antisymm
  · rintro _ ⟨w, rfl⟩
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ w
    rw [LinearMap.mem_ker, iMap_mk, jMap_mk, K.page_one_mk_eq_zero]
    simp only [abutmentZToZOne_coe, abutmentZIncl_coe]
    -- `z ∈ abutmentZ (p+1)`, so `z ∈ F(p+1) ∩ d⁻¹ F(p+1) ⊆ B_1^p`
    refine K.mem_B_left z.2.1 ?_
    rw [LinearMap.mem_ker.mp z.2.2]; exact zero_mem _
  · intro w hw
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ w
    rw [LinearMap.mem_ker, jMap_mk, K.page_one_mk_eq_zero] at hw
    simp only [abutmentZToZOne_coe] at hw
    obtain ⟨u, v, hu1, hu2, hv, hdv, hzeq⟩ := K.B_cases hw
    -- `z = u + d v`, `d z = 0` forces `d u = 0`, so `u ∈ abutmentZ (p+1)` and `i[u] = [z]`
    have hvp : v ∈ K.F p := by rwa [show p - 1 + 1 = p by ring] at hv
    have hdu : K.d u = 0 := by
      have hz0 : K.d (z : M) = 0 := LinearMap.mem_ker.mp z.2.2
      rw [hzeq, map_add, K.d_squared v, add_zero] at hz0; exact hz0
    refine ⟨Submodule.Quotient.mk ⟨u, Submodule.mem_inf.mpr ⟨hu1, LinearMap.mem_ker.mpr hdu⟩⟩, ?_⟩
    rw [iMap_mk, Submodule.Quotient.eq, K.mem_dF_comap]
    refine ⟨-v, neg_mem hvp, ?_⟩
    simp only [map_neg, Submodule.coe_sub, abutmentZIncl_coe, hzeq]; abel

/-- Exactness at `E` (`im j = ker k`): `range (jMap p) = ker (kMap p)`. -/
theorem range_jMap_eq_ker_kMap (p : ℤ) :
    range (K.jMap p) = ker (K.kMap p) := by
  apply le_antisymm
  · rintro _ ⟨w, rfl⟩
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ w
    rw [LinearMap.mem_ker, jMap_mk, kMap_mk, K.HF_mk_eq_zero]
    simp only [zOneToAbutmentZ_coe, abutmentZToZOne_coe]
    -- `k(j[z]) = [d z] = [0]` since `z ∈ ker d`
    rw [LinearMap.mem_ker.mp z.2.2]; exact zero_mem _
  · intro w hw
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ w
    rw [LinearMap.mem_ker, kMap_mk, K.HF_mk_eq_zero] at hw
    simp only [zOneToAbutmentZ_coe] at hw
    rw [dF, Submodule.mem_map] at hw
    obtain ⟨u, hu, hux⟩ := hw
    -- `d x = d u`, `u ∈ F(p+1)`; then `x - u ∈ abutmentZ p` and `j[x-u] = [x]`
    have hxu_ker : (x : M) - u ∈ ker K.d := by
      rw [LinearMap.mem_ker, map_sub, hux, sub_self]
    have hxu_F : (x : M) - u ∈ K.F p := sub_mem (K.mem_Z.mp x.2).1 (K.F_le p hu)
    refine ⟨Submodule.Quotient.mk ⟨(x : M) - u, Submodule.mem_inf.mpr ⟨hxu_F, hxu_ker⟩⟩, ?_⟩
    rw [jMap_mk, Submodule.Quotient.eq, Submodule.mem_comap, Submodule.coe_subtype]
    simp only [Submodule.coe_sub, abutmentZToZOne_coe]
    have hval : ((x : M) - u) - (x : M) = -u := by abel
    rw [hval]
    exact neg_mem (K.mem_B_left hu (by rw [hux]; exact (K.mem_Z.mp x.2).2))

/-- Exactness at `D` (`im k = ker i`): `range (kMap p) = ker (iMap p)`. -/
theorem range_kMap_eq_ker_iMap (p : ℤ) :
    range (K.kMap p) = ker (K.iMap p) := by
  apply le_antisymm
  · rintro _ ⟨w, rfl⟩
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ w
    rw [LinearMap.mem_ker, kMap_mk, iMap_mk, K.HF_mk_eq_zero]
    simp only [abutmentZIncl_coe, zOneToAbutmentZ_coe]
    -- `i(k[x]) = [d x]`, `d x ∈ d(F^p)`
    exact ⟨(x : M), (K.mem_Z.mp x.2).1, rfl⟩
  · intro w hw
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ w
    rw [LinearMap.mem_ker, iMap_mk, K.HF_mk_eq_zero] at hw
    simp only [abutmentZIncl_coe] at hw
    rw [dF, Submodule.mem_map] at hw
    obtain ⟨x, hx, hdx⟩ := hw
    -- `z = d x` for `x ∈ F p`; `d x = z ∈ F(p+1)`, so `x ∈ Z_1^p` and `k[x] = [z]`
    have hxZ : x ∈ K.Z 1 p := K.mem_Z.mpr ⟨hx, by rw [hdx]; exact z.2.1⟩
    refine ⟨Submodule.Quotient.mk ⟨x, hxZ⟩, ?_⟩
    rw [kMap_mk, Submodule.Quotient.eq, K.mem_dF_comap]
    refine ⟨0, zero_mem _, ?_⟩
    simp only [map_zero, Submodule.coe_sub, zOneToAbutmentZ_coe, hdx]; abel

/-! ## Assembly into an exact couple -/

universe u v w x

private lemma exact_lmap
    {S : Type u} [Ring S] {ι : Type v}
    {A : ι → Type w} {B : ι → Type x} {C : ι → Type*}
    [∀ i, AddCommGroup (A i)] [∀ i, Module S (A i)]
    [∀ i, AddCommGroup (B i)] [∀ i, Module S (B i)]
    [∀ i, AddCommGroup (C i)] [∀ i, Module S (C i)]
    (f : ∀ i, A i →ₗ[S] B i) (g : ∀ i, B i →ₗ[S] C i)
    (h : ∀ i, Function.Exact (f i) (g i)) :
    Function.Exact (DirectSum.lmap f) (DirectSum.lmap g) := by
  rw [LinearMap.exact_iff, DirectSum.ker_lmap, DirectSum.range_lmap]
  ext b
  simp only [Submodule.mem_comap, Submodule.mem_pi, Set.mem_univ, forall_const]
  exact forall_congr' fun i => (LinearMap.exact_iff.mp (h i)).symm ▸ Iff.rfl

/-- The filtration predecessor equivalence used to identify
`⨁ p, H(F^p)` with `⨁ p, H(F^{p+1})`. -/
def filtrationPredEquiv : ℤ ≃ ℤ where
  toFun p := p - 1
  invFun p := p + 1
  left_inv p := by simp
  right_inv p := by simp

@[simp] lemma filtrationPredEquiv_symm_apply (p : ℤ) :
    filtrationPredEquiv.symm p = p + 1 := rfl

/-- The direct sum `D = ⨁ p, H(F^p)`. -/
abbrev totalHF := ⨁ p : ℤ, K.HF p

/-- The direct sum `E = ⨁ p, E₁^p`. -/
abbrev totalPageOne := ⨁ p : ℤ, K.page 1 p

/-- The shifted direct sum `⨁ p, H(F^{p+1})`. -/
abbrev shiftedHF := ⨁ p : ℤ, K.HF (p + 1)

/-- Reindex `⨁ p, H(F^p)` as `⨁ p, H(F^{p+1})`. -/
noncomputable def shiftHF : K.totalHF ≃ₗ[R] K.shiftedHF :=
  DirectSum.lequivCongrLeft R filtrationPredEquiv

@[simp] lemma shiftHF_lof_succ (p : ℤ) (z : K.HF (p + 1)) :
    K.shiftHF (DirectSum.lof R ℤ (fun q => K.HF q) (p + 1) z) =
      DirectSum.lof R ℤ (fun q => K.HF (q + 1)) p z := by
  change (DirectSum.lequivCongrLeft R filtrationPredEquiv)
    (DirectSum.lof R ℤ (fun q => K.HF q) (p + 1) z) =
      DirectSum.lof R ℤ (fun q => K.HF (q + 1)) p z
  ext q
  rw [DirectSum.lequivCongrLeft_apply]
  simp only [filtrationPredEquiv_symm_apply]
  by_cases h : p = q
  · subst q
    trans z
    · exact DirectSum.lof_apply (M := fun q => K.HF q) R (p + 1) z
    · exact (DirectSum.lof_apply (M := fun q => K.HF (q + 1)) R p z).symm
  · have h' : p + 1 ≠ q + 1 := by omega
    change DirectSum.component R ℤ (fun q => K.HF q) (q + 1)
        (DirectSum.lof R ℤ (fun q => K.HF q) (p + 1) z) =
      DirectSum.component R ℤ (fun q => K.HF (q + 1)) q
        (DirectSum.lof R ℤ (fun q => K.HF (q + 1)) p z)
    rw [DirectSum.component.of, DirectSum.component.of, dif_neg h', dif_neg h]

@[simp] lemma shiftHF_symm_lof (p : ℤ) (z : K.HF (p + 1)) :
    K.shiftHF.symm (DirectSum.lof R ℤ (fun q => K.HF (q + 1)) p z) =
      DirectSum.lof R ℤ (fun q => K.HF q) (p + 1) z :=
  K.shiftHF.symm_apply_eq.mpr (K.shiftHF_lof_succ p z).symm

/-- The direct sum of the inclusion maps `iMap`. -/
noncomputable def totalI : K.totalHF →ₗ[R] K.totalHF :=
  (DirectSum.lmap fun p => K.iMap p).comp K.shiftHF.toLinearMap

/-- The direct sum of the quotient maps `jMap`. -/
noncomputable def totalJ : K.totalHF →ₗ[R] K.totalPageOne :=
  DirectSum.lmap fun p => K.jMap p

/-- The direct sum of the connecting maps `kMap`. -/
noncomputable def totalK : K.totalPageOne →ₗ[R] K.totalHF :=
  K.shiftHF.symm.toLinearMap.comp (DirectSum.lmap fun p => K.kMap p)

@[simp] lemma totalI_lof_succ (p : ℤ) (z : K.HF (p + 1)) :
    K.totalI (DirectSum.lof R ℤ (fun q => K.HF q) (p + 1) z) =
      DirectSum.lof R ℤ (fun q => K.HF q) p (K.iMap p z) := by
  simp [totalI]

@[simp] lemma totalJ_lof (p : ℤ) (z : K.HF p) :
    K.totalJ (DirectSum.lof R ℤ (fun q => K.HF q) p z) =
      DirectSum.lof R ℤ (fun q => K.page 1 q) p (K.jMap p z) := by
  simp [totalJ]

@[simp] lemma totalK_lof (p : ℤ) (z : K.page 1 p) :
    K.totalK (DirectSum.lof R ℤ (fun q => K.page 1 q) p z) =
      DirectSum.lof R ℤ (fun q => K.HF q) (p + 1) (K.kMap p z) := by
  simp [totalK]

lemma exact_totalI_totalJ : Function.Exact K.totalI K.totalJ := by
  apply LinearEquiv.precomp_exact_iff_exact.mpr
  apply exact_lmap
  intro p
  rw [LinearMap.exact_iff]
  exact (K.range_iMap_eq_ker_jMap p).symm

lemma exact_totalJ_totalK : Function.Exact K.totalJ K.totalK := by
  apply LinearEquiv.postcomp_exact_iff_exact.mpr
  apply exact_lmap
  intro p
  rw [LinearMap.exact_iff]
  exact (K.range_jMap_eq_ker_kMap p).symm

lemma exact_totalK_totalI : Function.Exact K.totalK K.totalI := by
  apply (LinearEquiv.conj_symm_exact_iff_exact
    (DirectSum.lmap fun p => K.kMap p)
    (DirectSum.lmap fun p => K.iMap p) K.shiftHF).mpr
  apply exact_lmap
  intro p
  rw [LinearMap.exact_iff]
  exact (K.range_kMap_eq_ker_iMap p).symm

/-- The exact couple of a filtered differential module, assembled on direct sums
over the filtration degree. -/
@[reducible] noncomputable def exactCouple : ExactCouple R where
  D := K.totalHF
  E := K.totalPageOne
  i := K.totalI
  j := K.totalJ
  k := K.totalK
  exact_ij := K.exact_totalI_totalJ
  exact_jk := K.exact_totalJ_totalK
  exact_ki := K.exact_totalK_totalI

/-! ## The internal gradings -/

/-- The canonical degree-`p` submodule of a direct sum. -/
def _root_.Slop.DirectSum.canonicalGrading {ι : Type*} [DecidableEq ι] {A : ι → Type*}
    [∀ p, AddCommGroup (A p)] [∀ p, Module R (A p)] (p : ι) :
    Submodule R (⨁ q, A q) :=
  LinearMap.range (DirectSum.lof R ι A p)

/-- The inclusion of one summand, corestricted to its canonical graded submodule. -/
def _root_.Slop.DirectSum.canonicalGradingComponent
    {ι : Type*} [DecidableEq ι] {A : ι → Type*}
    [∀ p, AddCommGroup (A p)] [∀ p, Module R (A p)] (p : ι) :
    A p →ₗ[R] DirectSum.canonicalGrading (R := R) (A := A) p :=
  (DirectSum.lof R ι A p).codRestrict _ fun z => ⟨z, rfl⟩

/-- Decompose a direct sum into its canonical graded submodules. -/
noncomputable def _root_.Slop.DirectSum.canonicalGradingDecompose
    {ι : Type*} [DecidableEq ι] {A : ι → Type*}
    [∀ p, AddCommGroup (A p)] [∀ p, Module R (A p)] :
    (⨁ q, A q) →ₗ[R] ⨁ p, DirectSum.canonicalGrading (R := R) (A := A) p :=
  DirectSum.lmap fun p => DirectSum.canonicalGradingComponent (R := R) (A := A) p

/-- The canonical internal decomposition of a direct sum by its summands. -/
@[implicit_reducible] noncomputable def _root_.Slop.DirectSum.canonicalGradingDecomposition
    {ι : Type*} [DecidableEq ι] {A : ι → Type*}
    [∀ p, AddCommGroup (A p)] [∀ p, Module R (A p)] :
    DirectSum.Decomposition (DirectSum.canonicalGrading (R := R) (A := A)) :=
  DirectSum.Decomposition.ofLinearMap _
      (DirectSum.canonicalGradingDecompose (R := R) (A := A)) (by
    apply DirectSum.linearMap_ext
    intro p
    apply LinearMap.ext
    intro z
    simp only [LinearMap.comp_apply, DirectSum.canonicalGradingDecompose,
      DirectSum.lmap_lof, DirectSum.coeLinearMap_lof,
      DirectSum.canonicalGradingComponent, LinearMap.id_apply]
    rfl) (by
    apply DirectSum.linearMap_ext
    intro p
    apply LinearMap.ext
    intro z
    simp only [LinearMap.comp_apply, DirectSum.coeLinearMap_lof, LinearMap.id_apply]
    obtain ⟨y, hy⟩ := z.property
    rw [← hy]
    simp only [DirectSum.canonicalGradingDecompose, DirectSum.lmap_lof]
    congr 2
    apply Subtype.ext
    exact hy)

theorem _root_.Slop.DirectSum.isInternal_canonicalGrading
    {ι : Type*} [DecidableEq ι] {A : ι → Type*}
    [∀ p, AddCommGroup (A p)] [∀ p, Module R (A p)] :
    DirectSum.IsInternal (DirectSum.canonicalGrading (R := R) (A := A)) := by
  letI := DirectSum.canonicalGradingDecomposition (R := R) (A := A)
  exact DirectSum.Decomposition.isInternal _

/-- The filtration-degree grading of `⨁ p, H(F^p)`. -/
def totalHFGrading (p : ℤ) : Submodule R K.totalHF :=
  DirectSum.canonicalGrading (R := R) (A := fun q => K.HF q) p

/-- The filtration-degree grading of `⨁ p, E₁^p`. -/
def totalPageOneGrading (p : ℤ) : Submodule R K.totalPageOne :=
  DirectSum.canonicalGrading (R := R) (A := fun q => K.page 1 q) p

lemma totalHFGrading_isInternal : DirectSum.IsInternal K.totalHFGrading :=
  DirectSum.isInternal_canonicalGrading (R := R) (A := fun q => K.HF q)

lemma totalPageOneGrading_isInternal : DirectSum.IsInternal K.totalPageOneGrading :=
  DirectSum.isInternal_canonicalGrading (R := R) (A := fun q => K.page 1 q)

/-- The graded exact couple associated to a filtered differential module.
The maps `i`, `j`, and `k` have filtration degrees `-1`, `0`, and `1`. -/
noncomputable def gradedExactCouple : GradedExactCouple R ℤ where
  toExactCouple := K.exactCouple
  di := -1
  dj := 0
  dk := 1
  gradD := K.totalHFGrading
  gradE := K.totalPageOneGrading
  internalD := K.totalHFGrading_isInternal
  internalE := K.totalPageOneGrading_isInternal
  homog_i := by
    intro p
    rw [show p = (p - 1) + 1 by omega]
    change (DirectSum.canonicalGrading (R := R) (A := fun q => K.HF q) ((p - 1) + 1)).map
        K.totalI ≤
      DirectSum.canonicalGrading (R := R) (A := fun q => K.HF q) (((p - 1) + 1) + (-1))
    rintro _ ⟨z, ⟨y, rfl⟩, rfl⟩
    change K.totalI (DirectSum.lof R ℤ (fun q => K.HF q) ((p - 1) + 1) y) ∈
      DirectSum.canonicalGrading (R := R) (A := fun q => K.HF q) (((p - 1) + 1) + (-1))
    rw [K.totalI_lof_succ]
    rw [show (p - 1) + 1 + (-1) = p - 1 by omega]
    exact ⟨_, rfl⟩
  homog_j := by
    intro p
    change (DirectSum.canonicalGrading (R := R) (A := fun q => K.HF q) p).map K.totalJ ≤
      DirectSum.canonicalGrading (R := R) (A := fun q => K.page 1 q) (p + 0)
    rintro _ ⟨z, ⟨y, rfl⟩, rfl⟩
    change K.totalJ (DirectSum.lof R ℤ (fun q => K.HF q) p y) ∈
      DirectSum.canonicalGrading (R := R) (A := fun q => K.page 1 q) (p + 0)
    rw [K.totalJ_lof]
    simpa using (show
      DirectSum.lof R ℤ (fun q => K.page 1 q) p (K.jMap p y) ∈
        DirectSum.canonicalGrading (R := R) (A := fun q => K.page 1 q) p from ⟨_, rfl⟩)
  homog_k := by
    intro p
    change (DirectSum.canonicalGrading (R := R) (A := fun q => K.page 1 q) p).map K.totalK ≤
      DirectSum.canonicalGrading (R := R) (A := fun q => K.HF q) (p + 1)
    rintro _ ⟨z, ⟨y, rfl⟩, rfl⟩
    change K.totalK (DirectSum.lof R ℤ (fun q => K.page 1 q) p y) ∈
      DirectSum.canonicalGrading (R := R) (A := fun q => K.HF q) (p + 1)
    rw [K.totalK_lof]
    exact ⟨_, rfl⟩

end FilteredDifferentialModule

end Slop
