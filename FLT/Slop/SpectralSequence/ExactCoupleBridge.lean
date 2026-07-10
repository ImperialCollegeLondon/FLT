/-
Copyright (c) 2026 Akhil Mathew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Akhil Mathew
-/
module

public import FLT.Slop.SpectralSequence.FilteredModule

/-!
# The exact couple of a filtered differential module

Given a `FilteredDifferentialModule R M` we build its exact couple (Weibel §5.9.1):
* `D^p = H(F^p M) = Z_∞^p / d(F^p)` — the homology of the subcomplex `F^p M`;
* `E^p = E_1^p = Z_1^p / B_1^p` — the first page;
* `i : D^{p+1} → D^p` induced by the inclusion `F^{p+1} ↪ F^p`;
* `j : D^p → E^p` induced by `Z_∞^p ↪ Z_1^p`;
* `k : E^p → D^{p+1}` the connecting map `[x] ↦ [d x]`.

This file establishes the per-degree maps and the three exactness statements
(`range_iMap_eq_ker_jMap`, `range_jMap_eq_ker_kMap`, `range_kMap_eq_ker_iMap`)
— the mathematical heart of the exact couple of a filtered differential module.
Assembling them into a `GradedExactCouple` on `⨁ p, HF p` (see the sibling
`FLT.Slop.ExactCouple` development) is the natural next step and is not done
here.
-/

@[expose] public section

open scoped DirectSum
open Submodule LinearMap

namespace FilteredDifferentialModule

variable {R : Type*} {M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
variable (K : FilteredDifferentialModule R M)

/-! ## The homology of the subcomplex `F^p` -/

/-- The boundaries of the subcomplex `F^p`: `d(F^p) = im(d|_{F^p})`. -/
def dF (p : ℤ) : Submodule R M := (K.F p).map K.d

lemma dF_le_Zinf (p : ℤ) : K.dF p ≤ K.Zinf p := by
  rintro _ ⟨x, hx, rfl⟩
  refine Submodule.mem_inf.mpr ⟨K.d_mem_F p x hx, ?_⟩
  exact LinearMap.mem_ker.mpr (K.d_squared x)

lemma dF_mono {p q : ℤ} (h : p ≤ q) : K.dF q ≤ K.dF p :=
  Submodule.map_mono (K.F_mono h)

/-- `D^p = H(F^p) = Z_∞^p / d(F^p)`, the homology of the subcomplex `F^p`. -/
abbrev HF (p : ℤ) := ↥(K.Zinf p) ⧸ (K.dF p).comap (K.Zinf p).subtype

/-- Membership in `d(F^p)` for a `Z_∞^p`-element, unfolded. -/
lemma mem_dF_comap {p : ℤ} (z : ↥(K.Zinf p)) :
    z ∈ (K.dF p).comap (K.Zinf p).subtype ↔ ∃ x ∈ K.F p, K.d x = z := by
  simp only [Submodule.mem_comap, Submodule.coe_subtype, dF, Submodule.mem_map]

/-! ## The map `i : D^{p+1} → D^p` -/

/-- The inclusion `Z_∞^{p+1} → Z_∞^p`. -/
def ZinfIncl (p : ℤ) : ↥(K.Zinf (p + 1)) →ₗ[R] ↥(K.Zinf p) :=
  Submodule.inclusion (inf_le_inf_right _ (K.F_le p))

/-- `i : D^{p+1} → D^p`, induced by `F^{p+1} ↪ F^p`. -/
def iMap (p : ℤ) : K.HF (p + 1) →ₗ[R] K.HF p :=
  Submodule.mapQ _ _ (K.ZinfIncl p) (by
    rintro z hz
    rw [Submodule.mem_comap] at hz ⊢
    obtain ⟨x, hx, hdx⟩ := (K.mem_dF_comap z).mp hz
    exact (K.mem_dF_comap _).mpr ⟨x, K.F_le p hx, hdx⟩)

@[simp] lemma iMap_mk (p : ℤ) (z : ↥(K.Zinf (p + 1))) :
    K.iMap p (Submodule.Quotient.mk z) = Submodule.Quotient.mk (K.ZinfIncl p z) :=
  Submodule.mapQ_apply _ _ _ z

/-! ## The map `j : D^p → E^p` -/

lemma Zinf_le_Z_one (p : ℤ) : K.Zinf p ≤ K.Z 1 p := by
  intro z hz
  obtain ⟨hzF, hzk⟩ := Submodule.mem_inf.mp hz
  refine K.mem_Z.mpr ⟨hzF, ?_⟩
  rw [LinearMap.mem_ker.mp hzk]
  exact zero_mem _

lemma dF_le_B_one (p : ℤ) : K.dF p ≤ K.B 1 p := by
  rintro _ ⟨x, hx, rfl⟩
  refine K.mem_B_right ?_ (K.d_mem_F p x hx)
  rwa [show p - 1 + 1 = p by ring]

/-- The inclusion `Z_∞^p → Z_1^p`. -/
def ZinfToZone (p : ℤ) : ↥(K.Zinf p) →ₗ[R] ↥(K.Z 1 p) :=
  Submodule.inclusion (K.Zinf_le_Z_one p)

/-- `j : D^p → E^p = E_1^p`, induced by `Z_∞^p ↪ Z_1^p`. -/
def jMap (p : ℤ) : K.HF p →ₗ[R] K.page 1 p :=
  Submodule.mapQ _ _ (K.ZinfToZone p) (by
    rintro z hz
    rw [Submodule.mem_comap] at hz ⊢
    obtain ⟨x, hx, hdx⟩ := (K.mem_dF_comap z).mp hz
    simp only [Submodule.mem_comap, Submodule.coe_subtype, ZinfToZone,
      Submodule.coe_inclusion] at *
    rw [← hdx]
    exact K.dF_le_B_one p ⟨x, hx, rfl⟩)

@[simp] lemma jMap_mk (p : ℤ) (z : ↥(K.Zinf p)) :
    K.jMap p (Submodule.Quotient.mk z) = Submodule.Quotient.mk (K.ZinfToZone p z) :=
  Submodule.mapQ_apply _ _ _ z

/-! ## The map `k : E^p → D^{p+1}` -/

lemma d_mem_Zinf_succ {p : ℤ} {x : M} (hx : x ∈ K.Z 1 p) : K.d x ∈ K.Zinf (p + 1) :=
  Submodule.mem_inf.mpr ⟨(K.mem_Z.mp hx).2, LinearMap.mem_ker.mpr (K.d_squared x)⟩

/-- The connecting map `Z_1^p → Z_∞^{p+1}`, `x ↦ d x`. -/
def ZoneToZinf (p : ℤ) : ↥(K.Z 1 p) →ₗ[R] ↥(K.Zinf (p + 1)) :=
  K.d.restrict fun _ hx ↦ K.d_mem_Zinf_succ hx

@[simp] lemma ZoneToZinf_coe (p : ℤ) (x : ↥(K.Z 1 p)) :
    (K.ZoneToZinf p x : M) = K.d x := rfl

/-- `k : E^p → D^{p+1}`, the connecting map `[x] ↦ [d x]`. -/
def kMap (p : ℤ) : K.page 1 p →ₗ[R] K.HF (p + 1) :=
  Submodule.mapQ _ _ (K.ZoneToZinf p) (by
    rintro x hx
    simp only [Submodule.mem_comap, Submodule.coe_subtype] at hx
    obtain ⟨u, v, hu1, hu2, hv, hdv, hxeq⟩ := K.B_cases hx
    rw [Submodule.mem_comap]
    change K.d (x : M) ∈ K.dF (p + 1)
    rw [hxeq, map_add, K.d_squared v, add_zero]
    exact Submodule.mem_map_of_mem hu1)

@[simp] lemma kMap_mk (p : ℤ) (x : ↥(K.Z 1 p)) :
    K.kMap p (Submodule.Quotient.mk x) = Submodule.Quotient.mk (K.ZoneToZinf p x) :=
  Submodule.mapQ_apply _ _ _ x

@[simp] lemma ZinfIncl_coe (p : ℤ) (z : ↥(K.Zinf (p + 1))) :
    (K.ZinfIncl p z : M) = z := rfl

@[simp] lemma ZinfToZone_coe (p : ℤ) (z : ↥(K.Zinf p)) :
    (K.ZinfToZone p z : M) = z := rfl

/-! ## Zero-membership criteria in the quotients -/

lemma HF_mk_eq_zero {p : ℤ} (z : ↥(K.Zinf p)) :
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
    simp only [ZinfToZone_coe, ZinfIncl_coe]
    -- `z ∈ Zinf (p+1)`, so `z ∈ F(p+1) ∩ d⁻¹ F(p+1) ⊆ B_1^p`
    refine K.mem_B_left z.2.1 ?_
    rw [LinearMap.mem_ker.mp z.2.2]; exact zero_mem _
  · intro w hw
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ w
    rw [LinearMap.mem_ker, jMap_mk, K.page_one_mk_eq_zero] at hw
    simp only [ZinfToZone_coe] at hw
    obtain ⟨u, v, hu1, hu2, hv, hdv, hzeq⟩ := K.B_cases hw
    -- `z = u + d v`, `d z = 0` forces `d u = 0`, so `u ∈ Zinf (p+1)` and `i[u] = [z]`
    have hvp : v ∈ K.F p := by rwa [show p - 1 + 1 = p by ring] at hv
    have hdu : K.d u = 0 := by
      have hz0 : K.d (z : M) = 0 := LinearMap.mem_ker.mp z.2.2
      rw [hzeq, map_add, K.d_squared v, add_zero] at hz0; exact hz0
    refine ⟨Submodule.Quotient.mk ⟨u, Submodule.mem_inf.mpr ⟨hu1, LinearMap.mem_ker.mpr hdu⟩⟩, ?_⟩
    rw [iMap_mk, Submodule.Quotient.eq, K.mem_dF_comap]
    refine ⟨-v, neg_mem hvp, ?_⟩
    simp only [map_neg, Submodule.coe_sub, ZinfIncl_coe, hzeq]; abel

/-- Exactness at `E` (`im j = ker k`): `range (jMap p) = ker (kMap p)`. -/
theorem range_jMap_eq_ker_kMap (p : ℤ) :
    range (K.jMap p) = ker (K.kMap p) := by
  apply le_antisymm
  · rintro _ ⟨w, rfl⟩
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ w
    rw [LinearMap.mem_ker, jMap_mk, kMap_mk, K.HF_mk_eq_zero]
    simp only [ZoneToZinf_coe, ZinfToZone_coe]
    -- `k(j[z]) = [d z] = [0]` since `z ∈ ker d`
    rw [LinearMap.mem_ker.mp z.2.2]; exact zero_mem _
  · intro w hw
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ w
    rw [LinearMap.mem_ker, kMap_mk, K.HF_mk_eq_zero] at hw
    simp only [ZoneToZinf_coe] at hw
    rw [dF, Submodule.mem_map] at hw
    obtain ⟨u, hu, hux⟩ := hw
    -- `d x = d u`, `u ∈ F(p+1)`; then `x - u ∈ Zinf p` and `j[x-u] = [x]`
    have hxu_ker : (x : M) - u ∈ ker K.d := by
      rw [LinearMap.mem_ker, map_sub, hux, sub_self]
    have hxu_F : (x : M) - u ∈ K.F p := sub_mem (K.mem_Z.mp x.2).1 (K.F_le p hu)
    refine ⟨Submodule.Quotient.mk ⟨(x : M) - u, Submodule.mem_inf.mpr ⟨hxu_F, hxu_ker⟩⟩, ?_⟩
    rw [jMap_mk, Submodule.Quotient.eq, Submodule.mem_comap, Submodule.coe_subtype]
    simp only [Submodule.coe_sub, ZinfToZone_coe]
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
    simp only [ZinfIncl_coe, ZoneToZinf_coe]
    -- `i(k[x]) = [d x]`, `d x ∈ d(F^p)`
    exact ⟨(x : M), (K.mem_Z.mp x.2).1, rfl⟩
  · intro w hw
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ w
    rw [LinearMap.mem_ker, iMap_mk, K.HF_mk_eq_zero] at hw
    simp only [ZinfIncl_coe] at hw
    rw [dF, Submodule.mem_map] at hw
    obtain ⟨x, hx, hdx⟩ := hw
    -- `z = d x` for `x ∈ F p`; `d x = z ∈ F(p+1)`, so `x ∈ Z_1^p` and `k[x] = [z]`
    have hxZ : x ∈ K.Z 1 p := K.mem_Z.mpr ⟨hx, by rw [hdx]; exact z.2.1⟩
    refine ⟨Submodule.Quotient.mk ⟨x, hxZ⟩, ?_⟩
    rw [kMap_mk, Submodule.Quotient.eq, K.mem_dF_comap]
    refine ⟨0, zero_mem _, ?_⟩
    simp only [map_zero, Submodule.coe_sub, ZoneToZinf_coe, hdx]; abel

end FilteredDifferentialModule
