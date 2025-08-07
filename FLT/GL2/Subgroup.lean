/-
Copyright (c) 2025 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/
-- import FLT.Mathlib.Algebra.IsQuaternionAlgebra
-- import FLT.Mathlib.Topology.Algebra.Valued.ValuationTopology
-- import FLT.Mathlib.Topology.Instances.Matrix
-- import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
-- import FLT.Hacks.RightActionInstances
-- import Mathlib
import Mathlib.Algebra.Group.Submonoid.Units
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Valuation.ValuationRing
import Mathlib.RingTheory.Valuation.ValuativeRel
import Mathlib.Topology.Algebra.Valued.ValuativeRel
/-!

# Definitions of various compact open subgrups of M₂ or GL₂
# in the local and global setting

We define U₁(v) as a subgroup of GL₂(Fᵥ), and U₁(S) as a subgroup
of GL₂(𝔸_F^∞). We introduce the concept
of a rigidification `r : (D ⊗[F] 𝔸_F^∞) ≅ M₂(𝔸_F^∞)` in order
to push U₁(S) over to a subgroup of `(D ⊗[F] 𝔸_F^∞)ˣ`.

-/


/-

If I just have a ValuativeRel, do I get a ring of integers and a residue field?

-/
open scoped ValuativeRel

variable (K : Type*) [Field K] [ValuativeRel K]

--#check (𝒪[K])
--#check (𝓀[K])

/- GL_2(O_K) now easy: -/
example : Subgroup (GL (Fin 2) K) := 𝒪[K].matrix.units

-- do we need this?
example (A : Type*) [Ring A] (R : Subring A) (n : Type*) [Fintype n] [DecidableEq n] :
    Matrix n n R ≃+* (R.matrix : Subring (Matrix n n A)) := sorry

example : 𝒪[K] →+* K := 𝒪[K].subtype
example : 𝒪[K] →+* 𝓀[K] := IsLocalRing.residue ↥𝒪[K]

namespace M2

def UpperTriangular (k : Type*) [CommRing k] : Subring (Matrix (Fin 2) (Fin 2) k) where
  carrier := {M | M.BlockTriangular id}
  mul_mem' := by
    intro a b ha hb i j hij
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Fin.isValue]
    simp only [Matrix.BlockTriangular, id_eq, Set.mem_setOf_eq] at ha hb
    simp only [id_eq] at hij
    rw [ha (lt_of_le_of_lt (Fin.zero_le j) hij), hb (lt_of_lt_of_le hij
      (StrictMono.maximal_preimage_top (fun ⦃a b⦄ a ↦ a) rfl i) : j < 1)]
    ring
  one_mem' := by intro i j hij; exact Matrix.one_apply_ne' (id (ne_of_lt hij))
  add_mem' := by intro a b ha hb i j hij; simp [ha hij,hb hij]
  zero_mem' := by intro i j hij; rfl
  neg_mem' := by intro x hx i j hij; simp [hx hij]

lemma mem_upperTriangular_iff {k : Type*} [CommRing k] (M : Matrix (Fin 2) (Fin 2) k) :
    M ∈ UpperTriangular k ↔ M 1 0 = 0 := by
  constructor
  · intro hM
    exact hM Nat.one_pos
  · intro hM i j hij
    rw [(Fin.lt_one_iff j).1 (lt_of_lt_of_le hij (StrictMono.maximal_preimage_top (fun ⦃a b⦄ a ↦ a)
    rfl (id i))),Fin.eq_one_of_ne_zero i (ne_of_lt (lt_of_le_of_lt (Fin.zero_le j) hij)).symm]
    exact hM

def UpperTriangularToProd {k : Type*} [CommRing k] : UpperTriangular k →+* k × k where
  toFun M := (M.1 0 0, M.1 1 1)
  map_one' := rfl
  map_mul' x y := by
    simp only [Fin.isValue, Subring.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, Prod.mk_mul_mk,
      Prod.mk.injEq, add_eq_left, add_eq_right]
    constructor
    · simp [(mem_upperTriangular_iff y.1).1 y.2]
    · simp [(mem_upperTriangular_iff x.1).1 x.2]
  map_zero' := rfl
  map_add' x y := rfl

end M2

namespace GL2

def UpperTriangular (k : Type*) [CommRing k] : Subgroup (GL (Fin 2) k) :=
  (M2.UpperTriangular k).units

def UpperTriangularToProd {k : Type*} [CommRing k] : UpperTriangular k →* kˣ × kˣ where
  toFun M := (⟨M.1 0 0, (M⁻¹).1 0 0, by
    rw [(by simp : 1 = (M.1.1 * M⁻¹.1.1) 0 0)]
    simp only [Fin.isValue, Matrix.mul_apply, Fin.sum_univ_two,
      (M2.mem_upperTriangular_iff M⁻¹.1.1).1 M.2.2]
    ring, by
    rw [(by simp : 1 = (M⁻¹.1.1 * M.1.1) 0 0)]
    simp only [Fin.isValue, Matrix.mul_apply, Fin.sum_univ_two,
      (M2.mem_upperTriangular_iff M.1.1).1 M.2.1]
    ring⟩, ⟨M.1 1 1, (M⁻¹).1 1 1, by
    rw [(by simp : 1 = (M.1.1 * M⁻¹.1.1) 1 1)]
    simp only [Fin.isValue, Matrix.mul_apply, Fin.sum_univ_two,
      (M2.mem_upperTriangular_iff M.1.1).1 M.2.1]
    ring, by
    rw [(by simp : 1 = (M⁻¹.1.1 * M.1.1) 1 1)]
    simp only [Fin.isValue, Matrix.mul_apply, Fin.sum_univ_two,
      (M2.mem_upperTriangular_iff M⁻¹.1.1).1 M.2.2]
    ring⟩)
  map_one' := rfl
  map_mul' a b := by
    simp only [Subgroup.coe_mul, Fin.isValue, Units.val_mul, mul_inv_rev, InvMemClass.coe_inv,
      Matrix.coe_units_inv, Prod.mk_mul_mk, Prod.mk.injEq]
    constructor
    <;> simp only [Fin.isValue, Matrix.mul_apply, Fin.sum_univ_two]
    · simp only [(M2.mem_upperTriangular_iff b.1.1).1 b.2.1, mul_zero, add_zero]
      exact Units.val_inj.1 rfl
    · simp only [(M2.mem_upperTriangular_iff a.1.1).1 a.2.1, zero_mul, zero_add]
      exact Units.val_inj.1 rfl

end GL2

namespace M2


/-- Submonoid of M_2(k) consisting of matrices (d*r q; 0 r) with d ∈ Δ -/
def R_Δ {k : Type*} [CommRing k] (Δ : Submonoid k) :
    Submonoid (Matrix (Fin 2) (Fin 2) k) where
      carrier := {M | M ∈ UpperTriangular k ∧ ∃ d ∈ Δ, M 0 0 = d * M 1 1}
      mul_mem' := by
        rintro _ _ ⟨hM0, d, hd, hMd⟩ ⟨hN0, e, he, hNe⟩
        use mul_mem hM0 hN0
        refine ⟨d * e, ?_⟩
        rw [mem_upperTriangular_iff] at hM0 hN0
        exact ⟨mul_mem hd he, by simp [Matrix.mul_apply, hM0, hN0, hMd, hNe]; ring⟩
      one_mem' := ⟨one_mem _, 1, one_mem _, (mul_one 1).symm⟩

end M2

namespace GL2

def R_Δ {k : Type*} [CommRing k] (Δ : Submonoid k) :
    Subgroup (GL (Fin 2) k) := (M2.R_Δ Δ).units

-- theorem we want: if x is in R_Delta then UpperTriangularToProd composed with (a,d) ↦ a / d
-- sends R_Delta to Delta
-- needs stating

lemma thing3 {k : Type*} [CommRing k] (Δ : Submonoid k) : R_Δ Δ ≤ GL2.UpperTriangular k := by
  intro x hx; exact ⟨hx.1.1,hx.2.1⟩

end GL2


--#check Matrix.map

#check 𝓀[K]

variable {K}
/-- The subgroup of GL_2(K) consisting of matrices with integer entries and which are
  congruent modulo the maximal ideal to something of the form (d*a b; 0 a) with d ∈ Δ -/
noncomputable def U_Δ_Int (Δ : Submonoid 𝓀[K]) : Subgroup (GL (Fin 2) 𝒪[K]) :=
  -- let foo := (RingHom.mapMatrix (m := Fin 2) 𝒪[K].subtype)
  -- let bar := Units.map foo.toMonoidHom
  -- refine Subgroup.map bar ?_
  -- let baz := (RingHom.mapMatrix (m := Fin 2) (IsLocalRing.residue 𝒪[K]))
  -- refine Subgroup.comap (Units.map baz.toMonoidHom) ?_
  -- exact GL2.R_Δ Δ
  --Subgroup.map (Units.map (RingHom.mapMatrix (m := Fin 2) 𝒪[K].subtype).toMonoidHom) <|
  Subgroup.comap (Units.map
    (RingHom.mapMatrix (m := Fin 2) (IsLocalRing.residue 𝒪[K])).toMonoidHom) (GL2.R_Δ Δ)

def MonoidHom.restrict' {G H : Type*} [Monoid G] [Monoid H] (φ : G →* H)
  (S : Submonoid H) : S.comap φ →* S :=(φ.comp ((S.comap φ).subtype)).codRestrict _ (by aesop)

noncomputable def thing (Δ : Submonoid 𝓀[K]) : U_Δ_Int Δ →* 𝓀[K]ˣ × 𝓀[K]ˣ :=
  GL2.UpperTriangularToProd.comp ((Subgroup.inclusion (GL2.thing3 Δ)).comp ((Units.map
    (RingHom.mapMatrix (m := Fin 2) (IsLocalRing.residue 𝒪[K])).toMonoidHom).restrict' _))

noncomputable def thing4 (Δ : Submonoid 𝓀[K]) :
    U_Δ_Int Δ →* 𝓀[K]ˣ := (divMonoidHom.comp (thing Δ))

lemma thing_fact2 (Δ : Submonoid 𝓀[K]) (g : U_Δ_Int Δ) : (thing4 Δ g).1 ∈ Δ :=
  by
    obtain ⟨d,hd⟩ := g.2.1.2
    simp only [RingHom.toMonoidHom_eq_coe, Fin.isValue, Units.coeHom_apply, Units.coe_map,
      MonoidHom.coe_coe, RingHom.mapMatrix_apply, Matrix.map_apply] at hd
    rw [←IsUnit.div_eq_of_eq_mul (Units.isUnit ((thing Δ) g).2) hd.2] at hd
    simp only [thing4, MonoidHom.coe_comp, Function.comp_apply, divMonoidHom_apply,
      Units.val_div_eq_div_val]
    exact hd.1

lemma thing_fact (Δ : Submonoid 𝓀[K]) (g : U_Δ_Int Δ) : ((thing Δ g).1 / (thing Δ g).2) ∈ Δ.units :=
  by
  constructor
  <;> rw [(by rfl : ((thing Δ g).1 / (thing Δ g).2) = (thing4 Δ g))]
  <;> simp only [Submonoid.coe_comap, Set.mem_preimage, Units.coeHom_apply, SetLike.mem_coe]
  · exact thing_fact2 Δ g
  · convert thing_fact2 Δ g⁻¹
    aesop

noncomputable def U_Δ_Int_to_Δ (Δ : Submonoid 𝓀[K]) :
    U_Δ_Int Δ →* Δ.units := (divMonoidHom.comp (thing Δ)).codRestrict _ (thing_fact Δ)
