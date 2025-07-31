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
  mul_mem' := sorry
  one_mem' := sorry
  add_mem' := sorry
  zero_mem' := sorry
  neg_mem' := sorry

lemma mem_upperTriangular_iff {k : Type*} [CommRing k] (M : Matrix (Fin 2) (Fin 2) k) :
    M ∈ UpperTriangular k ↔ M 1 0 = 0 := sorry

def UpperTriangularToProd {k : Type*} [CommRing k] : UpperTriangular k →+* k × k where
  toFun M := (M.1 0 0, M.1 1 1)
  map_one' := sorry
  map_mul' := sorry
  map_zero' := sorry
  map_add' := sorry

end M2

namespace GL2

def UpperTriangular (k : Type*) [CommRing k] : Subgroup (GL (Fin 2) k) :=
  (M2.UpperTriangular k).units

def UpperTriangularToProd {k : Type*} [CommRing k] : UpperTriangular k →* kˣ × kˣ where
  toFun M := (⟨M.1 0 0, (M⁻¹).1 0 0, sorry, sorry⟩, ⟨M.1 1 1, (M⁻¹).1 1 1, sorry, sorry⟩)
  map_one' := sorry
  map_mul' := sorry

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

lemma thing3 {k : Type*} [CommRing k] (Δ : Submonoid k) : R_Δ Δ ≤ GL2.UpperTriangular k := sorry

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

lemma thing2 (Δ : Submonoid 𝓀[K]) : U_Δ_Int Δ ≤ GL2.UpperTriangular 𝒪[K] := sorry

def MonoidHom.restrict' {G H : Type*} [Monoid G] [Monoid H] (φ : G →* H)
  (S : Submonoid H) : S.comap φ →* S :=(φ.comp ((S.comap φ).subtype)).codRestrict _ (by aesop)

noncomputable def thing (Δ : Submonoid 𝓀[K]) : U_Δ_Int Δ →* 𝓀[K]ˣ × 𝓀[K]ˣ :=
  GL2.UpperTriangularToProd.comp ((Subgroup.inclusion (GL2.thing3 Δ)).comp ((Units.map
    (RingHom.mapMatrix (m := Fin 2) (IsLocalRing.residue 𝒪[K])).toMonoidHom).restrict' _))

lemma thing_fact (Δ : Submonoid 𝓀[K]) (g : U_Δ_Int Δ) : ((thing Δ g).1 / (thing Δ g).2) ∈ Δ.units :=
  sorry

noncomputable def U_Δ_Int_to_Δ (Δ : Submonoid 𝓀[K]) :
    U_Δ_Int Δ →* Δ.units := (divMonoidHom.comp (thing Δ)).codRestrict _ (thing_fact Δ)
