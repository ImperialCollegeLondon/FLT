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

def UpperTriangularToProd {k : Type*} [CommRing k] : UpperTriangular k →+* k × k where
  toFun M := (M.1 0 0, M.1 1 1)
  map_one' := sorry
  map_mul' := sorry
  map_zero' := sorry
  map_add' := sorry

/-- Submonoid of M_2(k) consisting of matrices (d*r q; 0 r) with d ∈ Δ -/
def R_Δ {k : Type*} [CommRing k] (Δ : Submonoid k) :
    Submonoid (Matrix (Fin 2) (Fin 2) k) where
      carrier := {M | M 1 0 = 0 ∧ ∃ d ∈ Δ, M 0 0 = d * M 1 1}
      mul_mem' := by
        rintro _ _ ⟨hM0, d, hd, hMd⟩ ⟨hN0, e, he, hNe⟩
        refine ⟨by simp [Matrix.mul_apply, hM0, hN0], ?_⟩
        exact ⟨d * e, mul_mem hd he, by simp [Matrix.mul_apply, hM0, hN0, hMd, hNe]; ring⟩
      one_mem' := ⟨rfl, 1, one_mem _, (mul_one 1).symm⟩

--#check Matrix.map

/-- The subgroup of GL_2(K) consisting of matrices with integer entries and which are
  congruent modulo the maximal ideal to something of the form (d*a b; 0 a) with d ∈ Δ -/
noncomputable def U_Δ (Δ : Submonoid 𝓀[K]) : Subgroup (GL (Fin 2) K) :=
  -- first pull back R_Δ to get a submonoid of M₂(𝒪[K])
  (((R_Δ Δ).comap (RingHom.mapMatrix (IsLocalRing.residue 𝒪[K]))).map <|
    -- then push it forwards to get a submonoid of M₂(K) and then take the units
    RingHom.mapMatrix 𝒪[K].subtype).units

lemma U_Δ_le_integer_matrix_units (Δ : Submonoid 𝓀[K]) : U_Δ K Δ ≤ 𝒪[K].matrix.units := sorry

-- need some random statement like this to do the next thing
lemma mem_U_Δ_iff (M : GL (Fin 2) 𝒪[K]) (Δ : Submonoid 𝓀[K]) :
    Units.map (RingHom.mapMatrix 𝒪[K].subtype).toMonoidHom M ∈ U_Δ K Δ ↔
      M 1 0 ∈ 𝓂[K] ∧ M 0 0 ∉ 𝓂[K] ∧ M 1 1 ∉ 𝓂[K] ∧ ∃ d ∈ Δ.units,
      IsLocalRing.residue 𝒪[K] (M 0 0) * (d : 𝓀[K]) = IsLocalRing.residue 𝒪[K] (M 1 1) := sorry

def U_Δ_to_Δ (Δ : Submonoid 𝓀[K]) : U_Δ K Δ →* Δˣ where
  toFun M := ⟨⟨IsLocalRing.residue ↥𝒪[K] ⟨M.1 0 0 / (M.1 1 1), sorry⟩, sorry⟩,
    ⟨IsLocalRing.residue ↥𝒪[K] ⟨M.1 0 0 / (M.1 1 1), sorry⟩, sorry⟩,
    sorry, sorry⟩
  map_one' := by ext; simpa using by exact map_one (IsLocalRing.residue 𝒪[K])
  map_mul' := sorry
