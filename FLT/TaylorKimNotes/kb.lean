import Mathlib
import FLT.Basic.Reductions
namespace FLT
namespace FreyPackage
open Field
open LinearMap Module
open scoped TensorProduct

local notation "G_K" => absoluteGaloisGroup
local notation "ℤ[G]" => MonoidAlgebra ℤ

variable (p : ℕ) [Fact (Nat.Prime p)]
def rank2_p_torsion (C : WeierstrassCurve ℚ) (hC : C.IsElliptic) :
 (C.n_torsion p ≃ₗ[ZMod p] (Fin 2 → ZMod p)) := sorry

universe u
variable {k : Type u} [Field k] (E : WeierstrassCurve k) [E.IsElliptic] [DecidableEq k]
def WeierstrassCurve.torsionGaloisRepresentation (n : ℕ) (K : Type u) [Field K] [Algebra k K] :
    Representation (ZMod n) (K ≃ₐ[k] K) (E.n_torsion n) := sorry

abbrev r (E : WeierstrassCurve ℚ) : G_K ℚ →* (Fin 2 → ZMod p) →ₗ[ZMod p] (Fin 2 → ZMod p):=sorry
