import FLT.Deformations.RepresentationTheory.Basic
import Mathlib

-- The problem: uncommenting the FLT import on line 1 breaks the proof.
-- Show this by uncommenting the FLT import and then commenting it out again, and then
-- replace the import with the FLT files which it imports and see if this helps.
-- I don't know if this is relevant but I was trying to do this when not connected
-- to the internet (e.g. imagine I'm on the tube in London)

open Field

variable (K : Type*) [Field K]

-- instance : MulSemiringAction (absoluteGaloisGroup K) (AlgebraicClosure K) :=
--   inferInstance -- AlgEquiv.applyMulSemiringAction

instance : MulSemiringAction (absoluteGaloisGroup K) (AlgebraicClosure K) :=
  AlgEquiv.applyMulSemiringAction

-- -- We have this, right?
-- instance : MulSemiringAction (absoluteGaloisGroup K) (AlgebraicClosure K) where
--   one_smul _ := rfl
--   mul_smul _ _ _ := rfl
--   smul_zero g := map_zero g.toAlgHom
--   smul_add g := map_add g.toAlgHom
--   smul_one g := map_one g.toAlgHom
--   smul_mul g := map_mul g.toAlgHom

-- wtf deleting this causes error?
--instance (M R : Type*) [Monoid M] [Semiring R] [MulSemiringAction M R] :
--    MulAction M R := inferInstance

-- #exit here  for Oliver

#check AlgEquiv.applyMulSemiringAction
--#synth MulSemiringAction
#synth MulAction (absoluteGaloisGroup ℚ_[2]) (AlgebraicClosure ℚ_[2])

/-
Next question: what is the point of

-/
