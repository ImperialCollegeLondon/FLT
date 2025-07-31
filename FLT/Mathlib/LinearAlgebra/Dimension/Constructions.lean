import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.TensorProduct.Pi
import FLT.Mathlib.Algebra.BigOperators.Group.Finset.Basic
import FLT.Mathlib.RingTheory.TensorProduct.Pi
import Mathlib.GroupTheory.MonoidLocalization.Basic

open scoped TensorProduct

noncomputable def Module.Finite.equivPi (R M : Type*) [Ring R] [StrongRankCondition R]
    [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M] :
    M ≃ₗ[R] Fin (Module.finrank R M) → R :=
  LinearEquiv.ofFinrankEq _ _ <| by rw [Module.finrank_pi, Fintype.card_fin]

noncomputable abbrev TensorProduct.AlgebraTensorModule.finiteEquivPi (R M N : Type*) [CommRing R]
    [CommSemiring N] [Ring M] [Algebra R N] [Module R M] [Module.Free R M] [Module.Finite R M]
    [StrongRankCondition R] :
    N ⊗[R] M ≃ₗ[N] Fin (Module.finrank R M) → N :=
  (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl N N) (Module.Finite.equivPi _ _)).trans
    (TensorProduct.piScalarRight _ _ _ _)

theorem TensorProduct.AlgebraTensorModule.finiteEquivPi_symm_apply (R M N : Type*) [Field R]
    [CommSemiring N] [Ring M] [Algebra R N] [Module R M] [Module.Free R M] [Module.Finite R M]
    [StrongRankCondition R]
    (x : Fin (Module.finrank R M) → R) :
    (finiteEquivPi R M N).symm (fun i => algebraMap R N (x i)) =
      1 ⊗ₜ[R] (Module.Finite.equivPi R M).symm x := by
  simp [Algebra.TensorProduct.piScalarRight_symm_apply_of_algebraMap, Fintype.sum_pi_single_pi]
