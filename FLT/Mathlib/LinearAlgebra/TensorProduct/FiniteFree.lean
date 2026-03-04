import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic

open TensorProduct

/--
The M-algebra isomorphism `M ⊗ V ≃ₗ[M] (ι → M)` coming from the canonical
`ι`-indexed basis of a finite free `R`-module `V`.
-/
noncomputable def LinearEquiv.chooseBasis_piScalarRight (R : Type*) (M : Type*) (V : Type*)
    -- Probably OK for Semirings?
    -- commutativity needed in the below construction for `TensorProduct.piScalarRight`
    [CommSemiring M] [CommRing R] [Algebra R M]
    [AddCommGroup V] [Module R V] [Module.Finite R V] [Module.Free R V] :
    (M ⊗[R] V) ≃ₗ[M] (Module.Free.ChooseBasisIndex R V → M) := by
  letI b := Module.Free.chooseBasis R V
  letI f := b.equivFun
  refine (LinearEquiv.baseChange R M V (Module.Free.ChooseBasisIndex R V → R) f) ≪≫ₗ ?_
  exact TensorProduct.piScalarRight R M M (Module.Free.ChooseBasisIndex R V)
