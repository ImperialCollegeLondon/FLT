import Mathlib
import FLT.NumberField.Completion
import FLT.Mathlib.Algebra.Algebra.Pi

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

open NumberField InfinitePlace

open scoped Classical TensorProduct

noncomputable local instance : Algebra K (InfiniteAdeleRing L) := Pi.algebra _ _

-- TODO should be →A[K]
/-- The canonical map from the infinite adeles of K to the infinite adeles of L -/
noncomputable def NumberField.InfiniteAdeleRing.baseChange :
    InfiniteAdeleRing K →ₐ[K] InfiniteAdeleRing L :=
  letI (v : InfinitePlace K) := (Completion.baseChange L v).restrictScalars K |>.toAlgHom
  (AlgEquiv.piCongrLeft K _ (Equiv.sigmaFiberEquiv _) |>.toAlgHom).comp <|
    (AlgEquiv.piCurry K _).symm.toAlgHom.comp (Pi.mapAlgHom K _ _ this)

-- TODO should be ≃A[L]
/-- The canonical `L`-algebra isomorphism from `L ⊗_K K_∞` to `L_∞` induced by the
`K`-algebra base change map `K_∞ → L_∞`. -/
def NumberField.InfiniteAdeleRing.baseChangeIso :
    (L ⊗[K] (InfiniteAdeleRing K)) ≃ₐ[L] InfiniteAdeleRing L :=
  sorry
