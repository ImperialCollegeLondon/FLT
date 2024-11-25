import Mathlib

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

open NumberField

variable [Algebra K (InfiniteAdeleRing L)] [IsScalarTower K L (InfiniteAdeleRing L)]

/-- The canonical map from the infinite adeles of K to the infinite adeles of L -/
def NumberField.InfiniteAdeleRing.baseChange :
    InfiniteAdeleRing K →ₐ[K] InfiniteAdeleRing L :=
  sorry

open scoped TensorProduct

/-- The canonical `L`-algebra isomorphism from `L ⊗_K K_∞` to `L_∞` induced by the
`K`-algebra base change map `K_∞ → L_∞`. -/
def NumberField.InfiniteAdeleRing.baseChangeIso :
    (L ⊗[K] (InfiniteAdeleRing K)) ≃ₐ[L] InfiniteAdeleRing L :=
  sorry
