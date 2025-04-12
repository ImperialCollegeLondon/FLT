import Mathlib.Topology.Algebra.Module.Equiv
import Mathlib.Topology.Algebra.ContinuousMonoidHom

def ContinuousLinearEquiv.toContinuousAddEquiv
    {R₁ R₂ : Type*} [Semiring R₁] [Semiring R₂] {σ₁₂ : R₁ →+* R₂}  {σ₂₁ : R₂ →+* R₁}
    [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂] {M₁ M₂ : Type*} [TopologicalSpace M₁]
    [AddCommMonoid M₁] [TopologicalSpace M₂] [AddCommMonoid M₂] [Module R₁ M₁] [Module R₂ M₂]
    (e : M₁ ≃SL[σ₁₂] M₂) :
    M₁ ≃ₜ+ M₂ where
  __ := e.toLinearEquiv.toAddEquiv
  continuous_invFun := e.symm.continuous

@[simps!]
def ContinuousLinearEquiv.restrictScalars (R : Type*) {S M M₂ : Type*}
    [Semiring R] [Semiring S] [AddCommMonoid M] [AddCommMonoid M₂] [Module R M] [Module R M₂]
    [Module S M] [Module S M₂] [LinearMap.CompatibleSMul M M₂ R S] [TopologicalSpace M]
    [TopologicalSpace M₂] (f : M ≃L[S] M₂) :
    M ≃L[R] M₂ where
  __ := f.toLinearEquiv.restrictScalars R
  invFun := f.symm
  continuous_toFun := f.continuous_toFun
  continuous_invFun := f.continuous_invFun
