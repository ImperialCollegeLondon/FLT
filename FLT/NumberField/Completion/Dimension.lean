import Mathlib.NumberTheory.NumberField.Completion
import FLT.NumberField.Embeddings

/-! # Dimension formula for L ⊗[K] v.Completion -/

open scoped TensorProduct

noncomputable section

namespace NumberField.InfinitePlace

variable {K : Type*} [Field K] {L : Type*} [Field L] [Algebra K L] {v : InfinitePlace K}
  {w : InfinitePlace L}

/-! Isomorphisms between v.Completion and ℝ/ℂ

Note that mathlib already has `RingEquiv` and `IsometryEquiv`, we add here some `AlgEquiv` as
well as further API for the `RingEquiv` and `IsometryEquiv`. -/

class IsReal' (v : InfinitePlace K) : Prop where
  isReal : v.IsReal

class IsComplex' (v : InfinitePlace K) : Prop where
  isComplex : v.IsComplex

namespace Completion

instance algebraRealOfIsReal [h : v.IsReal'] : Algebra v.Completion ℝ :=
  RingHom.toAlgebra (ringEquivRealOfIsReal h.isReal)

def algEquivRealOfIsReal [h : v.IsReal']  :
    v.Completion ≃ₐ[v.Completion] ℝ :=
  AlgEquiv.ofRingEquiv (fun _ => rfl)

instance algebraComplexOfIsComplex [h : v.IsComplex'] : Algebra v.Completion ℂ :=
  RingHom.toAlgebra (ringEquivComplexOfIsComplex h.isComplex)

def algEquivComplexOfIsComplex [h : v.IsComplex'] :
    v.Completion ≃ₐ[v.Completion] ℂ :=
  AlgEquiv.ofRingEquiv (fun _ => rfl)

def algebraComplexOfIsComplexStar [h : v.IsComplex'] :
    Algebra v.Completion ℂ :=
  RingHom.toAlgebra <| starRingAut.toRingHom.comp (ringEquivComplexOfIsComplex h.isComplex)

attribute [local instance] algebraComplexOfIsComplexStar in
def algEquivComplexOfIsComplexStar [h : v.IsComplex'] :
    v.Completion ≃ₐ[v.Completion] ℂ :=
  AlgEquiv.ofRingEquiv (f := (ringEquivComplexOfIsComplex h.isComplex).trans starRingAut)
    (fun _ => rfl)

end Completion
/-! Main result -/
