import Mathlib.NumberTheory.NumberField.Completion
import Mathlib.Topology.Algebra.Module.ModuleTopology
import FLT.Mathlib.Algebra.Algebra.Hom
import FLT.Mathlib.Algebra.Algebra.Pi
import FLT.Mathlib.Algebra.Algebra.Bilinear
import FLT.Mathlib.Analysis.Normed.Ring.WithAbs
import FLT.NumberField.Embeddings

open scoped TensorProduct

/-!
# The completion of a number field at an infinite place
-/

noncomputable section

namespace NumberField.InfinitePlace.Completion

open AbsoluteValue.Completion UniformSpace.Completion

variable {K L : Type*} [Field K] [Field L] [Algebra K L] {v : InfinitePlace K} {w : InfinitePlace L}

def comapSemialgHom (h : w.comap (algebraMap K L) = v) :
    v.Completion →ₛₐ[algebraMap (WithAbs v.1) (WithAbs w.1)] w.Completion :=
  mapSemialgHom _ <| (WithAbs.uniformContinuous_algebraMap (v.comp_of_comap_eq _ h)).continuous

theorem comapSemialgHom_cont (h : w.comap (algebraMap K L) = v) :
    Continuous (comapSemialgHom h) := continuous_map

variable (L v)

abbrev baseChange :
    v.Completion →ₛₐ[algebraMap K L] ((wv : v.ExtensionPlace L) → wv.1.Completion) :=
  Pi.semialgHom _ _ fun wv => comapSemialgHom wv.2

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
instance : TopologicalSpace (L ⊗[K] v.Completion) := moduleTopology v.Completion _

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
instance : IsModuleTopology v.Completion (L ⊗[K] v.Completion) :=
  ⟨rfl⟩

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
def piExtensionPlaceContinuousAlgHom :
    L ⊗[K] v.Completion →A[L] ((wv : v.ExtensionPlace L) → wv.1.Completion) where
  __ := SemialgHom.baseChange_of_algebraMap (baseChange L v)
  cont := by
    apply IsModuleTopology.continuous_of_ringHom (R := v.Completion)
    show Continuous (RingHom.comp _ Algebra.TensorProduct.includeRight.toRingHom)
    convert (continuous_pi fun wv : v.ExtensionPlace L => comapSemialgHom_cont wv.2) using 1
    ext
    simp [baseChange]

end NumberField.InfinitePlace.Completion
