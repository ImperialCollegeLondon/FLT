import Mathlib.NumberTheory.NumberField.Completion
import FLT.Mathlib.Analysis.Normed.Ring.WithAbs
import FLT.NumberField.Embeddings

/-!
# The completion of a number field at an infinite place
-/

noncomputable section

namespace NumberField.InfinitePlace.Completion

open AbsoluteValue.Completion

variable {K L : Type*} [Field K] [Field L] [Algebra K L] {v : InfinitePlace K} {w : InfinitePlace L}

theorem algebraMap_eq_coe :
    (algebraMap K v.Completion).toFun = ((↑) : K → v.Completion) := rfl

instance {wv : v.ExtensionPlace L} : Algebra v.Completion wv.1.Completion :=
  mapOfComp wv.abs_comp |>.toAlgebra

open UniformSpace.Completion in
def extensionPlaceContinuousAlgHom (wv : v.ExtensionPlace L) :
    v.Completion →A[v.Completion] wv.1.Completion where
  __ := mapOfComp wv.abs_comp
  commutes' (r : _) := by
    simp only [RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe,
      MonoidHom.coe_coe, mapRingHom_apply, algebraMap_eq_coe, map_coe
      <| WithAbs.uniformContinuous_algebraMap wv.abs_comp]; rfl
  cont := continuous_map

end NumberField.InfinitePlace.Completion
