import Mathlib.NumberTheory.NumberField.Completion
import Mathlib.Topology.Algebra.Module.ModuleTopology
import FLT.Mathlib.Analysis.Normed.Ring.WithAbs
import FLT.NumberField.Embeddings

open scoped TensorProduct

/-!
# The completion of a number field at an infinite place
-/

noncomputable section

namespace NumberField.InfinitePlace.Completion

open AbsoluteValue.Completion

variable {K L : Type*} [Field K] [Field L] [Algebra K L] {v : InfinitePlace K} {w : InfinitePlace L}

instance {wv : v.ExtensionPlace L} : Algebra v.Completion wv.1.Completion :=
  mapOfComp wv.abs_comp |>.toAlgebra

theorem algebraMap_eq_coe :
    (algebraMap K v.Completion).toFun = ((↑) : K → v.Completion) := rfl

@[simp]
theorem algebraMap_apply (wv : v.ExtensionPlace L) (x : v.Completion) :
    algebraMap v.Completion wv.1.Completion x = UniformSpace.Completion.map
      (algebraMap (WithAbs v.1) (WithAbs wv.1.1)) x :=
  rfl

@[simp]
theorem algebraMap_coe (wv : v.ExtensionPlace L) (k : K) :
    algebraMap v.Completion wv.1.Completion k = algebraMap (WithAbs v.1) (WithAbs wv.1.1) k := by
  rw [algebraMap_apply]
  exact UniformSpace.Completion.map_coe (WithAbs.uniformContinuous_algebraMap wv.abs_comp) _

theorem algebraMap_comp (wv : v.ExtensionPlace L) (k : K) :
    algebraMap K wv.1.Completion k =
      algebraMap v.Completion wv.1.Completion (algebraMap K v.Completion k) := by
  simp only [UniformSpace.Completion.algebraMap_def, algebraMap_coe _]
  rfl

instance {wv : v.ExtensionPlace L} : IsScalarTower K v.Completion wv.1.Completion :=
  IsScalarTower.of_algebraMap_eq (algebraMap_comp wv)

open UniformSpace.Completion in
def extensionPlaceContinuousAlgHom (wv : v.ExtensionPlace L) :
    v.Completion →A[v.Completion] wv.1.Completion where
  __ := mapOfComp wv.abs_comp
  commutes' (r : _) := by
    simp only [RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe,
      MonoidHom.coe_coe, mapRingHom_apply, algebraMap_eq_coe, map_coe
      <| WithAbs.uniformContinuous_algebraMap wv.abs_comp]; rfl
  cont := continuous_map

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
instance : TopologicalSpace (L ⊗[K] v.Completion) := moduleTopology v.Completion _

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
instance : IsModuleTopology v.Completion (L ⊗[K] v.Completion) :=
  ⟨rfl⟩

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
def tensorPiExtensionPlaceContinuousAlgHom :
    L ⊗[K] v.Completion →A[L] ((wv : v.ExtensionPlace L) → wv.1.Completion) where
  __ := Algebra.TensorProduct.lift
    (Pi.algHom L _ fun wv => ⟨algebraMap L wv.1.Completion, fun _ => rfl⟩)
    (Pi.algHom K _ fun wv => (extensionPlaceContinuousAlgHom wv).restrictScalars K)
    (fun _ _ => Commute.all _ _)
  cont := by
    apply IsModuleTopology.continuous_of_ringHom (R := v.Completion)
    show Continuous (RingHom.comp _ (Algebra.TensorProduct.includeRight.toRingHom))
    convert (continuous_pi fun wv => (extensionPlaceContinuousAlgHom wv).cont) using 1
    ext
    simp [extensionPlaceContinuousAlgHom]

end NumberField.InfinitePlace.Completion
