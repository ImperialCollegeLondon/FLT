import FLT.HaarMeasure.HaarChar.Ring
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.NumberField.AdeleRing
import FLT.Mathlib.Topology.Algebra.Module.ModuleTopology
import FLT.Mathlib.RingTheory.TensorProduct.Finite

variable (K : Type*) [Field K] [NumberField K]
variable (B : Type*) [Ring B] [Algebra K B] [FiniteDimensional K B]

open scoped TensorProduct

open NumberField MeasureTheory

-- boilerplate to make `B ⊗[K] AdeleRing (𝓞 K) K` a locally compact space
-- TODO put this boilerplate into some scope?

noncomputable instance : Algebra (AdeleRing (𝓞 K) K) (B ⊗[K] AdeleRing (𝓞 K) K) :=
  Algebra.TensorProduct.rightAlgebra

instance : Module.Finite (AdeleRing (𝓞 K) K) (B ⊗[K] AdeleRing (𝓞 K) K) :=
  inferInstance

noncomputable instance : TopologicalSpace (B ⊗[K] AdeleRing (𝓞 K) K) :=
  moduleTopology (AdeleRing (𝓞 K) K) _

-- AdeleRing is locally compacy, B/K is finite
instance : LocallyCompactSpace (B ⊗[K] AdeleRing (𝓞 K) K) := sorry

local instance : IsModuleTopology (AdeleRing (𝓞 K) K) (B ⊗[K] AdeleRing (𝓞 K) K) := ⟨rfl⟩

local instance : IsTopologicalRing (B ⊗[K] AdeleRing (𝓞 K) K) :=
  IsModuleTopology.Module.topologicalRing (AdeleRing (𝓞 K) K) _

variable [MeasurableSpace (B ⊗[K] AdeleRing (𝓞 K) K)] [BorelSpace (B ⊗[K] AdeleRing (𝓞 K) K)]

lemma NumberField.AdeleRing.units_mem_ringHaarCharacter_ker (b : Bˣ) :
  (Units.map Algebra.TensorProduct.includeLeftRingHom.toMonoidHom b :
    (B ⊗[K] AdeleRing (𝓞 K) K)ˣ) ∈ ringHaarChar_ker (B ⊗[K] AdeleRing (𝓞 K) K) := sorry
