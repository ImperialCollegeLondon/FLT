import FLT.HaarMeasure.HaarChar.Ring
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.NumberField.AdeleRing
import FLT.Mathlib.Topology.Algebra.Module.ModuleTopology
import FLT.Mathlib.RingTheory.TensorProduct.Finite
import FLT.Hacks.RightActionInstances
import FLT.NumberField.AdeleRing

variable (K : Type*) [Field K] [NumberField K]
variable (B : Type*) [Ring B] [Algebra K B] [FiniteDimensional K B]

open scoped TensorProduct

open NumberField MeasureTheory


open scoped TensorProduct.RightActions

variable [MeasurableSpace (B ⊗[K] AdeleRing (𝓞 K) K)] [BorelSpace (B ⊗[K] AdeleRing (𝓞 K) K)]

lemma NumberField.AdeleRing.units_mem_ringHaarCharacter_ker (b : Bˣ) :
  (Units.map Algebra.TensorProduct.includeLeftRingHom.toMonoidHom b :
    (B ⊗[K] AdeleRing (𝓞 K) K)ˣ) ∈ ringHaarChar_ker (B ⊗[K] AdeleRing (𝓞 K) K) := sorry
