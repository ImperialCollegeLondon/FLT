import FLT.HaarMeasure.HaarChar.Ring
import FLT.NumberField.AdeleRing
import FLT.Hacks.RightAlgebraInstances
import Mathlib.NumberTheory.NumberField.AdeleRing

variable (K : Type*) [Field K] [NumberField K]
variable (B : Type*) [Ring B] [Algebra K B] [FiniteDimensional K B]

open scoped TensorProduct

open NumberField MeasureTheory

open scoped RightAlgebra in
/-- Left multiplication by an element of Bˣ on B ⊗ 𝔸_K does not scale additive
Haar measure. In other words, Bˣ is in the kernel of the `ringHaarChar` of `B ⊗ 𝔸_K`.
-/
lemma NumberField.AdeleRing.units_mem_ringHaarCharacter_ker
    [MeasurableSpace (B ⊗[K] AdeleRing (𝓞 K) K)] [BorelSpace (B ⊗[K] AdeleRing (𝓞 K) K)]
    (b : Bˣ) :
    (Units.map Algebra.TensorProduct.includeLeftRingHom.toMonoidHom b :
      (B ⊗[K] AdeleRing (𝓞 K) K)ˣ) ∈
    ringHaarChar_ker (B ⊗[K] AdeleRing (𝓞 K) K) := sorry

open scoped RightAlgebra in
/-- Right multiplication by an element of Bˣ on B ⊗ 𝔸_K does not scale additive
Haar measure.
-/
lemma NumberField.AdeleRing.addEquivAddHaarChar_mulRight_unit_eq_one
    [MeasurableSpace (B ⊗[K] AdeleRing (𝓞 K) K)] [BorelSpace (B ⊗[K] AdeleRing (𝓞 K) K)]
    (b : Bˣ) :
    addEquivAddHaarChar
      (ContinuousAddEquiv.mulRight
        (Units.map Algebra.TensorProduct.includeLeftRingHom.toMonoidHom b :
      (B ⊗[K] AdeleRing (𝓞 K) K)ˣ)) = 1 := by
  sorry
