import Mathlib.Algebra.Group.Pi.Units
import Mathlib.Algebra.Group.Submonoid.Units
import Mathlib.Topology.Algebra.Constructions
import Mathlib.Topology.Algebra.ContinuousMonoidHom

lemma Submonoid.units_isOpen {M : Type*} [TopologicalSpace M] [Monoid M] [ContinuousMul M]
    {U : Submonoid M} (hU : IsOpen (U : Set M)) : IsOpen (U.units : Set Mˣ) := by
  sorry -- FLT#587

lemma Submonoid.units_isCompact {M : Type*} [TopologicalSpace M] [Monoid M] [ContinuousMul M]
    [T2Space M] {U : Submonoid M} (hU : IsCompact (U : Set M)) : IsCompact (U.units : Set Mˣ) := by
  sorry -- FLT#588

/-- The monoid homeomorphism between the units of a product of topological monoids
and the product of the units of the monoids.
-/
@[nolint unusedArguments] -- continuity will be used when the sorries are filled in
-- and then this can be removed
def ContinuousMulEquiv.piUnits {ι : Type*}
    {M : ι → Type*} [(i : ι) → Monoid (M i)] [(i : ι) → TopologicalSpace (M i)]
    [(i : ι) → ContinuousMul (M i)] :
    (Π i, M i)ˣ ≃ₜ* Π i, (M i)ˣ where
  __ := MulEquiv.piUnits
  continuous_toFun := sorry -- #581
  continuous_invFun := sorry -- #581
