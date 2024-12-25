import Mathlib.Topology.Algebra.Module.Equiv
import FLT.Mathlib.Algebra.Module.Equiv.Defs
import FLT.Mathlib.Topology.Homeomorph

/-- Combine a family of linear equivalences into a linear equivalence of `pi`-types.

This is `Equiv.piCongrLeft` as a `ContinuousLinearEquiv` -/
@[simps]
def ContinuousLinearEquiv.piCongrLeft (R : Type*) [Semiring R] {ι ι' : Type*}
    (φ : ι → Type*) [∀ i, AddCommMonoid (φ i)] [∀ i, Module R (φ i)]
    [∀ i, TopologicalSpace (φ i)]
    (e : ι' ≃ ι) : ((i' : ι') → φ (e i')) ≃L[R] (i : ι) → φ i where
  __ := Homeomorph.piCongrLeft e
  __ := LinearEquiv.piCongrLeft R φ e

section Pi

/-- The space of functions from `S ⊕ T` into a family of topological modules
is isomorphic to the product of the functions from `S` and the functions from `T`.

This is `Equiv.sumPiEquivProdPi` as a `ContinuousLinearEquiv`
-/
def ContinuousLinearEquiv.sumPiEquivProdPi (R : Type*) [Semiring R] (S T : Type*)
    (A : S ⊕ T → Type*) [∀ st, AddCommMonoid (A st)] [∀ st, Module R (A st)]
    [∀ st, TopologicalSpace (A st)] :
    ((st : S ⊕ T) → A st) ≃L[R] ((s : S) → A (Sum.inl s)) × ((t : T) → A (Sum.inr t)) where
  __ := LinearEquiv.sumPiEquivProdPi R S T A
  __ := Homeomorph.sumPiEquivProdPi S T A

def ContinuousLinearEquiv.pUnitPiEquiv (R : Type*) [Semiring R] (f : PUnit → Type*)
    [∀ x, AddCommMonoid (f x)] [∀ x, Module R (f x)] [∀ x, TopologicalSpace (f x)] :
    ((t : PUnit) → f t) ≃L[R] f () where
  __ := LinearEquiv.pUnitPiEquiv R f
  __ := Homeomorph.pUnitPiEquiv f
