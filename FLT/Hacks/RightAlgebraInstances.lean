import FLT.Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.GroupTheory.MonoidLocalization.Basic
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.RingTheory.TensorProduct.Free
/-

# Right algebra instances

This file enables you to write `open scoped RightAlgebra` and magically `A ⊗[R] B`
becomes a `B`-algebra as well as an `A`-algebra, and you get instances like
`[Module.Finite R A] → [Module.Finite B (A ⊗[R] B)]`.

Mathlib would not have this hack because `A ⊗[R] A` is now an `A`-algebra in two
different ways. But this situation will not arise in the cases where we use this,
and it's very convenient to open the scope temporarily in order to prove theorems
which can be used without the scope open.
-/

scoped[RightAlgebra] attribute [instance] Algebra.TensorProduct.rightAlgebra

open scoped TensorProduct

namespace RightAlgebra

section semiring

variable (R : Type*) [CommSemiring R]
variable (A : Type*) [CommSemiring A] [Algebra R A]
variable (B : Type*) [Semiring B] [Algebra R B]

--noncomputable example : A ⊗[R] B ≃ₗ[R] B ⊗[R] A := TensorProduct.comm R A B
--noncomputable example : A ⊗[R] B ≃ₐ[R] B ⊗[R] A := Algebra.TensorProduct.comm R A B

noncomputable def TensorProduct.comm : A ⊗[R] B ≃ₐ[A] B ⊗[R] A where
  __ := Algebra.TensorProduct.comm R A B
  commutes' _ := rfl

scoped instance [Module.Finite R B] : Module.Finite A (B ⊗[R] A) :=
  Module.Finite.equiv (TensorProduct.comm R A B).toLinearEquiv

scoped instance [Module.Free R B] : Module.Free A (B ⊗[R] A) :=
  Module.Free.of_equiv (TensorProduct.comm R A B).toLinearEquiv

noncomputable scoped instance [TopologicalSpace A] : TopologicalSpace (B ⊗[R] A) :=
  moduleTopology A (B ⊗[R] A)

scoped instance [TopologicalSpace A] : IsModuleTopology A (B ⊗[R] A) := ⟨rfl⟩

end semiring

section ring

variable (R : Type*) [CommRing R]
variable (A : Type*) [CommRing A] [Algebra R A]
variable (B : Type*) [Ring B] [Algebra R B]

scoped instance [TopologicalSpace A] [IsTopologicalRing A] [Module.Finite R B] :
    IsTopologicalRing (B ⊗[R] A) :=
  IsModuleTopology.Module.topologicalRing A _

scoped instance [TopologicalSpace A] [IsTopologicalRing A]
    [LocallyCompactSpace A] [Module.Finite R B] :
    LocallyCompactSpace (B ⊗[R] A) := IsModuleTopology.locallyCompactSpaceOfFinite A

end ring

end RightAlgebra
