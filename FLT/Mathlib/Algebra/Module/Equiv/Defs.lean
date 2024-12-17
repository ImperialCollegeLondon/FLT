import Mathlib.Algebra.Module.Equiv.Defs
import Mathlib.Algebra.Module.Pi
import Mathlib.Algebra.Module.Prod

variable (R : Type*) [Semiring R] in
def LinearEquiv.sumPiEquivProdPi (S T : Type*) (A : S ⊕ T → Type*)
    [∀ st, AddCommMonoid (A st)] [∀ st, Module R (A st)] :
    (∀ (st : S ⊕ T), A st) ≃ₗ[R] (∀ (s : S), A (.inl s)) × (∀ (t : T), A (.inr t)) where
  __ := Equiv.sumPiEquivProdPi _
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

variable (R : Type*) [Semiring R] in
def LinearEquiv.pUnitPiEquiv (f : PUnit → Type*) [∀ x, AddCommMonoid (f x)] [∀ x, Module R (f x)] :
    ((t : PUnit) → (f t)) ≃ₗ[R] f () where
  toFun a := a ()
  invFun a _t := a
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
