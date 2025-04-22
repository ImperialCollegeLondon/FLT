import Mathlib.LinearAlgebra.Pi
import FLT.Mathlib.Logic.Equiv.Basic

/-- A class encoding the product scalar multiplication of `∀ b : β, R b` on `∀ a : α, M a`
that is determined by the fibers of a supplied function `f : α → β` on indices.
Specifically, if `f a = b`, then `(r • x) a = r b • x a` for any `r : ∀ b, R b` and
`x : ∀ a, M a`. -/
class Pi.FiberwiseSMul {α β : Type*} (f : α → β) (R : β → Type*) (M : α → Type*)
    [(b : β) → Semiring (R b)] [(a : α) → AddCommMonoid (M a)]
    [(b : β) → (σ : {a // f a = b}) → Module (R b) (M σ)]
    [Module ((b : β) → R b) ((a : α) → M a)] : Prop where
  -- TODO : remove this after https://github.com/leanprover/lean4/pull/7742 ?
  map_smul' (r : (b : β) → R b) (x : (a : α) → M a) (b : β) (σ : {a // f a = b}) :
    (r • x) σ = r b • x σ

theorem Pi.FiberwiseSMul.map_smul {α β : Type*} (f : α → β) (R : β → Type*) (M : α → Type*)
    [(b : β) → Semiring (R b)] [(a : α) → AddCommMonoid (M a)]
    [(b : β) → (σ : {a // f a = b}) → Module (R b) (M σ)]
    [Module ((b : β) → R b) ((a : α) → M a)] [Pi.FiberwiseSMul f R M]
    (r : (b : β) → R b) (x : (a : α) → M a) (b : β) (σ : {a // f a = b}) :
    (r • x) σ = r b • x σ := Pi.FiberwiseSMul.map_smul' r x b σ

/-- Let `f : α → β` be a function on index types. A family of `R b`-linear equivalences, indexed by
`b : β`, between the product over the fiber of `b` under `f` given as
`∀ (σ : { a : α // f a = b }) → γ₁ σ.1) ≃ₗ[R b] γ₂ b` lifts to an equivalence over the products
`∀ a, γ₁ a ≃ₗ[∀ b, R b] ∀ b, γ₂ b` with product scalars `∀ b, R b`, provided that `∀ b, R b` acts on
`∀ a, γ₁ a` fiberwise. This is `Equiv.piCongrFiberwise` as a `LinearEquiv` with product scalars. -/
def LinearEquiv.piScalarPiCongrFiberwise {α : Type*} {β : Type*} {R : β → Type*} {γ₁ : α → Type*}
    {γ₂ : β → Type*} {f : α → β} [(b : β) → Semiring (R b)] [(a : α) → AddCommMonoid (γ₁ a)]
    [(b : β) → AddCommMonoid (γ₂ b)] [(b : β) → (a : { a : α // f a = b }) → Module (R b) (γ₁ a)]
    [(b : β) → Module (R b) (γ₂ b)] [Module (∀ b, R b) (∀ a, γ₁ a)] [Pi.FiberwiseSMul f R γ₁]
    (e : (b : β) → ((σ : { a : α // f a = b }) → γ₁ σ.1) ≃ₗ[R b] γ₂ b) :
    ((a : α) → γ₁ a) ≃ₗ[∀ b, R b] ((b : β) → γ₂ b) where
  __ := Equiv.piCongrFiberwise fun b => (e b).toEquiv
  map_add' _ _ := by funext; simp [← Pi.add_def]
  map_smul' r x := by funext; simp [← (e _).map_smul, Pi.FiberwiseSMul.map_smul, Pi.smul_def]

def LinearEquiv.piScalarPiComm {α β : Type*} (R : α → Type*) (φ : α → β → Type*) [∀ a, Semiring (R a)]
    [∀ a b, AddCommMonoid (φ a b)] [∀ a b, Module (R a) (φ a b)] :
    ((a : α) → (b : β) → φ a b) ≃ₗ[∀ a, R a] ((b : β) → (a : α) → φ a b) where
  __ := Equiv.piComm φ
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
