/-
Copyright (c) 2025 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Salvatore Mercuri
-/
module

public import Mathlib.Algebra.Algebra.Pi
public import FLT.Mathlib.Algebra.Algebra.Hom

/-!
# Pi

Material destined for Mathlib.
-/

@[expose] public section

/-- A family of semialgebra homomorphisms `g i : A →ₛₐ[φ] f i` defines a single
semialgebra homomorphism `A →ₛₐ[φ] (i : I) → f i` to the product algebra. -/
def Pi.semialgHom {I : Type*} {R S : Type*} (f : I → Type*) [CommSemiring R] [CommSemiring S]
    (φ : R →+* S) [s : (i : I) → Semiring (f i)] [(i : I) → Algebra S (f i)] {A : Type*}
    [Semiring A] [Algebra R A] (g : (i : I) → A →ₛₐ[φ] f i) :
    A →ₛₐ[φ] (i : I) → f i where
  __ := Pi.ringHom fun i ↦ (g i).toRingHom
  map_smul' r a := by ext; simp

@[simp]
theorem Pi.semialgHom_apply {I : Type*} {R S : Type*} (f : I → Type*) [CommSemiring R]
    [CommSemiring S]
    (φ : R →+* S) [s : (i : I) → Semiring (f i)] [(i : I) → Algebra S (f i)] {A : Type*}
    [Semiring A] [Algebra R A] (g : (i : I) → A →ₛₐ[φ] f i) (a : A) (i : I) :
    (Pi.semialgHom _ φ g) a i = g i a :=
  rfl

/-- Given a reindexing `r : I → J` and a family of semialgebra homs
`p i : g (r i) →ₛₐ[φ] f i`, build a semialgebra hom from the product over `J` of the `g j` to
the product over `I` of the `f i`. -/
def Pi.semialgHomPi {I J : Type*} {R S : Type*} (f : I → Type*)
    (g : J → Type*) [CommSemiring R] [CommSemiring S] {φ : R →+* S}
    [(i : I) → Semiring (f i)] [(i : I) → Algebra S (f i)] [(j : J) → Semiring (g j)]
    [(j : J) → Algebra R (g j)] {r : I → J} (p : (i : I) → g (r i) →ₛₐ[φ] f i) :
    ((j : J) → g j) →ₛₐ[φ] (i : I) → f i where
  toFun x w := p w (x (r w))
  map_one' := by simp [Pi.one_def]
  map_mul' x y := funext fun w => by simp [map_mul]
  map_zero' := by simp [Pi.zero_def]
  map_add' x y := funext fun w => by simp [map_add]
  map_smul' k x := funext fun w => (p w).map_smul' k (x (r w))

@[simp]
theorem Pi.semialgHomPi_apply {I J : Type*} {R S : Type*} (f : I → Type*)
    (g : J → Type*) [CommSemiring R] [CommSemiring S] {φ : R →+* S}
    [(i : I) → Semiring (f i)] [(i : I) → Algebra S (f i)] [(j : J) → Semiring (g j)]
    [(j : J) → Algebra R (g j)] {r : I → J} (p : (i : I) → g (r i) →ₛₐ[φ] f i)
    (a : (j : J) → g j) (i : I) :
    Pi.semialgHomPi _ _ p a i = p i (a (r i)) := rfl

/-- Let `f : α → β` be a function on index types. A family of `R`-algebra equivalences, indexed by
`b : β`, between the product over the fiber of `b` under `f` given as
`∀ (σ : { a : α // f a = b }) → γ₁ σ.1) ≃ₐ[R] γ₂ b` lifts to an equivalence over the products
`∀ a, γ₁ a ≃ₐ[R] ∀ b, γ₂ b`. This is `Equiv.piCongrFiberwise` as an `AlgEquiv`. -/
def AlgEquiv.piCongrFiberwise {α : Type*} {β : Type*} {R : Type*} {γ₁ : α → Type*} {γ₂ : β → Type*}
    {f : α → β} [CommSemiring R] [(a : α) → Semiring (γ₁ a)] [(b : β) → Semiring (γ₂ b)]
    [(a : α) → Algebra R (γ₁ a)] [(b : β) → Algebra R (γ₂ b)]
    (e : (b : β) → ((x : { x : α // f x = b }) → γ₁ x.1) ≃ₐ[R] γ₂ b) :
    ((a : α) → γ₁ a) ≃ₐ[R] ((b : β) → γ₂ b) where
  __ := Equiv.piCongrFiberwise fun _ => (e _).toEquiv
  map_add' _ _ := by funext b; simp [← Pi.add_def]
  map_mul' _ _ := by funext b; simp [← Pi.mul_def]
  commutes' r := by funext b; simp [← (e b).commutes' r, Pi.algebraMap_def]
