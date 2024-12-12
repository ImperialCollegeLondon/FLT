
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.RingTheory.FreeCommRing
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.Order.DirectedInverseSystem
import Mathlib.Tactic.SuppressCompilation

/-!
# Inverse limit of modules, abelian groups, rings.

See Atiyah-Macdonald PP.32-33, Matsumura PP.269-270

## Main definitions

* `InverseSystem f`
* `Module.InverseLimit G f`
* `AddCommGroup.InverseLimit G f`
* `Ring.InverseLimit G f`

-/

suppress_compilation

universe u v v' v'' w u₁

open Submodule

variable {R : Type u} [Ring R]
variable {ι : Type v}
variable [Preorder ι]
variable (G : ι → Type w)

namespace Module

variable [∀ i, AddCommGroup (G i)] [∀ i, Module R (G i)]
variable {G}
variable (f : ∀ i j, i ≤ j → G j →ₗ[R] G i)

/-- A copy of `InverseSystem.map_self` specialized to linear maps, as otherwise the
`fun i j h ↦ f i j h` can confuse the simplifier. -/
nonrec theorem InverseSystem.map_self [InverseSystem (F := G) fun i j h => f i j h] (i x h) :
    f i i h x = x :=
  InverseSystem.map_self (f := (f · · ·)) x

/-- A copy of `InverseSystem.map_map` specialized to linear maps, as otherwise the
`fun i j h ↦ f i j h` can confuse the simplifier. -/
nonrec theorem InverseSystem.map_map [InverseSystem (F := G) fun i j h => f i j h]
  {i j k} (hij hjk x) :
    f i j hij (f j k hjk x) = f i k (le_trans hij hjk) x :=
  InverseSystem.map_map (f := (f · · ·)) hij hjk x

variable (G)

/-- The inverse limit of an inverse system is the modules glued together along the maps. -/
def InverseLimit [DecidableEq ι] : Set (Π i : ι, G i) :=
  span R <| { a : Π i : ι, G i |
    ∀ (i j : _) (h : i ≤ j), f i j h (a j) = a i }

namespace InverseLimit

section Basic

variable [DecidableEq ι]

instance addCommGroup : AddCommGroup (InverseLimit G f) := by
  unfold InverseLimit
  infer_instance

instance module : Module R (InverseLimit G f) := by
  unfold InverseLimit
  infer_instance

instance inhabited : Inhabited (InverseLimit G f) :=
  ⟨0⟩


variable (R ι)

def toComponent (i) : InverseLimit G f →ₗ[R] G i :=
  sorry


end Basic

end InverseLimit

end Module

namespace AddCommGroup

variable [∀ i, AddCommGroup (G i)]

def InverseLimit [DecidableEq ι] (f : ∀ i j, i ≤ j → G j →+ G i) : Type _ :=
  @Module.InverseLimit ℤ _ ι _ G _ _ (fun i j hij => (f i j hij).toIntLinearMap) _

namespace InverseLimit

variable (f : ∀ i j, i ≤ j → G j →+ G i)

protected theorem inverseSystem [h : InverseSystem (F := G) fun i j h => f i j h] :
    InverseSystem (F := G) fun i j hij => (f i j hij).toIntLinearMap :=
  h

attribute [local instance] InverseLimit.inverseSystem

variable [DecidableEq ι]

instance : AddCommGroup (InverseLimit G f) :=
  Module.InverseLimit.addCommGroup G fun i j hij => (f i j hij).toIntLinearMap

instance : Inhabited (InverseLimit G f) :=
  ⟨0⟩

-- instance [IsEmpty ι] : Unique (InverseLimit G f) := Module.InverseLimit.unique _ _

end InverseLimit

end AddCommGroup

namespace Ring

variable [∀ i, CommRing (G i)]

section

variable (f : ∀ i j, i ≤ j → G j →+* G i)

open FreeCommRing

/-- The inverse limit of an inverse system is the rings glued together along the maps. -/
def InverseLimit : Type max v w :=
  Subring.closure { a : Π i : ι, G i |
    ∀ (i j : _) (h : i ≤ j), f i j h (a j) = a i }

namespace InverseLimit

instance commRing : CommRing (InverseLimit G f) :=
  Subring.closureCommRingOfComm (by
    intro x hx y hy
    rw [mul_comm]
  )

instance ring : Ring (InverseLimit G f) :=
  CommRing.toRing

-- Porting note: Added a `Zero` instance to get rid of `0` errors.
instance zero : Zero (InverseLimit G f) := by
  unfold InverseLimit
  exact ⟨0⟩

instance : Inhabited (InverseLimit G f) :=
  ⟨0⟩

def toComponent (i) : InverseLimit G f →+* G i :=
  sorry


end InverseLimit

end

end Ring
