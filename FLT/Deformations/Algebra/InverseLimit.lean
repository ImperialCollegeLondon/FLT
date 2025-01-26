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
* `Module.InverseLimit obj f`
* `AddCommGroup.InverseLimit obj f`
* `Ring.InverseLimit obj f`
-/

suppress_compilation

open Submodule

variable {ι : Type*} [Preorder ι] [DecidableEq ι]
variable {obj : ι → Type*}

namespace Module

variable {R : Type*} [Ring R]
variable [∀ i : ι, AddCommGroup (obj i)] [∀ i, Module R (obj i)]
variable (func : ∀ i j : ι, i ≤ j → obj j →ₗ[R] obj i)

/-- A copy of `InverseSystem.map_self` specialized to linear maps, as otherwise the
`fun i j h ↦ func i j h` can confuse the simplifier. -/
nonrec theorem InverseSystem.map_self [InverseSystem (F := obj) (fun i j h => func i j h)]
    (i x h) : func i i h x = x :=
  InverseSystem.map_self (f := (func · · ·)) x

/-- A copy of `InverseSystem.map_map` specialized to linear maps, as otherwise the
`fun i j h ↦ func i j h` can confuse the simplifier. -/
nonrec theorem InverseSystem.map_map [InverseSystem (F := obj) fun i j h => func i j h]
    {i j k} (hij hjk x) : func i j hij (func j k hjk x) = func i k (le_trans hij hjk) x :=
  InverseSystem.map_map (f := (func · · ·)) hij hjk x

variable (obj) in
/-- The inverse limit of an inverse system is the modules glued together along the maps. -/
def InverseLimit : Set (Π i : ι, obj i) :=
  span R <| { a : Π i : ι, obj i |
    ∀ (i j : _) (h : i ≤ j), func i j h (a j) = a i }

namespace InverseLimit

instance addCommGroup : AddCommGroup (InverseLimit obj func) := by
  unfold InverseLimit
  infer_instance

instance module : Module R (InverseLimit obj func) := by
  unfold InverseLimit
  infer_instance

instance inhabited : Inhabited (InverseLimit obj func) :=
  ⟨0⟩

instance unique [IsEmpty ι] : Unique (InverseLimit obj func) where
  default := ⟨default, by
    unfold InverseLimit
    simp
  ⟩
  uniq := by
    rintro ⟨x, _⟩
    exact SetCoe.ext ((Pi.uniqueOfIsEmpty obj).uniq x)
variable (R ι)

def toComponent (i) : InverseLimit obj func →ₗ[R] obj i where
  toFun z := (z : Π j : ι, obj j) i
  map_add' := by simp
  map_smul' := by simp

variable {W : Type*} [AddCommGroup W] [Module R W]

def map_of_maps (maps : (i : ι) → W →ₗ[R] obj i)
    (comm : ∀ i j (h : i ≤ j), LinearMap.comp (func i j h) (maps j) = (maps i))
    : W →ₗ[R] InverseLimit obj func where
      toFun w := ⟨fun i ↦ maps i w, by
        unfold InverseLimit
        sorry
      ⟩
      map_add' := by aesop
      map_smul' := by aesop

end InverseLimit

end Module

namespace AddCommGroup

variable [∀ i : ι, AddCommGroup (obj i)]
variable (func : ∀ i j : ι, i ≤ j → obj j →+ obj i)

variable (obj) in
def InverseLimit : Type _ :=
  @Module.InverseLimit ι _ obj ℤ _ _ _ (fun i j hij => (func i j hij).toIntLinearMap)

namespace InverseLimit

protected theorem inverseSystem [h : InverseSystem (F := obj) (fun i j h => func i j h)] :
    InverseSystem (F := obj) fun i j hij => (func i j hij).toIntLinearMap :=
  h

attribute [local instance] InverseLimit.inverseSystem

instance : AddCommGroup (InverseLimit obj func) :=
  Module.InverseLimit.addCommGroup (fun i j hij => (func i j hij).toIntLinearMap)

instance : Inhabited (InverseLimit obj func) := ⟨0⟩

instance [IsEmpty ι] : Unique (InverseLimit obj func) := Module.InverseLimit.unique _

end InverseLimit

end AddCommGroup

namespace Ring

open FreeCommRing

variable [∀ i : ι, CommRing (obj i)]
variable (func : ∀ i j, i ≤ j → obj j →+* obj i)

variable (obj) in
/-- The inverse limit of an inverse system is the rings glued together along the maps. -/
def InverseLimit : Type _ :=
  Subring.closure { a : Π i : ι, obj i |
    ∀ (i j : _) (h : i ≤ j), func i j h (a j) = a i }

namespace InverseLimit

instance commRing : CommRing (InverseLimit obj func) :=
  Subring.closureCommRingOfComm (by
    intro x hx y hy
    rw [mul_comm]
  )

instance ring : Ring (InverseLimit obj func) :=
  CommRing.toRing

-- Porting note: Added a `Zero` instance to get rid of `0` errors.
instance zero : Zero (InverseLimit obj func) := by
  unfold InverseLimit
  exact ⟨0⟩

instance : Inhabited (InverseLimit obj func) :=
  ⟨0⟩

def toComponent (i) : InverseLimit obj func →+* obj i where
  toFun z := (z.1 : Π j : ι, obj j) i
  map_one' := by simp
  map_mul' := by aesop
  map_zero' := by simp
  map_add' := by aesop

end InverseLimit

end Ring
