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
variable (func : ∀ {i j : ι}, i ≤ j → obj j →ₗ[R] obj i)


variable (obj) in
/-- The inverse limit of an inverse system is the modules glued together along the maps. -/
def InverseLimit : Set (Π i : ι, obj i) :=
  span R <| { a : Π i : ι, obj i |
    ∀ (i j : _) (h : i ≤ j), func h (a j) = a i }

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
    (comm : ∀ i j (h : i ≤ j), LinearMap.comp (func h) (maps j) = (maps i))
    : W →ₗ[R] InverseLimit obj func where
      toFun w := ⟨fun i ↦ maps i w, by
        unfold InverseLimit
        sorry
      ⟩
      map_add' := by aesop
      map_smul' := by aesop

end InverseLimit

end Module

namespace Ring

open FreeCommRing

variable [∀ i : ι, CommRing (obj i)]
variable (func : ∀ {i j}, i ≤ j → obj j →+* obj i)

variable (obj) in
/-- The inverse limit of an inverse system is the rings glued together along the maps. -/
def InverseLimit : Type _ :=
  Subring.closure { a : Π i : ι, obj i |
    ∀ (i j : _) (h : i ≤ j), func h (a j) = a i }

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

variable {R' : Type*} [Ring R']

def map_of_maps (maps : (i : ι) → R' →+* obj i)
    (comm : ∀ r' i j (h : i ≤ j), (func h) ((maps j) r') = (maps i) r')
    : R' →+* InverseLimit obj func where
      toFun r := ⟨fun i ↦ maps i r, by
        suffices h : (fun i ↦ maps i r) ∈ { a : Π i : ι, obj i | ∀ (i j : _) (h : i ≤ j), func h (a j) = a i } by
          exact Subring.mem_closure.mpr fun K a ↦ a h
        aesop
      ⟩
      map_one' := by aesop
      map_mul' := by aesop
      map_zero' := by aesop
      map_add' := by aesop

end InverseLimit

end Ring

namespace Group

variable [∀ i : ι, Group (obj i)]
variable (func : ∀ {i j}, i ≤ j → obj j →* obj i)

variable (obj) in
/-- The inverse limit of an inverse system is the rings glued together along the maps. -/
@[to_additive]
def InverseLimit : Type _ :=
  Subgroup.closure { a : Π i : ι, obj i |
    ∀ (i j : _) (h : i ≤ j), func h (a j) = a i }

namespace InverseLimit

@[to_additive]
instance group : Group (InverseLimit obj func) := by unfold InverseLimit; infer_instance

@[to_additive]
instance zero : Zero (InverseLimit obj func) := by
  unfold InverseLimit
  exact ⟨1⟩

@[to_additive]
instance : Inhabited (InverseLimit obj func) :=
  ⟨0⟩

@[to_additive]
def toComponent (i) : InverseLimit obj func →* obj i where
  toFun z := (z.1 : Π j : ι, obj j) i
  map_one' := by simp
  map_mul' := by aesop

variable {G' : Type*} [Group G']

set_option maxHeartbeats 0 in
@[to_additive]
def map_of_maps (maps : (i : ι) → G' →* obj i)
    (comm : ∀ g' i j (h : i ≤ j), (func h) ((maps j) g') = (maps i) g')
    : G' →* InverseLimit obj func where
      toFun g := ⟨fun i ↦ maps i g, by
        suffices h : (fun i ↦ maps i g) ∈ { a : Π i : ι, obj i | ∀ (i j : _) (h : i ≤ j), func h (a j) = a i } by
          exact Subgroup.mem_closure.mpr fun K a ↦ a h
        aesop
      ⟩
      map_one' := by aesop
      map_mul' := by aesop

end InverseLimit

end Group
