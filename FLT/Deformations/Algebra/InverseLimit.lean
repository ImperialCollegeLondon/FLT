import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.RingTheory.FreeCommRing
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.Order.DirectedInverseSystem
import Mathlib.Tactic.SuppressCompilation
import Mathlib.RepresentationTheory.Basic

/-!
# Inverse limit of modules, abelian groups, rings.

See Atiyah-Macdonald PP.32-33, Matsumura PP.269-270

## Main definitions

* `Module.InverseLimit obj f`
* `Ring.InverseLimit obj f`
* `Group.InverseLimit obj f`
* `Representation.InverseLimit obj f`
-/

suppress_compilation

open Submodule

variable {ι : Type*} [Preorder ι] [DecidableEq ι]
variable {obj : ι → Type*}

namespace Module

variable {R : Type*} [Ring R]
variable [addCommGroupObj : ∀ {i : ι}, AddCommGroup (obj i)] [∀ i, Module R (obj i)]
variable (func : ∀ {i j : ι}, i ≤ j → obj j →ₗ[R] obj i)

variable (obj) in
/-- The inverse limit of an inverse system is the modules glued together along the maps. -/
def InverseLimit : Submodule R (Π i : ι, obj i) where
  carrier := { a : Π i : ι, obj i |
    ∀ (i j : _) (h : i ≤ j), func h (a j) = a i }
  add_mem' := by aesop
  zero_mem' := by aesop
  smul_mem' := by aesop

namespace InverseLimit

@[simp]
lemma component_eq_component_by_func {g : InverseLimit obj func} {i j : ι} {h : i ≤ j}:
    func h (g.1 j) = g.1 i := by
  unfold InverseLimit at g
  aesop

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
  map_add' := by aesop
  map_smul' := by aesop

variable {W : Type*} [AddCommGroup W] [Module R W]

def map_of_maps (maps : (i : ι) → W →ₗ[R] obj i)
    (comm : ∀ i j (h : i ≤ j) w, (func h) ((maps j) w) = (maps i) w)
    : W →ₗ[R] InverseLimit obj func where
      toFun w := ⟨fun i ↦ maps i w, by
        unfold InverseLimit
        aesop
      ⟩
      map_add' := by aesop
      map_smul' := by aesop

end InverseLimit

end Module

namespace Ring

variable [∀ i : ι, Ring (obj i)]
variable (func : ∀ {i j}, i ≤ j → obj j →+* obj i)

variable (obj) in
/-- The inverse limit of an inverse system is the rings glued together along the maps. -/
def InverseLimit : Subring (Π i : ι, obj i) where
  carrier := { a : Π i : ι, obj i |
    ∀ (i j : _) (h : i ≤ j), func h (a j) = a i }
  mul_mem' := by aesop
  one_mem' := by aesop
  add_mem' := by aesop
  zero_mem' := by aesop
  neg_mem' := by aesop

namespace InverseLimit

@[simp]
lemma component_eq_component_by_func {g : InverseLimit obj func} {i j : ι} {h : i ≤ j}:
    func h (g.1 j) = g.1 i := by
  unfold InverseLimit at g
  aesop

-- Porting note: Added a `Zero` instance to get rid of `0` errors.
instance zero : Zero (InverseLimit obj func) := by
  unfold InverseLimit
  exact ⟨0, by aesop⟩

instance : Inhabited (InverseLimit obj func) :=
  ⟨0⟩

def toComponent (i) : InverseLimit obj func →+* obj i where
  toFun z := (z.1 : Π j : ι, obj j) i
  map_one' := by aesop
  map_mul' := by aesop
  map_zero' := by aesop
  map_add' := by aesop

variable {R' : Type*} [Ring R']

def map_of_maps (maps : (i : ι) → R' →+* obj i)
    (comm : ∀ r' i j (h : i ≤ j), (func h) ((maps j) r') = (maps i) r')
    : R' →+* InverseLimit obj func where
      toFun r := ⟨fun i ↦ maps i r, by aesop⟩
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
def InverseLimit : Subgroup (Π i, obj i) where
  carrier := { a : Π i : ι, obj i |
    ∀ (i j : _) (h : i ≤ j), func h (a j) = a i }
  mul_mem' := by aesop
  one_mem' := by aesop
  inv_mem' := by aesop

namespace InverseLimit

@[to_additive, simp]
lemma component_eq_component_by_func {g : InverseLimit obj func} {i j : ι} {h : i ≤ j}:
    func h (g.1 j) = g.1 i := by
  unfold InverseLimit at g
  aesop

@[to_additive]
instance : Inhabited (InverseLimit obj func) := ⟨1⟩

@[to_additive]
def toComponent (i) : InverseLimit obj func →* obj i where
  toFun z := (z.1 : Π j : ι, obj j) i
  map_one' := by aesop
  map_mul' := by aesop

variable {G' : Type*} [Group G']

set_option maxHeartbeats 0 in
@[to_additive]
def map_of_maps (maps : (i : ι) → G' →* obj i)
    (comm : ∀ g' i j (h : i ≤ j), (func h) ((maps j) g') = (maps i) g')
    : G' →* InverseLimit obj func where
      toFun g := ⟨fun i ↦ maps i g, by aesop⟩
      map_one' := by aesop
      map_mul' := by aesop

end InverseLimit

end Group

namespace Representation

variable {grp_obj : ι → Type*} [∀ i, Group (grp_obj i)]
variable (grp_func : ∀ {i j}, i ≤ j → grp_obj j →* grp_obj i)

variable {R : Type*} [CommRing R]
variable {mod_obj : ι → Type*} [∀ i, AddCommGroup (mod_obj i)] [∀ i, Module R (mod_obj i)]
variable (mod_func : ∀ {i j}, i ≤ j → mod_obj j →ₗ[R] mod_obj i)

variable (ρ : (i : ι) → Representation R (grp_obj i) (mod_obj i))
variable (ρ_comm : ∀ {i j} (hle : i ≤ j) (gj : grp_obj j) (vj : mod_obj j),
                    ρ i (grp_func hle gj) (mod_func hle vj) = mod_func hle (ρ j gj vj))

def InverseLimit :
    Representation R (Group.InverseLimit grp_obj grp_func) (Module.InverseLimit mod_obj mod_func) where
  toFun g := {
    toFun := fun v ↦ {
      val := fun i ↦ ρ i (g.1 i) (v.1 i)
      property := by
        unfold Module.InverseLimit
        rintro i j hle
        have h := ρ_comm (i := i) (j := j) hle ((g : (k:ι)→grp_obj k) j) ((v : (k:ι)→mod_obj k) j)
        simp at h
        exact h.symm
    }
    map_add' := by aesop
    map_smul' := by aesop
  }
  map_one' := by aesop
  map_mul' := by aesop

end Representation
