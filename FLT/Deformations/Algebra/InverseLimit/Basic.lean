import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.RingTheory.FreeCommRing
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.Order.DirectedInverseSystem
import Mathlib.Tactic.SuppressCompilation
import Mathlib.RepresentationTheory.Basic
import Mathlib.Topology.Defs.Basic
import Mathlib.Topology.Algebra.Group.Basic

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

variable {ι : Type*} [instPreorder : Preorder ι]
variable {obj : ι → Type*}

namespace Module

variable {R : Type*} [Ring R]
variable [addCommGroupObj : ∀ i, AddCommGroup (obj i)] [∀ i, Module R (obj i)]
variable (func : ∀ {i j : ι}, i ≤ j → obj j →ₗ[R] obj i)

variable (obj) in
/-- The inverse limit of an inverse system is the modules glued together along the maps. -/
def InverseLimit : Type _ := ({
  carrier := { a : Π i, obj i |
    ∀ (i j : _) (h : i ≤ j), func h (a j) = a i }
  add_mem' := by aesop
  zero_mem' := by aesop
  smul_mem' := by aesop
}: Submodule R (Π i, obj i))

namespace InverseLimit

instance instCoeOutPi : CoeOut (InverseLimit obj func) ((i : ι) → obj i) where
  coe a := a.val

variable {func} in
@[simp]
lemma definingProp {a : InverseLimit obj func} : ∀ (i j : _) (h : i ≤ j), func h (a.val j) = a.val i := a.prop

variable {func} in
abbrev of (a : (i : ι) → obj i) (h :  ∀ (i j : _) (h : i ≤ j), func h (a j) = a i) : InverseLimit obj func :=
  ⟨a, h⟩

instance instZero : Zero (InverseLimit obj func) where
  zero := of 0 (by simp)

instance instAdd : Add (InverseLimit obj func) where
  add a b := of (a.val + b.val) (by simp)

instance instNeg : Neg (InverseLimit obj func) where
  neg a := of (-a.val) (by simp)

instance instAddCommGroup : AddCommGroup (InverseLimit obj func) where
  add_assoc a b c := by simp [InverseLimit, add_assoc]
  zero_add a := by simp [InverseLimit, zero_add]
  add_zero a := by simp [InverseLimit, add_zero]
  nsmul := nsmulRec
  zsmul := zsmulRec
  neg_add_cancel a := by unfold InverseLimit at *; aesop
  add_comm a b := by simp [InverseLimit, add_comm]

instance instModule : Module R (InverseLimit obj func) where
  smul r a := of (r • a.val) (by simp)
  one_smul := by simp [InverseLimit]
  mul_smul := by simp [InverseLimit, ← smul_eq_mul]
  smul_zero := by simp [InverseLimit]
  smul_add := by simp [InverseLimit]
  add_smul := by simp [InverseLimit, add_smul]
  zero_smul := by simp [InverseLimit]

@[simp]
lemma func_component {g : InverseLimit obj func} {i j : ι} {h : i ≤ j}:
    func h (g.1 j) = g.1 i := by
  unfold InverseLimit at g
  aesop

instance inhabited : Inhabited (InverseLimit obj func) :=
  ⟨0⟩

instance unique [IsEmpty ι] : Unique (InverseLimit obj func) where
  default := ⟨default, by simp [InverseLimit]⟩
  uniq := by
    rintro ⟨x, _⟩
    exact SetCoe.ext ((Pi.uniqueOfIsEmpty obj).uniq x)

def toComponent (i) : InverseLimit obj func →ₗ[R] obj i where
  toFun z := (z : Π j : ι, obj j) i
  map_add' := by aesop
  map_smul' := by aesop

@[simp]
lemma func_toComponent {i j : ι} {h : i ≤ j}:
    .comp (func h) (toComponent func j) = toComponent func i := by
  unfold toComponent
  aesop

variable {W : Type*} [AddCommGroup W] [Module R W]

def map_of_maps (maps : (i : ι) → W →ₗ[R] obj i)
    (comm : ∀ i j (h : i ≤ j) w, (func h) ((maps j) w) = (maps i) w)
    : W →ₗ[R] InverseLimit obj func where
      toFun w := ⟨fun i ↦ maps i w, by aesop⟩
      map_add' := by aesop
      map_smul' := by aesop

end InverseLimit

end Module

namespace Ring

variable [∀ i : ι, Ring (obj i)]
variable (func : ∀ {i j}, i ≤ j → obj j →+* obj i)

variable (obj) in
/-- The inverse limit of an inverse system is the rings glued together along the maps. -/
def InverseLimit : Type _ := ({
  carrier := { a : Π i : ι, obj i |
    ∀ (i j : _) (h : i ≤ j), func h (a j) = a i }
  mul_mem' := by aesop
  one_mem' := by aesop
  add_mem' := by aesop
  zero_mem' := by aesop
  neg_mem' := by aesop
} : Subring (Π i : ι, obj i))

namespace InverseLimit

instance instCoeOutPi : CoeOut (InverseLimit obj func) ((i : ι) → obj i) where
  coe a := a.val

variable {func} in
@[simp]
lemma definingProp {a : InverseLimit obj func} : ∀ (i j : _) (h : i ≤ j), func h (a.val j) = a.val i := a.prop

variable {func} in
abbrev of (a : (i : ι) → obj i) (h :  ∀ (i j : _) (h : i ≤ j), func h (a j) = a i) : InverseLimit obj func :=
  ⟨a, h⟩

@[simp]
lemma func_component {g : InverseLimit obj func} {i j : ι} {h : i ≤ j}:
    func h (g.1 j) = g.1 i := by
  unfold InverseLimit at g
  aesop

instance instZero : Zero (InverseLimit obj func) where
  zero := of 0 (by simp)

instance instAdd : Add (InverseLimit obj func) where
  add a b := of (a.val + b.val) (by simp)

instance instNeg : Neg (InverseLimit obj func) where
  neg a := of (-a.val) (by simp)

instance instRing : Ring (InverseLimit obj func) where
  add_assoc := by simp [InverseLimit, add_assoc]
  zero_add := by simp [InverseLimit, zero_add]
  add_zero := by simp [InverseLimit, add_zero]
  add_comm := by simp [InverseLimit, add_comm]
  mul a b := of (a.val * b.val) (by simp)
  left_distrib := by simp [InverseLimit, left_distrib]
  right_distrib := by simp [InverseLimit, right_distrib]
  zero_mul := by simp [InverseLimit, zero_mul]
  mul_zero := by simp [InverseLimit, mul_zero]
  mul_assoc := by simp [InverseLimit, mul_assoc]
  one := of 1 (by simp)
  one_mul := by simp [InverseLimit, one_mul]
  mul_one := by simp [InverseLimit, mul_one]
  neg_add_cancel a := by unfold InverseLimit at *; aesop
  nsmul := nsmulRec
  zsmul := zsmulRec

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

@[simp]
lemma func_toComponent {i j : ι} {h : i ≤ j}:
    .comp (func h) (toComponent func j) = toComponent func i := by
  unfold toComponent
  aesop

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
def InverseLimit : Type _ := ({
  carrier := { a : Π i, obj i |
    ∀ (i j : _) (h : i ≤ j), func h (a j) = a i }
  mul_mem' := by aesop
  one_mem' := by aesop
  inv_mem' := by aesop
} : Subgroup (Π i, obj i))
namespace InverseLimit

@[to_additive]
instance instCoeOutPi : CoeOut (InverseLimit obj func) ((i : ι) → obj i) where
  coe a := a.val

variable {func} in
@[to_additive, simp]
lemma definingProp {a : InverseLimit obj func} : ∀ (i j : _) (h : i ≤ j), func h (a.val j) = a.val i := a.prop

variable {func} in
@[to_additive]
abbrev of (a : (i : ι) → obj i) (h :  ∀ (i j : _) (h : i ≤ j), func h (a j) = a i) : InverseLimit obj func :=
  ⟨a, h⟩

@[to_additive, simp]
lemma func_component {g : InverseLimit obj func} {i j : ι} {h : i ≤ j}:
    func h (g.1 j) = g.1 i := by
  unfold InverseLimit at g
  aesop

@[to_additive]
instance instMul : Mul (InverseLimit obj func) where
  mul a b := of (a.val * b.val) (by simp)

@[to_additive]
instance instInv : Inv (InverseLimit obj func) where
  inv a := of (a⁻¹) (by simp)

@[to_additive]
instance instOne : One (InverseLimit obj func) where
  one := of 1 (by simp)

@[to_additive]
instance instGroup : Group (InverseLimit obj func) where
  mul_assoc a b c := by simp [InverseLimit, mul_assoc]
  one_mul a := by simp [InverseLimit]
  mul_one a := by simp [InverseLimit]
  inv_mul_cancel a := by
    simp only [InverseLimit] at *
    change of (a.val⁻¹ * a.val) _ = 1
    simp only [inv_mul_cancel]
    rfl
  div a b := a * b⁻¹

@[to_additive]
instance : Inhabited (InverseLimit obj func) := ⟨1⟩

@[to_additive]
def toComponent (i) : InverseLimit obj func →* obj i where
  toFun z := (z.1 : Π j : ι, obj j) i
  map_one' := by aesop
  map_mul' := by aesop

@[to_additive, simp]
lemma func_toComponent {i j : ι} {h : i ≤ j}:
    .comp (func h) (toComponent func j) = toComponent func i := by
  unfold toComponent
  aesop

variable {G' : Type*} [Group G']

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
        unfold Module.InverseLimit at *
        rintro i j hle
        have h := ρ_comm (i := i) (j := j) hle ((g : (k:ι)→grp_obj k) j) ((v : (k:ι)→mod_obj k) j)
        simp at h
        exact h.symm
    }
    map_add' := by unfold Module.InverseLimit at *; aesop
    map_smul' := by unfold Module.InverseLimit at *; aesop
  }
  map_one' := by unfold Module.InverseLimit at *; aesop
  map_mul' := by unfold Module.InverseLimit at *; unfold Group.InverseLimit at *; aesop

end Representation
