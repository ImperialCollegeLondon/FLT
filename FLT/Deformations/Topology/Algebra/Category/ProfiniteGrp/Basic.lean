import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Basic
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib

namespace ProfiniteGrp

variable {G : ProfiniteGrp} {U : OpenSubgroup G}

variable (G U) in
def index : Set (Subgroup G) :=
  setOf fun (Gi : Subgroup G) ↦ Gi.Normal ∧ Gi ≤ U

instance {Gi : index G U} : Gi.1.Normal := by
  unfold index at Gi
  aesop

def obj (Gi : index G U) : Type _ := G ⧸ Gi.1

instance obj_instGroup {Gi : index G U} : Group (obj Gi) := by
  unfold obj
  infer_instance

def func {Gi Gj : index G U} (h : Gi ≤ Gj) : obj Gi →* obj Gj := by
  unfold obj index
  exact {
    toFun := Subgroup.quotientMapOfLE h
    map_one' := by aesop
    map_mul' := by
      intro x y
      simp
      exact?

  }

namespace OpenAvoidingDecomposition

end OpenAvoidingDecomposition

end ProfiniteGrp
