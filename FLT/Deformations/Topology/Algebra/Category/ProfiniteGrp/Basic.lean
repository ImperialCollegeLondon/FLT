import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Basic
import Mathlib.Topology.Algebra.OpenSubgroup
import FLT.Mathlib.GroupTheory.Coset.Basic
import FLT.Deformations.Algebra.InverseLimit

import Mathlib -- TODO(jlcontreras): delete this via min imports

namespace ProfiniteGrp

variable (G : ProfiniteGrp) (V : OpenSubgroup G)

def index : Type _ :=
  setOf fun (Gi : Subgroup G) ↦ Gi.Normal ∧ Gi ≤ V

instance instCoeSubgroup : CoeOut (index G V) (Subgroup G) where
  coe a := a.val

instance : Preorder (index G V) where
  le a b := (a : Subgroup G) ≥ (b : Subgroup G)
  lt a b := (a : Subgroup G) > (b : Subgroup G)
  le_refl := by simp
  le_trans := by
    rintro a b c hab hbc
    simp_all
    exact le_trans hbc hab

instance {Gi : index G V} : Gi.1.Normal := by
  unfold index at Gi
  aesop

def obj (Gi : index G V) : Type _ := G ⧸ Gi.1

instance obj_instGroup {Gi : index G V} : Group (obj G V Gi) := by
  unfold obj
  infer_instance

def func {Gi Gj : index G V} (h : Gi ≤ Gj) : obj G V Gj →* obj G V Gi := by
  unfold obj
  exact {
    toFun := Subgroup.quotientMapOfLE h
    map_one' := by aesop
    map_mul' := by
      intro x y
      simp only [Set.mem_setOf_eq]
      exact Subgroup.quotientMapOfLE_mul h x y
  }

def OpenAvoidingDecomposition : Type _ := Group.InverseLimit (obj G V) (func G V)

noncomputable instance : Group (OpenAvoidingDecomposition G V) := by
  unfold OpenAvoidingDecomposition;
  infer_instance

instance : TopologicalSpace (OpenAvoidingDecomposition G V) := sorry

instance : TopologicalGroup (OpenAvoidingDecomposition G V) := sorry

namespace OpenAvoidingDecomposition

set_option maxHeartbeats 0 in
def diagonalMap_component (Gi : index G V) : G →* obj G V Gi := QuotientGroup.mk' Gi.1

def diagonalMap_commutes (g : G) (Gi Gj : index G V) (h : Gi ≤ Gj) :
    func G V h (diagonalMap_component G V Gj g) = diagonalMap_component G V Gi g :=
  by aesop

noncomputable def diagonalMap :=
  Group.InverseLimit.map_of_maps (func G V) (diagonalMap_component G V) (diagonalMap_commutes G V)

noncomputable def diagonalMap_homeo :
    ContinuousMonoidHom G (OpenAvoidingDecomposition G V) where
  toFun g := diagonalMap G V g
  map_one' := by aesop
  map_mul' := by aesop
  continuous_toFun := by
    sorry

end OpenAvoidingDecomposition

end ProfiniteGrp
