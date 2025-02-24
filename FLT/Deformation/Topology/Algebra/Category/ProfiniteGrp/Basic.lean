import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Basic
import Mathlib.Topology.Algebra.OpenSubgroup
import FLT.Mathlib.GroupTheory.Coset.Basic
import FLT.Deformation.Algebra.InverseLimit.Basic
import FLT.Deformation.Algebra.InverseLimit.Topology

import Mathlib -- TODO(jlcontreras): delete this via min imports

namespace ProfiniteGrp

variable (G : ProfiniteGrp) (V : OpenSubgroup G)

def index : Type _ :=
  setOf fun (Gi : OpenSubgroup G) ↦ Gi.Normal ∧ Gi ≤ V

instance instCoeSubgroup : CoeOut (index G V) (Subgroup G) where
  coe a := a.val

instance : Preorder (index G V) where
  le a b := (a : Subgroup G) ≥ (b : Subgroup G)
  le_refl a := by simp
  le_trans a b c hab hbc := by exact fun ⦃x⦄ a ↦ hab (hbc a)

variable {Gi Gj : index G V}

instance index_instNormal : Gi.1.Normal := by
  unfold index at Gi
  aesop

variable (Gi) in
def obj : Type _ := G ⧸ Gi.1.1

instance obj_instTopologicalSpace : TopologicalSpace (obj G V Gi) := ⊥

instance obj_instDiscreteTopology : DiscreteTopology (obj G V Gi) where
  eq_bot := rfl

instance obj_instGroup : Group (obj G V Gi) := by
  unfold obj
  infer_instance

instance obj_instTopologicalGroup : TopologicalGroup (obj G V Gi) where
  continuous_mul := by continuity
  continuous_inv := by continuity

instance obj_instFinite : Finite (obj G V Gi) := by
  unfold obj
  letI := Gi.1.2
  infer_instance

def func (h : Gi ≤ Gj) : obj G V Gj →* obj G V Gi := by
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

instance : TopologicalSpace (OpenAvoidingDecomposition G V) := by
  unfold OpenAvoidingDecomposition
  infer_instance

instance : TopologicalGroup (OpenAvoidingDecomposition G V) := by
  unfold OpenAvoidingDecomposition
  infer_instance

namespace OpenAvoidingDecomposition

def diagonalMap_component (Gi : index G V) : G →* obj G V Gi := QuotientGroup.mk' Gi.1.1

def diagonalMap_commutes {Gi Gj : index G V} (h : Gi ≤ Gj) (g : G) :
    func G V h (diagonalMap_component G V Gj g) = diagonalMap_component G V Gi g :=
  by aesop

noncomputable def diagonalMap :=
  Group.InverseLimit.map_of_maps'
  (func G V)
  (diagonalMap_component G V)
  (diagonalMap_commutes G V)

noncomputable def diagonalMap_homeo :
    ContinuousMonoidHom G (OpenAvoidingDecomposition G V) where
  toFun g := diagonalMap G V g
  map_one' := by aesop
  map_mul' := by aesop
  continuous_toFun := by
    sorry

end OpenAvoidingDecomposition

end ProfiniteGrp
