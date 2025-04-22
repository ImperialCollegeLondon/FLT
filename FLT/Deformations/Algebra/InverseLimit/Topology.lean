import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Data.Rat.Cast.Defs
import Mathlib.Order.DirectedInverseSystem
import Mathlib.Tactic.SuppressCompilation
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.Defs.Unbundled
import Mathlib.Algebra.Module.Submodule.Defs
import Mathlib.Algebra.Module.Pi
import FLT.Deformations.ContinuousRepresentation.IsTopologicalModule
import FLT.Deformations.Algebra.InverseLimit.Basic

open TopologicalSpace

variable {ι : Type*} [Preorder ι] {G : ι → Type*}
variable {T : ∀ ⦃i j : ι⦄, i ≤ j → Type*} {f : ∀ _ _ h, T h}
variable [∀ i j (h : i ≤ j), FunLike (T h) (G j) (G i)] [InverseSystem (f · · ·)]
variable [IsDirected ι (· ≤ ·)]
variable [∀ i : ι, TopologicalSpace (G i)]
  {cont : ∀ {i j}, (h : i ≤ j) → Continuous (f i j h)}

namespace InverseLimit

variable {W : Type*} {M : ι → Type*} (maps : ∀ i, M i) [∀ i, FunLike (M i) W (G i)]
variable [instInverseSystemHom : InverseSystemHom G f maps]
variable [TopologicalSpace W]
variable (maps_cont : (i : ι) → Continuous (maps i))

instance : TopologicalSpace (InverseLimit G f) := by
  unfold InverseLimit
  infer_instance

omit [InverseSystem fun x1 x2 x3 ↦ ⇑(f x1 x2 x3)] [IsDirected ι fun x1 x2 ↦ x1 ≤ x2] in
@[continuity]
lemma val_continuous : Continuous (fun (x : InverseLimit G f) ↦ x.val) := by
  unfold InverseLimit
  continuity

section ToComponent

omit [InverseSystem fun x1 x2 x3 ↦ ⇑(f x1 x2 x3)] [IsDirected ι fun x1 x2 ↦ x1 ≤ x2] in
@[continuity]
lemma to_component_continuous (i : ι) : Continuous (to_component G f i) := by
  unfold InverseLimit
  unfold to_component
  have : (fun (z : InverseLimit G f) ↦ z.val i) = (fun y ↦ y i) ∘ (fun z ↦ z.val) := rfl
  rw [this]
  refine Continuous.comp (by fun_prop) (val_continuous ..)

end ToComponent

section Maps

omit [InverseSystem fun x1 x2 x3 ↦ ⇑(f x1 x2 x3)] [IsDirected ι fun x1 x2 ↦ x1 ≤ x2] in
@[continuity]
lemma map_of_maps_continuous (maps_cont : ∀ i, Continuous (maps i)) : Continuous (map_of_maps G f maps) := by
  unfold InverseLimit
  unfold map_of_maps
  suffices Continuous fun w ↦ (fun i ↦ maps i w) by continuity
  continuity

end Maps

section TopologicalStructures

instance [∀ i, Group (G i)] [∀ i j h, MonoidHomClass (T h) (G j) (G i)]
    [∀ i : ι, IsTopologicalGroup (G i)] :
    IsTopologicalGroup (InverseLimit G f) := by
  unfold InverseLimit
  let S : Subgroup ((i : ι) → G i) := {
    carrier := { x | ∀ (i j : ι) (h : i ≤ j), (f i j h) (x j) = x i }
    mul_mem' := by aesop
    one_mem' := by aesop
    inv_mem' := by aesop
  }
  change IsTopologicalGroup S
  infer_instance

instance [∀ i, Ring (G i)] [∀ i j h, RingHomClass (T h) (G j) (G i)]
    [∀ i : ι, IsTopologicalRing (G i)] :
    IsTopologicalRing (InverseLimit G f) := by
  unfold InverseLimit
  let S : Subring ((i : ι) → G i) := {
    carrier := { x | ∀ (i j : ι) (h : i ≤ j), (f i j h) (x j) = x i }
    mul_mem' := by aesop
    one_mem' := by aesop
    add_mem' := by aesop
    zero_mem' := by aesop
    neg_mem' := by aesop
  }
  change IsTopologicalRing S
  infer_instance

instance {R : Type*} [Ring R] [TopologicalSpace R] [IsTopologicalRing R]
    [∀ i, AddCommGroup (G i)] [∀ i, Module R (G i)]
    [∀ i j h, LinearMapClass (T h) R (G j) (G i)]
    [∀ i : ι, IsTopologicalModule R (G i)] : IsTopologicalModule R (InverseLimit G f) := by
  unfold InverseLimit
  let S : Submodule R ((i : ι) → G i) := {
    carrier := { x | ∀ (i j : ι) (h : i ≤ j), (f i j h) (x j) = x i }
    add_mem' := by aesop
    zero_mem' := by aesop
    smul_mem' := by aesop
  }
  change IsTopologicalModule R S
  infer_instance


end TopologicalStructures

end InverseLimit
