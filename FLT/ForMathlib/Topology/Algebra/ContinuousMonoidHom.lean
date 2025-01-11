import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.Topology.Algebra.Module.Equiv
import FLT.ForMathlib.Topology.Algebra.Module.Equiv
import FLT.ForMathlib.Topology.Algebra.Module.Quotient

def ContinuousAddEquiv.toIntContinuousLinearEquiv {M M₂ : Type*} [AddCommGroup M]
    [TopologicalSpace M] [AddCommGroup M₂] [TopologicalSpace M₂] (e : M ≃ₜ+ M₂) :
    M ≃L[ℤ] M₂ where
  __ := e.toIntLinearEquiv
  continuous_toFun := e.continuous
  continuous_invFun := e.continuous_invFun

def ContinuousAddEquiv.quotientPi {ι : Type*} {G : ι → Type*} [(i : ι) → AddCommGroup (G i)]
    [(i : ι) → TopologicalSpace (G i)]
    [(i : ι) → TopologicalAddGroup (G i)]
    [Fintype ι] (p : (i : ι) → AddSubgroup (G i)) [DecidableEq ι] :
    ((i : ι) → G i) ⧸ AddSubgroup.pi (_root_.Set.univ) p ≃ₜ+ ((i : ι) → G i ⧸ p i) :=
  (Submodule.quotientPiContinuousLinearEquiv
    (fun (i : ι) => AddSubgroup.toIntSubmodule (p i))).toContinuousAddEquiv
