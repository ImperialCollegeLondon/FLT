import Mathlib.LinearAlgebra.Quotient.Pi
import Mathlib.Topology.Algebra.Module.Equiv

def Submodule.Quotient.continuousLinearEquiv {R : Type*} [Ring R] (G H : Type*) [AddCommGroup G]
    [Module R G] [AddCommGroup H] [Module R H] [TopologicalSpace G] [TopologicalSpace H]
    (G' : Submodule R G) (H' : Submodule R H) (e : G ≃L[R] H)
    (h : Submodule.map e.toLinearMap G' = H') :
    (G ⧸ G') ≃L[R] (H ⧸ H') where
  toLinearEquiv := Submodule.Quotient.equiv G' H' e.toLinearEquiv (by simp [h])
  continuous_toFun := by
    apply continuous_quot_lift
    simp only [LinearMap.toAddMonoidHom_coe, LinearMap.coe_comp]
    exact Continuous.comp continuous_quot_mk e.continuous
  continuous_invFun := by
    apply continuous_quot_lift
    simp only [LinearMap.toAddMonoidHom_coe, LinearMap.coe_comp]
    exact Continuous.comp continuous_quot_mk e.continuous_invFun

def Submodule.quotientPiContinuousLinearEquiv {R ι : Type*} [CommRing R] {G : ι → Type*}
    [(i : ι) → AddCommGroup (G i)] [(i : ι) → Module R (G i)] [(i : ι) → TopologicalSpace (G i)]
    [(i : ι) → IsTopologicalAddGroup (G i)] [Fintype ι] [DecidableEq ι]
    (p : (i : ι) → Submodule R (G i)) :
    (((i : ι) → G i) ⧸ Submodule.pi Set.univ p) ≃L[R] ((i : ι) → G i ⧸ p i) where
  toLinearEquiv := Submodule.quotientPi p
  continuous_toFun := by
    apply Continuous.quotient_lift
    exact continuous_pi (fun i => Continuous.comp continuous_quot_mk (continuous_apply _))
  continuous_invFun := by
    rw [show (quotientPi p).invFun = fun a => (quotientPi p).invFun a from rfl]
    simp only [quotientPi, quotientPi_aux.toFun, quotientPi_aux.invFun, piQuotientLift,
      LinearMap.lsum_apply, LinearMap.coe_sum, LinearMap.coe_comp, LinearMap.coe_proj,
      LinearEquiv.invFun_eq_symm, LinearEquiv.coe_symm_mk, Finset.sum_apply, Function.comp_apply,
      Function.eval]
    refine continuous_finset_sum _ (fun i _ => ?_)
    apply Continuous.comp ?_ (continuous_apply _)
    apply Continuous.quotient_lift <| Continuous.comp (continuous_quot_mk) (continuous_single _)
