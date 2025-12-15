import FLT.NumberField.Completion.Infinite
import FLT.Mathlib.LinearAlgebra.Dimension.Constructions
import FLT.Mathlib.LinearAlgebra.Pi
import FLT.Mathlib.Topology.Constructions
import FLT.Mathlib.Topology.Algebra.Module.Equiv
import Mathlib.RingTheory.TensorProduct.Pi
import FLT.Mathlib.NumberTheory.NumberField.InfiniteAdeleRing

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

open NumberField InfinitePlace SemialgHom

open scoped TensorProduct

namespace NumberField.InfiniteAdeleRing

/-- The canonical map from the infinite adeles of K to the infinite adeles of L -/
noncomputable def baseChange :
    InfiniteAdeleRing K →ₛₐ[algebraMap K L] InfiniteAdeleRing L :=
  Pi.semialgHomPi _ _ fun _ => Completion.comapHom rfl

omit [NumberField K] [NumberField L] in
theorem baseChange_cont : Continuous (baseChange K L) :=
  Continuous.piSemialgHomPi Completion Completion _ fun _ => Completion.comapHom_cont rfl

open scoped TensorProduct.RightActions

noncomputable instance : Algebra (InfiniteAdeleRing K) (InfiniteAdeleRing L) :=
  (baseChange K L).toAlgebra

-- should we make `InfiniteAdeleRing` an `abbrev` to avoid these?
noncomputable instance :
    Algebra ((v : InfinitePlace K) → v.Completion) ((w : InfinitePlace L) → w.Completion) :=
  inferInstanceAs (Algebra (InfiniteAdeleRing K) (InfiniteAdeleRing L))

noncomputable instance : Algebra K (InfiniteAdeleRing L) := Pi.algebra _ _

instance : IsScalarTower K L (InfiniteAdeleRing L) := Pi.isScalarTower

/-! Show that `L_∞` has the `K_∞`-module topology. -/

instance : Pi.FiberwiseSMul (fun a => a.comap (algebraMap K L)) Completion Completion where
  -- `K_∞` acts on `L_∞` fiberwise with respect to `comap (algebraMap K L)` because we specifically
  -- built such a product action out of the action from fibers, see `baseChange` and
  -- `Completion.comapHom`
  map_smul' r x b σ := by obtain ⟨a, rfl⟩ := σ; rfl

/-- The $K_{\infty}$-linear homeomorphism $K_{\infty}^{[L:K]} \cong L_{\infty}$. -/
noncomputable
def piEquiv : let d := Module.finrank K L
    (Fin d → InfiniteAdeleRing K) ≃L[InfiniteAdeleRing K] InfiniteAdeleRing L := by
  -- I think we could remove convert if we make `InfiniteAdeleRing` an `abbrev`
  -- (K_∞)^d ≃[K_∞] ∏ v, K_v^d
  convert (ContinuousLinearEquiv.piScalarPiComm _ _).symm.trans
    -- lift the equivalence K_v^d ≃[v.Completion] ∏ w ∣ v, L_w on fibers of comap
    (ContinuousLinearEquiv.piScalarPiCongrFiberwise
      (fun v : InfinitePlace K => (Completion.piEquiv L v).symm)).symm

instance : IsModuleTopology (InfiniteAdeleRing K) (InfiniteAdeleRing L) := by
  exact IsModuleTopology.iso (piEquiv K L)

/-! Prove base change as a `L`-algebra homeomorphism. -/

-- First establish the map as an `L`-algebra isomorphism by lifting the established
-- equivalences for infinite completions of `K` and the product over all `w` lying above `v`
open scoped Classical in
/-- The $L$-algebra isomorphism $L\otimes_K K_{\infty} \cong L_{\infty}$. -/
noncomputable def baseChangeEquivAux :
    L ⊗[K] InfiniteAdeleRing K ≃ₐ[L] InfiniteAdeleRing L :=
  -- L ⊗ K_∞ ≃[K_∞] ∏ v, L ⊗ K_v
  Algebra.TensorProduct.piRight K L L Completion |>.trans
    -- lift the established equivalence L ⊗ K_v ≃[v.Completion] ∏ w ∣ v, L_w on fibers of comap
    (AlgEquiv.piCongrFiberwise
      (fun v : InfinitePlace K => (Completion.baseChangeEquiv L v).toAlgEquiv.symm)).symm

-- Then we show that this lift is the same as the lift of `baseChange : K_∞ → L_∞` coming from
-- `SemialgHom.baseChange_of_algebraMap`

theorem baseChangeEquivAux_tmul (l : L) (x : InfiniteAdeleRing K) :
    baseChangeEquivAux K L (l ⊗ₜ[K] x) = algebraMap _ _ l * baseChange K L x := by
  classical
  simp only [baseChangeEquivAux, AlgEquiv.trans_apply]
  funext
  -- erw are needed here because cannot unify InfiniteAdeleRing K with
  -- (v : InfinitePlace K) → v.Completion maybe we should make InfiniteAdeleRing K an abbrev?
  erw [Algebra.TensorProduct.piRight_tmul K L L Completion, Equiv.piCongrFiberwise_symm_apply]
  rfl

theorem baseChangeEquivAux_coe_eq_baseChange_of_algebraMap :
    ↑(baseChangeEquivAux K L) = SemialgHom.baseChange_of_algebraMap (baseChange K L) := by
  refine Algebra.TensorProduct.ext' fun l x => ?_
  simp [baseChangeEquivAux_tmul, SemialgHom.baseChange_of_algebraMap_tmul]

theorem baseChangeEquivAux_apply (x : L ⊗[K] InfiniteAdeleRing K) :
    baseChangeEquivAux K L x = SemialgHom.baseChange_of_algebraMap (baseChange K L) x := by
  simpa using AlgHom.ext_iff.1 (baseChangeEquivAux_coe_eq_baseChange_of_algebraMap K L) x

open TensorProduct.AlgebraTensorModule in
instance : Module.Free (InfiniteAdeleRing K) (L ⊗[K] InfiniteAdeleRing K) := by
  --  L ⊗ K_∞ ≃ₗ[K_∞] K_∞ ⊗ L
  let e₁ := (TensorProduct.RightActions.Algebra.TensorProduct.comm K (InfiniteAdeleRing K) L)
    |>.toLinearEquiv.symm
  --  K_∞ ⊗ L ≃ₗ[K_∞] ∏ v, K_v ⊗ L
  let e₂ := finiteEquivPi K L (InfiniteAdeleRing K)
  -- Compose to transfer freeness of ∏ v, K_v ⊗ L to L ⊗ K_∞
  exact Module.Free.of_equiv (e₁.trans e₂).symm

-- `IsModuleTopology.continuousAlgEquivOfIsScalarTower` is then applicable in the same
-- way it was for `baseChangeEquiv` in `InfinitePlace.Completion`

/-- The canonical `L`-algebra homeomorphism from `L ⊗_K K_∞` to `L_∞` induced by the
`K`-algebra base change map `K_∞ → L_∞`. -/
noncomputable
def baseChangeEquiv :
    L ⊗[K] InfiniteAdeleRing K ≃A[L] InfiniteAdeleRing L :=
  /- Because both `L ⊗[K] K_∞` and `L_∞` have the `K_∞` module topology, we obtain a _continuous_
  `L`-algebra equivalence, using the following set up of algebras
  ```
  K_∞    L
    \   /
    \  /
     K
  ```
  -/
  IsModuleTopology.continuousAlgEquivOfIsScalarTower K _ (baseChangeEquivAux K L)
    (by simp_rw [baseChangeEquivAux_apply]; exact SemialgHom.baseChange_of_algebraMap_tmul_right _)

instance : IsScalarTower K (InfiniteAdeleRing K) (InfiniteAdeleRing L) :=
  IsScalarTower.of_algebraMap_eq (fun x ↦ by
    apply funext
    intro w
    rw [IsScalarTower.algebraMap_apply K L, RingHom.algebraMap_toAlgebra,
      SemialgHom.toRingHom_eq_coe, RingHom.coe_coe, SemialgHom.commutes])

end NumberField.InfiniteAdeleRing
