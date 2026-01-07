import FLT.NumberField.Completion.Infinite
import FLT.Mathlib.LinearAlgebra.Dimension.Constructions
import FLT.Mathlib.LinearAlgebra.Pi
import FLT.Mathlib.Topology.Constructions
import FLT.Mathlib.Topology.Algebra.Module.Equiv
import Mathlib.RingTheory.TensorProduct.Pi
import FLT.Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
import FLT.Mathlib.Topology.Algebra.Algebra.Hom

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

open NumberField InfinitePlace SemialgHom

open scoped TensorProduct

namespace NumberField.InfiniteAdeleRing

/-- `K∞` is notation for `InfiniteAdeleRing K`. -/
scoped notation:10000 K "∞" => InfiniteAdeleRing K

/-- The canonical map from the infinite adeles of K to the infinite adeles of L -/
noncomputable def baseChange :
    K∞ →SA[algebraMap K L] L∞ where
  __ := Pi.semialgHomPi _ _ fun _ => Completion.comapHom rfl
  cont := .piSemialgHomPi Completion Completion _ fun _ => Completion.comapHom_cont rfl

open scoped TensorProduct.RightActions

-- should we make `InfiniteAdeleRing` an `abbrev` to avoid these?
noncomputable instance [Algebra K∞ L∞] :
    Algebra ((v : InfinitePlace K) → v.Completion) ((w : InfinitePlace L) → w.Completion) :=
  inferInstanceAs (Algebra K∞ L∞)

/-! Show that `L_∞` has the `K_∞`-module topology. -/

variable [Algebra K∞ L∞]
  [Pi.FiberwiseSMul (fun a => a.comap (algebraMap K L)) Completion Completion]

/-- The $K_{\infty}$-linear homeomorphism $K_{\infty}^{[L:K]} \cong L_{\infty}$. -/
noncomputable
def piEquiv : (Fin (Module.finrank K L) → K∞) ≃L[K∞] L∞ := by
  -- I think we could remove convert if we make `InfiniteAdeleRing` an `abbrev`
  -- (K_∞)^d ≃[K_∞] ∏ v, K_v^d
  convert (ContinuousLinearEquiv.piScalarPiComm _ _).symm.trans
    -- lift the equivalence K_v^d ≃[v.Completion] ∏ w ∣ v, L_w on fibers of comap
    (ContinuousLinearEquiv.piScalarPiCongrFiberwise
      (fun v : InfinitePlace K => (Completion.piEquiv L v).symm)).symm

instance : IsModuleTopology K∞ L∞ := .iso (piEquiv K L)

/-! Prove base change as a `L`-algebra homeomorphism. -/

-- First establish the map as an `L`-algebra isomorphism by lifting the established
-- equivalences for infinite completions of `K` and the product over all `w` lying above `v`
open scoped Classical in
/-- The $L$-algebra isomorphism $L\otimes_K K_{\infty} \cong L_{\infty}$. -/
noncomputable def baseChangeEquivAux :
    L ⊗[K] K∞ ≃ₐ[L] L∞ :=
  -- L ⊗ K_∞ ≃[K_∞] ∏ v, L ⊗ K_v
  Algebra.TensorProduct.piRight K L L Completion |>.trans
    -- lift the established equivalence L ⊗ K_v ≃[v.Completion] ∏ w ∣ v, L_w on fibers of comap
    (AlgEquiv.piCongrFiberwise
      (fun v : InfinitePlace K => (Completion.baseChangeEquiv L v).toAlgEquiv.symm)).symm

-- Then we show that this lift is the same as the lift of `baseChange : K_∞ → L_∞` coming from
-- `SemialgHom.baseChange_of_algebraMap`

omit [Algebra K∞ L∞]
  [Pi.FiberwiseSMul (fun a => a.comap (algebraMap K L)) Completion Completion] in
theorem baseChangeEquivAux_tmul (l : L) (x : InfiniteAdeleRing K) :
    baseChangeEquivAux K L (l ⊗ₜ[K] x) = algebraMap _ _ l * baseChange K L x := by
  classical
  simp only [baseChangeEquivAux, AlgEquiv.trans_apply]
  funext
  -- erw are needed here because cannot unify InfiniteAdeleRing K with
  -- (v : InfinitePlace K) → v.Completion maybe we should make InfiniteAdeleRing K an abbrev?
  erw [Algebra.TensorProduct.piRight_tmul K L L Completion, Equiv.piCongrFiberwise_symm_apply]
  rfl

example (φ : K →+* L) (x : _) : φ.toAddMonoidHom x = φ x := by
  simp only [RingHom.toAddMonoidHom_eq_coe, AddMonoidHom.coe_coe]
omit [Algebra K∞ L∞]
  [Pi.FiberwiseSMul (fun a => a.comap (algebraMap K L)) Completion Completion] in
theorem baseChangeEquivAux_coe_eq_baseChange_of_algebraMap [Algebra K L∞] [IsScalarTower K L L∞] :
    ↑(baseChangeEquivAux K L) = (baseChange K L).baseChange_of_algebraMap := by
  refine Algebra.TensorProduct.ext' fun l x => ?_
  simp [baseChangeEquivAux_tmul, baseChange_of_algebraMap_tmul]

omit [Algebra K∞ L∞]
  [Pi.FiberwiseSMul (fun a => a.comap (algebraMap K L)) Completion Completion] in
theorem baseChangeEquivAux_apply (x : L ⊗[K] InfiniteAdeleRing K)
    [Algebra K L∞] [IsScalarTower K L L∞] :
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
def baseChangeEquiv [Algebra K L∞] [IsScalarTower K L L∞] [Algebra K∞ L∞]
    [Pi.FiberwiseSMul (fun a => a.comap (algebraMap K L)) Completion Completion]
    [(baseChangeEquivAux K L).toAlgHom.CompatibleSMulFor K∞] :
    L ⊗[K] K∞ ≃A[L] L∞ :=
  /- Because both `L ⊗[K] K_∞` and `L_∞` have the `K_∞` module topology, we obtain a _continuous_
  `L`-algebra equivalence, using the following set up of algebras
  ```
  K_∞    L
    \   /
    \  /
     K
  ```
  -/
  IsModuleTopology.continuousAlgEquivOfIsScalarTower K K∞ (baseChangeEquivAux K L)

end NumberField.InfiniteAdeleRing
