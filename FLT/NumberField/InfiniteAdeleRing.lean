import FLT.NumberField.Completion.Infinite
import FLT.Mathlib.LinearAlgebra.Dimension.Constructions
import FLT.Mathlib.LinearAlgebra.Pi
import FLT.Mathlib.Topology.Constructions
import FLT.Mathlib.Topology.Algebra.Module.Equiv
import Mathlib.RingTheory.TensorProduct.Pi
import FLT.Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
import FLT.Mathlib.Topology.Algebra.Algebra.Hom

/-! # Base change for the infinite adele ring

If `v` is an infinite place of a number field `K`, we have established in
`FLT.NumberField.Completion.Infinite` a continuous `L`-algebra homomorphism
`L ⊗[K] K_v ≃ₐ[L] ∏ w ∣ v, L_w` where the product is over all infinite places `w` of `L`
lying above `v`.

In this file we analogously establish the base change for the infinite adele ring
`L ⊗[K] K_∞ ≃ₐ[L] L_∞` where `K_∞` is the infinite adele ring of `K` and `L_∞` that of `L`.
There are two approaches:

(1) Piece together the local results on completions at infinite places to get a global result on
infinite adele rings.
(2) Follow the same path as that of the local result by establishing `K∞ → L∞` and lifting it to a
base change.

In this file we favour approach (1) because it bundles bijectivity and avoids having to
reprove it. Regardless, we show that they are actually the same map in
`NumberField.InfiniteAdeleRing.baseChangeEquivAux_apply`.

## Diamonds
Global instances of the form `Algebra K L → (f K) (f L)` are avoided in this file. For example
we do not define
```
instance [Algebra K L] : Algebra K∞ L∞ := ...
```
This is to prevent diamonds when `K = K` which was observed to cause timeouts in other files in
a previous version of the repository. Instead, we add the `Algebra K∞ L∞` assumption explicitly
where needed.

This is in contrast to `FLT.NumberField.Completion.Infinite` where we do define such
global instances `Algebra v.Completion wv.1.Completion`, but those are safe because
`wv : v.Extension L` has a separate type to `w : InfinitePlace L` so no diamonds can arise.

However, we still need to make sure that the abstract `K∞`-algebra structure on `L∞` agrees with
the local structures which are already defined. This is provided by the compatibility typeclass
`Pi.FiberwiseSMul (fun a => a.comap (algebraMap K L)) Completion Completion` which guarantees
exactly this. Hence this also appears as an assumption where needed.

The desired instances are constructed later as `scoped` instances in `FLT.NumberField.AdeleRing`.

## Main definitions:
- `NumberField.InfiniteAdeleRing.baseChange` : the canonical map from `K_∞` to `L_∞`.
- `NumberField.InfiniteAdeleRing.piEquiv` : the `K_∞`-linear homeomorphism
  `K_∞^[L:K] ≃[K_∞] L_∞`.
- `NumberField.InfiniteAdeleRing.baseChangeEquivAux` : the `L`-algebra isomorphism
  `L ⊗[K] K_∞ ≃ₐ[L] L_∞`. Note that this does not require `Algebra K∞ L∞` or
  `Pi.FiberwiseSMul ...` assumptions.
- `NumberField.InfiniteAdeleRing.baseChangeEquiv` : the   `L`-algebra homeomorphism
  `L ⊗[K] K_∞ ≃A[L] L_∞` induced by `baseChange`. This requires the
  `Algebra K∞ L∞` and `Pi.FiberwiseSMul ...` assumptions to ensure the correct `K∞`-module
  topology on `L_∞`.
-/

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
  continuous_toFun := .piSemialgHomPi Completion Completion _ fun _ => Completion.comapHom_cont rfl

open scoped TensorProduct.RightActions

noncomputable instance [Algebra K∞ L∞] :
    Algebra ((v : InfinitePlace K) → v.Completion) ((w : InfinitePlace L) → w.Completion) :=
  inferInstanceAs (Algebra K∞ L∞)

/-! Show that `L_∞` has the `K_∞`-module topology. -/

/-- The $K_{\infty}$-linear homeomorphism $K_{\infty}^{[L:K]} \cong L_{\infty}$. -/
noncomputable
def piEquiv [Algebra K∞ L∞]
    [Pi.FiberwiseSMul (fun a => a.comap (algebraMap K L)) Completion Completion] :
    (Fin (Module.finrank K L) → K∞) ≃L[K∞] L∞ := by
  -- I think we could remove convert if we make `InfiniteAdeleRing` an `abbrev`
  -- (K_∞)^d ≃[K_∞] ∏ v, K_v^d
  convert (ContinuousLinearEquiv.piScalarPiComm _ _).symm.trans
    -- lift the equivalence K_v^d ≃[v.Completion] ∏ w ∣ v, L_w on fibers of comap
    (ContinuousLinearEquiv.piScalarPiCongrFiberwise
      (fun v : InfinitePlace K => (Completion.piEquiv L v).symm)).symm

instance [Algebra K∞ L∞]
    [Pi.FiberwiseSMul (fun a => a.comap (algebraMap K L)) Completion Completion] :
    IsModuleTopology K∞ L∞ := .iso (piEquiv K L)

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

theorem baseChangeEquivAux_tmul (l : L) (x : InfiniteAdeleRing K) :
    baseChangeEquivAux K L (l ⊗ₜ[K] x) = algebraMap _ _ l * baseChange K L x := rfl

theorem baseChangeEquivAux_coe_eq_baseChange_of_algebraMap [Algebra K L∞] [IsScalarTower K L L∞] :
    ↑(baseChangeEquivAux K L) = (baseChange K L).baseChange_of_algebraMap :=
  Algebra.TensorProduct.ext' fun _ _ ↦ rfl

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
    [IsBiscalar L K∞ (baseChangeEquivAux K L).toAlgHom] :
    L ⊗[K] K∞ ≃A[L] L∞ :=
  IsModuleTopology.continuousAlgEquivOfIsBiscalar K K∞ (baseChangeEquivAux K L)

end NumberField.InfiniteAdeleRing
