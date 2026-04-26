module

public import Mathlib.NumberTheory.NumberField.Completion.Ramification
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import FLT.Mathlib.Algebra.Algebra.Bilinear
public import FLT.Mathlib.LinearAlgebra.Dimension.Constructions
public import FLT.Mathlib.Topology.Algebra.Module.FiniteDimension
public import FLT.Mathlib.Topology.Algebra.Module.ModuleTopology
public import FLT.Mathlib.Topology.MetricSpace.Pseudo.Matrix
public import FLT.Mathlib.Topology.Algebra.UniformRing
public import FLT.Mathlib.Topology.Algebra.ContinuousAlgEquiv
public import FLT.NumberField.InfinitePlace.Extension

@[expose] public section

open scoped TensorProduct

/-!
# The completion of a number field at an infinite place
-/

noncomputable section

namespace NumberField.InfinitePlace.Completion

open AbsoluteValue.Completion UniformSpace.Completion SemialgHom
open scoped NumberField.LiesOver

variable {K L : Type*} [Field K] [Field L] [Algebra K L] {v : InfinitePlace K} {w : InfinitePlace L}
  {wv : v.Extension L}

instance : wv.1.1.LiesOver v.1 where
  comp_eq := by simp [← wv.2, InfinitePlace.comap]

instance {v : InfinitePlace K} : NontriviallyNormedField v.Completion where
  non_trivial :=
    let ⟨x, hx⟩ := v.isNontrivial.exists_abv_gt_one
    ⟨x, by rw [UniformSpace.Completion.norm_coe]; exact hx⟩

noncomputable instance : FiniteDimensional v.Completion wv.1.Completion :=
  FiniteDimensional.of_locallyCompactSpace v.Completion

variable (K) in
theorem denseRange_algebraMap_subtype_pi (p : InfinitePlace K → Prop) [NumberField K] :
    DenseRange <| algebraMap K ((v : Subtype p) → v.1.Completion) := by
  apply DenseRange.comp (g := Subtype.restrict p)
    (f := algebraMap K ((v : InfinitePlace K) → v.1.Completion))
  · exact Subtype.surjective_restrict (β := fun v => v.1.Completion) p |>.denseRange
  · exact InfiniteAdeleRing.denseRange_algebraMap K
  · exact continuous_pi (fun _ => continuous_apply _)

attribute [local instance] WithAbs.algebraLeft

/-- The map `(R,v) → (S,w)` as a semialgebra map over `R → S` (which is the same map!). -/
@[simps!]
def _root_.WithAbs.semialgebraMap {R R' S : Type*} [CommSemiring R] [CommSemiring R'] [Semiring S]
    [PartialOrder S] [Algebra R R'] (v : AbsoluteValue R S) (w : AbsoluteValue R' S) :
    WithAbs v →ₛₐ[algebraMap R R'] WithAbs w where
  __ := algebraMap (WithAbs v) (WithAbs w)
  map_smul' r x := by
    simp [WithAbs.algebraMap_left_apply, WithAbs.algebraMap_right_apply, Algebra.smul_def]

/-- The map from `v.Completion` to `w.Completion` whenever the infinite place `w` of `L` lies
above the infinite place `v` of `K`. -/
abbrev comapHom (h : w.comap (algebraMap K L) = v) :
    v.Completion →ₛₐ[algebraMap K L] w.Completion :=
  have h' : w.1.LiesOver v.1 := ⟨by simp [← h, InfinitePlace.comap]⟩
  .restrictScalars (WithAbs.semialgebraMap v.1 w.1) <| UniformSpace.Completion.mapSemialgHom _
    (LiesOver.isometry_algebraMap (v := v) w).uniformContinuous.continuous

theorem comapHom_cont (h : w.comap (algebraMap K L) = v) : Continuous (comapHom h) := continuous_map

variable (L v)

/-- The map from `v.Completion` to the product of all completions of `L` lying above `v`. -/
def piExtension :
    v.Completion →ₛₐ[algebraMap K L] (wv : v.Extension L) → wv.1.Completion :=
  Pi.semialgHom _ _ fun wv ↦ comapHom wv.2

@[simp]
theorem piExtension_apply (x : v.Completion) :
    piExtension L v x = fun wv ↦ comapHom wv.2 x := rfl

open scoped TensorProduct.RightActions

instance : TopologicalSpace (L ⊗[K] v.Completion) := moduleTopology v.Completion _

instance : IsModuleTopology v.Completion (L ⊗[K] v.Completion) := ⟨rfl⟩

/-- The `L`-algebra map `L ⊗[K] v.Completion` to the product of all completions of `L` lying
above `v`, induced by `piExtension`. -/
abbrev baseChange :
    L ⊗[K] v.Completion →ₐ[L] (wv : v.Extension L) → wv.1.Completion :=
  baseChange_of_algebraMap (piExtension L v)

/- The motivation for changing the scalars of `baseChange L v` to `v.Completion` is that
both sides are _finite-dimensional_ `v.Completion`-modules, which have the same dimension.
This fact is used to show that `baseChangeRight` (and therefore `baseChange`) is surjective. -/
/-- The `v.Completion`-algebra map `L ⊗[K] v.Completion` to the product of all completions of `L`
lying above `v`, induced by `piExtension`. -/
abbrev baseChangeRight :
    L ⊗[K] v.Completion →ₐ[v.Completion] ((wv : v.Extension L) → wv.1.Completion) :=
  baseChangeRightOfAlgebraMap (piExtension L v)

theorem mem_placesOver_iff_comap (v : InfinitePlace K) (w : InfinitePlace L) :
    w ∈ placesOver L v ↔ w.comap (algebraMap K L) = v := by
  simp only [placesOver, Set.mem_setOf_eq]
  exact ⟨fun _ ↦ LiesOver.comap_eq _ _, fun h ↦ ⟨by simp [← h, InfinitePlace.comap]⟩⟩

variable [NumberField L]

variable {L v}

-- A shortcut as this instance takes a while to synth
instance : Module.Free v.Completion wv.1.Completion :=
  Module.free_of_finite_type_torsion_free'

variable (L v)

open scoped Classical in
theorem finrank_prod_eq_finrank [NumberField K] :
    Module.finrank v.Completion ((wv : Extension L v) → wv.1.Completion) =
      Module.finrank K L := by
  classical
  rw [Module.finrank_pi_fintype v.Completion, ← sum_inertiaDeg_eq_finrank K L v,
    ← Finset.sum_congr rfl fun (w : v.Extension L) _ ↦ inertiaDeg_eq_finrank (K := K) (L := L) v w,
    ← Finset.sum_subtype (placesOver L v).toFinset (by simpa using mem_placesOver_iff_comap L v)]

theorem finrank_pi_eq_finrank_tensorProduct [NumberField K] :
    Module.finrank v.Completion ((w : v.Extension L) → w.1.Completion) =
      Module.finrank v.Completion (L ⊗[K] v.Completion) := by
  rw [(TensorProduct.RightActions.Algebra.TensorProduct.comm
       K v.Completion L).symm.toLinearEquiv.finrank_eq,
      Module.finrank_tensorProduct, Module.finrank_self, one_mul,
    finrank_prod_eq_finrank]

set_option backward.isDefEq.respectTransparency false in
open scoped Classical in
theorem baseChange_surjective : Function.Surjective (baseChange L v) := by
  -- Let `Bw` be a `K_v` basis of `Π v | w, L_w`
  let Bw := Module.finBasis v.Completion ((w : v.Extension L) → w.1.Completion)
  -- `L` is dense inside Π v | w, L_w
  have := denseRange_algebraMap_subtype_pi _ fun w : InfinitePlace L => w.comap (algebraMap K L) = v
  -- So there exists a vector `α ∈ L^d` whose matrix wrt `Bw` gets close to `1` (has non-zero det)
  classical
  let ⟨α, h⟩ := (DenseRange.piMap fun _ => this).exists_matrix_det_ne_zero
    (Basis.toMatrix_continuous Bw) Bw.toMatrix_self
  -- Therefore `α` is a basis under the image of `piExtension L v`, hence it's surjective
  rw [← isUnit_iff_ne_zero, ← Bw.det_apply, ← Module.Basis.is_basis_iff_det Bw] at h
  rw [← baseChangeRightOfAlgebraMap_coe, ← AlgHom.coe_toLinearMap, ← LinearMap.range_eq_top,
    ← top_le_iff, ← h.2, Submodule.span_le]
  rintro x ⟨i, rfl⟩
  exact ⟨α i ⊗ₜ 1, by simp⟩

variable [NumberField K]

set_option backward.isDefEq.respectTransparency false in
theorem baseChange_injective :
    Function.Injective (baseChange L v) := by
  rw [← baseChangeRightOfAlgebraMap_coe, ← AlgHom.coe_toLinearMap,
    LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (finrank_pi_eq_finrank_tensorProduct L v).symm]
  simp [baseChange_surjective L v]

instance : IsModuleTopology v.Completion wv.1.Completion :=
  IsModuleTopology.iso (FiniteDimensional.nonempty_continuousLinearEquiv_of_finrank_eq
    (Module.finrank_fin_fun v.Completion)).some

set_option backward.isDefEq.respectTransparency false in
/-- The `L`-algebra homeomorphism between `L ⊗[K] v.Completion` and the product of all completions
of `L` lying above `v`. -/
def baseChangeEquiv :
    L ⊗[K] v.Completion ≃A[L] (wv : v.Extension L) → wv.1.Completion :=
  let e := AlgEquiv.ofBijective _ ⟨baseChange_injective L v, baseChange_surjective L v⟩
  have : IsBiscalar L v.Completion e.toAlgHom :=
    inferInstanceAs (IsBiscalar L v.Completion (baseChange L v))
  IsModuleTopology.continuousAlgEquivOfIsBiscalar v.Completion e

set_option backward.isDefEq.respectTransparency false in
instance : IsBiscalar L v.Completion (baseChangeEquiv L v).toAlgHom :=
  inferInstanceAs (IsBiscalar L v.Completion (baseChange L v))

@[simp]
theorem baseChangeEquiv_tmul (l : L) (x : v.Completion) :
    baseChangeEquiv L v (l ⊗ₜ[K] x) = fun wv : v.Extension L => l * comapHom wv.2 x := by
  simp [baseChangeEquiv, baseChange, SemialgHom.baseChange_of_algebraMap_tmul]
  rfl

open TensorProduct.AlgebraTensorModule in
/-- The `Kᵥ`-linear homeomorphism between `Kᵥ^d` and the product of all completions
of `L` lying above `v`, where `d = [K : L]`. -/
def piEquiv :
    (Fin (Module.finrank K L) → v.Completion) ≃L[v.Completion]
      (wv : v.Extension L) → wv.1.Completion := by
  -- `L ⊗ Kᵥ ≃ₗ[Kᵥ] Kᵥ ⊗ L`
  let e₁ := (TensorProduct.RightActions.Algebra.TensorProduct.comm K v.Completion L).symm
     |>.toLinearEquiv
  -- `Kᵥ ⊗ L ≃ₗ[Kᵥ] Kᵥ^d`
  let e₂ := finiteEquivPi K L v.Completion
  -- Compose and apply module topologies to get the `Kᵥ`-linear homeomorphism
  -- `Kᵥ^d ≃L[Kᵥ] L ⊗ Kᵥ`
  let e₃ := IsModuleTopology.continuousLinearEquiv (e₁.trans <| e₂) |>.symm
  -- Compose with `Kᵥ`-scalar base change to finish
  -- `Kᵥ^d ≃L[Kᵥ] ∏ w | v, L_w`
  exact e₃.trans ((baseChangeEquiv L v).changeScalars v.Completion)

theorem piEquiv_smul (x : v.Completion) (y : Fin (Module.finrank K L) → v.Completion)
    (wv : v.Extension L) :
    piEquiv L v (x • y) wv = comapHom wv.2 x * piEquiv L v y wv := by
  simp_rw [(piEquiv L v).map_smul x y, Pi.smul_def, RingHom.smul_toAlgebra]
  rfl

end NumberField.InfinitePlace.Completion
