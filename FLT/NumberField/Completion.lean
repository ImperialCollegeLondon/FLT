import Mathlib.NumberTheory.NumberField.Completion
import Mathlib.Topology.Algebra.Module.ModuleTopology
import FLT.Mathlib.Algebra.Algebra.Pi
import FLT.Mathlib.Algebra.Algebra.Bilinear
import FLT.Mathlib.Algebra.Algebra.Tower
import FLT.Mathlib.Analysis.Normed.Ring.WithAbs
import FLT.Mathlib.Topology.Algebra.UniformRing
import FLT.NumberField.Embeddings
import FLT.NumberField.WeakApproximation

open scoped TensorProduct

/-!
# The completion of a number field at an infinite place
-/

noncomputable section

namespace NumberField.InfinitePlace.Completion

open AbsoluteValue.Completion UniformSpace.Completion

variable {K L : Type*} [Field K] [Field L] [Algebra K L] {v : InfinitePlace K} {w : InfinitePlace L}
  {wv : v.ExtensionPlace L}

instance {v : InfinitePlace K} : NontriviallyNormedField (v.Completion) where
  toNormedField := InfinitePlace.Completion.instNormedField v
  non_trivial :=
    let ⟨x, hx⟩ := v.isNontrivial.exists_abv_gt_one
    ⟨x, by rw [UniformSpace.Completion.norm_coe]; exact hx⟩

instance : Algebra v.Completion wv.1.Completion :=
  semiAlgHomOfComp (comp_of_comap_eq wv.2) |>.toAlgebra

instance : NormedSpace v.Completion wv.1.Completion where
  norm_smul_le x y := by
    rw [Algebra.smul_def, norm_mul, SemialgHom.algebraMap_coe]
    have := AbsoluteValue.Completion.isometry_semiAlgHomOfComp (comp_of_comap_eq wv.2)
    rw [this.norm_map_of_map_zero (map_zero _)]

noncomputable instance : FiniteDimensional v.Completion wv.1.Completion :=
  FiniteDimensional.of_locallyCompactSpace v.Completion

def comapSemialgHom (h : w.comap (algebraMap K L) = v) :
    v.Completion →ₛₐ[algebraMap (WithAbs v.1) (WithAbs w.1)] w.Completion :=
  mapSemialgHom _ <| (WithAbs.uniformContinuous_algebraMap (v.comp_of_comap_eq h)).continuous

theorem comapSemialgHom_cont (h : w.comap (algebraMap K L) = v) :
    Continuous (comapSemialgHom h) := continuous_map

variable (L v)

abbrev baseChange :
    v.Completion →ₛₐ[algebraMap K L] ((wv : v.ExtensionPlace L) → wv.1.Completion) :=
  Pi.semialgHom _ _ fun wv => comapSemialgHom wv.2

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
instance : TopologicalSpace (L ⊗[K] v.Completion) := moduleTopology v.Completion _

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
instance : IsModuleTopology v.Completion (L ⊗[K] v.Completion) :=
  ⟨rfl⟩

variable (K)
attribute [local instance] Algebra.TensorProduct.rightAlgebra in
def piExtensionPlace :
    L ⊗[K] v.Completion →A[L] ((wv : v.ExtensionPlace L) → wv.1.Completion) where
  __ := SemialgHom.baseChange_of_algebraMap (baseChange L v)
  cont := by
    apply IsModuleTopology.continuous_of_ringHom (R := v.Completion)
    show Continuous (RingHom.comp _ Algebra.TensorProduct.includeRight.toRingHom)
    convert (continuous_pi fun wv : v.ExtensionPlace L => comapSemialgHom_cont wv.2) using 1
    ext
    simp [baseChange]

instance : UniformContinuousConstSMul K (WithAbs w.1) :=
  uniformContinuousConstSMul_of_continuousConstSMul _ _

instance : IsScalarTower K L (WithAbs w.1) := inferInstanceAs (IsScalarTower K L L)

-- above two give
#synth IsScalarTower K L wv.1.Completion
-- So to generalise to SemialgHom, we want the assumption IsScalarTower _ S B
attribute [local instance] Algebra.TensorProduct.rightAlgebra in
def piExtensionPlace' :
    L ⊗[K] v.Completion →ₐ[v.Completion] ((wv : v.ExtensionPlace L) → wv.1.Completion) where
  __ := (AlgHom.restrictScalars K (piExtensionPlace K L v).toAlgHom).extendScalars v.Completion
  commutes' := by
    intro r
    simp
    sorry

theorem piExtensionPlace_coe_eq : ⇑(piExtensionPlace K L v) = ⇑(piExtensionPlace' K L v) := rfl

variable {K L}

-- TODO generalise this
open scoped Classical in
theorem matrix_det_approx [NumberField L] {n : ℕ}
    (B : Basis (Fin n) v.Completion ((w : v.ExtensionPlace L) → w.1.Completion))
    (h : ∀ r, r > 0 → ∃ α : Fin n → L, ∀ i,
      dist (B i) (algebraMap _ ((w : ExtensionPlace L v) → w.1.Completion) (α i)) < r)
    (ε : ℝ)
    (hε : ε > 0) :
    ∃ β : Fin n → L,
      dist (B.toMatrix B).det
        (B.toMatrix (fun i => algebraMap _
          ((w : v.ExtensionPlace L) → w.1.Completion) (β i))).det < ε := by
  have := Continuous.matrix_det B.toMatrixEquiv.toLinearMap.continuous_of_finiteDimensional
  rw [Metric.continuous_iff] at this
  choose δ hδ using this B ε hε
  let ⟨α, hα⟩ := h δ hδ.1
  use α
  rw [dist_comm]
  apply hδ.2
  rw [dist_comm, dist_eq_norm, Pi.norm_def]
  simp_rw [dist_eq_norm] at hα
  have := Finset.sup_lt_iff
    (f := fun i => ‖B i - algebraMap L ((w : v.ExtensionPlace L) → w.1.Completion) (α i)‖₊)
    (a := ⟨δ, le_of_lt hδ.1⟩) (s := Finset.univ) hδ.1
  exact this.2 fun i _ => hα i

open scoped Classical in
theorem matrix_approx [NumberField L] {n : ℕ}
    (B : Basis (Fin n) v.Completion ((w : ExtensionPlace L v) → w.1.Completion))
    (h : ∀ r, r > 0 → ∃ α : Fin n → L, ∀ i,
      dist (B i) (algebraMap _ ((w : ExtensionPlace L v) → w.1.Completion) (α i)) < r) :
    ∃ β : Fin n → L,
      IsUnit (B.det (fun (i : Fin n) => piExtensionPlace' K L v (β i ⊗ₜ 1))) := by
  let ⟨β, h⟩ := matrix_det_approx v B h (1 / 2) (by linarith)
  simp_rw [isUnit_iff_ne_zero, Basis.det_apply]
  refine ⟨β, fun hc => ?_⟩
  sorry
  /-simp [piExtensionPlace] at hc
  rw [← Basis.det_apply, B.det_self, hc, dist_zero_right, norm_one] at h
  linarith-/

variable (L)

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
-- upstreaming this to mathlib instead
theorem finrank_prod_eq_finrank_eq_finrank_tensorProduct :
    Module.finrank v.Completion ((w : v.ExtensionPlace L) → w.1.Completion) =
      Module.finrank v.Completion (L ⊗[K] v.Completion) := by
  sorry

open scoped Classical in
attribute [local instance] Algebra.TensorProduct.rightAlgebra in
theorem piExtensionPlace_surjective [NumberField L] :
    Function.Surjective (piExtensionPlace K L v) := by
  let n := Module.finrank v.Completion (L ⊗[K] v.Completion)
  let Bw := Module.finBasisOfFinrankEq v.Completion
    ((w : v.ExtensionPlace L) → w.1.Completion)
      (finrank_prod_eq_finrank_eq_finrank_tensorProduct L v)
  have := denseRange_algebraMap_subtype_pi _ fun w : InfinitePlace L => w.comap (algebraMap K L) = v
  have hr (r : _) (h : r > 0) : ∃ (α : Fin n → L),
      ∀ i : Fin n, dist (Bw i) (algebraMap _ _ (α i)) < r := by
    exact ⟨fun i => Classical.choose (this.exists_dist_lt (Bw i) h),
        fun i => Classical.choose_spec (this.exists_dist_lt (Bw i) h)⟩
  let ⟨α, h⟩ := matrix_approx v Bw hr
  have := is_basis_iff_det Bw
    (v := (fun (i : Fin n) => piExtensionPlace' K L v (α i ⊗ₜ 1)))
  rw [← this] at h
  rw [piExtensionPlace_coe_eq, ← LinearMap.range_eq_top, ← top_le_iff, ← h.2, Submodule.span_le]
  intro x hx
  rw [SetLike.mem_coe, LinearMap.mem_range]
  let ⟨i, hi⟩ := hx
  rw [← hi]
  use α i ⊗ₜ[K] 1

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
instance Module.Finite.base_change_right
    (R A M : Type*) [CommRing R] [CommRing A] [Algebra R A] [CommRing M] [Algebra R M]
    [h : Module.Finite R M] :
    Module.Finite A (M ⊗[R] A) :=
  Module.Finite.of_equiv_equiv (RingEquiv.refl A) (Algebra.TensorProduct.comm R A M).toRingEquiv rfl

variable [FiniteDimensional K L]
--#synth Module.Finite v.Completion (L ⊗[K] v.Completion)
open scoped Classical in
attribute [local instance] Algebra.TensorProduct.rightAlgebra in
theorem piExtensionPlace_injective [NumberField L] :
    Function.Injective (piExtensionPlace K L v) := by
  rw [piExtensionPlace_coe_eq]
  rw [show ⇑(piExtensionPlace' K L v) = ⇑(piExtensionPlace' K L v).toLinearMap from rfl]
  rw [LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (finrank_prod_eq_finrank_eq_finrank_tensorProduct L v).symm]
  exact piExtensionPlace_surjective L v

open scoped Classical in
attribute [local instance] Algebra.TensorProduct.rightAlgebra in
def piExtensionPlaceEquiv [NumberField L] :
    L ⊗[K] v.Completion ≃A[L] ((wv : v.ExtensionPlace L) → wv.1.Completion) where
  __ := AlgEquiv.ofBijective _ ⟨piExtensionPlace_injective L v, piExtensionPlace_surjective L v⟩
  continuous_toFun := (piExtensionPlace K L v).cont
  continuous_invFun := by
    sorry

end NumberField.InfinitePlace.Completion
