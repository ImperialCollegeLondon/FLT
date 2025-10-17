import Mathlib.Topology.Algebra.Module.Equiv
import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.ToLin
import FLT.Mathlib.LinearAlgebra.Pi
import FLT.Mathlib.LinearAlgebra.Determinant

def ContinuousLinearEquiv.toContinuousAddEquiv
    {R₁ R₂ : Type*} [Semiring R₁] [Semiring R₂] {σ₁₂ : R₁ →+* R₂} {σ₂₁ : R₂ →+* R₁}
    [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂] {M₁ M₂ : Type*} [TopologicalSpace M₁]
    [AddCommMonoid M₁] [TopologicalSpace M₂] [AddCommMonoid M₂] [Module R₁ M₁] [Module R₂ M₂]
    (e : M₁ ≃SL[σ₁₂] M₂) :
    M₁ ≃ₜ+ M₂ where
  __ := e.toLinearEquiv.toAddEquiv
  continuous_invFun := e.symm.continuous

@[simps!]
def ContinuousLinearEquiv.restrictScalars (R : Type*) {S M M₂ : Type*}
    [Semiring R] [Semiring S] [AddCommMonoid M] [AddCommMonoid M₂] [Module R M] [Module R M₂]
    [Module S M] [Module S M₂] [LinearMap.CompatibleSMul M M₂ R S] [TopologicalSpace M]
    [TopologicalSpace M₂] (f : M ≃L[S] M₂) :
    M ≃L[R] M₂ where
  __ := f.toLinearEquiv.restrictScalars R
  invFun := f.symm
  continuous_toFun := f.continuous_toFun
  continuous_invFun := f.continuous_invFun

/-- Let `f : α → β` be a function on index types. A family of `R b`-linear homeomorphisms, indexed
by `b : β`, between the product over the fiber of `b` under `f` given as
`∀ (σ : { a : α // f a = b }) → γ₁ σ.1) ≃ₗ[R b] γ₂ b` lifts to an equivalence over the products
`∀ a, γ₁ a ≃ₗ[∀ b, R b] ∀ b, γ₂ b` with product scalars `∀ b, R b`, provided that `∀ b, R b` acts on
`∀ a, γ₁ a` fiberwise. This is `Equiv.piCongrFiberwise` as a `ContinuousLinearEquiv` with product
scalars. -/
def ContinuousLinearEquiv.piScalarPiCongrFiberwise {α : Type*} {β : Type*} {R : β → Type*}
    {γ₁ : α → Type*} {γ₂ : β → Type*} {f : α → β} [(a : α) → TopologicalSpace (γ₁ a)]
    [(b : β) → TopologicalSpace (γ₂ b)] [(b : β) → Semiring (R b)] [(a : α) → AddCommMonoid (γ₁ a)]
    [(b : β) → AddCommMonoid (γ₂ b)] [(b : β) → (a : { a : α // f a = b }) → Module (R b) (γ₁ a)]
    [(b : β) → Module (R b) (γ₂ b)] [Module ((b : β) → R b) ((a : α) → γ₁ a)]
    [Pi.FiberwiseSMul f R γ₁]
    (e : (b : β) → ((σ : { a : α // f a = b }) → γ₁ σ.1) ≃L[R b] γ₂ b) :
    ((a : α) → γ₁ a) ≃L[∀ b, R b] ((b : β) → γ₂ b) where
  __ := LinearEquiv.piScalarPiCongrFiberwise fun b => (e b).toLinearEquiv
  continuous_invFun := by
    change Continuous (fun (g : (b : β) → γ₂ b) a => (e (f a)).symm (g (f a)) ⟨a, rfl⟩)
    fun_prop

/-- Given `φ : α → β → Type*` and `R : α → Type*` such that `φ a b` is an `R a` module for all
`a b`, this is the continuous linear equivalence between `∀ a b, φ a b` and `∀ b a, φ a b` with
product scalars. This is `Equiv.piComm` as a product-scalar `ContinuousLinearEquiv`. -/
def ContinuousLinearEquiv.piScalarPiComm {α β : Type*} (R : α → Type*) (φ : α → β → Type*)
    [(a : α) → Semiring (R a)] [(a : α) → (b : β) → AddCommMonoid (φ a b)]
    [(a : α) → (b : β) → Module (R a) (φ a b)] [(a : α) → (b : β) → TopologicalSpace (φ a b)] :
    ((a : α) → (b : β) → φ a b) ≃L[∀ a, R a] ((b : β) → (a : α) → φ a b) where
  __ := LinearEquiv.piScalarPiComm R φ

lemma ContinuousLinearEquiv.toContinuousAddEquiv_trans
    {R : Type*} {E : Type*} [Semiring R] [AddCommMonoid E] [Module R E]
    [TopologicalSpace E] {e f : E ≃L[R] E} :
    (e.trans f).toContinuousAddEquiv =
      e.toContinuousAddEquiv.trans f.toContinuousAddEquiv := rfl

lemma ContinuousLinearEquiv.toMatrix_det_ne_zero
 {F : Type*} [Field F] {ι : Type*} [Fintype ι] [DecidableEq ι]
  {V : Type*} [AddCommGroup V] [Module F V] [TopologicalSpace V]
    (b : Module.Basis ι F V) (ρ : V ≃L[F] V) :
      (ρ.toLinearMap.toMatrix b b).det ≠ 0 := by
      simp[LinearEquiv.det_ne_zero]

section toContinuousLinearEquiv

variable {F : Type*} [Field F] [TopologicalSpace F]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {V : Type*} [AddCommGroup V] [Module F V] [TopologicalSpace V]
variable [IsModuleTopology F V] [ContinuousAdd V]

namespace Matrix

/-- Given `M : Matrix ι ι F`, `b : Module.Basis ι F V` and `h : M.det ≠ 0`,
  this is the continuous linear equivalence arising from
  `Matrix.toLinearEquiv b M (Ne.isUnit h)` -/
noncomputable def toContinuousLinearEquiv
  (M : Matrix ι ι F) (b : Module.Basis ι F V) (h : M.det ≠ 0) : V ≃L[F] V :=
  let e := Matrix.toLinearEquiv b M (Ne.isUnit h)
  have ce : Continuous e :=
    IsModuleTopology.continuous_of_linearMap e.toLinearMap
  have ce_inv : Continuous e.symm :=
    IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap
  ⟨e, ce, ce_inv⟩

@[simp]
lemma toContinousLinearEquiv_apply
  (M : Matrix ι ι F) (b : Module.Basis ι F V) (h : M.det ≠ 0) (x : V) :
  (M.toContinuousLinearEquiv b h) x = toLin b b M x := rfl

@[simp]
lemma toContinuousLinearEquiv_toLin_coe
  (M : Matrix ι ι F) (b : Module.Basis ι F V) (h : M.det ≠ 0) :
  ⇑(M.toContinuousLinearEquiv b h) = ⇑(toLin b b M) := rfl

@[simp]
lemma toContinuousLinearEquiv_toLinearEquiv
  (b : Module.Basis ι F V) (M : Matrix ι ι F) (h : M.det ≠ 0) :
  (M.toContinuousLinearEquiv b h).toLinearEquiv = Matrix.toLinearEquiv b M (Ne.isUnit h) := rfl

lemma toContinousLinearEquiv_toMatrix
    (b : Module.Basis ι F V) (M : Matrix ι ι F) (h : M.det ≠ 0) :
    (M.toContinuousLinearEquiv b h ).toLinearMap.toMatrix b b = M := by
  exact (LinearEquiv.eq_symm_apply (LinearMap.toMatrix b b)).mp rfl

lemma toContinousLinearEquiv_prod
    (b : Module.Basis ι F V)
    (A : Matrix ι ι F) (hA : A.det ≠ 0) (B : Matrix ι ι F) (hB : B.det ≠ 0) :
    have h_ne : (A * B).det ≠ 0 := by
      rw[Matrix.det_mul ]; exact (mul_ne_zero_iff_right hB).mpr hA
    (A * B).toContinuousLinearEquiv b h_ne =
    (B.toContinuousLinearEquiv b hB).trans (A.toContinuousLinearEquiv b hA) := by
  ext x
  simp[ContinuousLinearEquiv.trans_apply, Matrix.toLin_mul b b]

end Matrix

lemma ContinuousLinearEquiv.toMatrix_toContinousLinearEquiv
    (b : Module.Basis ι F V) (ρ : V ≃L[F] V) :
    (ρ.toLinearEquiv.toMatrix b b).toContinuousLinearEquiv b
    (ContinuousLinearEquiv.toMatrix_det_ne_zero b ρ ) = ρ := by
  apply ContinuousLinearEquiv.ext
  simp[]

end toContinuousLinearEquiv
