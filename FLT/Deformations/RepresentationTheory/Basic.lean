import FLT.Deformations.RepresentationTheory.AbsoluteGaloisGroup
import FLT.Deformations.RepresentationTheory.Etale
import Mathlib.LinearAlgebra.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.Unique
import Mathlib.RingTheory.Bialgebra.TensorProduct
import Mathlib.RingTheory.HopfAlgebra.Basic

open NumberField

universe uA

variable {K L : Type*} [Field K] [Field L]
variable {A : Type uA} [CommRing A] [TopologicalSpace A]
variable {B : Type*} [CommRing B] [TopologicalSpace B]
variable {M N : Type*} [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
variable {n : Type*} [Fintype n] [DecidableEq n]

variable [NumberField K] (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))

local notation3 "Γ" K:max => Field.absoluteGaloisGroup K
local notation3 K:max "ᵃˡᵍ" => AlgebraicClosure K
local notation3 "𝔪" => IsLocalRing.maximalIdeal
local notation3 "κ" => IsLocalRing.ResidueField
local notation "Ω" K => IsDedekindDomain.HeightOneSpectrum (𝓞 K)
local notation "Kᵥ" => IsDedekindDomain.HeightOneSpectrum.adicCompletion K v
local notation "𝒪ᵥ" => IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers K v
local notation "Frobᵥ" => Field.AbsoluteGaloisGroup.adicArithFrob v

attribute [local instance 100000]
  instAlgebraSubtypeMemValuationSubring_fLT IntermediateField.algebra'
  Algebra.toSMul Subalgebra.toCommRing Algebra.toModule
  Subalgebra.toRing Ring.toAddCommGroup AddCommGroup.toAddGroup
  ValuationSubring.smulCommClass IntermediateField.toAlgebra
  IntermediateField.smulCommClass_of_normal
  mulSemiringActionIntegralClosure
  Subalgebra.algebra
  CommRing.toCommSemiring
  Valued.toIsUniformAddGroup

variable (K A M) in
def GaloisRep :=
  letI := moduleTopology A (Module.End A M)
  Γ K →ₜ* Module.End A M

instance : FunLike (GaloisRep K A M) (Γ K) (Module.End A M) :=
  letI := moduleTopology A (Module.End A M)
  ContinuousMonoidHom.instFunLike

instance : MonoidHomClass (GaloisRep K A M) (Γ K) (Module.End A M) :=
  letI := moduleTopology A (Module.End A M)
  ContinuousMonoidHom.instMonoidHomClass

omit [NumberField K] in
@[ext]
lemma GaloisRep.ext {ρ ρ' : GaloisRep K A M} (H : ∀ σ, ρ σ = ρ' σ) : ρ = ρ' :=
  letI := moduleTopology A (Module.End A M)
  ContinuousMonoidHom.ext H

nonrec
abbrev GaloisRep.ker (ρ : GaloisRep K A M) : Subgroup (Γ K) :=
  letI := moduleTopology A (Module.End A M)
  ρ.ker

noncomputable
def GaloisRep.map (ρ : GaloisRep K A M) (f : K →+* L) : GaloisRep L A M :=
  letI := moduleTopology A (Module.End A M)
  ρ.comp (Field.absoluteGaloisGroup.map f)

@[simp]
lemma GaloisRep.ker_map (ρ : GaloisRep K A M) (f : K →+* L) :
    (ρ.map f).ker = ρ.ker.comap (Field.absoluteGaloisGroup.map f) := rfl

variable (K A n) in
abbrev FramedGaloisRep := GaloisRep K A (n → A)

noncomputable
abbrev FramedGaloisRep.map (ρ : FramedGaloisRep K A n) (f : K →+* L) : FramedGaloisRep L A n :=
  GaloisRep.map ρ f

noncomputable
def GaloisRep.conj (ρ : GaloisRep K A M) (e : M ≃ₗ[A] N) : GaloisRep K A N :=
  letI := moduleTopology A (Module.End A M)
  letI := moduleTopology A (Module.End A N)
  let e' : Module.End A M ≃A[A] Module.End A N := .ofIsModuleTopology <| LinearEquiv.algConj A e
  e'.toContinuousAlgHom.toContinuousMonoidHom.comp ρ

omit [NumberField K] in
lemma GaloisRep.conj_apply (ρ : GaloisRep K A M) (e : M ≃ₗ[A] N) (σ : Γ K) :
    ρ.conj e σ = e.conj (ρ σ) := rfl

omit [NumberField K] in
@[simp]
lemma GaloisRep.conj_apply_apply (ρ : GaloisRep K A M) (e : M ≃ₗ[A] N) (σ : Γ K) (x : N) :
    ρ.conj e σ x = e (ρ σ (e.symm x)) := rfl

@[simp]
lemma GaloisRep.map_conj (ρ : GaloisRep K A M) (e : M ≃ₗ[A] N) (f : K →+* L) :
    (ρ.conj e).map f = (ρ.map f).conj e := rfl

omit [NumberField K] in
@[simp]
lemma GaloisRep.ker_conj (ρ : GaloisRep K A M) (e : M ≃ₗ[A] N) :
    (ρ.conj e).ker = ρ.ker := by
  letI := moduleTopology A (Module.End A M)
  letI := moduleTopology A (Module.End A N)
  ext; simp [conj]

noncomputable
def GaloisRep.conjEquiv (e : M ≃ₗ[A] N) : GaloisRep K A M ≃ GaloisRep K A N where
  toFun := (conj · e)
  invFun := (conj · e.symm)
  left_inv _ := by ext; simp
  right_inv _ := by ext; simp

noncomputable
def GaloisRep.frame (ρ : GaloisRep K A M) (b : Basis n A M) : FramedGaloisRep K A n :=
  ρ.conj (b.repr ≪≫ₗ Finsupp.linearEquivFunOnFinite A A n)

noncomputable
def FramedGaloisRep.unframe (ρ : FramedGaloisRep K A n) (b : Basis n A M) : GaloisRep K A M :=
  ρ.conj (b.repr ≪≫ₗ Finsupp.linearEquivFunOnFinite A A n).symm

omit [DecidableEq n] [NumberField K] in
@[simp]
lemma GaloisRep.unframe_frame (ρ : GaloisRep K A M) (b : Basis n A M) :
    (ρ.frame b).unframe b = ρ := by
  ext; simp [frame, FramedGaloisRep.unframe]

omit [DecidableEq n] [NumberField K] in
@[simp]
lemma FramedGaloisRep.unframe_frame (ρ : FramedGaloisRep K A n) (b : Basis n A M) :
    (ρ.unframe b).frame b = ρ := by
  ext; simp [unframe, GaloisRep.frame]; rfl

variable [IsTopologicalRing A]

def FramedGaloisRep.GL : FramedGaloisRep K A n ≃ (Γ K →ₜ* GL n A) :=
  letI := moduleTopology A (Module.End A (n → A))
  letI : ContinuousMul _ := ⟨IsModuleTopology.continuous_mul_of_finite A (Module.End A (n → A))⟩
  letI e : Module.End A (n → A) ≃A[A] Matrix n n A :=
    .ofIsModuleTopology LinearMap.toMatrixAlgEquiv'
  { toFun ρ := (e.toContinuousAlgHom.toContinuousMonoidHom.comp ρ).toHomUnits
    invFun ρ := e.symm.toContinuousAlgHom.toContinuousMonoidHom.comp ((Units.coeHomₜ _).comp ρ)
    left_inv _ := by ext; simp [GaloisRep]
    right_inv _ := by ext; simp }

omit [NumberField K] in
@[simp]
lemma FramedGaloisRep.GL_apply (ρ : FramedGaloisRep K A n) (σ) : (ρ.GL σ).1 = (ρ σ).toMatrix' := rfl

abbrev FramedGaloisRep.ofGL := FramedGaloisRep.GL (K := K) (A := A) (n := n).symm

omit [NumberField K] in
@[simp]
lemma FramedGaloisRep.GL_symm_apply (ρ : Γ K →ₜ* GL n A) (σ) : GL.symm ρ σ = (ρ σ).toLin := rfl

omit [NumberField K] in
@[simp]
lemma FramedGaloisRep.ofGL_apply (ρ : Γ K →ₜ* GL n A) (σ) : ofGL ρ σ = (ρ σ).toLin := rfl

def FramedGaloisRep.equivChar {n : Type*} [Unique n] : FramedGaloisRep K A n ≃ (Γ K →ₜ* A) :=
  letI := moduleTopology A (Module.End A (n → A))
  letI : ContinuousMul _ := ⟨IsModuleTopology.continuous_mul_of_finite A (Module.End A (n → A))⟩
  letI e : A ≃ₐ[A] Matrix n n A := (Matrix.uniqueAlgEquiv).symm
  letI e : Module.End A (n → A) ≃A[A] A :=
    .ofIsModuleTopology (LinearMap.toMatrixAlgEquiv'.trans Matrix.uniqueAlgEquiv)
  { toFun ρ := e.toContinuousAlgHom.toContinuousMonoidHom.comp ρ
    invFun ρ := e.symm.toContinuousAlgHom.toContinuousMonoidHom.comp ρ
    left_inv _ := by ext; simp [GaloisRep]
    right_inv _ := by ext; simp }

noncomputable
def GaloisRep.det [IsTopologicalRing A] (ρ : GaloisRep K A M) : Γ K →ₜ* A :=
  letI := moduleTopology A (Module.End A M)
  .comp ⟨LinearMap.det, IsModuleTopology.continuous_det⟩ ρ

open TensorProduct in
variable (B) in
noncomputable
def GaloisRep.baseChange [IsTopologicalRing B] [Algebra A B] [ContinuousSMul A B]
    [Module.Finite A M] [Module.Free A M]
    (ρ : GaloisRep K A M) : GaloisRep K B (B ⊗[A] M) :=
  letI := moduleTopology A (Module.End A M)
  letI := moduleTopology B (Module.End B (B ⊗[A] M))
  letI : ContinuousMul _ := ⟨IsModuleTopology.continuous_mul_of_finite B (Module.End B (B ⊗[A] M))⟩
  letI := IsModuleTopology.toContinuousAdd B (Module.End B (B ⊗[A] M))
  let F : Module.End A M →+* Module.End B (B ⊗[A] M) := Module.End.baseChangeHom A B M
  have : Continuous F := by
    have : IsTopologicalSemiring (Module.End B (B ⊗[A] M)) := ⟨⟩
    have : Continuous (algebraMap A (Module.End B (B ⊗[A] M))) := by
      rw [IsScalarTower.algebraMap_eq A B, RingHom.coe_comp]
      exact (continuous_algebraMap _ _).comp (continuous_algebraMap _ _)
    exact IsModuleTopology.continuous_of_ringHom (R := A) F (by simpa [F])
  .comp ⟨F, this⟩ ρ

omit [IsTopologicalRing A] [NumberField K] in
open TensorProduct in
@[simp]
lemma GaloisRep.baseChange_tmul [IsTopologicalRing B] [Algebra A B] [ContinuousSMul A B]
    [Module.Finite A M] [Module.Free A M] (ρ : GaloisRep K A M) (σ : Γ K) (r : B) (x : M) :
    ρ.baseChange B σ (r ⊗ₜ x) = r ⊗ₜ (ρ σ x) := rfl

omit [IsTopologicalRing A] [NumberField K] in
lemma GaloisRep.ker_baseChange [IsTopologicalRing B] [Algebra A B] [ContinuousSMul A B]
    [Module.Finite A M] [Module.Free A M] (ρ : GaloisRep K A M) :
    ρ.ker ≤ (ρ.baseChange B).ker := by
  intro _; simp +contextual [baseChange]

omit [IsTopologicalRing A] in
lemma GaloisRep.baseChange_map [IsTopologicalRing B] [Algebra A B] [ContinuousSMul A B]
    [Module.Finite A M] [Module.Free A M]
    (ρ : GaloisRep K A M) (f : K →+* L) : (ρ.baseChange B).map f = (ρ.map f).baseChange B := rfl

noncomputable
def FramedGaloisRep.baseChange [IsTopologicalRing B]
    (ρ : FramedGaloisRep K A n) (f : A →+* B) (hf : Continuous f) : FramedGaloisRep K B n :=
  .ofGL (.comp (Units.mapₜ ⟨f.mapMatrix.toMonoidHom, continuous_id.matrix_map hf⟩) ρ.GL)

omit [NumberField K] in
@[simp]
lemma FramedGaloisRep.baseChange_GL [IsTopologicalRing B]
    (ρ : FramedGaloisRep K A n) (f : A →+* B) (hf : Continuous f) {σ i j} :
    (ρ.baseChange f hf).GL σ i j = f (ρ.GL σ i j) := by
  simp [baseChange]

omit [NumberField K] in
variable (B) in
lemma GaloisRep.frame_baseChange [IsTopologicalRing B] [Algebra A B] [ContinuousSMul A B]
    [Module.Finite A M] [Module.Free A M]
    (ρ : GaloisRep K A M) (b : Basis n A M) :
    (ρ.baseChange B).frame (b.baseChange B) =
      (ρ.frame b).baseChange _ (continuous_algebraMap A B) := by
  apply FramedGaloisRep.GL.injective
  ext σ i j
  simp [GaloisRep.frame, ← Pi.single_apply, Algebra.smul_def]

omit [NumberField K] in
lemma FramedGaloisRep.baseChange_def [IsTopologicalRing B]
    (ρ : FramedGaloisRep K A n) (f : A →+* B) (hf : Continuous f) :
    ρ.baseChange f hf =
      letI := f.toAlgebra
      haveI : ContinuousSMul A B := continuousSMul_of_algebraMap A B hf
      (GaloisRep.baseChange B ρ).frame ((Pi.basisFun A n).baseChange B) := by
  letI := f.toAlgebra
  haveI : ContinuousSMul A B := continuousSMul_of_algebraMap A B hf
  rw [GaloisRep.frame_baseChange]
  rfl

lemma FramedGaloisRep.baseChange_map [IsTopologicalRing B]
    (ρ : FramedGaloisRep K A n) (f : A →+* B) (hf : Continuous f)
    (g : K →+* L) : (ρ.baseChange f hf).map g = (ρ.map g).baseChange f hf := rfl

lemma Matrix.map_trace {F α β n : Type*} [AddCommMonoid β] [AddCommMonoid α] [Fintype n]
    (M : Matrix n n α) (f : F) [FunLike F α β] [AddMonoidHomClass F α β] :
    (M.map f).trace = f M.trace :=
  (AddMonoidHom.map_trace f M).symm

lemma Matrix.map_det {F α β n : Type*} [CommRing β] [CommRing α] [Fintype n]
    [DecidableEq n]
    (M : Matrix n n α) (f : F) [FunLike F α β] [RingHomClass F α β] :
    (M.map f).det = f M.det :=
  (RingHom.map_det (f : α →+* β) M).symm

@[simp]
lemma LinearMap.trace_toLin' {R n : Type*} [CommSemiring R] [DecidableEq n]
    [Fintype n] (M : Matrix n n R) : LinearMap.trace _ _ M.toLin' = M.trace := by
  rw [LinearMap.trace_eq_matrix_trace _ (Pi.basisFun ..), LinearMap.toMatrix_eq_toMatrix',
      LinearMap.toMatrix'_toLin']

omit [NumberField K] in
lemma FramedGaloisRep.det_baseChange [IsTopologicalRing B]
    (ρ : FramedGaloisRep K A n) (f : A →+* B) (hf : Continuous f) :
    (ρ.baseChange f hf).det = .comp ⟨f, hf⟩ ρ.det := by
  ext σ
  dsimp [baseChange, GaloisRep.det]
  rw [GL_symm_apply]
  dsimp [← Matrix.toLin'_apply']
  rw [LinearMap.det_toLin', Matrix.map_det, LinearMap.det_toMatrix']

-- Note: this fixes an arbitrary embedding `Kᵃˡᵍ → Kᵥᵃˡᵍ`, or equivalently,
-- an arbitrary choice of valuation on `Kᵃˡᵍ` extending `v`.
noncomputable
abbrev GaloisRep.adic (ρ : GaloisRep K A M) (v : Ω K) : GaloisRep (v.adicCompletion K) A M :=
  ρ.map (algebraMap _ _)

universe v u
variable {R : Type u} [CommRing R]

class GaloisRep.IsUnramifiedAt (ρ : GaloisRep K A M) (v : Ω K) : Prop where
  localInertiaGroup_le :
    letI := moduleTopology A (Module.End A M)
    localInertiaGroup v ≤ (ρ.adic v).ker

instance (ρ : GaloisRep K A M) (v : Ω K) [ρ.IsUnramifiedAt v] (e : M ≃ₗ[A] N) :
    (ρ.conj e).IsUnramifiedAt v where
  localInertiaGroup_le := (GaloisRep.IsUnramifiedAt.localInertiaGroup_le (ρ := ρ)).trans (by simp)

instance [IsTopologicalRing B] [Algebra A B] [ContinuousSMul A B]
    [Module.Finite A M] [Module.Free A M] (ρ : GaloisRep K A M) (v : Ω K) [ρ.IsUnramifiedAt v] :
    (ρ.baseChange B).IsUnramifiedAt v :=
  ⟨(GaloisRep.IsUnramifiedAt.localInertiaGroup_le (ρ := ρ)).trans
    (((ρ.adic v).ker_baseChange (B := B)))⟩

variable [Module.Free A M] [Module.Finite A M] [Module.Free A N] [Module.Finite A N]

noncomputable
def GaloisRep.charFrob (ρ : GaloisRep K A M) : Polynomial A := (ρ.adic v Frobᵥ).charpoly

omit [IsTopologicalRing A] in
lemma GaloisRep.charFrob_eq (ρ : GaloisRep K A M) [ρ.IsUnramifiedAt v] (σ : Γ Kᵥ)
    (hσ : IsArithFrobAt 𝒪ᵥ σ (𝔪 (IntegralClosure 𝒪ᵥ (Kᵥᵃˡᵍ)))) :
    (ρ.adic v σ).charpoly = ρ.charFrob v := by
  have := IsUnramifiedAt.localInertiaGroup_le (ρ := ρ)
    (hσ.mul_inv_mem_inertia (Field.AbsoluteGaloisGroup.isArithFrobAt_adicArithFrob v))
  replace this := congr($this * ρ.adic v Frobᵥ)
  simp only [ContinuousMonoidHom.coe_toMonoidHom, ← map_mul, MonoidHom.coe_coe, one_mul,
    inv_mul_cancel_right] at this
  rw [this, charFrob]

section Flat

set_option linter.unusedVariables false in
@[nolint unusedArguments]
abbrev GaloisRep.Space (ρ : GaloisRep K A M) : Type _ := M

instance (ρ : GaloisRep K A M) : DistribMulAction (Γ K) ρ.Space where
  smul g v := ρ g v
  one_smul := by simp [instHSMul]
  mul_smul := by simp [instHSMul]
  smul_zero := by simp [instHSMul]
  smul_add := by simp [instHSMul]

attribute [instance 10000]
  MulSemiringAction.toDistribMulAction
  DistribMulAction.toMulAction
  MulAction.toSMul

open TensorProduct in
def GaloisRep.IsFlatFiberAt (ρ : GaloisRep K A M) : Prop :=
  ∃ (G : Type uA) (_ : CommRing G) (_ : HopfAlgebra 𝒪ᵥ G)
    (f : Additive (Kᵥ ⊗[𝒪ᵥ] G →ₐ[Kᵥ] Kᵥᵃˡᵍ) →+[Γ Kᵥ] (ρ.adic v).Space),
    Function.Bijective f

class GaloisRep.IsFlatAt [IsLocalRing A] (ρ : GaloisRep K A M) : Prop where
  cond : ∀ n : ℕ, n ≠ 0 → (ρ.baseChange (A ⧸ IsLocalRing.maximalIdeal A ^ n)).IsFlatFiberAt v

end Flat
#min_imports
