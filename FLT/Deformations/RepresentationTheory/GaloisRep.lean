module

public import FLT.Deformations.RepresentationTheory.AbsoluteGaloisGroup
public import FLT.Deformations.RepresentationTheory.Etale
public import Mathlib.LinearAlgebra.Charpoly.Basic
public import Mathlib.LinearAlgebra.Matrix.Unique
public import Mathlib.RingTheory.Bialgebra.TensorProduct
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import FLT.Deformations.RepresentationTheory.Irreducible

@[expose] public section

open NumberField

universe uK

variable {K : Type uK} {L : Type*} [Field K] [Field L]
variable {A : Type*} [CommRing A] [TopologicalSpace A]
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

variable (K A M) in
/-- `GaloisRep K A M` are the `A`-linear galois reps of a field `K` on the `A`-module `M`. -/
def GaloisRep :=
  letI := moduleTopology A (Module.End A M)
  Γ K →ₜ* Module.End A M

noncomputable instance : FunLike (GaloisRep K A M) (Γ K) (Module.End A M) :=
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

/-- The kernel of a galois rep. -/
noncomputable nonrec
abbrev GaloisRep.ker (ρ : GaloisRep K A M) : Subgroup (Γ K) :=
  letI := moduleTopology A (Module.End A M)
  ρ.ker

/-- A field extension induces a map between galois reps.
Note that this relies on an arbitrarily chosen embedding of the algebraic closures. -/
noncomputable
def GaloisRep.map (ρ : GaloisRep K A M) (f : K →+* L) : GaloisRep L A M :=
  letI := moduleTopology A (Module.End A M)
  ρ.comp (Field.absoluteGaloisGroup.map f)

-- remark: `.toMonoidHom` added in bump to v4.30.0-rc1
@[simp]
lemma GaloisRep.ker_map (ρ : GaloisRep K A M) (f : K →+* L) :
    (ρ.map f).ker = ρ.ker.comap (Field.absoluteGaloisGroup.map f).toMonoidHom := rfl

variable (K A n) in
/-- A framed galois rep is a galois rep with a distinguished basis.
We implement it by via a galois rep on `Aⁿ`. -/
abbrev FramedGaloisRep := GaloisRep K A (n → A)

/-- A field extension induces a map between framed galois reps.
Note that this relies on an arbitrarily chosen embedding of the algebraic closures. -/
noncomputable
abbrev FramedGaloisRep.map (ρ : FramedGaloisRep K A n) (f : K →+* L) : FramedGaloisRep L A n :=
  GaloisRep.map ρ f

/-- We can conjugate a galois rep by a linear isomorphism on the space. -/
noncomputable
def GaloisRep.conj (ρ : GaloisRep K A M) (e : M ≃ₗ[A] N) : GaloisRep K A N :=
  letI := moduleTopology A (Module.End A M)
  letI := moduleTopology A (Module.End A N)
  let e' : Module.End A M ≃A[A] Module.End A N :=
    .ofIsModuleTopology <| LinearEquiv.conjAlgEquiv A e
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

/-- Equivalent modules have equivalent set of galois reps. -/
noncomputable
def GaloisRep.conjEquiv (e : M ≃ₗ[A] N) : GaloisRep K A M ≃ GaloisRep K A N where
  toFun := (conj · e)
  invFun := (conj · e.symm)
  left_inv _ := by ext; simp
  right_inv _ := by ext; simp

/-- Given a basis, we may frame a galois rep into a framed galois rep. -/
noncomputable
def GaloisRep.frame (ρ : GaloisRep K A M) (b : Module.Basis n A M) : FramedGaloisRep K A n :=
  ρ.conj (b.repr ≪≫ₗ Finsupp.linearEquivFunOnFinite A A n)

/-- Given a basis of `M`, we may realize a framed galois rep as a galois rep on `M`. -/
noncomputable
def FramedGaloisRep.unframe (ρ : FramedGaloisRep K A n) (b : Module.Basis n A M) :
    GaloisRep K A M :=
  ρ.conj (b.repr ≪≫ₗ Finsupp.linearEquivFunOnFinite A A n).symm

-- **TODO** this should be frame_unframe maybe?
omit [DecidableEq n] [NumberField K] in
@[simp]
lemma GaloisRep.unframe_frame (ρ : GaloisRep K A M) (b : Module.Basis n A M) :
    (ρ.frame b).unframe b = ρ := by
  ext; simp [frame, FramedGaloisRep.unframe]

omit [DecidableEq n] [NumberField K] in
@[simp]
lemma FramedGaloisRep.unframe_frame (ρ : FramedGaloisRep K A n) (b : Module.Basis n A M) :
    (ρ.unframe b).frame b = ρ := by
  ext; simp [unframe, GaloisRep.frame]

variable [IsTopologicalRing A]

/-- `A`-linear framed galois reps are equivalent to continuous homomorphisms into `GLₙ(A)`. -/
noncomputable
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

/-- Make an `A`-linear framed galois reps from a continuous hom into `GLₙ(A)`. -/
noncomputable
abbrev FramedGaloisRep.ofGL := FramedGaloisRep.GL (K := K) (A := A) (n := n).symm

omit [NumberField K] in
@[simp]
lemma FramedGaloisRep.GL_symm_apply (ρ : Γ K →ₜ* GL n A) (σ) : GL.symm ρ σ = (ρ σ).toLin := rfl

omit [NumberField K] in
@[simp]
lemma FramedGaloisRep.ofGL_apply (ρ : Γ K →ₜ* GL n A) (σ) : ofGL ρ σ = (ρ σ).toLin := rfl

/-- `1`-dimensional framed galois reps are equivalent to (continuous) characters. -/
noncomputable def FramedGaloisRep.equivChar {n : Type*} [Unique n] :
    FramedGaloisRep K A n ≃ (Γ K →ₜ* A) :=
  letI := moduleTopology A (Module.End A (n → A))
  letI : ContinuousMul _ := ⟨IsModuleTopology.continuous_mul_of_finite A (Module.End A (n → A))⟩
  letI e : Module.End A (n → A) ≃A[A] A :=
    .ofIsModuleTopology (LinearMap.toMatrixAlgEquiv'.trans Matrix.uniqueAlgEquiv)
  { toFun ρ := e.toContinuousAlgHom.toContinuousMonoidHom.comp ρ
    invFun ρ := e.symm.toContinuousAlgHom.toContinuousMonoidHom.comp ρ
    left_inv _ := by ext; simp [GaloisRep]
    right_inv _ := by ext; simp }

/-- The determinant of a galois rep. -/
noncomputable
def GaloisRep.det [IsTopologicalRing A] (ρ : GaloisRep K A M) : Γ K →ₜ* A :=
  letI := moduleTopology A (Module.End A M)
  .comp ⟨LinearMap.det, IsModuleTopology.continuous_det⟩ ρ

open TensorProduct in
variable (B) in
/-- Make a `A`-linear galois rep on `M` into a `B`-linear rep on `B ⊗ M`. -/
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

/-- Make a framed `n` dimensional `A`-linear galois rep into a `B`-linear rep by composing with
`GLₙ(A) → GLₙ(B)`. -/
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
    (ρ : GaloisRep K A M) (b : Module.Basis n A M) :
    (ρ.baseChange B).frame (b.baseChange B) =
      (ρ.frame b).baseChange _ (continuous_algebraMap A B) := by
  apply FramedGaloisRep.GL.injective
  ext σ i j
  simp [GaloisRep.frame, Algebra.smul_def]

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

lemma Matrix.map_det {F α β n : Type*} [CommRing β] [CommRing α] [Fintype n]
    [DecidableEq n]
    (M : Matrix n n α) (f : F) [FunLike F α β] [RingHomClass F α β] :
    (M.map f).det = f M.det :=
  (RingHom.map_det (f : α →+* β) M).symm

lemma LinearMap.trace_toLin' {R n : Type*} [CommSemiring R] [DecidableEq n]
    [Fintype n] (M : Matrix n n R) : LinearMap.trace _ _ M.toLin' = M.trace := by
  simp

set_option backward.isDefEq.respectTransparency false in
omit [NumberField K] in
lemma FramedGaloisRep.det_baseChange [IsTopologicalRing B]
    (ρ : FramedGaloisRep K A n) (f : A →+* B) (hf : Continuous f) :
    (ρ.baseChange f hf).det = .comp ⟨f, hf⟩ ρ.det := by
  ext σ
  dsimp [baseChange, GaloisRep.det]
  rw [GL_symm_apply]
  dsimp [← Matrix.toLin'_apply']
  rw [LinearMap.det_toLin', Matrix.map_det, LinearMap.det_toMatrix']

/-- Given a (global) galois rep, this is the local galois rep at a finite prime `v`.
Note: this fixes an arbitrary embedding `Kᵃˡᵍ → Kᵥᵃˡᵍ`, or equivalently,
an arbitrary choice of valuation on `Kᵃˡᵍ` extending `v`. -/
noncomputable
abbrev GaloisRep.toLocal (ρ : GaloisRep K A M) (v : Ω K) : GaloisRep (v.adicCompletion K) A M :=
  ρ.map (algebraMap _ _)

universe v u
variable {R : Type u} [CommRing R]

/-- The class of galois reps unramified at `v`. -/
class GaloisRep.IsUnramifiedAt (ρ : GaloisRep K A M) (v : Ω K) : Prop where
  localInertiaGroup_le :
    letI := moduleTopology A (Module.End A M)
    localInertiaGroup v ≤ (ρ.toLocal v).ker

instance (ρ : GaloisRep K A M) (v : Ω K) [ρ.IsUnramifiedAt v] (e : M ≃ₗ[A] N) :
    (ρ.conj e).IsUnramifiedAt v where
  localInertiaGroup_le := (GaloisRep.IsUnramifiedAt.localInertiaGroup_le (ρ := ρ)).trans (by simp)

instance [IsTopologicalRing B] [Algebra A B] [ContinuousSMul A B]
    [Module.Finite A M] [Module.Free A M] (ρ : GaloisRep K A M) (v : Ω K) [ρ.IsUnramifiedAt v] :
    (ρ.baseChange B).IsUnramifiedAt v :=
  ⟨(GaloisRep.IsUnramifiedAt.localInertiaGroup_le (ρ := ρ)).trans
    (((ρ.toLocal v).ker_baseChange (B := B)))⟩

variable [Module.Free A M] [Module.Finite A M] [Module.Free A N] [Module.Finite A N]

/-- The characteristic polynomial of the frobenious conjugacy class at `v` under `ρ`. -/
noncomputable
def GaloisRep.charFrob (ρ : GaloisRep K A M) : Polynomial A := (ρ.toLocal v Frobᵥ).charpoly

set_option backward.isDefEq.respectTransparency false in
omit [IsTopologicalRing A] in
lemma GaloisRep.charFrob_eq (ρ : GaloisRep K A M) [ρ.IsUnramifiedAt v] (σ : Γ Kᵥ)
    (hσ : IsArithFrobAt 𝒪ᵥ σ (𝔪 (IntegralClosure 𝒪ᵥ (Kᵥᵃˡᵍ)))) :
    (ρ.toLocal v σ).charpoly = ρ.charFrob v := by
  have := IsUnramifiedAt.localInertiaGroup_le (ρ := ρ)
    (hσ.mul_inv_mem_inertia (Field.AbsoluteGaloisGroup.isArithFrobAt_adicArithFrob v))
  replace this := congr($this * ρ.toLocal v Frobᵥ)
  simp only [ContinuousMonoidHom.coe_toMonoidHom, ← map_mul, MonoidHom.coe_coe, one_mul,
    inv_mul_cancel_right] at this
  rw [this, charFrob]

section Flat

set_option linter.unusedVariables false in
/-- The underlying space of a galois rep. This is a type class synonym that allows `G` to act
on it via `ρ`. -/
@[nolint unusedArguments]
def GaloisRep.Space (ρ : GaloisRep K A M) : Type _ := M

instance (ρ : GaloisRep K A M) : AddCommGroup ρ.Space := inferInstanceAs (AddCommGroup M)

-- dirty hack
set_option backward.isDefEq.respectTransparency false in
noncomputable instance (ρ : GaloisRep K A M) : DistribMulAction (Γ K) ρ.Space where
  smul g v := ρ g v
  one_smul b := by unfold HSMul.hSMul; simp [instHSMul]
  mul_smul := by unfold HSMul.hSMul; simp [instHSMul]
  smul_zero := by unfold HSMul.hSMul; simp [instHSMul]
  smul_add := by unfold HSMul.hSMul; simp [instHSMul]

open TensorProduct in
/-- A galois rep `ρ : Γ K → Aut_A(M)` has a flat prolongation at `v` if `M` (when viewed as a
`Γ Kᵥ`) module is isomorphic to the geometric points of a finite etale hopf algebra over `Kᵥ`, and
there exists an finite flat hopf algebra over `𝒪ᵥ` whose generic fiber is isomorphic to it.
In particular this requires `M` (and by extension `A`) to have finite cardinality.

Note that the `Algebra.Etale Kᵥ (Kᵥ ⊗[𝒪ᵥ] G)` condition is redundant because `Kᵥ` has char 0
and all finite flat group schemes over `Kᵥ` are etale.
But this would be hard to prove in general, while in the applications they would come from
finite groups so it would be easy to show that they are etale. If this turns out to not be the case,
we can remove this condition and state the aforementioned result as a sorry.
-/
def GaloisRep.HasFlatProlongationAt (ρ : GaloisRep K A M) : Prop :=
  ∃ (G : Type uK) (_ : CommRing G) (_ : HopfAlgebra 𝒪ᵥ G)
    (_ : Module.Flat 𝒪ᵥ G) (_ : Module.Finite 𝒪ᵥ G) (_ : Algebra.Etale Kᵥ (Kᵥ ⊗[𝒪ᵥ] G))
    (f : Additive (Kᵥ ⊗[𝒪ᵥ] G →ₐ[Kᵥ] Kᵥᵃˡᵍ) →+[Γ Kᵥ] (ρ.toLocal v).Space),
    Function.Bijective f

/-- A galois rep `ρ : Γ K → Aut_A(M)` is flat at `v` if `A/I ⊗ M` has a flat prolongation at `v`
for all open ideals `I`. -/
class GaloisRep.IsFlatAt [IsLocalRing A] (ρ : GaloisRep K A M) : Prop where
  cond : ∀ (I : Ideal A), IsOpen (I : Set A) →
    (ρ.baseChange (A ⧸ I)).HasFlatProlongationAt v

end Flat

/-- A Galois representation is a representation (note that we
are forgetting topological information here). -/
def GaloisRep.toRepresentation (ρ : GaloisRep K A M) : Representation A (Γ K) M :=
  letI := moduleTopology A (Module.End A M) -- ?!
  ρ.toMonoidHom

/-- Irreducibility of a Galois representation over a field. -/
def GaloisRep.IsIrreducible {k : Type*} [Field k] [TopologicalSpace k] [Module k M]
    (ρ : GaloisRep K k M) : Prop := ρ.toRepresentation.IsIrreducible
