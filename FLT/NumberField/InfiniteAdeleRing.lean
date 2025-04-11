import Mathlib
import FLT.NumberField.Completion
import FLT.Mathlib.RingTheory.TensorProduct.Finite
import FLT.Mathlib.LinearAlgebra.Dimension.Constructions
import FLT.Mathlib.Topology.Constructions

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

open NumberField InfinitePlace SemialgHom

open scoped TensorProduct

namespace NumberField.InfiniteAdeleRing

/-- The canonical map from the infinite adeles of K to the infinite adeles of L -/
noncomputable def baseChange :
    InfiniteAdeleRing K →ₛₐ[algebraMap K L] InfiniteAdeleRing L :=
  Pi.semialgHomPi _ _ fun _ => Completion.comapHom rfl

omit [NumberField K] [NumberField L] in
theorem baseChange_toFun :
    ⇑(baseChange K L) = fun (x : InfiniteAdeleRing K) (w : InfinitePlace L) =>
      Completion.comapHom (v := w.comap (algebraMap K L)) rfl (x _) := rfl

omit [NumberField K] [NumberField L] in
theorem baseChange_cont : Continuous (baseChange K L) := by
  simp [baseChange]
  apply Continuous.piSemialgHomPi Completion Completion _
  intro v
  exact Completion.comapHom_cont rfl

noncomputable instance : Algebra (InfiniteAdeleRing K) (L ⊗[K] InfiniteAdeleRing K) :=
  Algebra.TensorProduct.rightAlgebra

instance : TopologicalSpace (L ⊗[K] InfiniteAdeleRing K) :=
  moduleTopology (InfiniteAdeleRing K) (L ⊗[K] InfiniteAdeleRing K)

instance : IsModuleTopology (InfiniteAdeleRing K) (L ⊗[K] InfiniteAdeleRing K) := ⟨rfl⟩

noncomputable
instance : Algebra (InfiniteAdeleRing K) (InfiniteAdeleRing L) := (baseChange K L).toAlgebra

noncomputable
instance : Algebra K (InfiniteAdeleRing L) := Pi.algebra _ _

instance : IsScalarTower K L (InfiniteAdeleRing L) := Pi.isScalarTower

def ContinuousLinearEquiv.toContinuousAddEquiv {R₁ R₂ : Type*} [Semiring R₁] [Semiring R₂] {σ₁₂ : R₁ →+* R₂}
    {σ₂₁ : R₂ →+* R₁} [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂] {M₁ : Type*} [TopologicalSpace M₁]
    [AddCommMonoid M₁] [Module R₁ M₁] {M₂ : Type*} [TopologicalSpace M₂] [AddCommMonoid M₂]
    [Module R₂ M₂] (e : M₁ ≃SL[σ₁₂] M₂) :
    M₁ ≃ₜ+ M₂ :=
  { e with
    continuous_toFun := e.continuous_toFun
    continuous_invFun := e.continuous_invFun }

@[simp]
theorem ContinuousLinearEquiv.coe_toContinuousAddEquiv {R₁ R₂ : Type*} [Semiring R₁] [Semiring R₂] {σ₁₂ : R₁ →+* R₂}
    {σ₂₁ : R₂ →+* R₁} [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂] {M₁ : Type*} [TopologicalSpace M₁]
    [AddCommMonoid M₁] [Module R₁ M₁] {M₂ : Type*} [TopologicalSpace M₂] [AddCommMonoid M₂]
    [Module R₂ M₂] (e : M₁ ≃SL[σ₁₂] M₂) :
    ⇑(ContinuousLinearEquiv.toContinuousAddEquiv e) = e := by
  rfl

noncomputable
def piAddEquiv : (Fin (Module.finrank K L) → InfiniteAdeleRing K) ≃ₜ+ InfiniteAdeleRing L := by
  let e₁ : (Fin (Module.finrank K L) → InfiniteAdeleRing K) ≃ₜ+
      ((v : InfinitePlace K) → ((Fin (Module.finrank K L) → v.Completion))) := {
    toEquiv := Equiv.piComm _
    map_add' _ _ := rfl
    continuous_invFun := by
      show Continuous Function.swap
      fun_prop
  }
  let e₂ : ((v : InfinitePlace K) → ((Fin (Module.finrank K L) → v.Completion))) ≃ₜ+
      ((v : InfinitePlace K) → ((w : v.ExtensionPlace L) → w.1.Completion)) := {
    toAddEquiv := AddEquiv.piCongrRight fun v => (InfinitePlace.Completion.piEquiv L v)
    continuous_toFun := by
      apply continuous_pi
      intro v
      exact (InfinitePlace.Completion.piEquiv L v).continuous.comp (by fun_prop)
    continuous_invFun :=
      continuous_pi fun v => (InfinitePlace.Completion.piEquiv L v).continuous_invFun.comp (by fun_prop)
      }
  let e₃ : ((v : InfinitePlace K) → ((w : v.ExtensionPlace L) → w.1.Completion)) ≃ₜ+
      ((w : Sigma (ExtensionPlace L)) → w.2.1.Completion) := {
    toAddEquiv := LinearEquiv.piCurry K _ |>.symm.toAddEquiv
    continuous_toFun := by
      simp [LinearEquiv.piCurry, Equiv.piCurry]
      delta Sigma.uncurry
      fun_prop
    continuous_invFun := by
      refine continuous_pi (fun ⟨x, y⟩ => ?_)
      simp [Equiv.piCurry, Sigma.uncurry]
      apply Continuous.comp' (continuous_apply _)
      delta Sigma.curry
      fun_prop
  }
  let e₄ : ((w : Sigma (ExtensionPlace L)) → w.2.1.Completion) ≃ₜ+ InfiniteAdeleRing L := by
    let e : Sigma (ExtensionPlace (K := K) L) ≃ InfinitePlace L := Equiv.sigmaFiberEquiv _
    exact ContinuousLinearEquiv.toContinuousAddEquiv <| ContinuousLinearEquiv.piCongrLeft K InfinitePlace.Completion e
  apply e₁.trans
  apply e₂.trans
  apply e₃.trans
  apply e₄.trans (ContinuousAddEquiv.refl _)

theorem ContinuousLinearEquiv.piCongrLeft_apply_apply (R : Type*) [Semiring R] {ι : Type*} {ι' : Type*}
    (φ : ι → Type*) [(i : ι) → AddCommMonoid (φ i)] [(i : ι) → Module R (φ i)]
    [(i : ι) → TopologicalSpace (φ i)] (e : ι' ≃ ι) (g : (i' : ι') → φ (e i')) (i' : ι') :
    (ContinuousLinearEquiv.piCongrLeft R φ e) g (e i') = g i' := by
  rw [← Equiv.piCongrLeft_apply_apply φ e g i']
  rfl

theorem piAddEquiv_apply (x : Fin (Module.finrank K L) → InfiniteAdeleRing K) (w : InfinitePlace L) :
    piAddEquiv K L x w = InfinitePlace.Completion.piEquiv L
      (w.comap (algebraMap K L)) (fun i => x i (w.comap (algebraMap K L))) ⟨_, rfl⟩ := by
  simp [piAddEquiv]
  obtain ⟨v, rfl⟩ := Equiv.sigmaFiberEquiv (fun x : InfinitePlace L ↦ x.comap (algebraMap K L)) |>.surjective w
  erw [ContinuousLinearEquiv.piCongrLeft_apply_apply]

noncomputable
def piEquiv : (Fin (Module.finrank K L) → InfiniteAdeleRing K) ≃L[InfiniteAdeleRing K] InfiniteAdeleRing L where
  __ := piAddEquiv K L
  map_smul' r x := by
    simp
    funext w
    rw [show ⇑((piAddEquiv K L) : _ ≃+ _) = ⇑(piAddEquiv K L) from rfl]
    simp [piAddEquiv_apply]
    rw [RingHom.smul_toAlgebra, Pi.mul_def]
    simp [piAddEquiv_apply, baseChange]
    rw [SemialgHom.toLinearMap_eq_coe]
    simp
    erw [Pi.semialgHomPi_apply Completion Completion _ r w]
    rw [← Completion.piEquiv_smul L _ (r (w.comap (algebraMap K L))) _ ⟨w, rfl⟩]
    rfl

instance : IsModuleTopology (InfiniteAdeleRing K) (InfiniteAdeleRing L) := by
  exact IsModuleTopology.iso (piEquiv K L)

@[simps!]
def AlgEquiv.piCurry {ι : Type*} (S : Type*) [CommSemiring S] {Y : ι → Type*} (α : (i : ι) → Y i → Type*)
    [(i : ι) → (y : Y i) → Semiring (α i y)] [(i : ι) → (y : Y i) → Algebra S (α i y)] :
    ((i : Sigma Y) → α i.1 i.2) ≃ₐ[S] ((i : ι) → (y : Y i) → α i y) where
  toEquiv := Equiv.piCurry α
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

@[simps!]
def AlgEquiv.piCongrLeft' {α β : Type*} (S : Type*) [CommSemiring S] (A : α → Type*) (e : α ≃ β)
    [∀ a, Semiring (A a)] [∀ a, Algebra S (A a)] :
    ((a : α) → A a) ≃ₐ[S] ((b : β) → A (e.symm b)) where
  toEquiv := Equiv.piCongrLeft' A e
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

@[simp]
theorem AlgEquiv.piCongrLeft'_symm {α β : Type*} (S : Type*) {A : Type*} [CommSemiring S]
    [Semiring A] [Algebra S A] (e : α ≃ β) :
    (AlgEquiv.piCongrLeft' S (fun _ => A) e).symm = AlgEquiv.piCongrLeft' S _ e.symm := by
  simp [AlgEquiv.piCongrLeft', AlgEquiv.symm, RingEquiv.symm, MulEquiv.symm,
    Equiv.piCongrLeft'_symm]
  rfl

@[simp]
theorem AlgEquiv.piCongrLeft'_symm_apply_apply {α β : Type*} (S : Type*) (A : α → Type*) [CommSemiring S]
    [∀ a, Semiring (A a)] [∀ a, Algebra S (A a)] (e : α ≃ β) (g : (b : β) → A (e.symm b)) (b : β) :
    (piCongrLeft' S A e).symm g (e.symm b) = g b := by
  rw [← Equiv.piCongrLeft'_symm_apply_apply A e g b]
  rfl

@[simps!]
def AlgEquiv.piCongrLeft {α β : Type*} (S : Type*) [CommSemiring S] (B : β → Type*) (e : α ≃ β)
    [∀ b, Semiring (B b)] [∀ b, Algebra S (B b)] :
    ((a : α) → B (e a)) ≃ₐ[S] ((b : β) → B b) :=
  (AlgEquiv.piCongrLeft' S B e.symm).symm

theorem AlgEquiv.piCongrLeft_apply_apply {α β : Type*} (S : Type*) [CommSemiring S] (B : β → Type*) (e : α ≃ β)
    [∀ b, Semiring (B b)] [∀ b, Algebra S (B b)] (g : (a : α) → B (e a)) (a : α) :
    (AlgEquiv.piCongrLeft S B e) g (e a) = g a := by
  rw [← Equiv.piCongrLeft_apply_apply B e g a]
  rfl

open scoped Classical in
noncomputable def baseChangeEquivHom :
    L ⊗[K] InfiniteAdeleRing K ≃ₐ[L] InfiniteAdeleRing L := by
  apply Algebra.TensorProduct.piRight K L L InfinitePlace.Completion |>.trans
  apply AlgEquiv.piCongrRight (fun v : InfinitePlace K => (InfinitePlace.Completion.baseChangeEquiv L v).toAlgEquiv) |>.trans
  apply AlgEquiv.piCurry L _ |>.symm.trans
  exact AlgEquiv.refl.trans (AlgEquiv.piCongrLeft _ _ (Equiv.sigmaFiberEquiv _))

open scoped Classical in
theorem baseChangeEquivHom_tmul (l : L) (x : InfiniteAdeleRing K) :
    baseChangeEquivHom K L (l ⊗ₜ[K] x) = algebraMap _ _ l * baseChange K L x := by
  simp [baseChangeEquivHom]
  erw [Algebra.TensorProduct.piRight_tmul K L L Completion]
  funext w
  obtain ⟨v, rfl⟩ := Equiv.sigmaFiberEquiv (fun x : InfinitePlace L ↦ x.comap (algebraMap K L)) |>.surjective w
  erw [AlgEquiv.piCongrLeft_apply_apply]
  simp [Sigma.uncurry]
  rw [Pi.mul_def]
  simp [baseChange]
  left
  erw [Pi.semialgHomPi_apply]
  apply eq_of_heq
  congr! <;> rw [v.2.2] <;> rfl

theorem baseChangeEquivHom_eq_baseChange_of_algebraMap :
    (baseChangeEquivHom K L).toAlgHom = SemialgHom.baseChange_of_algebraMap (baseChange K L) := by
  apply Algebra.TensorProduct.ext'
  intro l x
  simp [baseChangeEquivHom_tmul, SemialgHom.baseChange_of_algebraMap_tmul]

theorem baseChangeEquivHom_apply (x : L ⊗[K] InfiniteAdeleRing K) :
    baseChangeEquivHom K L x = SemialgHom.baseChange_of_algebraMap (baseChange K L) x := by
  simpa using AlgHom.ext_iff.1 (baseChangeEquivHom_eq_baseChange_of_algebraMap K L) x

open TensorProduct.AlgebraTensorModule in
instance : Module.Free (InfiniteAdeleRing K) (L ⊗[K] InfiniteAdeleRing K) := by
  let comm := (Algebra.TensorProduct.comm K (InfiniteAdeleRing K) L).extendScalars (InfiniteAdeleRing K) |>.toLinearEquiv
  let π := finiteEquivPi K L (InfiniteAdeleRing K)
  exact Module.Free.of_equiv (M := (Fin (Module.finrank K L) → InfiniteAdeleRing K)) (comm.symm.trans π).symm

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
instance : IsTopologicalSemiring (L ⊗[K] InfiniteAdeleRing K) :=
  IsModuleTopology.topologicalSemiring (InfiniteAdeleRing K) _

theorem continuous_baseChangeEquivHom_tmul_right :
    Continuous fun x => baseChangeEquivHom K L (1 ⊗ₜ x) := by
  simp [baseChangeEquivHom_apply]
  have := baseChange_cont K L
  fun_prop

open scoped Classical in
attribute [local instance] Algebra.TensorProduct.rightAlgebra in
/-- The canonical `L`-algebra isomorphism from `L ⊗_K K_∞` to `L_∞` induced by the
`K`-algebra base change map `K_∞ → L_∞`. -/
noncomputable
def baseChangeEquivCLE :
    L ⊗[K] InfiniteAdeleRing K ≃A[L] InfiniteAdeleRing L := by
  apply IsModuleTopology.continuousAlgEquiv K (InfiniteAdeleRing K) (baseChangeEquivHom K L)
    (continuous_baseChangeEquivHom_tmul_right K L)
    (by simp_rw [baseChangeEquivHom_apply]; exact SemialgHom.baseChange_of_algebraMap_tmul_right _)

end NumberField.InfiniteAdeleRing
