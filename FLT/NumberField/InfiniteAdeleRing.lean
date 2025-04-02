import Mathlib
import FLT.NumberField.Completion
import FLT.Mathlib.RingTheory.TensorProduct.Finite
import FLT.Mathlib.LinearAlgebra.Dimension.Constructions

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

open NumberField InfinitePlace SemialgHom

open scoped TensorProduct

namespace NumberField.InfiniteAdeleRing

-- see https://leanprover.zulipchat.com/#narrow/channel/416277-FLT/topic/Functoriality.20of.20infinite.20completion.20for.20number.20fields/near/492313867
/-- The canonical map from the infinite adeles of K to the infinite adeles of L -/
noncomputable def baseChange :
    InfiniteAdeleRing K →ₛₐ[algebraMap K L] InfiniteAdeleRing L :=
  Pi.semialgHomPi _ _ fun _ => Completion.comapHom rfl

noncomputable instance : Algebra (InfiniteAdeleRing K) (L ⊗[K] InfiniteAdeleRing K) :=
  Algebra.TensorProduct.rightAlgebra

instance : TopologicalSpace (L ⊗[K] InfiniteAdeleRing K) :=
  moduleTopology (InfiniteAdeleRing K) (L ⊗[K] InfiniteAdeleRing K)

instance : IsModuleTopology (InfiniteAdeleRing K) (L ⊗[K] InfiniteAdeleRing K) := ⟨rfl⟩

noncomputable
instance : Algebra (InfiniteAdeleRing K) (InfiniteAdeleRing L) := (baseChange K L).toAlgebra

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
theorem AlgEquiv.piCongrLeft'_symm {α β : Type*} (S : Type*) {A : Type*} [CommSemiring S] [Semiring A]
    [Algebra S A] (e : α ≃ β) :
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

@[simps! apply toEquiv]
def AlgEquiv.piCongrLeft {α β : Type*} (S : Type*) [CommSemiring S] (B : β → Type*) (e : α ≃ β)
    [∀ b, Semiring (B b)] [∀ b, Algebra S (B b)] :
    ((a : α) → B (e a)) ≃ₐ[S] ((b : β) → B b) :=
  (AlgEquiv.piCongrLeft' S B e.symm).symm

def ContinuousAlgEquiv.piCongrRight {R ι : Type*} {A₁ A₂ : ι → Type*} [CommSemiring R]
    [(i : ι) → Semiring (A₁ i)] [(i : ι) → Semiring (A₂ i)] [(i : ι) → TopologicalSpace (A₁ i)]
    [(i : ι) → TopologicalSpace (A₂ i)] [(i : ι) → Algebra R (A₁ i)] [(i : ι) → Algebra R (A₂ i)]
    (e : (i : ι) → A₁ i ≃A[R] A₂ i) :
    ((i : ι) → A₁ i) ≃A[R] (i : ι) → A₂ i where
  __ := AlgEquiv.piCongrRight <| fun _ => (e _).toAlgEquiv
  continuous_toFun := Pi.continuous_postcomp' fun i ↦ (e i).continuous
  continuous_invFun := Pi.continuous_postcomp' fun i ↦ (e i).symm.continuous

@[simps!]
def ContinuousAlgEquiv.piCurry {ι : Type*} (S : Type*) [CommSemiring S] {Y : ι → Type*}
    (α : (i : ι) → Y i → Type*) [(i : ι) → (y : Y i) → Semiring (α i y)]
    [(i : ι) → (y : Y i) → Algebra S (α i y)]  [(i : ι) → (y : Y i) → TopologicalSpace (α i y)] :
    ((i : Sigma Y) → α i.1 i.2) ≃A[S] ((i : ι) → (y : Y i) → α i y) where
  toAlgEquiv := AlgEquiv.piCurry S α
  continuous_toFun := continuous_pi (fun _ => continuous_pi <| fun _ => continuous_apply _)
  continuous_invFun := by
    refine continuous_pi (fun ⟨x, y⟩ => ?_)
    simp only [AlgEquiv.toEquiv_eq_coe, Equiv.invFun_as_coe, AlgEquiv.symm_toEquiv_eq_symm,
      EquivLike.coe_coe, AlgEquiv.piCurry_symm_apply, Sigma.uncurry]
    exact Continuous.comp' (continuous_apply _) (continuous_apply _)

@[simps!]
def ContinuousAlgEquiv.piCongrLeft {α β : Type*} (S : Type*) [CommSemiring S] (B : β → Type*)
    (e : α ≃ β) [∀ b, Semiring (B b)] [∀ b, Algebra S (B b)] [∀ b, TopologicalSpace (B b)]  :
    ((a : α) → B (e a)) ≃A[S] ((b : β) → B b) where
  toAlgEquiv := AlgEquiv.piCongrLeft S B e
  continuous_toFun := continuous_pi <| e.forall_congr_right.mp fun i ↦ by
    simp only [AlgEquiv.toEquiv_eq_coe, AlgEquiv.piCongrLeft, Equiv.toFun_as_coe, EquivLike.coe_coe]
    have := AlgEquiv.piCongrLeft'_symm_apply_apply S B e.symm
    simp only [Equiv.symm_symm_apply] at this
    simp only [this]
    exact continuous_apply _
  continuous_invFun := Pi.continuous_precomp' e

noncomputable
def Algebra.TensorProduct.piRightContinuousAlgEquiv (R S A : Type*) {ι : Type*}  (B : ι → Type*)
    [CommSemiring R] [CommSemiring A] [Algebra R A] [CommSemiring S]
    [Algebra R S] [Algebra S A] [IsScalarTower R S A] [TopologicalSpace S]
    [(i : ι) → CommSemiring (B i)] [(i : ι) → Algebra R (B i)]
    [(i : ι) → TopologicalSpace (A ⊗[R] B i)] [(i : ι) → IsModuleTopology S (A ⊗[R] B i)]
    [TopologicalSpace (A ⊗[R] ((i : ι) → B i))] [IsModuleTopology S (A ⊗[R] ((i : ι) → B i))]
    [Fintype ι] [DecidableEq ι] :
    A ⊗[R] ((i : ι) → B i) ≃A[S] (i : ι) → A ⊗[R] B i :=
  IsModuleTopology.continuousAlgEquiv (Algebra.TensorProduct.piRight R S A B)

open scoped Classical in
noncomputable def baseChangeEquivHom :
    L ⊗[K] InfiniteAdeleRing K ≃ₐ[L] InfiniteAdeleRing L := by
  apply Algebra.TensorProduct.piRight K L L InfinitePlace.Completion |>.trans
  have (v : InfinitePlace K) : L ⊗[K] v.Completion ≃ₐ[L] (wv : v.ExtensionPlace L) → wv.1.Completion :=
    (InfinitePlace.Completion.baseChangeEquiv L v).toAlgEquiv
  apply AlgEquiv.piCongrRight this |>.trans
  apply AlgEquiv.piCurry L _ |>.symm.trans
  exact AlgEquiv.refl.trans (AlgEquiv.piCongrLeft _ _ (Equiv.sigmaFiberEquiv _))

#synth Module.Finite (InfiniteAdeleRing K) (L ⊗[K] InfiniteAdeleRing K)
noncomputable instance : Module.Finite (InfiniteAdeleRing K) (InfiniteAdeleRing L) := by
  apply Module.Finite.of_equiv_equiv (A₁ := InfiniteAdeleRing K) (A₂ := InfiniteAdeleRing K)
    (B₁ := L ⊗[K] InfiniteAdeleRing K) (B₂ := InfiniteAdeleRing L) (RingEquiv.refl _)
    (baseChangeEquivHom K L)
  rw [RingHom.algebraMap_toAlgebra]
  rw [RingHom.algebraMap_toAlgebra]
  ext k
  simp [baseChange]
  sorry


instance : Module.Free (InfiniteAdeleRing K) (L ⊗[K] InfiniteAdeleRing K) := sorry

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
instance : IsTopologicalSemiring (L ⊗[K] InfiniteAdeleRing K) :=
  IsModuleTopology.topologicalSemiring (InfiniteAdeleRing K) _

--instance : Algebra K (InfiniteAdeleRing L) := sorry
instance Pi.algebra' {I : Type*} {f g : I → Type*} {r : ∀ i, CommSemiring (f i)}
    {m : ∀ i, Semiring (g i)}
    [∀ i, Algebra (f i) (g i)] : Algebra (∀ i, f i) (∀ i, g i) where
  algebraMap := {
    toFun := Pi.map fun i => algebraMap (f i) (g i)
    map_one' := by funext; simp [Pi.map_apply]
    map_add' a b := by funext; simp [Pi.map_apply]
    map_mul' a b := by funext; simp [Pi.map_apply]
    map_zero' := by funext; simp [Pi.map_apply]
  }
  commutes' r x := by
    simp
    funext
    simp [Algebra.commutes]
  smul_def' r x := by
    simp
    funext
    simp [Algebra.smul_def]
    sorry
  /-add_smul := by
    intros
    ext1
    apply add_smul
  zero_smul := by
    intros
    ext1
    rw [zero_smul]-/

/-
attribute [local instance] Algebra.TensorProduct.rightAlgebra in
noncomputable
instance : Algebra (InfiniteAdeleRing K) ((i : InfinitePlace K) → L ⊗[K] i.Completion) :=
  Pi.algebra'-/

instance : Module.Free (InfiniteAdeleRing K) (InfiniteAdeleRing L) := sorry

open scoped Classical in
attribute [local instance] Algebra.TensorProduct.rightAlgebra in
/-- The canonical `L`-algebra isomorphism from `L ⊗_K K_∞` to `L_∞` induced by the
`K`-algebra base change map `K_∞ → L_∞`. -/
noncomputable
def baseChangeEquiv :
    L ⊗[K] InfiniteAdeleRing K ≃ₐ[L] InfiniteAdeleRing L := by
  apply AlgEquiv.ofBijective (SemialgHom.baseChange_of_algebraMap (baseChange K L)) sorry

instance : IsModuleTopology (InfiniteAdeleRing K) (InfiniteAdeleRing L) :=
  let d := Module.finrank (InfiniteAdeleRing K) (InfiniteAdeleRing L)
  -- Idea is to build a continuous linear equiv out of the components, using `ContinuousLinearEquiv.piCongrLeft`?
  let e : (Fin d → InfiniteAdeleRing K) ≃ₗ[InfiniteAdeleRing K] InfiniteAdeleRing L := by
    exact Module.Finite.equivPi _ _ |>.symm
  IsModuleTopology.iso e

theorem continuous_baseChangeEquiv_tmul_right :
    Continuous fun x => baseChangeEquiv K L (1 ⊗ₜ x) := by
  sorry--simpa [SemialgHom.baseChange_of_algebraMap_tmul_right] using
    --continuous_pi fun _ => Completion.comapHom_cont rfl

noncomputable
instance : Algebra K (InfiniteAdeleRing L) := Pi.algebra _ _

instance : IsScalarTower K L (InfiniteAdeleRing L) := Pi.isScalarTower

open scoped Classical in
attribute [local instance] Algebra.TensorProduct.rightAlgebra in
/-- The canonical `L`-algebra isomorphism from `L ⊗_K K_∞` to `L_∞` induced by the
`K`-algebra base change map `K_∞ → L_∞`. -/
noncomputable
def baseChangeEquivCLE :
    L ⊗[K] InfiniteAdeleRing K ≃A[L] InfiniteAdeleRing L := by
  apply IsModuleTopology.continuousAlgEquiv' K (InfiniteAdeleRing K) (baseChangeEquiv K L)
    (continuous_baseChangeEquiv_tmul_right K L) (SemialgHom.baseChange_of_algebraMap_tmul_right _)

end NumberField.InfiniteAdeleRing
