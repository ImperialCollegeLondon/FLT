import FLT.Patching.Utils.TopologicallyFG
import Mathlib.Algebra.Ring.Ext
import Mathlib.Topology.Algebra.Module.Equiv

@[to_additive]
instance {α : Type*} [Finite α] : Finite (Monoid α) :=
  .of_injective (fun g ↦ g.1.1.1)
    fun g₁ g₂ e ↦ by ext a b; exact congr_fun (congr_fun e a) b

@[to_additive]
instance {α : Type*} [Finite α] : Finite (Group α) :=
  .of_injective (fun g ↦ g.1.1.1.1.1)
    fun g₁ g₂ e ↦ by ext a b; exact congr_fun (congr_fun e a) b

@[to_additive]
instance {α : Type*} [Finite α] : Finite (CommGroup α) :=
  .of_injective _ CommGroup.toGroup_injective

instance {α : Type*} [Finite α] : Finite (Ring α) :=
  .of_injective (fun g ↦ (g.toMonoid, g.toAddMonoid))
    fun g₁ g₂ e ↦ by ext a b; exacts [congr(($e).2.1.1.1 a b), congr(($e).1.1.1.1 a b)]

section Module

variable {R : Type*} [Ring R] [Algebra.FiniteType ℤ R]

instance {α : Type*} [Finite α] [AddCommGroup α] : Finite (Module R α) := by
  obtain ⟨s, hs⟩ := Algebra.FiniteType.out (self := ‹_›)
  refine .of_injective (fun g ↦ g.1.1.1.1 ∘ ((↑) : s → R)) fun g₁ g₂ e ↦ ?_
  ext r a
  replace hs := SetLike.le_def.mp hs.ge (x := r) trivial
  induction hs using Algebra.adjoin_induction generalizing a with
  | mem x hx => exact congr_fun (congr_fun e ⟨x, hx⟩) a
  | algebraMap r =>
    exact (@Int.cast_smul_eq_zsmul R _ _ _ g₁ r a).trans
      (Int.cast_smul_eq_zsmul R r a).symm
  | add x y hx hy hx' hy' =>
      exact (g₁.add_smul _ _ _).trans (congr($(hx' a) + $(hy' a)).trans (g₂.add_smul _ _ _).symm)
  | mul x y hx hy hx' hy' =>
      exact (g₁.mul_smul _ _ _).trans
        (((hx' _).trans congr(x • $(hy' a))).trans (g₂.mul_smul _ _ _).symm)

variable (R) in
def ModuleTypeCardLT (N : ℕ) : Type _ :=
  Σ (n : Fin N) (_ : AddCommGroup (Fin n)), Module R (Fin n)

instance (N : ℕ) : Finite (ModuleTypeCardLT R N) := by delta ModuleTypeCardLT; infer_instance

instance (N : ℕ) (α : ModuleTypeCardLT R N) : AddCommGroup (Fin α.1) := α.2.1

instance (N : ℕ) (α : ModuleTypeCardLT R N) : Module R (Fin α.1) := α.2.2

variable (R) in
noncomputable
def ModuleTypeCardLT.ofModule (N : ℕ) (M : Type*) [AddCommGroup M] [Module R M]
    [Finite M] (hM : Nat.card M < N) : ModuleTypeCardLT R N :=
  ⟨⟨Nat.card M, hM⟩, (Finite.equivFin M).symm.addCommGroup, (Finite.equivFin M).symm.module R⟩

noncomputable
def ModuleTypeCardLT.equivOfModule (N : ℕ) {M : Type*} [AddCommGroup M] [Module R M]
    [Finite M] (hM : Nat.card M < N) : M ≃ₗ[R] Fin ((ModuleTypeCardLT.ofModule R N M hM).1) :=
  ((show M ≃ Fin ((ModuleTypeCardLT.ofModule R N M hM).1)
    from Finite.equivFin M).symm.linearEquiv R).symm

end Module

section Algebra

variable {R : Type*} [CommRing R] [Algebra.FiniteType ℤ R]

instance {α : Type*} [Finite α] [Ring α] : Finite (Algebra R α) := by
  refine .of_injective (fun g ↦ g.toModule) fun g₁ g₂ e ↦ ?_
  ext r a
  exact congr($e.1.1.1.1 r a)

variable (R) in
def AlgebraTypeCardLT (N : ℕ) : Type _ :=
  Σ (n : Fin N) (_ : Ring (Fin n)), Algebra R (Fin n)

instance (N : ℕ) : Finite (AlgebraTypeCardLT R N) := by delta AlgebraTypeCardLT; infer_instance

instance (N : ℕ) (α : AlgebraTypeCardLT R N) : Ring (Fin α.1) := α.2.1

instance (N : ℕ) (α : AlgebraTypeCardLT R N) : Algebra R (Fin α.1) := α.2.2

variable (R) in
noncomputable
def AlgebraTypeCardLT.ofAlgebra (N : ℕ) (M : Type*) [Ring M] [Algebra R M]
    [Finite M] (hM : Nat.card M < N) : AlgebraTypeCardLT R N :=
  ⟨⟨Nat.card M, hM⟩, (Finite.equivFin M).symm.ring, (Finite.equivFin M).symm.algebra R⟩

noncomputable
def AlgebraTypeCardLT.equivOfAlgebra (N : ℕ) {M : Type*} [Ring M] [Algebra R M]
    [Finite M] (hM : Nat.card M < N) : M ≃ₐ[R] Fin ((AlgebraTypeCardLT.ofAlgebra R N M hM).1) :=
  ((show M ≃ Fin ((AlgebraTypeCardLT.ofAlgebra R N M hM).1)
    from Finite.equivFin M).symm.algEquiv R).symm

end Algebra

section Topology

instance {α} [Finite α] : Finite (TopologicalSpace α) :=
  .of_injective (fun t ↦ t.1) fun _ _ ↦ TopologicalSpace.ext

end Topology

section TopologicalModule

variable {R : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
  [Algebra.TopologicallyFG ℤ R]

instance {α : Type*} [Finite α] [AddCommGroup α] [TopologicalSpace α] [T2Space α] :
    Finite (Σ' (_ : Module R α), ContinuousSMul R α) := by
  obtain ⟨s, hs⟩ := Algebra.TopologicallyFG.out (self := ‹_›)
  refine .of_injective (fun g ↦ g.1.1.1.1.1 ∘ ((↑) : s → R)) fun g₁ g₂ e ↦ ?_
  obtain ⟨g₁, hg₁⟩ := g₁
  obtain ⟨g₂, hg₂⟩ := g₂
  congr
  exact Algebra.TopologicallyFG.module_ext ℤ R (↑s) hs inferInstance inferInstance hg₁ hg₂
    fun x hx ↦ congr_fun (congr_fun e ⟨x, hx⟩)

variable (R) in
def TopologicalModuleTypeCardLT (N : ℕ) : Type _ :=
  Σ' (n : Fin N) (_ : AddCommGroup (Fin n)) (_ : TopologicalSpace (Fin n)) (_ : T2Space (Fin n))
    (_ : Module R (Fin n)), ContinuousSMul R (Fin n)

instance (N : ℕ) : Finite (TopologicalModuleTypeCardLT R N) := by
  apply (config := { allowSynthFailures := true }) Finite.instPSigma; intro
  apply (config := { allowSynthFailures := true }) Finite.instPSigma; intro
  apply (config := { allowSynthFailures := true }) Finite.instPSigma; intro
  apply (config := { allowSynthFailures := true }) Finite.instPSigma; intro
  infer_instance

instance (N : ℕ) (α : TopologicalModuleTypeCardLT R N) : AddCommGroup (Fin α.1) := α.2.1
instance (N : ℕ) (α : TopologicalModuleTypeCardLT R N) : TopologicalSpace (Fin α.1) := α.2.2.1
instance (N : ℕ) (α : TopologicalModuleTypeCardLT R N) : T2Space (Fin α.1) := α.2.2.2.1
instance (N : ℕ) (α : TopologicalModuleTypeCardLT R N) : Module R (Fin α.1) := α.2.2.2.2.1
instance (N : ℕ) (α : TopologicalModuleTypeCardLT R N) : ContinuousSMul R (Fin α.1) := α.2.2.2.2.2

open scoped Topology in
variable (R) in
noncomputable
def TopologicalModuleTypeCardLT.ofModule (N : ℕ) (M : Type*) [AddCommGroup M]
    [TopologicalSpace M] [Module R M] [TopologicalSpace M] [T2Space M] [ContinuousSMul R M]
    [Finite M] (hM : Nat.card M < N) : TopologicalModuleTypeCardLT R N :=
  ⟨⟨Nat.card M, hM⟩, (Finite.equivFin M).symm.addCommGroup, .coinduced (Finite.equivFin M)
    inferInstance,
    letI := TopologicalSpace.coinduced (Finite.equivFin M) inferInstance
    Topology.IsEmbedding.t2Space (f := (Finite.equivFin M).symm)
    ⟨⟨by rw [(Finite.equivFin M).induced_symm.symm]⟩, (Finite.equivFin M).symm.injective⟩,
    (Finite.equivFin M).symm.module _, by
  letI := (Finite.equivFin M).symm.addCommGroup
  letI := (Finite.equivFin M).symm.module R
  letI := TopologicalSpace.coinduced (Finite.equivFin M) inferInstance
  constructor
  let e := Homeomorph.prodCongr (.refl R) ((Finite.equivFin M).toHomeomorph (fun _ ↦ Iff.rfl))
  refine continuous_coinduced_rng.comp (e.comp_continuous_iff'.mp ?_)
  convert continuous_smul (M := R) (X := M)
  simp [e]⟩

noncomputable
def TopologicalModuleTypeCardLT.equivOfModule (N : ℕ) (M : Type*) [AddCommGroup M] [Module R M]
    [TopologicalSpace M] [Module R M] [TopologicalSpace M] [T2Space M] [ContinuousSMul R M]
    [Finite M] (hM : Nat.card M < N) :
    M ≃L[R] Fin (TopologicalModuleTypeCardLT.ofModule R N M hM).1 where
  __ := ((show M ≃ Fin ((ModuleTypeCardLT.ofModule R N M hM).1) from
    Finite.equivFin M).symm.linearEquiv R).symm
  __ := (Finite.equivFin M).toHomeomorph (Y := Fin (ofModule R N M hM).1) (fun _ ↦ Iff.rfl)

end TopologicalModule

section TopologicalAlgebra

variable {R : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
  [Algebra.TopologicallyFG ℤ R]

instance {α : Type*} [Finite α] [Ring α] [TopologicalSpace α] [T2Space α] :
    Finite (Σ' (_ : Algebra R α), ContinuousSMul R α) := by
  refine .of_injective (β := Σ' (_ : Module R α), ContinuousSMul R α)
    (fun g ↦ PSigma.mk g.1.toModule g.2)
    fun g₁ g₂ e ↦ ?_
  obtain ⟨g₁, hg₁⟩ := g₁
  obtain ⟨g₂, hg₂⟩ := g₂
  congr
  ext
  exact congr(($e).1.smul _ _)

variable (R) in
def TopologicalAlgebraTypeCardLT [IsTopologicalRing R] [Algebra.TopologicallyFG ℤ R] (N : ℕ) :
    Type _ :=
  Σ' (n : Fin N) (_ : Ring (Fin n)) (_ : TopologicalSpace (Fin n)) (_ : T2Space (Fin n))
    (_ : Algebra R (Fin n)), ContinuousSMul R (Fin n)

instance (N : ℕ) : Finite (TopologicalAlgebraTypeCardLT R N) := by
  apply (config := { allowSynthFailures := true }) Finite.instPSigma; intro
  apply (config := { allowSynthFailures := true }) Finite.instPSigma; intro
  apply (config := { allowSynthFailures := true }) Finite.instPSigma; intro
  apply (config := { allowSynthFailures := true }) Finite.instPSigma; intro
  infer_instance

instance (N : ℕ) (α : TopologicalAlgebraTypeCardLT R N) : Ring (Fin α.1) := α.2.1
instance (N : ℕ) (α : TopologicalAlgebraTypeCardLT R N) : TopologicalSpace (Fin α.1) := α.2.2.1
instance (N : ℕ) (α : TopologicalAlgebraTypeCardLT R N) : T2Space (Fin α.1) := α.2.2.2.1
instance (N : ℕ) (α : TopologicalAlgebraTypeCardLT R N) : Algebra R (Fin α.1) := α.2.2.2.2.1
instance (N : ℕ) (α : TopologicalAlgebraTypeCardLT R N) : ContinuousSMul R (Fin α.1) := α.2.2.2.2.2

open scoped Topology in
variable (R) in
noncomputable
def TopologicalAlgebraTypeCardLT.ofAlgebra (N : ℕ) (M : Type*) [Ring M]
    [TopologicalSpace M] [Algebra R M] [TopologicalSpace M] [T2Space M] [ContinuousSMul R M]
    [Finite M] (hM : Nat.card M < N) : TopologicalAlgebraTypeCardLT R N :=
  ⟨⟨Nat.card M, hM⟩, (Finite.equivFin M).symm.ring, .coinduced (Finite.equivFin M) inferInstance,
    letI := TopologicalSpace.coinduced (Finite.equivFin M) inferInstance
    Topology.IsEmbedding.t2Space (f := (Finite.equivFin M).symm)
    ⟨⟨congr_fun (Finite.equivFin M).induced_symm.symm inferInstance⟩,
    (Finite.equivFin M).symm.injective⟩,
    (Finite.equivFin M).symm.algebra _, (TopologicalModuleTypeCardLT.ofModule R N M hM).2.2.2.2.2⟩

noncomputable
def TopologicalAlgebraTypeCardLT.equivOfAlgebra (N : ℕ) (M : Type*) [Ring M]
    [TopologicalSpace M] [Algebra R M] [TopologicalSpace M] [T2Space M] [ContinuousSMul R M]
    [Finite M] (hM : Nat.card M < N) :
    M ≃ₐ[R] Fin (TopologicalAlgebraTypeCardLT.ofAlgebra R N M hM).1 :=
  ((show M ≃ Fin ((AlgebraTypeCardLT.ofAlgebra R N M hM).1)
    from Finite.equivFin M).symm.algEquiv R).symm

lemma TopologicalAlgebraTypeCardLT.isHomeomorph_equivOfAlgebra (N : ℕ) (M : Type*) [Ring M]
    [TopologicalSpace M] [Algebra R M] [TopologicalSpace M] [T2Space M] [ContinuousSMul R M]
    [Finite M] (hM : Nat.card M < N) : IsHomeomorph (equivOfAlgebra (R := R) N M hM) :=
  ((Finite.equivFin M).toHomeomorph (Y := Fin (ofAlgebra R N M hM).1)
    (fun _ ↦ Iff.rfl)).isHomeomorph

end TopologicalAlgebra
