import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.Topology.Algebra.Module.Equiv
import FLT.Mathlib.Topology.Algebra.Module.Equiv
import FLT.Mathlib.Topology.Algebra.Module.Quotient

def ContinuousAddEquiv.toIntContinuousLinearEquiv {M M₂ : Type*} [AddCommGroup M]
    [TopologicalSpace M] [AddCommGroup M₂] [TopologicalSpace M₂] (e : M ≃ₜ+ M₂) :
    M ≃L[ℤ] M₂ where
  __ := e.toIntLinearEquiv
  continuous_toFun := e.continuous
  continuous_invFun := e.continuous_invFun

def ContinuousAddEquiv.quotientPi {ι : Type*} {G : ι → Type*} [(i : ι) → AddCommGroup (G i)]
    [(i : ι) → TopologicalSpace (G i)]
    [(i : ι) → IsTopologicalAddGroup (G i)]
    [Fintype ι] (p : (i : ι) → AddSubgroup (G i)) [DecidableEq ι] :
    ((i : ι) → G i) ⧸ AddSubgroup.pi (_root_.Set.univ) p ≃ₜ+ ((i : ι) → G i ⧸ p i) :=
  (Submodule.quotientPiContinuousLinearEquiv
    (fun (i : ι) => AddSubgroup.toIntSubmodule (p i))).toContinuousAddEquiv

/-- A family indexed by a type with a unique element
is `ContinuousMulEquiv` to the element at the single index. -/
@[to_additive
/-- A family indexed by a type with a unique element
is `ContinuousAddEquiv` to the element at the single index. -/]
def ContinuousMulEquiv.piUnique {ι : Type*} (M : ι → Type*) [(j : ι) → Mul (M j)]
    [(j : ι) → TopologicalSpace (M j)] [Unique ι] :
    ((j : ι) → M j) ≃ₜ* M default where
  __ := MulEquiv.piUnique M
  continuous_toFun := continuous_apply default
  continuous_invFun := by simpa [continuous_pi_iff, Unique.forall_iff] using continuous_id'

/-- Splits the indices of `∀ (i : ι), Y i` along the predicate `p`.
This is `Equiv.piEquivPiSubtypeProd` as a `ContinuousMulEquiv`. -/
@[to_additive piEquivPiSubtypeProd
/-- Splits the indices of `∀ (i : ι), Y i` along the predicate `p`.
This is `Equiv.piEquivPiSubtypeProd` as a `ContinuousAddEquiv`. -/]
def ContinuousMulEquiv.piEquivPiSubtypeProd {ι : Type*} (p : ι → Prop) (Y : ι → Type*)
    [(i : ι) → TopologicalSpace (Y i)] [(i : ι) → Mul (Y i)] [DecidablePred p] :
    ((i : ι) → Y i) ≃ₜ* ((i : { x : ι // p x }) → Y i) × ((i : { x : ι // ¬p x }) → Y i) :=
  {Homeomorph.piEquivPiSubtypeProd p Y with map_mul' _ _ := rfl}

/-- Any `ContinuousMulEquiv` induces a `ContinuousMulEquiv` on units. -/
def ContinuousMulEquiv.units_map {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
    [Monoid M] [Monoid N] (f : M ≃ₜ* N) : Mˣ ≃ₜ* Nˣ :=
  {
  __ := Units.mapEquiv f
  continuous_toFun := by apply Continuous.units_map _ f.continuous_toFun
  continuous_invFun := by apply Continuous.units_map _ f.continuous_invFun
      }

@[to_additive]
theorem ContinuousMulEquiv.coe_toHomeomorph {M N : Type*} [TopologicalSpace M]
    [TopologicalSpace N] [AddCommMonoid M] [AddCommMonoid N]
    (f : M ≃ₜ* N) : f.toHomeomorph = ⇑f := rfl
