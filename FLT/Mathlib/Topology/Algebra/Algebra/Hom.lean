import Mathlib.Topology.Algebra.Algebra.Equiv
import FLT.Mathlib.Algebra.Algebra.Hom
import FLT.Mathlib.Algebra.Algebra.Tower

/-- A `SemialgHom` (i.e., `ψ` such that `ψ (r • a) = φ r • ψ a` for some `φ : R →+* S`) that
is also continuous. -/
structure ContinuousSemialgHom {R S : Type*} [CommSemiring R] [CommSemiring S]
    (φ : R →+* S) (A B : Type*) [TopologicalSpace A] [TopologicalSpace B]
    [Semiring A] [Semiring B] [Algebra R A] [Algebra S B]
    extends SemialgHom φ A B where
  continuous_toFun : Continuous toFun

@[inherit_doc SemialgHom]
infixr:25 " →SA " => ContinuousSemialgHom _

@[inherit_doc]
notation:25 A " →SA[" φ:25 "] " B:0 => ContinuousSemialgHom φ A B

class ContinuousSemialgHomClass (F : Type*) {R S : outParam Type*}
  [CommSemiring R] [CommSemiring S] (φ : outParam (R →+* S)) (A B : outParam Type*)
  [Semiring A] [Semiring B] [Algebra R A] [Algebra S B] [TopologicalSpace A] [TopologicalSpace B]
  [FunLike F A B] extends SemialgHomClass F φ A B where continuous_toFun (f : F) : Continuous f

namespace ContinuousSemialgHom

variable {R S : Type*} [CommSemiring R] [CommSemiring S] (φ : R →+* S)
    (A B : Type*) [Semiring A] [Semiring B] [Algebra R A] [Algebra S B]
    [TopologicalSpace A] [TopologicalSpace B]

instance instFunLike : FunLike (A →SA[φ] B) A B where
  coe f := f.toFun
  coe_injective' f g h := by
    cases f
    cases g
    congr
    exact DFunLike.coe_injective' h

instance : CoeOut (A →SA[φ] B) (A →ₛₐ[φ] B) :=
  ⟨fun f => f.toSemialgHom⟩

variable (F : Type*) (A B : outParam Type*)
  [Semiring A] [Semiring B] [Algebra R A] [Algebra S B]
  [FunLike F A B] [TopologicalSpace A] [TopologicalSpace B] [ContinuousSemialgHomClass F φ A B]

instance : ContinuousSemialgHomClass (A →SA[φ] B) φ A B where
  map_add ψ := ψ.map_add
  map_smulₛₗ ψ := ψ.map_smulₛₗ
  map_mul ψ := ψ.map_mul
  map_one ψ := ψ.map_one
  map_zero ψ := ψ.map_zero
  continuous_toFun ψ := ψ.continuous_toFun

variable {F} {φ} {A} {B} in
def _root_.ContinuousSemialgHomClass.toContinuousSemialgHom (f : F) : A →SA[φ] B :=
  { (f : A →ₛₐ[φ] B) with continuous_toFun := ContinuousSemialgHomClass.continuous_toFun f }

instance : CoeTC F (A →SA[φ] B) :=
  ⟨ContinuousSemialgHomClass.toContinuousSemialgHom⟩

@[simp]
theorem coe_coe (f : F) : ⇑(f : A →SA[φ] B) = f :=
  rfl

theorem toSemialgHom_eq_coe (f : A →SA[φ] B) : f.toSemialgHom = f :=
  rfl

@[simp]
theorem toLinearMap_eq_coe (f : A →SA[φ] B) : f.toLinearMap = f := by
  rfl

@[simp]
theorem toRingHom_eq_coe (f : A →SA[φ] B) : f.toRingHom = f :=
  rfl

theorem commutes (ψ : A →SA[φ] B) (r : R) :
    ψ (algebraMap R A r) = algebraMap S B (φ r) := by
  simpa using ψ.toSemialgHom.commutes r

/-- The product of two continuous semi-algebra isomorphisms on the same domain. -/
def prod {C : Type*} [Semiring C] [Algebra R C] [Algebra S C] [TopologicalSpace C] (f : A →SA[φ] B)
    (g : A →SA[φ] C) :
    A →SA[φ] B × C where
  __ := f.toSemialgHom.prod g.toSemialgHom
  continuous_toFun := f.continuous_toFun.prodMk g.continuous_toFun

variable {φ A B} in
/-- the product of two continuous semi-algebra isomorphisms on different domains. -/
def prodMap {C D : Type*} [Semiring C] [Semiring D]
    [Algebra S C] [Algebra S D] [Algebra R D]
    [TopologicalSpace C] [TopologicalSpace D]
    [Algebra R B] (f : A →SA[φ] C) (g : B →SA[φ] D) :
    A × B →SA[φ] C × D where
  __ := SemialgHom.prodMap f g
  continuous_toFun := Continuous.prodMap f.continuous_toFun g.continuous_toFun

end ContinuousSemialgHom
