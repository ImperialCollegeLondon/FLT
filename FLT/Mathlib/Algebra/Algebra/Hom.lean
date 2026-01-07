import Mathlib.Algebra.Algebra.Hom
import Mathlib.Algebra.Algebra.Prod

section semialghom

/-- Let `φ : R →+* S` be a ring homomorphism, let `A` be an `R`-algebra and let `B` be
an `S`-algebra. Then `SemialgHom φ A B` or `A →ₛₐ[φ] B` is the ring homomorphisms `ψ : A →+* B`
making lying above `φ` (i.e. such that `ψ (r • a) = φ r • ψ a`).
-/
structure SemialgHom {R S : Type*} [CommSemiring R] [CommSemiring S] (φ : R →+* S)
    (A B : Type*)  [Semiring A] [Semiring B] [Algebra R A] [Algebra S B]
    extends A →ₛₗ[φ] B, RingHom A B

@[inherit_doc SemialgHom]
infixr:25 " →ₛₐ " => SemialgHom _

@[inherit_doc]
notation:25 A " →ₛₐ[" φ:25 "] " B:0 => SemialgHom φ A B

variable {R S : Type*} [CommSemiring R] [CommSemiring S] (φ : R →+* S)
    (A B : Type*) [Semiring A] [Semiring B] [Algebra R A] [Algebra S B]

instance instFunLike : FunLike (A →ₛₐ[φ] B) A B where
  coe f := f.toFun
  coe_injective' f g h := by
    cases f
    cases g
    congr
    exact DFunLike.coe_injective' h

variable {φ} {A} {B} in
lemma SemialgHom.map_smul (ψ : A →ₛₐ[φ] B) (m : R) (x : A) : ψ (m • x) = φ m • ψ x :=
  LinearMap.map_smul' ψ.toLinearMap m x

@[simp]
theorem coe_mk (f : A →ₛₗ[φ] B) (h₁ h₂ h₃) : ((⟨f, h₁, h₂, h₃⟩ : A →ₛₐ[φ] B) : A → B) = f :=
  rfl

end semialghom

section semialghomclass

class SemialgHomClass (F : Type*) {R S : outParam Type*}
  [CommSemiring R] [CommSemiring S] (φ : outParam (R →+* S)) (A B : outParam Type*)
  [Semiring A] [Semiring B] [Algebra R A] [Algebra S B]
  [FunLike F A B] extends SemilinearMapClass F φ A B, RingHomClass F A B

variable (F : Type*) {R S : Type*}
  [CommSemiring R] [CommSemiring S] (φ : R →+* S) (A B : outParam Type*)
  [Semiring A] [Semiring B] [Algebra R A] [Algebra S B]
  [FunLike F A B] [SemialgHomClass F φ A B]

instance SemialgHomClass.instSemialgHom : SemialgHomClass (A →ₛₐ[φ] B) φ A B where
  map_add ψ := ψ.map_add
  map_smulₛₗ ψ := ψ.map_smulₛₗ
  map_mul ψ := ψ.map_mul
  map_one ψ := ψ.map_one
  map_zero ψ := ψ.map_zero

variable {F} {φ} {A} {B} in
def SemialgHomClass.toSemialgHom (f : F) : A →ₛₐ[φ] B :=
  { (f : A →ₛₗ[φ] B), (f : A →+* B) with }

instance : CoeTC F (A →ₛₐ[φ] B) :=
  ⟨SemialgHomClass.toSemialgHom⟩

@[simp]
theorem SemialgHom.coe_coe (f : F) : ⇑(f : A →ₛₐ[φ] B) = f :=
  rfl

end semialghomclass

section semialghom

variable {R S : Type*} [CommSemiring R] [CommSemiring S] {φ : R →+* S}
    {A B : Type*} [Semiring A] [Semiring B] [Algebra R A] [Algebra S B]

lemma SemialgHom.commutes (ψ : A →ₛₐ[φ] B) (r : R) :
    ψ (algebraMap R A r) = algebraMap S B (φ r) := by
  have := ψ.map_smul r 1
  rw [Algebra.smul_def, mul_one, map_one] at this
  rw [this, Algebra.smul_def, mul_one]

theorem SemialgHom.toLinearMap_eq_coe (f : A →ₛₐ[φ] B) : f.toLinearMap = f :=
  rfl

theorem SemialgHom.toRingHom_eq_coe (f : A →ₛₐ[φ] B) : f.toRingHom = f :=
  rfl

theorem SemialgHom.algebraMap_apply {A B : Type*} [CommSemiring A] [CommSemiring B]
    [Algebra R A] [Algebra S B] (f : A →ₛₐ[φ] B) (a : A) :
    letI := f.toAlgebra
    algebraMap A B a = f a := rfl

def SemialgHom.comp {T : Type*} [CommSemiring T] {C : Type*} [Semiring C]
    [Algebra T C] {ψ : S →+* T} {ξ : R →+* T} [RingHomCompTriple φ ψ ξ]
    (g : B →ₛₐ[ψ] C) (f : A →ₛₐ[φ] B) :
    A →ₛₐ[ξ] C where
  __ := LinearMap.comp (SemialgHom.toLinearMap g) (SemialgHom.toLinearMap f)
  __ := RingHom.comp g.toRingHom f.toRingHom

def SemialgHom.prod {C : Type*} [Semiring C] [Algebra R C] [Algebra S C] (f : A →ₛₐ[φ] B)
    (g : A →ₛₐ[φ] C) :
    A →ₛₐ[φ] B × C where
  __ := RingHom.prod f.toRingHom g.toRingHom
  map_smul' r x := by simp

variable (A) in
class AlgHom.CompatibleSMul {R S : Type*} [CommSemiring R] [CommSemiring S]
    (φ : R →+* S) (B : Type*) [Semiring B] [Algebra S B] [Algebra S A] [Algebra R A] where
  map_smul (f : A →ₐ[S] B) (r : R) (a : A) : f (r • a) = (φ r) • f a

variable (φ) (A) in
def SemialgHom.fst (C : Type*) [Semiring C] [Algebra S C] [Algebra S A] [Algebra R C]
    [AlgHom.CompatibleSMul (C × A) φ C] :
    C × A →ₛₐ[φ] C where
  __ := AlgHom.fst S C A
  map_smul' r x := AlgHom.CompatibleSMul.map_smul (AlgHom.fst S C A) r x

variable (φ) (A) in
def SemialgHom.snd (C : Type*) [Semiring C] [Algebra S C] [Algebra S A] [Algebra R C]
    [AlgHom.CompatibleSMul (C × A) φ A] :
    C × A →ₛₐ[φ] A where
  __ := AlgHom.snd S C A
  map_smul' r x := AlgHom.CompatibleSMul.map_smul (AlgHom.snd S C A) r x

instance [Algebra R B] : AlgHom.CompatibleSMul (A × B) (RingHom.id R) A where
  map_smul f r a := by simp

instance [Algebra R B] : AlgHom.CompatibleSMul (A × B) (RingHom.id R) B where
  map_smul f r a := by simp

def SemialgHom.prodMap {C D : Type*} [Semiring C] [Semiring D]
    [Algebra S C] [Algebra S D] [Algebra R D]
    [Algebra R B] (f : A →ₛₐ[φ] C) (g : B →ₛₐ[φ] D) :
    A × B →ₛₐ[φ] C × D := by
  let p₁ : A × B →ₛₐ[RingHom.id R] A := SemialgHom.fst (RingHom.id R) B A
  let p₂ : A × B →ₛₐ[RingHom.id R] B := SemialgHom.snd (RingHom.id R) B A
  let l := SemialgHom.comp (ψ := φ) (ξ := φ) (φ := RingHom.id R) f p₁
  let r := SemialgHom.comp (ψ := φ) (ξ := φ) (φ := RingHom.id R) g p₂
  exact SemialgHom.prod l r

end semialghom
