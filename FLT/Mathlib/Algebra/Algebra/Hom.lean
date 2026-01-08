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
/-- Turn an element of `F` which satisfies `SemialgHomClass F φ A B` to a `SemialgHom`. -/
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

/-- The composition of two semi-algebra maps. -/
def SemialgHom.comp {T : Type*} [CommSemiring T] {C : Type*} [Semiring C]
    [Algebra T C] {ψ : S →+* T} {ξ : R →+* T} [RingHomCompTriple φ ψ ξ]
    (g : B →ₛₐ[ψ] C) (f : A →ₛₐ[φ] B) :
    A →ₛₐ[ξ] C where
  __ := LinearMap.comp (SemialgHom.toLinearMap g) (SemialgHom.toLinearMap f)
  __ := RingHom.comp g.toRingHom f.toRingHom

/-- An algebra map defines a semi-algebra map using `RingHom.id` -/
def AlgHom.toSemialgHom {R : Type*} [CommSemiring R] {A B : Type*} [Semiring A] [Semiring B]
    [Algebra R A] [Algebra R B] (f : A →ₐ[R] B) :
    A →ₛₐ[RingHom.id R] B where
  __ := f
  map_smul' _ _ := by simp

/-- The composition `(B →ₛₐ[ψ] C) ∘ (A →ₐ[S] B) → `A →ₛₐ[ψ] C` of a semi-algebra map with an
algebra map to give a semi-algebra map. -/
def SemialgHom.compAlgHom {T : Type*} [CommSemiring T] {C : Type*} [Semiring C]
    [Algebra T C] {ψ : S →+* T} [Algebra S A] (g : B →ₛₐ[ψ] C) (f : A →ₐ[S] B) :
    A →ₛₐ[ψ] C :=
  g.comp f.toSemialgHom

/-- The product of two semi-algebra maps on the same domain. -/
def SemialgHom.prod {C : Type*} [Semiring C] [Algebra R C] [Algebra S C] (f : A →ₛₐ[φ] B)
    (g : A →ₛₐ[φ] C) :
    A →ₛₐ[φ] B × C where
  __ := RingHom.prod f.toRingHom g.toRingHom
  map_smul' r x := by simp

/-- The product of two semi-algebra maps on separate domains. -/
def SemialgHom.prodMap {C D : Type*} [Semiring C] [Semiring D]
    [Algebra S C] [Algebra S D] [Algebra R D]
    [Algebra R B] (f : A →ₛₐ[φ] C) (g : B →ₛₐ[φ] D) :
    A × B →ₛₐ[φ] C × D :=
  (f.compAlgHom (AlgHom.fst R A B)).prod (g.compAlgHom (AlgHom.snd R A B))

end semialghom
