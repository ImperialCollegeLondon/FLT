import Mathlib.Algebra.Algebra.Pi
import FLT.Mathlib.Algebra.Algebra.Hom

universe u v w

namespace Pi

-- The indexing type
variable {I : Type u}

-- The scalar type
variable {R : Type*}

-- The family of types already equipped with instances
variable {f : I → Type v} {a : I → Type w}
variable (R f a)

def mapAlgHom [CommSemiring R] [(i : I) → Semiring (f i)] [(i : I) → Algebra R (f i)]
    [(i : I) → Semiring (a i)] [(i : I) → Algebra R (a i)]
    (g : (i : I) → a i →ₐ[R] f i) :
    ((i : I) → a i) →ₐ[R] (i : I) → f i where
  toFun := Pi.map fun i => (g i).toFun
  map_one' := funext fun i => map_one (g i)
  map_mul' _ _ := funext fun i => map_mul (g i) _ _
  map_zero' := funext fun i => map_zero (g i)
  map_add' _ _ := funext fun i => map_add (g i) _ _
  commutes' _ := by ext; simp

end Pi

variable {α β ι : Type*}

@[simps!]
def AlgEquiv.piCurry (S : Type*) [CommSemiring S] {Y : ι → Type*} (α : (i : ι) → Y i → Type*)
    [(i : ι) → (y : Y i) → Semiring (α i y)] [(i : ι) → (y : Y i) → Algebra S (α i y)] :
    ((i : Sigma Y) → α i.1 i.2) ≃ₐ[S] ((i : ι) → (y : Y i) → α i y) where
  toEquiv := Equiv.piCurry α
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

@[simps!]
def AlgEquiv.piCongrLeft' (S : Type*) [CommSemiring S] (A : α → Type*) (e : α ≃ β)
    [∀ a, Semiring (A a)] [∀ a, Algebra S (A a)] :
    ((a : α) → A a) ≃ₐ[S] ((b : β) → A (e.symm b)) where
  toEquiv := Equiv.piCongrLeft' A e
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

@[simp]
theorem AlgEquiv.piCongrLeft'_symm (S : Type*) {A : Type*} [CommSemiring S] [Semiring A]
    [Algebra S A] (e : α ≃ β) :
    (AlgEquiv.piCongrLeft' S (fun _ => A) e).symm = AlgEquiv.piCongrLeft' S _ e.symm := by
  simp [AlgEquiv.piCongrLeft', AlgEquiv.symm, RingEquiv.symm, MulEquiv.symm,
    Equiv.piCongrLeft'_symm]
  rfl

@[simp]
theorem AlgEquiv.piCongrLeft'_symm_apply_apply (S : Type*) (A : α → Type*) [CommSemiring S]
    [∀ a, Semiring (A a)] [∀ a, Algebra S (A a)] (e : α ≃ β) (g : (b : β) → A (e.symm b)) (b : β) :
    (piCongrLeft' S A e).symm g (e.symm b) = g b := by
  rw [← Equiv.piCongrLeft'_symm_apply_apply A e g b]
  rfl

@[simps! apply toEquiv]
def AlgEquiv.piCongrLeft (S : Type*) [CommSemiring S] (B : β → Type*) (e : α ≃ β)
    [∀ b, Semiring (B b)] [∀ b, Algebra S (B b)] :
    ((a : α) → B (e a)) ≃ₐ[S] ((b : β) → B b) :=
  (AlgEquiv.piCongrLeft' S B e.symm).symm

def Pi.semialgHom  {I : Type*} {R S : Type*} (f : I → Type*) [CommSemiring R] [CommSemiring S]
    (φ : R →+* S) [s : (i : I) → Semiring (f i)] [(i : I) → Algebra S (f i)] {A : Type*}
    [Semiring A]  [Algebra R A] (g : (i : I) → A →ₛₐ[φ] f i) :
  A →ₛₐ[φ] (i : I) → f i where
  __ := Pi.ringHom fun i ↦ (g i).toRingHom
  map_smul' r a := by ext; simp
