import Mathlib.Logic.Equiv.Basic

variable {α : Type*} {β : Type*} {f : α → β}

/-- A family of equivalences `∀ a, γ₁ a ≃ γ₂ a` generates an equivalence between the product
over the fibers of a function `f : α → β` on index types. -/
def Equiv.piCongrSigmaFiber {γ₁ γ₂ : α → Sort*} (e : (a : α) → γ₁ a ≃ γ₂ a) :
    ((σ : (y : β) × { x : α // f x = y }) → γ₁ σ.2.1) ≃ ((a : α) → γ₂ a) :=
  Equiv.piCongrLeft γ₁ (Equiv.sigmaFiberEquiv f) |>.trans (Equiv.piCongrRight e)

@[simp]
theorem Equiv.piCongrSigmaFiber_apply {γ₁ γ₂ : α → Sort*} (e : (a : α) → γ₁ a ≃ γ₂ a)
    (g : (σ : (y : β) × { x : α // f x = y }) → γ₁ σ.2.1) (a : α) :
    Equiv.piCongrSigmaFiber e g a = e a (g ⟨f a, ⟨a, rfl⟩⟩) := rfl

@[simp]
theorem Equiv.piCongrSigmaFiber_symm_apply {γ₁ γ₂ : α → Sort*} (e : (a : α) → γ₁ a ≃ γ₂ a)
    (g : (a : α) → γ₂ a) (σ : (y : β) × { x : α // f x = y }) :
    (Equiv.piCongrSigmaFiber e).symm g σ = (e σ.2.1).symm (g σ.2.1) := rfl

/-- Let `f : α → β` be a function on index types. A family of equivalences, indexed by `b : β`,
between the product over the fiber of `b` under `f` given as
`∀ (σ : { a : α // f a = b }) → γ₁ σ.1) ≃ γ₂ b` lifts to an equivalence over the products
`∀ a, γ₁ a ≃ ∀ b, γ₂ b`. -/
def Equiv.piCongrFiberwise {γ₁ : α → Type*} {γ₂ : β → Type*} {f : α → β}
    (e : (b : β) → ((σ : { a : α // f a = b }) → γ₁ σ.1) ≃ γ₂ b) :
    ((a : α) → γ₁ a) ≃ ((b : β) → γ₂ b) :=
  ((Equiv.piCongrSigmaFiber (fun _ => Equiv.refl _)).symm.trans
    (Equiv.piCurry fun b (x : { x : α // f x = b }) => γ₁ x.1)).trans
      (Equiv.piCongrRight e)

@[simp]
theorem Equiv.piCongrFiberwise_apply {γ₁ : α → Type*} {γ₂ : β → Type*} {f : α → β}
    (e : (b : β) → ((σ : { a : α // f a = b }) → γ₁ σ.1) ≃ γ₂ b) (g : (a : α) → γ₁ a) (b : β) :
    Equiv.piCongrFiberwise e g b = e b fun σ => g σ.1 := rfl

@[simp]
theorem Equiv.piCongrFiberwise_symm_apply {γ₁ : α → Type*} {γ₂ : β → Type*} {f : α → β}
    (e : (b : β) → ((σ : { a : α // f a = b }) → γ₁ σ.1) ≃ γ₂ b) (g : (b : β) → γ₂ b) (a : α) :
    (Equiv.piCongrFiberwise e).symm g a = (e (f a)).symm (g (f a)) ⟨a, rfl⟩ := rfl
