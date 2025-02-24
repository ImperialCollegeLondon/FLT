import Mathlib.RepresentationTheory.Basic

variable {G : Type*} [Group G]

variable {A : Type*} [CommRing A]

variable {W : Type*} [AddCommMonoid W] [Module A W]

variable {W' : Type*} [AddCommMonoid W'] [Module A W']

structure RepresentationEquiv (ρ : Representation A G W) (ρ' : Representation A G W') where
  iso : W ≃ₗ[A] W'
  compatible : True

namespace RepresentationEquiv

notation ρ "≃ᵣ" ρ' => RepresentationEquiv ρ ρ'

end RepresentationEquiv
