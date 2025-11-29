import Mathlib

variable {G M : Type*} [Group G] [AddCommGroup M]

structure Representation.Equiv {R : Type*} [CommSemiring R] {G : Type*} [Group G]
    {M₁ M₂ : Type*} [AddCommMonoid M₁] [AddCommMonoid M₂] [Module R M₁] [Module R M₂]
    (ρ₁ : Representation R G M₁) (ρ₂ : Representation R G M₂)
     extends M₁ ≃ₗ[R] M₂ where
     exchange : ∀(g : G), ∀(m : M₁), toFun (ρ₁ g m) = (ρ₂ g (toFun m))

def twist (ρ : Representation ℤ G M) (δ : G →* ℤˣ) : Representation ℤ G M where
  toFun g := {
    toFun m := δ g • ρ g m
    map_add' := by aesop
    map_smul' := by {
    intro m x
    simp only [map_smul, eq_intCast, Int.cast_eq]
    exact smul_comm (δ g) m ((ρ g) x)
    }}
  map_one' := by aesop
  map_mul' g h := by {
    ext m
    simp only [map_mul, Module.End.mul_apply, LinearMap.coe_mk, AddHom.coe_mk, map_zsmul_unit]
    rw[mul_comm, mul_smul]
  }
