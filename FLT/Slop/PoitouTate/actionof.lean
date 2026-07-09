open CategoryTheory

namespace TopModuleCat

variable (G : Type*) (R : Type*) (M : Type*)
  [Monoid G] [CommRing R] [TopologicalSpace R]
  [AddCommGroup M] [Module R M] [TopologicalSpace M]
  [IsTopologicalAddGroup M] [ContinuousSMul R M]
  [DistribMulAction G M] [SMulCommClass G R M] [ContinuousConstSMul G M]

/-- A topological `R`-module `M` with a continuous (in the module variable) linear `G`-action,
as an object of `Action (TopModuleCat R) G`. The action of `g` is `m ↦ g • m`. -/
abbrev actionOf : Action (TopModuleCat R) G where
  V := .of R M
  ρ :=
  { toFun g := TopModuleCat.ofHom ⟨DistribSMul.toLinearMap R M g, continuous_const_smul g⟩
    map_one' := ConcreteCategory.ext (by ext m; exact one_smul G m)
    map_mul' g₁ g₂ := ConcreteCategory.ext (by ext m; exact mul_smul g₁ g₂ m) }

end TopModuleCat
