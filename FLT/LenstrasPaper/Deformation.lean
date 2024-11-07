import Mathlib

section Definitions

variable {𝓞 : Type*} [CommRing 𝓞] [LocalRing 𝓞] [IsNoetherianRing 𝓞]
local notation3:max "𝓴" 𝓞 => (LocalRing.ResidueField 𝓞)

variable (𝓞) in
class 𝓒 (A : Type*) extends
  CommRing A,
  LocalRing A,
  Algebra 𝓞 A,
  TopologicalSpace A,
  TopologicalRing A
    where
  isAdic : IsAdic (LocalRing.maximalIdeal A)
  isLocalHom : IsLocalHom (algebraMap 𝓞 A)
  has_matching_residue : Function.Surjective (LocalRing.residue A ∘ algebraMap 𝓞 A)

variable (A : Type*) [𝓒 𝓞 A]
variable {G : Type*} [Group G] [TopologicalSpace G] [TopologicalGroup G]
variable {M : Type*} [AddCommMonoid M] [Module A M] [Module.Free A M] [Module.Finite A M]

variable {V : Type*} [AddCommMonoid V]
variable [Module (𝓴 𝓞) V] [Module.Free (𝓴 𝓞) V] [Module.Finite (𝓴 𝓞) V]
variable (ρbar : Representation (𝓴 𝓞) G V)

instance algebra_on_residue : Algebra A (𝓴 𝓞) :=
  Algebra.mk (LocalRing.residue A ∘ algebraMap 𝓞 A)

structure Lift where
  W: Type*
  [is_add_comm_monoid : AddCommMonoid W]
  [is_module : Module A W]
  [is_free : Module.Free A W]
  [is_finite : Module.Finite A W]
  ρ: Representation A G W
  is_lift: Function.Bijective (fun (x : W ⊗[A] (𝓴 𝓞)) => (0 : V))

instance : Setoid (Lift A ρ) where
  r := sorry
  iseqv := sorry

structure Deformation where
  lift: Quotient (Lift A ρ)

end Definitions
