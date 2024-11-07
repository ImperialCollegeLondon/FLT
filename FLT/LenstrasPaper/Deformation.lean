import Mathlib

universe u

section Definitions

def ProjectiveCompletion (A : Type*) [LocalRing A] :=

class 𝓒 (𝓞 A : Type*) [CommRing 𝓞] [LocalRing 𝓞] extends CommRing A, LocalRing A, Algebra 𝓞 A, TopologicalSpace A, TopologicalRing A where
  has_matching_residue : Function.Surjective (LocalRing.residue A ∘ algebraMap 𝓞 A)
  has_projective_topology: A ≃ₜ ProjectiveCompletion A

variable {𝓞 : Type u} [CommRing 𝓞] [LocalRing 𝓞] [IsNoetherianRing 𝓞]
def 𝓴 := LocalRing.ResidueField 𝓞

variable {G : Type u} [Group G] [TopologicalSpace G] [TopologicalGroup G]


variable (A : Type u) [LenstraLocalTopologicalAlgebra 𝓞 A]

variable {V : Type u} [AddCommMonoid V] [Module (𝓴 𝓞) V]
variable {M : Type u} [AddCommMonoid M] [Module A M]

structure Lift (ρ :  Representation k G V) where
  carrier: Type u
  [is_add_comm_monoid : AddCommMonoid carrier]
  [is_module : Module A carrier]
  map: Representation A G carrier
  is_lift: ρ (1:G) 0 = 0 -- Representation.tprod map k


variable (a : Lift ρ A)


#exit

instance : Setoid (Lift ρ) where
  r := _
  iseqv := _


structure Deformation where
  lift: Quotient (Lift ρ)  -- Quotient of Lifts up to isomorphism


-- structure Deformation

end Definitions
