import Mathlib

open scoped TensorProduct

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
variable (ρ : Representation (𝓴 𝓞) G V)

instance : Algebra A (𝓴 𝓞) := sorry

#synth (Module A (𝓴 𝓞))

structure Lift where
  carrier: Type*
  [is_add_comm_monoid : AddCommMonoid carrier]
  [is_module : Module A carrier]
  [is_free : Module.Free A carrier]
  [is_finite : Module.Finite A carrier]
  map: Representation A G carrier
  -- is_lift is wrong, but defining W ⊗[A] (𝓴 𝓞) is hard. Just adding a foo condition for templating
  -- Function.Bijective (fun (_ : W ⊗[A] (𝓴 𝓞)) => (____ : V))
  is_lift: Function.Bijective (fun (x : carrier ⊗[A] (𝓴 𝓞)) => (0 : V))

def setoid : Setoid (Lift A ρ) where
  r W W' := W.carrier = W'.carrier -- this needs to be isomorphism
  iseqv := {
    refl := sorry
    symm := sorry
    trans := sorry
  }

#check Quotient

def Deformation := Quotient <| setoid A ρ

end Definitions
