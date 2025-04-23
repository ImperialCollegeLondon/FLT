import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.Algebra.Algebra.Equiv
import FLT.Mathlib.Algebra.Module.LinearMap.Defs
import FLT.Mathlib.Algebra.Algebra.Tower
import FLT.Mathlib.Topology.Algebra.Monoid

namespace IsModuleTopology

open ModuleTopology

section semiring_bilinear

-- I need commutativity of R because we don't have bilinear maps for non-commutative rings.
-- **TODO** ask on the Zulip whether this is an issue.
variable {R : Type*} [τR : TopologicalSpace R] [CommSemiring R]

variable {A : Type*} [AddCommMonoid A] [Module R A] [aA : TopologicalSpace A] [IsModuleTopology R A]
variable {B : Type*} [AddCommMonoid B] [Module R B] [aB : TopologicalSpace B] [IsModuleTopology R B]
variable {C : Type*} [AddCommMonoid C] [Module R C] [aC : TopologicalSpace C] [IsModuleTopology R C]

-- R^n x B -> C bilinear is continuous for module topologies.
-- Didn't someone give a counterexample when not fg on MO?
-- This works for semirings
theorem Module.continuous_bilinear_of_pi_finite (ι : Type*) [Finite ι]
    (bil : (ι → R) →ₗ[R] B →ₗ[R] C) : Continuous (fun ab ↦ bil ab.1 ab.2 : ((ι → R) × B → C)) := by
  classical
  -- far too long proof that a bilinear map bil : R^n x B -> C
  -- equals the function sending (f,b) to ∑ i, f(i)*bil(eᵢ,b)
  have foo : (fun fb ↦ bil fb.1 fb.2 : ((ι → R) × B → C)) =
      (fun fb ↦ ∑ᶠ i, ((fb.1 i) • (bil (Pi.single i 1) fb.2) : C)) := by
    ext ⟨f, b⟩
    simp_rw [← LinearMap.smul_apply]
    rw [← LinearMap.finsum_apply]
    congr
    simp_rw [LinearMap.smul_apply, ← LinearMap.map_smul]
    convert AddMonoidHom.map_finsum bil.toAddMonoidHom _
    · ext j
      simp_rw [← Pi.single_smul, smul_eq_mul, mul_one]
      symm
      -- Is there a missing delaborator? No ∑ᶠ notation
      change (∑ᶠ (i : ι), Pi.single i (f i)) j = f j
      -- last tactic has no effect
      rw [finsum_apply (Set.toFinite _)]
      convert finsum_eq_single (fun i ↦ Pi.single i (f i) j) j
        (by simp (config := {contextual := true})) using 1
      simp
    · apply Set.toFinite _--(Function.support fun x ↦ f x • Pi.single x 1)
  rw [foo]
  haveI : ContinuousAdd C := toContinuousAdd R C
  exact continuous_finsum (fun i ↦ by fun_prop) (locallyFinite_of_finite _)

theorem Module.continuous_bilinear_of_finite_free [IsTopologicalSemiring R] [Module.Finite R A]
    [Module.Free R A] (bil : A →ₗ[R] B →ₗ[R] C) :
    Continuous (fun ab ↦ bil ab.1 ab.2 : (A × B → C)) := by
  let ι := Module.Free.ChooseBasisIndex R A
  let hι : Fintype ι := Module.Free.ChooseBasisIndex.fintype R A
  let b : Basis ι R A := Module.Free.chooseBasis R A
  let elinear : A ≃ₗ[R] (ι → R) := b.equivFun
  let bil' : (ι → R) →ₗ[R] B →ₗ[R] C := bil.comp elinear.symm.toLinearMap
  have := Module.continuous_bilinear_of_pi_finite ι bil'
  have foo : (fun ab ↦ (bil ab.1) ab.2 : A × B → C) = (fun fb ↦ bil' fb.1 fb.2) ∘
    (fun ab ↦ (elinear ab.1, ab.2) : A × B → (ι → R) × B) := by
    ext ⟨a, b⟩
    simp [bil']
  rw [foo]
  apply Continuous.comp this
  apply Continuous.prodMk
  · exact continuous_of_linearMap (elinear.toLinearMap ∘ₗ (LinearMap.fst R A B))
  · fun_prop

end semiring_bilinear

section ring_bilinear

variable {R : Type*} [τR : TopologicalSpace R] [CommRing R] [IsTopologicalRing R]

variable {A : Type*} [AddCommGroup A] [Module R A] [aA : TopologicalSpace A] [IsModuleTopology R A]
variable {B : Type*} [AddCommGroup B] [Module R B] [aB : TopologicalSpace B] [IsModuleTopology R B]
variable {C : Type*} [AddCommGroup C] [Module R C] [aC : TopologicalSpace C] [IsModuleTopology R C]

-- This needs rings
theorem Module.continuous_bilinear_of_finite [Module.Finite R A]
    (bil : A →ₗ[R] B →ₗ[R] C) : Continuous (fun ab ↦ bil ab.1 ab.2 : (A × B → C)) := by
  obtain ⟨m, f, hf⟩ := Module.Finite.exists_fin' R A
  let bil' : (Fin m → R) →ₗ[R] B →ₗ[R] C := bil.comp f
  let φ := f.prodMap (LinearMap.id : B →ₗ[R] B)
  have foo : Function.Surjective (LinearMap.id : B →ₗ[R] B) :=
    Function.RightInverse.surjective (congrFun rfl)
  have hφ : Function.Surjective φ := Function.Surjective.prodMap hf foo
  have := (isQuotientMap_of_surjective hφ).2
  rw [this, continuous_def]
  intro U hU
  rw [isOpen_coinduced, ← Set.preimage_comp]
  suffices Continuous ((fun ab ↦ (bil ab.1) ab.2) ∘ φ : (Fin m → R) × B → C) by
    rw [continuous_def] at this
    convert this _ hU
  rw [show (fun ab ↦ (bil ab.1) ab.2 : A × B → C) ∘ φ = (fun fb ↦ bil' fb.1 fb.2) by
    ext ⟨a, b⟩
    simp [bil', φ]]
  apply Module.continuous_bilinear_of_finite_free

end ring_bilinear

section semiring_algebra

open scoped TensorProduct

-- these shouldn't be rings, they should be semirings
variable (R) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
variable (D : Type*) [Ring D] [Algebra R D] [Module.Finite R D]
variable [TopologicalSpace D] [IsModuleTopology R D]

open scoped TensorProduct

@[continuity, fun_prop]
theorem continuous_mul'
    (R : Type*) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    (D : Type*) [Ring D] [Algebra R D] [Module.Finite R D] [Module.Free R D] [TopologicalSpace D]
    [IsModuleTopology R D] : Continuous (fun ab ↦ ab.1 * ab.2 : D × D → D) :=
  Module.continuous_bilinear_of_finite (LinearMap.mul R D)

include R in
lemma topologicalSemiring [Module.Free R D] : IsTopologicalSemiring D where
  continuous_add := (toContinuousAdd R D).1
  continuous_mul := continuous_mul' R D

end semiring_algebra

section ring_algebra

-- confusion about whether these are rings or semirings should ideally be resolved
-- Is it: for D finite free R can be a semiring but for D finite it has to be a ring?
variable (R) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
variable (D : Type*) [Ring D] [Algebra R D] [Module.Finite R D]
variable [TopologicalSpace D] [IsModuleTopology R D]

open scoped TensorProduct

include R in
@[continuity, fun_prop]
theorem continuous_mul : Continuous (fun ab ↦ ab.1 * ab.2 : D × D → D) := by
  letI : TopologicalSpace (D ⊗[R] D) := moduleTopology R _
  haveI : IsModuleTopology R (D ⊗[R] D) := { eq_moduleTopology' := rfl }
  convert Module.continuous_bilinear_of_finite <| (LinearMap.mul R D : D →ₗ[R] D →ₗ[R] D)

include R in
lemma Module.topologicalRing : IsTopologicalRing D where
  continuous_add := (toContinuousAdd R D).1
  continuous_mul := continuous_mul R D
  continuous_neg := continuous_neg R D

end ring_algebra

-- two other results (not needed for FLT but would be
-- independently interesting in the theory)
section trans

variable (R S M : Type*)
  [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
  [CommRing S] [TopologicalSpace S] [IsTopologicalRing S]
    [Algebra R S] [Module.Finite R S] [IsModuleTopology R S]
  [AddCommGroup M]
    [Module R M]
    [Module S M]
      [IsScalarTower R S M]

example : moduleTopology R M = moduleTopology S M := by
  sorry

/-

Proof: First, it suffices to show that if M has the R-module topology
τRM then it's a topological S-module, and that if M has the S-module
topology τSM then it's a topological R-module. This is because the former
claim shows τSM ≤ τRM and the latter shows τRM ≤ τSM.

If M has the S-module topology then it's clearly a topological R-module,
because it's a topological S-module so (+ : M × M → M) is continuous
and (• : S × M → M) are continuous, and the map R → S is continuous
because it's R-linear and S has the R-module topology, so
R × M → S × M is continuous and thus (• : R × M → M) is continuous.

The converse is more subtle and it's here where we need some finiteness
assumptions. If M has the R-module topology then certainly (+ : M × M → M)
is continuous, so it all rests on showing that (• : S × M → M) is
continuous. But everything here is an R-module and • is R-bilinear,
and thus if either S or M are module-finite over R the result is
automatic.
-/

-- maybe
end trans

section opensubring

variable (R S : Type*)
  [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
  [CommRing S] [TopologicalSpace S] [IsTopologicalRing S]
    [Algebra R S]

example (hcont : Continuous (algebraMap R S))
    (hopen : IsOpenMap (algebraMap R S)) : IsModuleTopology R S := by
  sorry

/-
Proof.

First note that `S` is a topological ring so addition and multiplication
on `S` are continuous. Futhermore the hypothesis `Contiuous (algebraMap R S)`
shows that • : R × S → S is continuous, so S is a topological R-module.
In particular the identity map (S,R-module top) -> (S, given top) is continuous.

The algebra map from R to (S,R-module top) is R-linear
and hence also continuous. Furthermore, the composite is open
and I claim that the two topologies on S thus "look the same near 0".
More precisely, the image of R is open in S with the given topology
and hence also with the module topology (by continuity of the identity map above),
and if U ⊆ S is a subset of the image of R then we claim that it's open for
the given topology iff it's open for the module topology. Firstly,
continuity of the identity
map shows that if U is open for the given topology it's open for the module
topology. Secondly, if U is open for the module topology then its preimage
in R is open for R's topology, and then the image of this in S is open for
the given topology, and this is U again as U is a subset of the image of R.

-/
end opensubring

/-

Consequence: if one defines the finite adeles of a number field K
as K ⊗[ℤ] ℤ-hat and gives it the ℤ-hat-module topology,
this gives the right answer. Proof: algebraically we have 𝔸_K^f=𝔸_ℚ^f ⊗[ℚ] K
and 𝔸_ℚ^f=ℤhat ⊗[ℤ] ℚ, so certainly 𝔸_K^f=K ⊗[ℤ] ℤhat algebraically.
It thus suffices to show that the topologies agree. Writing R for the integers
of K we have K = K ⊗[R] R so 𝔸_K^f = ℤhat ⊗[ℤ] R ⊗[R] K = Rhat ⊗[R] K
and because Rhat is open in K with its usual topology this shows that 𝔸_K^f
has the Rhat-module topology by one of the above results. And Rhat=Zhat ⊗[ℤ] R
is finite over ℤhat so we're done if we can check that Rhat with its usual
topology is the ℤhat topology and this should be fine, it's finite and free
over a complete thing so I don't think there can be any other possibility
(the argument is weak here)
-/

@[simps!]
def continuousLinearEquiv {A B R : Type*} [TopologicalSpace A]
    [TopologicalSpace B] [TopologicalSpace R] [Semiring R] [AddCommMonoid A] [AddCommMonoid B]
    [Module R A] [Module R B] [IsModuleTopology R A] [IsModuleTopology R B]
    (e : A ≃ₗ[R] B) :
    A ≃L[R] B where
  toFun := e
  __ := e
  continuous_toFun :=
    letI := IsModuleTopology.toContinuousAdd
    IsModuleTopology.continuous_of_linearMap e.toLinearMap
  continuous_invFun :=
    letI := IsModuleTopology.toContinuousAdd
    IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap

/--
Given the following
```
e : A <–––––––––> B
     \     /\    /
      \   /  \  /
       \ /    \/
        S₁    S₂
         \   /
          \ /
           R
```
where `A` and `B` are both `S₁` and `S₂`-algebras, `S₁` and `S₂` are algebras
over a common base ring `R`, and `A` and `B` both have the `S₁`-module topology. If the algebras
form scalar towers and the algebra map from  `S₁` to `B` factors through `e`, and if `A` and `B`
are equivalent as `S₂`-algebras, then they are topologically equivalent as `S₂`-algebras as well
(even though they do not necessarily have the `S₂`-module topologies).

In application this is used for a situation where we have
```
v.Completion    L
         \    /
          \  /
           K
```
for an infinite place `v` of a number field `K`. We have an `L`-algebra equivalence
`L ⊗[K] v.Completion ≃ₐ[L] Π (w : v.ExtensionPlace L), wv.1.Completion`
between `v.Completion`-module topological spaces. And so this allows us to assert that this
is a _continuous_ `L`-algebra equivalence as well.
-/
def continuousAlgEquiv {A B : Type*} (R S₁ : Type*) {S₂ : Type*} [TopologicalSpace A] [CommRing S₁]
    [CommRing S₂] [TopologicalSpace B] [CommRing R] [CommRing A] [CommRing B] [Algebra S₁ A]
    [Algebra S₁ B] [Algebra S₂ A] [Algebra S₂ B] [IsTopologicalSemiring B]
    [TopologicalSpace S₁] [Algebra R A] [Algebra R B] [IsModuleTopology S₁ A]
    [IsModuleTopology S₁ B] [Algebra R S₁] [IsScalarTower R S₁ A] [Algebra R S₂]
    [IsScalarTower R S₂ A] [IsScalarTower R S₂ B] (e : A ≃ₐ[S₂] B)
    (he₁ : Continuous (e.toRingHom.comp (algebraMap S₁ A)))
    (he₂ : ∀ s, e (algebraMap S₁ A s) = algebraMap S₁ B s) :
    A ≃A[S₂] B where
  toAlgEquiv := e
  continuous_toFun :=
    IsModuleTopology.continuous_of_ringHom (φ := e.toRingHom) he₁
  continuous_invFun := by
    -- the inverse is continuous if `A`'s topology is coinduced by it
    convert continuous_coinduced_rng
    -- `A` has the `S₁`-module topology
    rw [eq_moduleTopology S₁ A]
    -- switch the equivalence scalars of `e` from `S₂` over to `S₁`
    have := e.changeScalars R S₁ he₂ |>.toLinearEquiv.symm.surjective
    -- then the `S₁`-module topology is coinduced by this `S₁`-algebra equivalence
    rw [ModuleTopology.eq_coinduced_of_surjective this]
    -- and the underlying functions are the same
    congr
