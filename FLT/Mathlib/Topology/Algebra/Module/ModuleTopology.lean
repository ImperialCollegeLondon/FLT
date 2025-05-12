import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.Algebra.Algebra.Equiv
import Mathlib.Topology.Algebra.Algebra.Equiv
import FLT.Mathlib.Algebra.Module.LinearMap.Defs
import FLT.Mathlib.Algebra.Algebra.Tower

theorem ModuleTopology.isModuleTopology (R : Type*) [TopologicalSpace R] (S : Type*) [Add S]
    [SMul R S] : @IsModuleTopology R _ S _ _ (moduleTopology R S) where
  __ := moduleTopology R S
  eq_moduleTopology' := rfl

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
    (D : Type*) [Ring D] [Algebra R D] [Module.Finite R D] [TopologicalSpace D]
    [IsModuleTopology R D] : Continuous (fun ab ↦ ab.1 * ab.2 : D × D → D) :=
  Module.continuous_bilinear_of_finite (LinearMap.mul R D)

include R in
lemma topologicalSemiring : IsTopologicalSemiring D where
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

-- Proved this thinking I could use it to prove `IsModuleTopology K_∞ L_∞`,
-- which application failed, but may as well keep this proof
open scoped Topology in
/-- An `R`-algebra `S` has the `R`-module topology if the embedding `R →+* S` is continuous
and open. -/
theorem of_continuous_isOpenMap_algebraMap (hcont : Continuous (algebraMap R S))
    (hopen : IsOpenMap (algebraMap R S)) : IsModuleTopology R S where
  eq_moduleTopology' := by
    -- Let `τS` denote the topology on `S`, `τRS` denote the `R`-module topology on `S`,
    -- `τR` denote the topology on `R`.. This proof consists of pushing fowards and pulling
    -- back open sets between three topological spaces as follows:
    -- ```
    -- (S, τRS) <-[hcont_id]- (S, τS)
    --       |                 ↗
    -- [hcont_alg]      [hopen]
    --       |          /
    --       |        /
    --       |   [hcont]
    --       ↓   ↙
    --     (R, τR)
    -- ```
    -- where the arrows indicate the direction in which open sets are moved, `hopen` and `hcont`
    -- are given hypotheses, and `hcont_id` and `hcont_alg` are the continuity of the identity map
    -- and the algebra map respectively, which are proved below.
    -- • : R × S → S is continuous
    have : ContinuousSMul R S := continuousSMul_of_algebraMap R S hcont
    -- The identity map `(S, τRS) → (S, τS)` is continuous, by minimality of module topology.
    have hcont_id : Continuous[moduleTopology R S, _] id :=
      continuous_id_iff_le.2 <| moduleTopology_le _ _
    -- The algebra map `(R, τR) →ₗ[R] (S, τRS)` from `R` is continuous, since `τR` is the
    -- `R`-module topology on `R`, and any `R`-linear map on this domain is continuous.
    have hcont_alg : Continuous[_, moduleTopology R S] (Algebra.linearMap R S) :=
      -- Give `S` the `R`-module topology
      letI := moduleTopology R S
      letI : ContinuousAdd S := ModuleTopology.continuousAdd _ _
      letI : ContinuousSMul R S := ModuleTopology.continuousSMul _ _
      IsModuleTopology.continuous_of_linearMap _
    -- If `U` is open in `(S, τS)`, then it is open in `(S, τRS)` by pullback along [hcont_id].
    have hopen_mpr {U : Set S} (h : IsOpen U) : IsOpen[moduleTopology R S] U :=
      @Continuous.isOpen_preimage S S (moduleTopology R S) _ id hcont_id U h
    -- If `U` is open in `(S, τRS)` and is contained in the image of `R` inside `S`, then it is
    -- open in `(S, τS)`, by pullback along [hcont_alg] and push forward along [hopen].
    have hopen_mp {U : Set S} (h : IsOpen[moduleTopology R S] U)
        (hUS : U ⊆ Set.range (algebraMap R S)) : IsOpen U :=
      Set.image_preimage_eq_of_subset hUS ▸ hopen _ <|
        @Continuous.isOpen_preimage R S _ (moduleTopology R S) _ hcont_alg U h
    -- To finish the proof, we now show that the neighbourhoods of zero in `τS` and `τ_R_S` coincide
    rw [IsTopologicalRing.to_topologicalAddGroup.ext_iff <|
      -- `(S, τRS)` is a topological add group
      @IsModuleTopology.topologicalAddGroup R _ _ S _ _ (moduleTopology R S) (isModuleTopology R S)]
    -- It is enough to show that the basis of neighbourhoods of zero are contained within each other
    apply (nhds_basis_opens 0).ext (@nhds_basis_opens S (moduleTopology R S) 0)
    · -- Assume `U` is open in `(S, τS)`, then it is open in `(S, τRS)` by `hopen_mpr` above.
      exact fun U hU => ⟨U, ⟨⟨hU.1, hopen_mpr hU.2⟩, by simp⟩⟩
    · -- Assume `U` is open in `(S, τRS)`
      intro U hU
      -- Intersect `U` with the image of `R` in `(S, τRS)`.
      refine ⟨Set.range (algebraMap R S) ∩ U, ⟨⟨⟨⟨0, by simp⟩, hU.1⟩, ?_⟩, by simp⟩⟩
      -- `Set.range (algebraMap R S)` is open in `(S, τS)` by hopen, so too in `(S, τRS)`
      -- by hopen_mpr.
      let hopen_range := hopen_mpr hopen.isOpen_range
      -- Therefore `U ∩ Set.range (algebraMap R S)` is open in `(S, τRS)`, so too in `(S, τS)`
      -- by hopen_mp.
      exact hopen_mp (@IsOpen.inter _ (moduleTopology R S) _ _ hopen_range hU.2) (by simp)

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

/-- Given a linear isomorphism between two topological modules with the module topology,
upgrades it to a continuous linear isomorphism using the fact that linear maps between modules
with the module topology are automatically continuous. -/
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
`L ⊗[K] v.Completion ≃ₐ[L] Π (w : v.Extension L), wv.1.Completion`
between `v.Completion`-module topological spaces. And so this allows us to assert that this
is a _continuous_ `L`-algebra equivalence as well.
-/
def continuousAlgEquivOfIsScalarTower {A B : Type*} (R S₁ : Type*) {S₂ : Type*} [TopologicalSpace A]
    [CommRing S₁] [CommRing S₂] [TopologicalSpace B] [CommRing R] [CommRing A] [CommRing B]
    [Algebra S₁ A] [Algebra S₁ B] [Algebra S₂ A] [Algebra S₂ B] [IsTopologicalSemiring B]
    [IsTopologicalSemiring A] [TopologicalSpace S₁] [Algebra R A] [Algebra R B]
    [IsModuleTopology S₁ A] [IsModuleTopology S₁ B] [Algebra R S₁] [IsScalarTower R S₁ A]
    [Algebra R S₂] [IsScalarTower R S₂ A] [IsScalarTower R S₂ B] (e : A ≃ₐ[S₂] B)
    (he : ∀ s, e (algebraMap S₁ A s) = algebraMap S₁ B s) :
    A ≃A[S₂] B where
  toAlgEquiv := e
  continuous_toFun := by
    -- switch the equivalence scalars of `e` from `S₂` over to `S₁`
    show Continuous (e.changeScalars R S₁ he).toLinearEquiv
    -- then this is an `S₁`-linear map on the `S₁`-module topology, so is continuous
    exact IsModuleTopology.continuous_of_linearMap _
  continuous_invFun := by
    show Continuous (e.changeScalars R S₁ he).toLinearEquiv.symm
    exact IsModuleTopology.continuous_of_linearMap _

@[simp]
theorem continuousAlgEquivOsIfScalarTower_apply {A B : Type*} (R S₁ : Type*) {S₂ : Type*}
    [TopologicalSpace A] [CommRing S₁] [CommRing S₂] [TopologicalSpace B] [CommRing R] [CommRing A]
    [CommRing B] [Algebra S₁ A] [Algebra S₁ B] [Algebra S₂ A] [Algebra S₂ B]
    [IsTopologicalSemiring B] [IsTopologicalSemiring A] [TopologicalSpace S₁] [Algebra R A]
    [Algebra R B] [IsModuleTopology S₁ A] [IsModuleTopology S₁ B] [Algebra R S₁]
    [IsScalarTower R S₁ A] [Algebra R S₂] [IsScalarTower R S₂ A] [IsScalarTower R S₂ B]
    (e : A ≃ₐ[S₂] B) (he: ∀ s, e (algebraMap S₁ A s) = algebraMap S₁ B s) (a : A) :
    continuousAlgEquivOfIsScalarTower R S₁ e he a = e a :=
  rfl

/-- An algebra isomorphism between two topological algebras over `R` with the
`R`-module topology is automatically an algebra homeomorphism. -/
def continuousAlgEquivOfAlgEquiv {A B R : Type*} [TopologicalSpace A]
    [TopologicalSpace B] [TopologicalSpace R] [CommSemiring R] [Semiring A] [Semiring B]
    [Algebra R A] [Algebra R B] [IsModuleTopology R A] [IsModuleTopology R B]
    (e : A ≃ₐ[R] B) :
    A ≃A[R] B where
  __ := e
  continuous_toFun :=
    letI := IsModuleTopology.toContinuousAdd
    IsModuleTopology.continuous_of_linearMap e.toLinearMap
  continuous_invFun :=
    letI := IsModuleTopology.toContinuousAdd
    IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap

/-- A free module with the module topology over a `T2Space` ring is a `T2Space`.
-/
theorem t2Space {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] [Module.Free R M]
    [TopologicalSpace R] [TopologicalSpace M] [T2Space R]
    [ContinuousAdd R] [ContinuousMul R] [IsModuleTopology R M]
    : T2Space M := by
  have := IsModuleTopology.topologicalAddGroup R M
  rw [IsTopologicalAddGroup.t2Space_iff_zero_closed]
  let f := Module.Free.repr R M |>.toLinearMap
  let g : (Module.Free.ChooseBasisIndex R M →₀ R) →ₗ[R] (Module.Free.ChooseBasisIndex R M → R) := {
    __ := Finsupp.coeFnAddHom
    map_smul' _ _ := rfl
  }
  suffices hpre : (g.comp f) ⁻¹' {0} = {0}  by
    rw [← hpre]
    apply IsClosed.preimage <| IsModuleTopology.continuous_of_linearMap (g.comp f)
    exact isClosed_singleton
  ext x
  simp [map_eq_zero_iff g DFunLike.coe_injective,
    map_eq_zero_iff f (Module.Free.repr R M).injective]

/-- A vector space with the module topology over a `T2Space` ring is a `T2Space`.
-/
theorem t2Space' {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [TopologicalSpace K] [TopologicalSpace V] [T2Space K]
    [ContinuousAdd K] [ContinuousMul K] [mt : IsModuleTopology K V]
    : T2Space V := by
  apply t2Space (R := K)
