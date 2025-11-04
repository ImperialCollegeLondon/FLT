import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.Algebra.Algebra.Equiv
import FLT.Mathlib.Algebra.Algebra.Tower
import FLT.Deformations.ContinuousRepresentation.IsTopologicalModule
import FLT.Mathlib.Algebra.Module.Prod
import FLT.Mathlib.Topology.Constructions.SumProd

theorem ModuleTopology.isModuleTopology (R : Type*) [TopologicalSpace R] (S : Type*) [Add S]
    [SMul R S] : @IsModuleTopology R _ S _ _ (moduleTopology R S) where
  __ := moduleTopology R S
  eq_moduleTopology' := rfl

-- should be in Mathlib
lemma ModuleTopology.iff (R M : Type*) [Add M] [SMul R M] [TopologicalSpace R]
    [τ : TopologicalSpace M] : IsModuleTopology R M ↔ τ = moduleTopology R M :=
  ⟨fun m ↦ m.eq_moduleTopology', fun a ↦ { eq_moduleTopology' := a }⟩

namespace IsModuleTopology

open ModuleTopology

section semiring_bilinear

-- I need commutativity of R because we don't have bilinear maps for non-commutative rings.
-- **TODO** ask on the Zulip whether this is an issue.
variable {R : Type*} [τR : TopologicalSpace R] [CommSemiring R]

variable {A : Type*} [AddCommMonoid A] [Module R A] [aA : TopologicalSpace A] [IsModuleTopology R A]
variable {B : Type*} [AddCommMonoid B] [Module R B] [aB : TopologicalSpace B] [IsModuleTopology R B]
variable {C : Type*} [AddCommMonoid C] [Module R C] [aC : TopologicalSpace C] [IsModuleTopology R C]

theorem Module.continuous_bilinear_of_finite_free [IsTopologicalSemiring R] [Module.Finite R A]
    [Module.Free R A] (bil : A →ₗ[R] B →ₗ[R] C) :
    Continuous (fun ab ↦ bil ab.1 ab.2 : (A × B → C)) := by
  let ι := Module.Free.ChooseBasisIndex R A
  let hι : Fintype ι := Module.Free.ChooseBasisIndex.fintype R A
  let b : Module.Basis ι R A := Module.Free.chooseBasis R A
  let elinear : A ≃ₗ[R] (ι → R) := b.equivFun
  let bil' : (ι → R) →ₗ[R] B →ₗ[R] C := bil.comp elinear.symm.toLinearMap
  have := continuous_bilinear_of_pi_fintype ι bil'
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
  continuous_bilinear_of_finite_left (LinearMap.mul R D)

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
  convert continuous_bilinear_of_finite_left <| (LinearMap.mul R D : D →ₗ[R] D →ₗ[R] D)

include R in
lemma Module.topologicalRing : IsTopologicalRing D where
  continuous_add := (toContinuousAdd R D).1
  continuous_mul := continuous_mul R D
  continuous_neg := continuous_neg R D

end ring_algebra

section algebra

variable (R S : Type*)
  [CommRing R] [TopologicalSpace R]
  [CommRing S] [TopologicalSpace S] [IsTopologicalRing S] [Algebra R S]

lemma iff_Continuous_algebraMap :
    IsTopologicalModule R S ↔ Continuous (algebraMap R S) := by
  refine ⟨fun _ ↦ continuous_algebraMap R S, fun h ↦ ?_⟩
  have : Continuous (fun rs ↦ algebraMap R S rs.1 • rs.2 : R × S → S) := by fun_prop
  simp_rw [← algebra_compatible_smul S] at this
  have : ContinuousSMul R S := ⟨this⟩
  exact IsTopologicalModule.mk

end algebra

section trans

variable (R : Type*) [CommRing R] [TopologicalSpace R]

-- making this into an instance causes timeouts in the BaseChange file :-/
theorem isTopologicalModule
    (M : Type*) [AddCommGroup M] [TopologicalSpace M] [Module R M]
    [IsModuleTopology R M] : IsTopologicalModule R M where
      continuous_smul := eq_moduleTopology R M ▸ (continuousSMul R M).1
      continuous_add := eq_moduleTopology R M ▸ (continuousAdd R M).1

variable (S : Type*) [CommRing S] [TopologicalSpace S] [Algebra R S]

variable (M : Type*) [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]

lemma _root_.Algebra.moduleTopology_le [IsTopologicalModule R S] :
    moduleTopology R M ≤ moduleTopology S M := by
  letI : TopologicalSpace M := moduleTopology S M
  haveI : ContinuousAdd M := continuousAdd S M
  have ⟨cts_smul⟩ : ContinuousSMul S M := continuousSMul S M
  suffices ContinuousSMul R M from _root_.moduleTopology_le R M
  constructor
  suffices Continuous (fun rm ↦ algebraMap R S rm.1 • rm.2 : R × M → M) by
    simpa [← algebra_compatible_smul S]
  fun_prop

/-- If S is an R-algebra, finite as an R-module, with the module topology,
  then the S-module topology on an S-module coincides with the R-module topology.
-/
lemma _root_.moduleTopology.trans [IsTopologicalRing R] [Module.Finite R S] [IsModuleTopology R S] :
    moduleTopology R M = moduleTopology S M := by
  have := IsModuleTopology.isTopologicalModule
  refine le_antisymm (Algebra.moduleTopology_le _ _ _) ?_
  letI : TopologicalSpace M := moduleTopology R M
  haveI : IsModuleTopology R M := isModuleTopology R M
  haveI : ContinuousAdd M := continuousAdd R M
  have ⟨cts_smul⟩ : ContinuousSMul R M := continuousSMul R M
  suffices ContinuousSMul S M from _root_.moduleTopology_le S M
  constructor
  let bil : S →ₗ[R] M →ₗ[R] M := {
    toFun s := {
      toFun m := s • m
      map_add' := DistribSMul.smul_add s
      map_smul' := smul_comm s
    }
    map_add' s t := by
      ext m
      exact Module.add_smul s t m
    map_smul' r s := by
      ext m
      exact IsScalarTower.smul_assoc r s m
  }
  exact continuous_bilinear_of_finite_left bil

lemma trans [IsTopologicalRing R] [Module.Finite R S] [IsModuleTopology R S]
    [τ : TopologicalSpace M] :
    IsModuleTopology R M ↔ IsModuleTopology S M := by
  simp [iff R M, iff S M, moduleTopology.trans R S]

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

end opensubring

section quotientMap

variable {R M : Type*} [Ring R] [TopologicalSpace R]
  [AddCommGroup M] [Module R M] [TopologicalSpace M]
  (N : Type*) [AddCommGroup N] [Module R N] [TopologicalSpace N] [IsModuleTopology R N]

theorem of_isQuotientMap (f : N →ₗ[R] M) (h : Topology.IsQuotientMap f) : IsModuleTopology R M := by
  rw [iff, eq_coinduced_of_surjective h.surjective, h.eq_coinduced]

variable [ContinuousAdd M] [ContinuousSMul R M]

theorem of_isOpenMap_surjective (f : N →ₗ[R] M) (h : IsOpenMap f) (hsurj : Function.Surjective f)
    : IsModuleTopology R M := by
  apply of_isQuotientMap N f
  refine IsOpenQuotientMap.isQuotientMap ⟨hsurj, continuous_of_linearMap f, h⟩

theorem of_inverse (f : N →ₗ[R] M) (g : M → N) (hc : Continuous g) (hi : Function.LeftInverse f g)
    : IsModuleTopology R M := by
  apply of_isQuotientMap N f
  exact Topology.IsQuotientMap.of_inverse hc (continuous_of_linearMap f) hi

end quotientMap

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
    change Continuous (e.changeScalars R S₁ he).toLinearEquiv
    -- then this is an `S₁`-linear map on the `S₁`-module topology, so is continuous
    exact IsModuleTopology.continuous_of_linearMap _
  continuous_invFun := by
    change Continuous (e.changeScalars R S₁ he).toLinearEquiv.symm
    exact IsModuleTopology.continuous_of_linearMap _

@[simp]
theorem continuousAlgEquivOsIfScalarTower_apply {A B : Type*} (R S₁ : Type*) {S₂ : Type*}
    [TopologicalSpace A] [CommRing S₁] [CommRing S₂] [TopologicalSpace B] [CommRing R] [CommRing A]
    [CommRing B] [Algebra S₁ A] [Algebra S₁ B] [Algebra S₂ A] [Algebra S₂ B]
    [IsTopologicalSemiring B] [IsTopologicalSemiring A] [TopologicalSpace S₁] [Algebra R A]
    [Algebra R B] [IsModuleTopology S₁ A] [IsModuleTopology S₁ B] [Algebra R S₁]
    [IsScalarTower R S₁ A] [Algebra R S₂] [IsScalarTower R S₂ A] [IsScalarTower R S₂ B]
    (e : A ≃ₐ[S₂] B) (he : ∀ s, e (algebraMap S₁ A s) = algebraMap S₁ B s) (a : A) :
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
theorem t2Space (R : Type*) {M : Type*} [Semiring R] [AddCommGroup M] [Module R M] [Module.Free R M]
    [TopologicalSpace R] [TopologicalSpace M] [T2Space R]
    [ContinuousAdd R] [ContinuousMul R] [IsModuleTopology R M]
    : T2Space M := by
  have := IsModuleTopology.topologicalAddGroup R M
  rw [IsTopologicalAddGroup.t2Space_iff_zero_closed]
  let f := (Module.Free.chooseBasis R M).repr |>.toLinearMap
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
    map_eq_zero_iff f (Module.Free.chooseBasis R M).repr.injective]

/-- A vector space with the module topology over a `T2Space` ring is a `T2Space`.
-/
theorem t2Space' {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [TopologicalSpace K] [TopologicalSpace V] [T2Space K]
    [ContinuousAdd K] [ContinuousMul K] [mt : IsModuleTopology K V]
    : T2Space V := by
  apply t2Space (R := K)

section Prod

variable {A B M N : Type*} [CommRing A] [CommRing B] [AddCommGroup M] [AddCommGroup N]
  [Module A M] [Module B N]

/-- `A` can be viewed as an `(A × B)`-algebra by having `B` act trivially. -/
local instance _root_.Prod.leftAlgebra : Algebra (A × B) A :=
  RingHom.toAlgebra <| RingHom.fst A B

/-- `B` can be viewed as an `(A × B)`-algebra by having `A` act trivially. -/
local instance _root_.Prod.rightAlgebra : Algebra (A × B) B :=
  RingHom.toAlgebra <| RingHom.snd A B

/-- An `A` module can be viewed as an `(A × B)`-module by having `B` act trivially. -/
local instance _root_.Prod.leftModule : Module (A × B) M :=
  Module.compHom M (RingHom.fst A B)

/-- A `B` module can be viewed as an `(A × B)`-module by having `A` act trivially. -/
local instance _root_.Prod.rightModule : Module (A × B) N :=
  Module.compHom N (RingHom.snd A B)

/-- `A` is a finite `(A × B)`-module. -/
instance _root_.Prod.instFinite_leftAlgebra : Module.Finite (A × B) A :=
  Module.Finite.of_surjective (LinearMap.fst (A × B) A B) LinearMap.fst_surjective

/-- `B` is a finite `(A × B)`-module. -/
instance _root_.Prod.instFinite_rightAlgebra : Module.Finite (A × B) B :=
  Module.Finite.of_surjective (LinearMap.snd (A × B) A B) LinearMap.snd_surjective

variable [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace M]
  [TopologicalSpace N] [IsModuleTopology A M] [IsModuleTopology B N] [IsTopologicalRing A]
  [IsTopologicalRing B]

/-- `A` has the `(A × B)`-module topology. -/
instance Prod.instLeftAlgebra : IsModuleTopology (A × B) A :=
  of_continuous_isOpenMap_algebraMap _ _ continuous_fst isOpenMap_fst

/-- `B` has the `(A × B)`-module topology. -/
instance Prod.instRightAlgebra : IsModuleTopology (A × B) B :=
  of_continuous_isOpenMap_algebraMap _ _ continuous_snd isOpenMap_snd

/-- If `M` has the `A`-module topology, then it also has the `(A × B)`-module topology. -/
instance Prod.instLeftModule : IsModuleTopology (A × B) M := by
  have : IsScalarTower (A × B) A M := IsScalarTower.of_algebraMap_smul fun (a, b) m ↦ rfl
  rw [IsModuleTopology.trans (A × B) A M]
  infer_instance

/-- If `N` has the `B`-module topology, then it also has the `(A × B)`-module topology. -/
instance Prod.instRightModule : IsModuleTopology (A × B) N := by
  have : IsScalarTower (A × B) B N := IsScalarTower.of_algebraMap_smul fun (a, b) m ↦ rfl
  rw [IsModuleTopology.trans (A × B) B N]
  infer_instance

/-- If `M` has the `A`-module topology and `N` has the `B`-module topology
  then `M × N` has the `(A × B)`-module topology. -/
instance instProd' : IsModuleTopology (A × B) (M × N) := inferInstance

end Prod

section ModuleProd

/- This should probably replace the Prod section above ... reduces CommRing → Ring. -/

variable {R S M N : Type*} [Semiring R] [Semiring S] [TopologicalSpace R] [TopologicalSpace S]
  [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module S N]

local instance : Module (R × S) (M × N) := ModuleProd.instModuleProd

/-- Inclusion `M → M × N` by `a ↦ (a, 0)`. -/
abbrev incl1 : M → M × N :=
  fun a => (a, 0)

/-- Inclusion `N → M × N` by `a ↦ (0, a)`. -/
abbrev incl2 : N → M × N :=
  fun b => (0 , b)

lemma induced_continuous_add : @ContinuousAdd M
    (TopologicalSpace.induced (incl1) (moduleTopology (R × S) (M × N))) _ := by
  suffices h : @Continuous (M × M) (M × N) (@instTopologicalSpaceProd M M
      (TopologicalSpace.induced (incl1) (moduleTopology (R × S) (M × N)))
      (TopologicalSpace.induced (incl1) (moduleTopology (R × S) (M × N))))
      ((moduleTopology (R × S) (M × N))) (fun (a : M × M) => (a.1 + a.2, (0 : N))) by
    convert (@Topology.IsInducing.continuous_iff (M × M) M (M × N) (fun (a : M × M) ↦ a.1 + a.2)
        (incl1) (TopologicalSpace.induced (incl1) (moduleTopology (R × S) (M × N)))
        (@instTopologicalSpaceProd M M
        (TopologicalSpace.induced (incl1) (moduleTopology (R × S) (M × N)))
        (TopologicalSpace.induced (incl1) (moduleTopology (R × S) (M × N))))
        (moduleTopology (R × S) (M × N)) _).mpr h
    · constructor <;> intro h
      · exact ContinuousAdd.continuous_add
      · rw [continuous_def] at h
        use h
    · rw [@Topology.isInducing_iff]
  have h : (fun (a : M × M) => (a.1 + a.2, (0 : N))) =
      (fun (b : (M × N) × (M × N)) => (b.1.1 + b.2.1, b.1.2 + b.2.2)) ∘
      (fun (a : M × M ) => (((a.1, 0) : (M × N)) , (((a.2, 0)) : (M × N)))) := by
    ext a
    all_goals simp
  rw [h]
  refine @Continuous.comp (M × M) ((M × N) × M × N) (M × N) (@instTopologicalSpaceProd M M
    (TopologicalSpace.induced (incl1) (moduleTopology (R × S) (M × N)))
    (TopologicalSpace.induced (incl1) (moduleTopology (R × S) (M × N))))
    (@instTopologicalSpaceProd (M × N) (M × N) (moduleTopology (R × S) (M × N))
    (moduleTopology (R × S) (M × N))) (moduleTopology (R × S) (M × N))
    (f := (fun (a : M × M ) => (((a.1, 0) : (M × N)) , (((a.2, 0)) : (M × N)))))
    (g := (fun (b : (M × N) × (M × N)) => (b.1.1 + b.2.1, b.1.2 + b.2.2))) ?_ ?_
  · convert ContinuousAdd.continuous_add
    exact ModuleTopology.continuousAdd (R × S) (M × N)
  · refine @Continuous.prodMap (M × N) (M × N) M M (moduleTopology (R × S) (M × N))
      (moduleTopology (R × S) (M × N))
      (TopologicalSpace.induced (incl1) (moduleTopology (R × S) (M × N)))
      (TopologicalSpace.induced (incl1) (moduleTopology (R × S) (M × N)))
      (f := incl1) (g := incl1) ?_ ?_
    all_goals exact continuous_iff_le_induced.mpr fun U a ↦ a

lemma induced_continuous_smul : @ContinuousSMul R M _ _
    (TopologicalSpace.induced (incl1) (moduleTopology (R × S) (M × N))) := by
  suffices h : @Continuous (R × M) (M × N) (@instTopologicalSpaceProd R M _
      (TopologicalSpace.induced (incl1) (moduleTopology (R × S) (M × N))))
      ((moduleTopology (R × S) (M × N))) (fun (a : R × M) => (a.1 • a.2, (0 : N))) by
    convert (@Topology.IsInducing.continuous_iff (R × M) M (M × N) (fun (a : R × M) ↦ a.1 • a.2)
        (incl1) (TopologicalSpace.induced (incl1) (moduleTopology (R × S) (M × N)))
        (@instTopologicalSpaceProd R M _
        (TopologicalSpace.induced (incl1) (moduleTopology (R × S) (M × N))))
        (moduleTopology (R × S) (M × N)) _).mpr h
    · constructor <;> intro h
      · exact ContinuousSMul.continuous_smul
      · rw [continuous_def] at h
        use h
    · rw [@Topology.isInducing_iff]
  have : (fun (a : R × M) ↦ (a.1 • a.2, 0)) =
      (fun (c : (R × S) × (M × N)) => (c.1.1 • c.2.1, c.1.2 • c.2.2)) ∘
      (fun (b : R × M × N) => ((b.1, (0 : S)), (b.2.1, b.2.2))) ∘
      (fun (a : R × M) => (a.1, a.2, (0 : N))) := by
    ext a
    · rfl
    · simp only [Prod.mk.eta, Function.comp_apply, smul_zero]
  rw [this]
  refine @Continuous.comp (R × M) ((R × S) × M × N) (M × N) (@instTopologicalSpaceProd R M _
    (TopologicalSpace.induced (incl1) (moduleTopology (R × S) (M × N))))
    (@instTopologicalSpaceProd (R × S) (M × N) _ (moduleTopology (R × S) (M × N)))
    (moduleTopology (R × S) (M × N))
    (f := (fun (b : R × M × N) => ((b.1, (0 : S)), (b.2.1, b.2.2))) ∘
      (fun (a : R × M) => (a.1, a.2, (0 : N))))
    (g := (fun (c : (R × S) × (M × N)) => (c.1.1 • c.2.1, c.1.2 • c.2.2))) ?_ ?_
  · exact ContinuousSMul.continuous_smul
  · refine @Continuous.comp (R × M) (R × M × N) ((R × S) × M × N) (@instTopologicalSpaceProd R M _
      (TopologicalSpace.induced (incl1) (moduleTopology (R × S) (M × N))))
      (@instTopologicalSpaceProd R (M × N) _ (moduleTopology (R × S) (M × N)))
      (@instTopologicalSpaceProd (R × S) (M × N) _ (moduleTopology (R × S) (M × N)))
      (f := (fun (a : R × M) => (a.1, a.2, (0 : N))))
      (g := (fun (b : R × M × N) => ((b.1, (0 : S)), (b.2.1, b.2.2)))) ?_ ?_
    · simp only [Prod.mk.eta, continuous_prodMk]
      · constructor
        · constructor
          · exact @continuous_fst R (M × N) _ (moduleTopology (R × S) (M × N))
          · rw [continuous_def] --is there a better way?
            intro s hs
            have : ((fun (x : R × M × N) ↦ 0) ⁻¹' s) = ∅ ∨
                ((fun (x : R × M × N) ↦ 0) ⁻¹' s = Set.univ) := by
              rcases (Classical.em (0 ∈ s)) with h | h
              all_goals aesop
            aesop
        · exact @continuous_snd R (M × N) _ (moduleTopology (R × S) (M × N))
    · simp only [continuous_prodMk]
      constructor
      · exact @continuous_fst R M _
          (TopologicalSpace.induced (incl1) (moduleTopology (R × S) (M × N)))
      · refine @Continuous.comp (R × M) M (M × N) (@instTopologicalSpaceProd R M _
          (TopologicalSpace.induced (incl1) (moduleTopology (R × S) (M × N))))
          (TopologicalSpace.induced (incl1) (moduleTopology (R × S) (M × N)))
          (moduleTopology (R × S) (M × N))
          (f := fun (a : R × M) => a.2) (g := incl1)  ?_ ?_
        · exact continuous_iff_le_induced.mpr fun U a ↦ a
        · exact @continuous_snd R M _
            (TopologicalSpace.induced (incl1) (moduleTopology (R × S) (M × N)))

lemma continuous_incl1 : @Continuous M (M × N) (moduleTopology R M) (moduleTopology (R × S) (M × N))
    (incl1) := by
  refine continuous_iff_le_induced.mpr ?_
  refine sInf_le ?_
  constructor
  · exact induced_continuous_smul
  · exact induced_continuous_add

lemma induced_continuous_add' : @ContinuousAdd N
    (TopologicalSpace.induced (incl2) (moduleTopology (R × S) (M × N))) _ := by
  suffices h : @Continuous (N × N) (M × N) (@instTopologicalSpaceProd N N
      (TopologicalSpace.induced (incl2) (moduleTopology (R × S) (M × N)))
      (TopologicalSpace.induced (incl2) (moduleTopology (R × S) (M × N))))
      ((moduleTopology (R × S) (M × N))) (fun (a : N × N) => ((0 : M), a.1 + a.2)) by
    convert (@Topology.IsInducing.continuous_iff (N × N) N (M × N) (fun (a : N × N) ↦ a.1 + a.2)
        (incl2) (TopologicalSpace.induced (incl2) (moduleTopology (R × S) (M × N)))
        (@instTopologicalSpaceProd N N
        (TopologicalSpace.induced (incl2) (moduleTopology (R × S) (M × N)))
        (TopologicalSpace.induced (incl2) (moduleTopology (R × S) (M × N))))
        (moduleTopology (R × S) (M × N)) _).mpr h
    · constructor <;> intro h
      · exact ContinuousAdd.continuous_add
      · rw [continuous_def] at h
        use h
    · rw [@Topology.isInducing_iff]
  have h : (fun (a : N × N) => ((0 : M), a.1 + a.2)) =
      (fun (b : (M × N) × (M × N)) => (b.1.1 + b.2.1, b.1.2 + b.2.2)) ∘
      (fun (a : N × N ) => (((0, a.1) : (M × N)) , (((0, a.2)) : (M × N)))) := by
    ext a
    all_goals simp
  rw [h]
  refine @Continuous.comp (N × N) ((M × N) × M × N) (M × N) (@instTopologicalSpaceProd N N
    (TopologicalSpace.induced (incl2) (moduleTopology (R × S) (M × N)))
    (TopologicalSpace.induced (incl2) (moduleTopology (R × S) (M × N))))
    (@instTopologicalSpaceProd (M × N) (M × N) (moduleTopology (R × S) (M × N))
    (moduleTopology (R × S) (M × N))) (moduleTopology (R × S) (M × N))
    (f := (fun (a : N × N ) => (((0, a.1) : (M × N)) , (((0, a.2)) : (M × N)))))
    (g := (fun (b : (M × N) × (M × N)) => (b.1.1 + b.2.1, b.1.2 + b.2.2))) ?_ ?_
  · convert ContinuousAdd.continuous_add
    exact ModuleTopology.continuousAdd (R × S) (M × N)
  · refine @Continuous.prodMap (M × N) (M × N) N N (moduleTopology (R × S) (M × N))
      (moduleTopology (R × S) (M × N))
      (TopologicalSpace.induced (incl2) (moduleTopology (R × S) (M × N)))
      (TopologicalSpace.induced (incl2) (moduleTopology (R × S) (M × N)))
      (f := incl2) (g := incl2) ?_ ?_
    all_goals exact continuous_iff_le_induced.mpr fun U a ↦ a

lemma induced_continuous_smul' : @ContinuousSMul S N _ _
    (TopologicalSpace.induced (incl2) (moduleTopology (R × S) (M × N))) := by
  suffices h : @Continuous (S × N) (M × N) (@instTopologicalSpaceProd S N _
      (TopologicalSpace.induced (incl2) (moduleTopology (R × S) (M × N))))
      ((moduleTopology (R × S) (M × N))) (fun (a : S × N) => ((0 : M), a.1 • a.2)) by
    convert (@Topology.IsInducing.continuous_iff (S × N) N (M × N) (fun (a : S × N) ↦ a.1 • a.2)
        (incl2) (TopologicalSpace.induced (incl2) (moduleTopology (R × S) (M × N)))
        (@instTopologicalSpaceProd S N _
        (TopologicalSpace.induced (incl2) (moduleTopology (R × S) (M × N))))
        (moduleTopology (R × S) (M × N)) _).mpr h
    · constructor <;> intro h
      · exact ContinuousSMul.continuous_smul
      · rw [continuous_def] at h
        use h
    · rw [@Topology.isInducing_iff]
  have : (fun (a : S × N) ↦ (0, a.1 • a.2)) =
      (fun (c : (R × S) × (M × N)) => (c.1.1 • c.2.1, c.1.2 • c.2.2)) ∘
      (fun (b : S × M × N) => (((0 : R), b.1), (b.2.1, b.2.2))) ∘
      (fun (a : S × N) => (a.1, (0 : M), a.2)) := by
    ext a
    · aesop
    · simp only [Prod.mk.eta, Function.comp_apply, smul_zero]
  rw [this]
  refine @Continuous.comp (S × N) ((R × S) × M × N) (M × N) (@instTopologicalSpaceProd S N _
    (TopologicalSpace.induced (incl2) (moduleTopology (R × S) (M × N))))
    (@instTopologicalSpaceProd (R × S) (M × N) _ (moduleTopology (R × S) (M × N)))
    (moduleTopology (R × S) (M × N))
    (f := (fun (b : S × M × N) => (((0 : R), b.1), (b.2.1, b.2.2))) ∘
      (fun (a : S × N) => (a.1, (0 : M), a.2)))
    (g := (fun (c : (R × S) × (M × N)) => (c.1.1 • c.2.1, c.1.2 • c.2.2))) ?_ ?_
  · exact ContinuousSMul.continuous_smul
  · refine @Continuous.comp (S × N) (S × M × N) ((R × S) × M × N) (@instTopologicalSpaceProd S N _
      (TopologicalSpace.induced (incl2) (moduleTopology (R × S) (M × N))))
      (@instTopologicalSpaceProd S (M × N) _ (moduleTopology (R × S) (M × N)))
      (@instTopologicalSpaceProd (R × S) (M × N) _ (moduleTopology (R × S) (M × N)))
      (f := (fun (a : S × N) => (a.1, (0 : M), a.2)))
      (g := (fun (b : S × M × N) => (((0 : R), b.1), (b.2.1, b.2.2)))) ?_ ?_
    · simp only [Prod.mk.eta, continuous_prodMk]
      · constructor
        · constructor
          · rw [continuous_def]
            intro s hs
            have : ((fun (x : S × M × N) ↦ 0) ⁻¹' s) = ∅ ∨
                ((fun (x : S × M × N) ↦ 0) ⁻¹' s = Set.univ) := by
              rcases (Classical.em (0 ∈ s)) with h | h
              all_goals aesop
            aesop
          · exact @continuous_fst S (M × N) _ (moduleTopology (R × S) (M × N))
        · exact @continuous_snd S (M × N) _ (moduleTopology (R × S) (M × N))
    · simp only [continuous_prodMk]
      constructor
      · exact @continuous_fst S N _
          (TopologicalSpace.induced (incl2) (moduleTopology (R × S) (M × N)))
      · refine @Continuous.comp (S × N) N (M × N) (@instTopologicalSpaceProd S N _
          (TopologicalSpace.induced (incl2) (moduleTopology (R × S) (M × N))))
          (TopologicalSpace.induced (incl2) (moduleTopology (R × S) (M × N)))
          (moduleTopology (R × S) (M × N))
          (f := fun (a : S × N) => a.2) (g := incl2)  ?_ ?_
        · exact continuous_iff_le_induced.mpr fun U a ↦ a
        · exact @continuous_snd S N _
            (TopologicalSpace.induced (incl2) (moduleTopology (R × S) (M × N)))

lemma continuous_incl2 : @Continuous N (M × N) (moduleTopology S N) (moduleTopology (R × S) (M × N))
    (incl2) := by
  refine continuous_iff_le_induced.mpr ?_
  refine sInf_le ?_
  constructor
  · exact induced_continuous_smul'
  · exact induced_continuous_add'

lemma id_eq : @id (M × N) = ((incl1) ∘ (Prod.fst)) + ((incl2) ∘ (Prod.snd)) := by
  ext a
  all_goals simp

variable [TopologicalSpace M] [TopologicalSpace N] [IsModuleTopology R M] [IsModuleTopology S N]

lemma continuous_smul : ContinuousSMul (R × S) (M × N) where
  continuous_smul := by
    have : (fun p ↦ p.1 • p.2 : (R × S) × M × N → M × N) =
        (ModuleProd.smul) ∘ (Equiv.prodProdProdComm R S M N) := by
      ext a
      all_goals simp only [Function.comp_apply, ModuleProd.smul]
      all_goals rfl
    rw [this]
    refine Continuous.comp ?_ (continuous_prodProdProdComm R S M N)
    · apply Continuous.prodMap
      all_goals exact ContinuousSMul.continuous_smul

/-- If `M` has the `A`-module topology and `N` has the `B`-module topology
  then `M × N` has the `(A × B)`-module topology. -/
instance instProd'' : IsModuleTopology (R × S) (M × N) := by
  haveI : ContinuousAdd M := IsModuleTopology.toContinuousAdd R M
  haveI : ContinuousAdd N := IsModuleTopology.toContinuousAdd S N
  have h2 := continuous_smul (R := R) (S := S) (M := M) (N := N)
  refine IsModuleTopology.of_continuous_id ?_
  rw [id_eq]
  have a : @Continuous (M × N) (M × N) instTopologicalSpaceProd
      (moduleTopology (R × S) (M × N)) ((incl1) ∘ (Prod.fst)) := by
    refine @Continuous.comp (M × N) M (M × N) instTopologicalSpaceProd (moduleTopology R M)
      (moduleTopology (R × S) (M × N)) (Prod.fst) (incl1) ?_ ?_
    · exact continuous_incl1
    · convert @continuous_fst M N (moduleTopology R M) (moduleTopology S N)
      all_goals exact IsModuleTopology.eq_moduleTopology' -- maybe I need to be synthesising better?
  have b : @Continuous (M × N) (M × N) instTopologicalSpaceProd
      (moduleTopology (R × S) (M × N)) ((incl2) ∘ (Prod.snd)) := by
    refine @Continuous.comp (M × N) N (M × N) instTopologicalSpaceProd (moduleTopology S N)
      (moduleTopology (R × S) (M × N)) (Prod.snd) (incl2) ?_ ?_
    · exact continuous_incl2
    · convert @continuous_snd M N (moduleTopology R M) (moduleTopology S N)
      all_goals exact IsModuleTopology.eq_moduleTopology'
  exact @Continuous.add _ (moduleTopology (R × S) (M × N)) _
    (ModuleTopology.continuousAdd (R × S) (M × N)) _ _ _ _  a b


end ModuleProd

section locally_compact

variable (R : Type*) [τR : TopologicalSpace R] [Ring R] [IsTopologicalRing R]
variable {M : Type*} [AddCommGroup M] [Module R M] [TopologicalSpace M] [IsModuleTopology R M]

-- can't be an instance because typeclass inference can't find `R`
theorem locallyCompactSpaceOfFinite [LocallyCompactSpace R] [Module.Finite R M] :
    LocallyCompactSpace M := by
  -- M is generated by image of φ : Fin n → M
  obtain ⟨n, φ, h⟩ := Module.Finite.exists_fin (R := R) (M := M)
  -- so M is locally compact because it's the image of R^n under a map
  exact IsOpenQuotientMap.locallyCompactSpace <|
    -- which is an open quotient map because it's a quotient map between additive groups
    AddMonoidHom.isOpenQuotientMap_of_isQuotientMap <|
    -- and it's a quotient map because it's surjective and everything has the module topology
    isQuotientMap_of_surjective <|
    LinearMap.range_eq_top.mp <|
    h ▸ Fintype.range_linearCombination R φ

end locally_compact

end IsModuleTopology
