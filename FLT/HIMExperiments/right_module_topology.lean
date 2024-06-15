import Mathlib.RingTheory.TensorProduct.Basic -- we need tensor products of rings at some point
import Mathlib.Topology.Algebra.Module.Basic -- and we need topological rings and modules
import Mathlib.Tactic

/-

# A "module topology" for a module over a topological ring.

Let `A` denote a topological ring.

If `M` is an `A`-module, then we can let `M` inherit a topology from `A`, namely
the finest topology which makes all the `A`-linear maps `A →ₗ[A] M` continuous.

## Constructions on modules.

This module-topology may or may not have the following cool properties:

1) Any `A`-linear map `φ : M →ₗ[A] N` is continuous.
2) The `A`-module topology on `Unit` is the topology already present on `Unit`.
3) The `A`-module topology on `A` is `A`s original topology.
4) The `A`-module topology on a product `M × N` of two modules-with-module-topology is
   the product topology.
5) The `A`-module topology on a power `M^n`, that is, `n → M` with `n : Type`, is the
(now possibly infinite) product topology.

6) Now say `A` is commutative. Then the tensor product of two `A`-modules is an `A`-module,
and so we can ask if the canonical bilinear map from `M × N` (with the module or product topology?
probably they're the same) to `M ⊗[A] N` is continuous.

7) Commutativity of `A` also gives spaces of `A`-linear maps the structure of `A`-modules,
so we can ask for example whether the function application map `M × (M →ₗ[A] N) → N` is continuous.

8) We could also ask whether the evaluation map, from `M →ₗ[A] N` to the power space `N^M` of bare
functions from `M` (now considered only as an index set, so with no topology) to `N` is continuous.

-/

-- Let A be a ring, with a compatible topology.
variable (A : Type*) [CommRing A] [TopologicalSpace A] [TopologicalRing A]


/-- The "right topology" on a module `M` over a topological ring `A`. It's defined as
the finest topology on `M` which makes every `A`-linear map `A → M` continuous. It's called
the "right topology" because `M` goes on the right.  -/
abbrev Module.rtopology (M : Type*) [AddCommGroup M] [Module A M]: TopologicalSpace M :=
-- Topology defined as LUB of pushforward.
  ⨆ (f : A →ₗ[A] M), TopologicalSpace.coinduced f inferInstance

-- let `M` and `N` be `A`-modules
variable (M : Type*) [AddCommGroup M] [Module A M]
variable {N : Type*} [AddCommGroup N] [Module A N]

/-- Every `A`-linear map between two `A`-modules with the canonical topology is continuous. -/
lemma Module.continuous_linear (e : M →ₗ[A] N) :
    @Continuous M N (Module.rtopology A M) (Module.rtopology A N) e := by
  sorry -- maybe some appropriate analogue of Hannah/Lugwig's proof will work?

-- A formal corollary should be that
def Module.homeomorphism_equiv (e : M ≃ₗ[A] N) :
    -- lean needs to be told the topologies explicitly in the statement
    let τM := Module.rtopology A M
    let τN := Module.rtopology A N
    M ≃ₜ N :=
  -- And also at the point where lean puts the structure together, unfortunately
  let τM := Module.rtopology A M
  let τN := Module.rtopology A N
  -- all the sorries should be formal.
  { toFun := e
    invFun := e.symm
    left_inv := sorry
    right_inv := sorry
    continuous_toFun := sorry
    continuous_invFun := sorry
  }

-- Claim: topology on A doesn't change
example : (inferInstance : TopologicalSpace A) = Module.rtopology A A := by
  sorry

-- claim: topology on the 1-point set is the canonical one
example : (inferInstance : TopologicalSpace Unit) = Module.rtopology A Unit := by
  sorry

example :
  let _τM : TopologicalSpace M := Module.rtopology A M
  let _τN : TopologicalSpace N := Module.rtopology A N
  (inferInstance : TopologicalSpace (M × N)) = Module.rtopology A (M × N) := by sorry

example :
  let _τM : TopologicalSpace M := Module.rtopology A M
  let _τN : TopologicalSpace N := Module.rtopology A N
  (inferInstance : TopologicalSpace (M × N)) = Module.rtopology A (M × N) := by sorry

#exit

-- -- sanity check: the topology on A^n is the product topology
-- example (ι : Type*) [Finite ι] :
--     (Pi.topologicalSpace : TopologicalSpace (ι → A)) = Module.topology2 A := by
--   -- suffices to prove that each topology is ≤ the other one
--   apply le_antisymm
--   · -- you're ≤ `iInf S` iff you're ≤ all elements of `S`
--     apply le_iInf
--     -- so take an element of `S`, the topology induced by `b : (ι → A) → A`
--     intro b
--     -- and we've got to prove that the product topology is `≤` it, which is the
--     -- same as saying that `b` is continuous with the product topology on `A^ι`
--     rw [← continuous_iff_le_induced]
--     -- and we've already proved that all linear maps are continuous.
--     apply LinearMap.continuous_on_pi b
--   · -- the set Inf application works better here for some reason
--     -- We've got to prove the module topology is ≤ the product topology, which is defined here to
--     -- be the coarsest topology making all the projection maps continuous
--     -- So it suffices to prove that all projections are linear
--     apply sSup_le
--     -- so let's look at the i'th projection
--     rintro _ ⟨φ, rfl⟩
--     dsimp
--     apply le_iInf
--     intro i
--     rw [← continuous_iff_coinduced_le]
--     rw [continuous_iff_le_induced]
--     rw [induced_compose]
--     simp
--     rw [← continuous_iff_le_induced]
    -- -- it's linear, because Lean has the projections as linear maps.
    -- exact ⟨LinearMap.proj i, rfl⟩

lemma ext (φ : A →ₗ[A] M) : ⇑φ = fun a ↦ a • φ 1 := by
  ext a
  rw [← map_smul, smul_eq_mul, mul_one]

lemma foo {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (f : X → Y × Z) (h1 : Continuous (Prod.fst ∘ f)) (h2 : Continuous (Prod.snd ∘ f)) :
    Continuous f := continuous_prod_mk.2 ⟨h1, h2⟩

variable {A} in
lemma bar (φ : A →ₗ[A] M) : @Continuous A M _ (Module.topology2 A M) φ := by
  rw [continuous_iff_coinduced_le]
  apply le_sSup
  use φ

-- We need that the module topology on a product is the product topology
lemma Module.prod_canonical :
    @instTopologicalSpaceProd M N (Module.topology2 A M) (Module.topology2 A N) =
    (Module.topology2 A (M × N)) := by
  -- the goal is to prove that an iSup equals an inf (of two topologies).
  --unfold instTopologicalSpaceProd -- you can probably delete this later
  apply le_antisymm
  · refine le_trans inf_le_left ?_
    apply le_sSup
    sorry
  · apply sSup_le
    rintro - ⟨φ, rfl⟩
    dsimp
    rw [← continuous_iff_coinduced_le]
    let τM := Module.topology2 A M
    let τN := Module.topology2 A N
    apply foo
    · apply bar (LinearMap.fst _ _ _ ∘ₗ φ)
    · apply bar (LinearMap.snd _ _ _ ∘ₗ φ)

-- Maybe we need something being Module.Finite or Module.Free here?
lemma Module.continuous_bilinear {P : Type*} [AddCommGroup P] [Module A P]
    (b : M →ₗ[A] N →ₗ[A] P) :
    @Continuous (M × N) P (Module.topology2 A (M × N)) (Module.topology2 A P)
    (fun mn ↦ b mn.1 mn.2) := by
  sorry

-- Linear maps are automatically continuous, so let's make a couple of handy ones:
-- they're probably there already but I couldn't find them
/-- Negation on a module as a linear map. -/
noncomputable def LinearMap.neg (M : Type*) [AddCommGroup M] [Module A M] :
    M →ₗ[A] M where
  toFun := (- .)
  map_add' := neg_add
  map_smul' r m := (smul_neg r m).symm

/-- Addition on a module as a linear map from `M²` to `M`. -/
noncomputable def LinearMap.add (M : Type*) [AddCommGroup M] [Module A M] :
    M × M →ₗ[A] M where
  toFun mn := mn.1 + mn.2
  map_add' _ _ := add_add_add_comm _ _ _ _
  map_smul' _ _ := (DistribSMul.smul_add _ _ _).symm

-- Note that we have multiplication as a bilinear map.

-- Now say we have a non-commutative `A`-algebra `D` which is free of finite type.

variable (D : Type*) [Ring D] [Algebra A D] [Module.Finite A D] [Module.Free A D]

-- Let's put the module topology on `D`
def D_topology : TopologicalSpace D := Module.topology2 A D

instance moobar : @TopologicalRing D (Module.topology2 A D) _ :=
  let _ : TopologicalSpace D := Module.topology2 A D
  { -- first we prove that addition is continuous
    continuous_add := by
      -- the product topology is the module topology
      rw [Module.prod_canonical A]
      -- and addition is linear so it's continuous for the module topology
      exact Module.continuous_linear A (LinearMap.add A D)
    -- multiplication is continuous:
    continuous_mul := by
      -- the product topology is the module topology
      rw [Module.prod_canonical A]
      -- and multiplication is bilinear so it's continuous for the module topology (I hope)
      apply Module.continuous_bilinear A (LinearMap.mul A D)
    -- finally negation is continuous because it's linear.
    continuous_neg := Module.continuous_linear A (LinearMap.neg _ _) }
