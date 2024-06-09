import Mathlib.RingTheory.TensorProduct.Basic -- we need tensor products of rings at some point
import Mathlib.Topology.Algebra.Module.Basic -- and we need topological rings and modules

/-

# The "module topology" for a module over a topological ring.

Let `A` denote a topological ring.

If `M` is an `A`-module, then `M` seems to inherit a topology from `A`, which we call the
"module topology" until someone tells me its proper name. It's the coarsest topology
making all the `A`-linear maps `M →ₗ[A] A` continuous.

This topology has the following cool properties:

1) Any `A`-linear map `φ : M →ₗ[A] N` is continuous for the module topologies on source
and target.

2)

-/

-- This was an early theorem I proved when I didn't know what was true or not, and
-- was just experimenting.

-- theorem LinearMap.continuous_on_prod {ι κ : Type*} {R : Type*} {M : Type*}
--     [Finite ι] [Finite κ] [CommSemiring R] [TopologicalSpace R] [TopologicalSemiring R]
--     [AddCommMonoid M] [Module R M]
--     [TopologicalSpace M] [ContinuousAdd M] [ContinuousSMul R M]
--     (f : (ι → R) →ₗ[R] (κ → R) →ₗ[R] M) :
--     Continuous (fun xy ↦ f xy.1 xy.2 : (ι → R) × (κ → R) → M) := by
--   cases nonempty_fintype (ι × κ)
--   cases nonempty_fintype κ
--   cases nonempty_fintype ι
--   classical
--   have foo : (fun xy ↦ f xy.1 xy.2 : (ι → R) × (κ → R) → M) =
--       fun xy ↦ ∑ ik : ι × κ, ((xy.1 ik.1) * (xy.2 ik.2)) •
--         f (fun i ↦ if i = ik.1 then 1 else 0) (fun k ↦ if k = ik.2 then 1 else 0) := by
--     ext ⟨x, y⟩
--     simp only [pi_apply_eq_sum_univ (f x) y]
--     -- `rw [Fintype.sum_prod_type_right]` doesn't work and I don't know why
--     -- `rw [@Fintype.sum_prod_type_right _ ι κ ‹_› ‹_› _ _]` also doesn't work and I don't know why
--     -- annoying workaround
--     symm
--     convert @Fintype.sum_prod_type_right _ ι κ ‹_› ‹_› _ _
--     simp only [pi_apply_eq_sum_univ f x, mul_comm (x _), mul_smul, ← Finset.smul_sum, Eq.comm]
--     congr
--     apply sum_apply
--   rw [foo]
--   refine continuous_finset_sum _ fun i _ => Continuous.smul ?_ continuous_const
--   refine Continuous.mul (Continuous.comp (continuous_apply _) (continuous_fst)) ?_
--   exact (Continuous.comp (continuous_apply _) (continuous_snd))

variable (A : Type*) [CommRing A] [TopologicalSpace A] [TopologicalRing A]

-- let M be an A-module
variable {M : Type*} [AddCommGroup M] [Module A M]

-- Here is a conceptual way to put a topology on `M`. Let's define it to be
-- the coarsest topology such that all `A`-linear maps from `M` to `A` are continuous
-- (recall that `A` already has a topology). If M is free of finite rank then
-- we'll see that this is the same as just choosing an isomorphism M = A^n and giving
-- it the product topology

/-- The "canonical topology" on a module `M` over a topological ring `A`. It's defined as
the weakest topology on `M` which makes every `A`-linear map `M → A` continuous. -/
-- make it an abbreviation not a definition; this means that Lean "prints `Module.topology`
-- in the tactic state for the human reader" but interally is syntactically equal to
-- to the `iInf`, meaning that all the `iInf` rewrites still work.
abbrev Module.topology : TopologicalSpace M :=
-- Topology defined as greatest lower bound of pullback topologies. So it's the biggest
-- topology making all the `f`s continuous.
  ⨅ (f : M →ₗ[A] A), TopologicalSpace.induced f inferInstance

-- let `N` be another module
variable {N : Type*} [AddCommGroup N] [Module A N]

/-- Every `A`-linear map between two `A`-modules with the canonical topology is continuous. -/
lemma Module.continuous_linear (e : M →ₗ[A] N) :
    @Continuous M N (Module.topology A) (Module.topology A) e := by
  -- rewrite the goal (continuity of `e`) as in inequality:
  --(canonical topology) ≤ (pullback of induced topology)
  rw [continuous_iff_le_induced]
  -- There's an already-proven lemma in mathlib that says the pullback of an `iInf` of
  -- topologies is the `iInf` of the pullbacks
  rw [induced_iInf]
  -- composite of the induced topologies is just topology induced by the composition
  -- need `simp_rw` because it's under a binder.
  simp_rw [induced_compose]
  -- so now we've got to prove `iInf S` is `≤ iInf T` for `S` the set of all linear
  -- maps from `M` to `A` and `T` the subset of those which factor through `e`.
  -- It of course suffices to prove `T` ⊆ `S`.
  apply sInf_le_sInf
  -- and this is a trivial calculation.
  rintro τ ⟨φ, rfl⟩
  exact ⟨φ ∘ₗ e, rfl⟩

-- A formal corollary should be that
def Module.homeomorphism_equiv (e : M ≃ₗ[A] N) :
    -- lean needs to be told the topologies explicitly in the statement
    let τM : TopologicalSpace M := Module.topology A
    let τN : TopologicalSpace N := Module.topology A
    M ≃ₜ N :=
  -- And also at the point where lean puts the structure together, unfortunately
  let τM : TopologicalSpace M := Module.topology A
  let τN : TopologicalSpace N := Module.topology A
  -- all the sorries should be formal.
  { toFun := e
    invFun := e.symm
    left_inv := sorry
    right_inv := sorry
    continuous_toFun := sorry
    continuous_invFun := sorry
  }

-- sanity check: the topology on A^n is the product topology
example (ι : Type*) [Finite ι] :
    (Pi.topologicalSpace : TopologicalSpace (ι → A)) = Module.topology A := by
  -- suffices to prove that each topology is ≤ the other one
  apply le_antisymm
  · -- you're ≤ `iInf S` iff you're ≤ all elements of `S`
    apply le_iInf
    -- so take an element of `S`, the topology induced by `b : (ι → A) → A`
    intro b
    -- and we've got to prove that the product topology is `≤` it, which is the
    -- same as saying that `b` is continuous with the product topology on `A^ι`
    rw [← continuous_iff_le_induced]
    -- and we've already proved that all linear maps are continuous.
    apply LinearMap.continuous_on_pi b
  · -- the set Inf application works better here for some reason
    -- We've got to prove the module topology is ≤ the product topology, which is defined here to
    -- be the coarsest topology making all the projection maps continuous
    -- So it suffices to prove that all projections are linear
    apply sInf_le_sInf
    -- so let's look at the i'th projection
    rintro _ ⟨i, rfl⟩
    -- it's linear, because Lean has the projections as linear maps.
    exact ⟨LinearMap.proj i, rfl⟩

-- We need that the module topology on a product is the product topology
lemma Module.prod_canonical :
    @instTopologicalSpaceProd M N (Module.topology A) (Module.topology A) =
    (Module.topology A : TopologicalSpace (M × N)) := by
  -- the goal is to prove that an iInf equals an inf (of two topologies).
  unfold instTopologicalSpaceProd -- you can probably delete this later
  sorry

-- I assume this is true! Lots of things like this seem to be true.
lemma Module.continuous_bilinear {P : Type*} [AddCommGroup P] [Module A P]
    (b : M →ₗ[A] N →ₗ[A] P) :
    @Continuous (M × N) P (Module.topology A) (Module.topology A) (fun mn ↦ b mn.1 mn.2) := by
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
def D_topology : TopologicalSpace D := Module.topology A

instance moobar : @TopologicalRing D (Module.topology A) _ :=
  let _ : TopologicalSpace D := Module.topology A
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
