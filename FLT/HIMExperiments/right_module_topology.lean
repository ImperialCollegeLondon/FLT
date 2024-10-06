import Mathlib.RingTheory.TensorProduct.Basic -- we need tensor products of rings at some point
import Mathlib.Topology.Algebra.Module.Basic -- and we need topological rings and modules
import Mathlib
set_option lang.lemmaCmd true
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

set_option linter.unusedSectionVars false

-- See FLT.ForMathlib.ActionTopology for a parallel development.
namespace right_module_topology

section defs

class IsActionTopology (R M : Type*) [SMul R M]
    [τR : TopologicalSpace R] [τM : TopologicalSpace M] : Prop where
  isActionTopology' : τM = ⨆ m, .coinduced (· • m) τR

-- just to make R and M explicit
def isActionTopology (R M : Type*) [SMul R M]
    [TopologicalSpace R] [TopologicalSpace M] [IsActionTopology R M ]:=
  IsActionTopology.isActionTopology' (R := R) (M := M)

def actionTopology (R M : Type*) [SMul R M] [TopologicalSpace R] :
    TopologicalSpace M := ⨆ m, .coinduced (· • m) (inferInstance : TopologicalSpace R)

end defs
namespace ActionTopology


section one

variable {R : Type*} [τR : TopologicalSpace R]

-- this proof should be much easier
example [Monoid R] [ContinuousMul R] :
    IsActionTopology R R where
  isActionTopology' := by
    rw [iSup.eq_1]
    symm
    rw [← isLUB_iff_sSup_eq]
    constructor
    · rintro - ⟨r, rfl⟩
      simp
      rw [← continuous_iff_coinduced_le]
      fun_prop
    · intro σR hσ
      rw [mem_upperBounds] at hσ
      specialize hσ ?_ ⟨?_, ?_⟩
      swap
      use 1
      exact (fun m ↦ TopologicalSpace.coinduced (fun x ↦ x • m) τR) 1
      rfl
      convert hσ
      simp only [smul_eq_mul, mul_one]
      rfl
-- this proof should be much easier
end one

section type_stuff

variable {R : Type*} [τR : TopologicalSpace R]


-- let `M` and `N` have an action of `R`
variable {M : Type*} [SMul R M] [τM : TopologicalSpace M] [IsActionTopology R M]
variable {N : Type*} [SMul R N] [τN : TopologicalSpace N] [IsActionTopology R N]

example (L) [CompleteLattice L] (f : M → N) (g : N → L) : ⨆ m, g (f m) ≤ ⨆ n, g n := by
  exact iSup_comp_le g f

theorem map_smul_pointfree (f : M →[R] N) (r : R) : (fun m ↦ f (r • m)) = fun m ↦ r • f m :=
  by ext; apply map_smul


/-- Every `A`-linear map between two `A`-modules with the canonical topology is continuous. -/
lemma continuous_of_mulActionHom (e : M →[R] N) : Continuous e := by
  -- Let's turn this question into an inequality question about coinduced topologies
  rw [continuous_iff_coinduced_le]
  -- Now let's use the fact that τM and τN are action topologies (hence also coinduced)
  rw [isActionTopology R M, isActionTopology R N]
  -- There's an already-proven lemma in mathlib that says that coinducing an `iSup` is the
  -- same thing as taking the `iSup`s of the coinduced topologies
  -- composite of the coinduced topologies is just topology coinduced by the composite
  rw [coinduced_iSup]
  simp_rw [coinduced_compose]
  -- restate the current state of the question with better variables
  change ⨆ m, TopologicalSpace.coinduced (fun r ↦ e (r • m)) τR ≤
    ⨆ n, TopologicalSpace.coinduced (fun x ↦ x • n) τR
  -- use the fact that `e (r • m) = r • (e m)`
  simp_rw [map_smul]
  -- and now the goal follows from the fact that the sup over a small set is ≤ the sup
  -- over a big set
  apply iSup_comp_le (_ : N → TopologicalSpace N)

-- A formal corollary should be that
def homeomorph_of_mulActionEquiv (φ : M →[R] N) (ψ : N →[R] M) (h1 : ∀ m, ψ (φ m) = m)
    (h2 : ∀ n, φ (ψ n) = n) : M ≃ₜ N :=
  { toFun := φ
    invFun := ψ
    left_inv := h1
    right_inv := h2
    continuous_toFun := continuous_of_mulActionHom φ
    continuous_invFun := continuous_of_mulActionHom ψ
  }

lemma unit : (inferInstance : TopologicalSpace Unit) = actionTopology R Unit := by
  unfold actionTopology
  rw [ciSup_unique]
  exact le_antisymm (fun U _ ↦ trivial) <|
    Subsingleton.le (TopologicalSpace.coinduced (fun _ ↦ PUnit.unit) inferInstance) inferInstance

-- is this true?
lemma prod : (inferInstance : TopologicalSpace (M × N)) = actionTopology R (M × N) := by
  sorry

-- is this true? If not, is it true if ι is finite?
lemma pi {ι : Type*} {M : ι → Type*} [∀ i, SMul R (M i)] [τM : ∀ i, TopologicalSpace (M i)]
    [∀ i, IsActionTopology R (M i)] :
    (inferInstance : TopologicalSpace (∀ i, M i)) = actionTopology R (∀ i, M i) := by
  sorry

-- is this true? If not, is it true if ι is finite?
lemma sigma {ι : Type*} {M : ι → Type*} [∀ i, SMul R (M i)] [τM : ∀ i, TopologicalSpace (M i)]
    [∀ i, IsActionTopology R (M i)] :
    (inferInstance : TopologicalSpace (Σ i, M i)) = actionTopology R (Σ i, M i) := by
  sorry

end type_stuff

section R_is_M_stuff

variable {R : Type} [τR : TopologicalSpace R] [Monoid R]

-- is this true? Do we need that R is commutative? Does it work if R is a only semigroup?
example : (inferInstance : TopologicalSpace R) = actionTopology R R := by
  sorry

end R_is_M_stuff

section what_i_want

-- Let A be a commutative ring, with a compatible topology.
variable (A : Type*) [CommRing A] [TopologicalSpace A] [TopologicalRing A]
-- let `M` and `N` be `A`-modules
variable (M : Type*) [AddCommGroup M] [Module A M] [TopologicalSpace M] [TopologicalAddGroup M] [IsActionTopology A M]
variable {N : Type*} [AddCommGroup N] [Module A N] [TopologicalSpace N] [TopologicalAddGroup N] [IsActionTopology A N]
-- Remark: A needs to be commutative so that I get an A-action on M ⊗ N.

-- What generality is this true in? I only need it when M and N are finite and free
open scoped TensorProduct
lemma continuous_of_bilinear :
    letI : TopologicalSpace (M ⊗[A] N) := actionTopology A (M ⊗[A] N)
    Continuous (fun (mn : M × N) ↦ mn.1 ⊗ₜ mn.2 : M × N → M ⊗[A] N) := by sorry

-- Now say we have a (not necessarily commutative) `A`-algebra `D` which is free of finite type.
-- are all these assumptions needed?
variable (D : Type*) [Ring D] [Algebra A D] [Module.Finite A D] [Module.Free A D] [TopologicalSpace D] [IsActionTopology A D]

theorem needed_for_FLT : TopologicalRing D where
  continuous_add := sorry
  continuous_mul := sorry
  continuous_neg := sorry

end what_i_want

-- possible hints at https://github.com/ImperialCollegeLondon/FLT/blob/main/FLT/HIMExperiments/module_topology.lean
-- except there the topology is *different* so the work does not apply
end ActionTopology

end right_module_topology
