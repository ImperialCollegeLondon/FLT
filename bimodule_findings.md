# Bimodule prototype: findings

*A build-one-to-throw-away experiment in FLT (`FLT/Mathlib/Algebra/Module/Bimodule/`,
`FLT/NumberField/AdeleRing/Bimodule.lean`), prototyping a native right-module class to
inform the recurring right-actions design discussion (Eric Wieser, Kenny Lau, Andrew
Yang, Anatole Dedecker; threads: "#4773 base change", "Right actions on tensor products
(again)", "product of modules over product of rings").*

*Status: 689 lines across four files (Defs 244, Basic 251, TensorProduct 92, adele
instances 102), zero diagnostics, sorry-free, every declaration axiom-checked to
`{propext, Classical.choice, Quot.sound}`, full FLT `lake build` green.*

## The design that was built

Not one class but a data class and a `Prop`-mixin, mirroring the shape of mathlib's
op-encoded `[Module A M] [Module Bᵐᵒᵖ M] [SMulCommClass A Bᵐᵒᵖ M]`:

```lean
class RightModule (B M : Type*) [Semiring B] [AddCommMonoid M] where
  rsmul : M → B → M          -- notation `m <• b`, scoped in `Bimodule`
  -- + 6 axioms mirroring Module's (rsmul_one, rsmul_mul, add_rsmul, rsmul_add,
  --   zero_rsmul, rsmul_zero)

class Bimodule (A M B : Type*) [Semiring A] [Semiring B] [AddCommMonoid M]
    [Module A M] [RightModule B M] : Prop where
  smul_rsmul : ∀ (a : A) (m : M) (b : B), (a • m) <• b = a • (m <• b)
```

Deliberately there is **no instance in either direction** between `RightModule B M` and
`Module Bᵐᵒᵖ M` (nor `Module B M` in the commutative case); the bridges exist only as
`@[instance_reducible] def`s for `letI`-style local transport.

Two structural points that were *forced* during the experiment, not chosen up front:

1. **The right action cannot live in a class parametrized by the left ring.** A
   monolithic `class Bimodule A M B extends Module A M` (the original spec) fails twice:
   the parent projection `Bimodule.toModule : Module A M` is an instance whose conclusion
   doesn't mention `B` (every `Module A M` search then spawns `Bimodule A M ?B`), and if
   `rsmul` is a field of the monolithic class then `x <• b` must synthesize
   `Bimodule ?A M B` with `?A` a dangling metavariable — genuinely ambiguous, since e.g.
   `𝔸_L` is at once an `(L, 𝔸_K)`- and a `(ℤ, 𝔸_K)`-bimodule *with the same right
   action*. The action's identity belongs to `(B, M)` alone; only the compatibility
   involves `A`. The factored design is therefore not a style choice but the load-bearing
   part of the prototype.

2. **The mixin costs one extra binder.** Generic bimodule statements read
   `variable [Module A M] [RightModule B M] [Bimodule A M B]` — three classes where the
   op-encoding also has three (`Module`, `Module ᵐᵒᵖ`, `SMulCommClass`), so no
   regression, but no improvement either.

Notation: `m <• b`, scoped in the `Bimodule` namespace, with the same arrow and
precedences as mathlib's scoped `RightActions` notation for `MulOpposite.op b • m` — so
native and op-encoded code *read identically*, and the two scopes only collide when a
file opens both **and** both a `RightModule B M` and an `SMul Bᵐᵒᵖ M` instance exist for
the same pair.

## The headline example

"`𝔸_L` is an `(L, 𝔸_K)`-bimodule" is two one-line **global** instances — no scoped
instances, no `open`-a-hack-namespace, nothing imported that mathlib would blush at:

```lean
noncomputable instance : RightModule (𝔸 K) (𝔸 L) :=
  .ofRingHom (baseChange K L).toRingHom

instance : Bimodule L (𝔸 L) (𝔸 K) :=
  Bimodule.ofRingHom (baseChange K L).toRingHom
```

Both conclusions determine all their arguments, so neither instance has the
`SMul X Y → SMul (F X) (F Y)` shape that forces FLT's `Algebra 𝔸ᶠ[K] 𝔸ᶠ[L]` to be
scoped. The constructor is the primitive one:

* `RightModule.ofRingHom (f : B →+* S) : RightModule B S` — right multiplication
  through a ring hom (`s <• b = s * f b`); the right-module analogue of
  `RingHom.toAlgebra`.
* `Bimodule.ofRingHom` — under `[Module A S] [IsScalarTower A S S]` (any `A`-algebra),
  compatibility is exactly `smul_mul_assoc`, so the bimodule structure is free.

This is the same observation that fixes #39699: right multiplication commutes with
everything a left structure does, because associativity says so.

## Cost accounting: what had to be duplicated

**Cheap (mechanical one-liners, done in the prototype):**

* The class + 6 axioms + ~10 root-level restatement lemmas with the mirrored simp set
  (`rsmul_one`, `add_rsmul`, … following the `one_smul`, `smul_add` conventions).
* `neg_rsmul`/`sub_rsmul` — free once `rsmulAddMonoidHom : M →+ M` exists, via
  `map_neg`/`map_sub`.
* `Bimodule ℕ M B` and `Bimodule ℤ M B` instances — free via `map_nsmul`/`map_zsmul`;
  this is the "no zsmul diamond" point, confirmed in practice.
* `Finset.sum_rsmul` / `Finset.rsmul_sum` — free via `map_sum` on the two bundled homs.
* Units cancellation, `RightModule.compHom` (restriction of the *right* scalars along
  `B' →+* B`), `Bimodule.restrictScalars` (restriction of the *left* scalars along a
  tower) — a few lines each.

**Reused, not duplicated:** everything additive. `RightLinearMap` extends `M →+ N` and
gets an `AddMonoidHomClass` instance, so `map_zero`, `map_add`, `map_sum`, `map_neg`, …
apply verbatim. The additive half of the module library never needs touching.

**The real cost — bundled structures.** The `RightLinearMap B M N` probe
(`M →ᵣ[B] N`): structure, `FunLike`, `AddMonoidHomClass`, `ext`, `map_rsmul`, `id`,
`comp` with simp lemmas. That is the *skeleton only* — no `AddCommMonoid (M →ᵣ[B] N)`,
no composition algebra, no kernels. Extrapolating to `RightSubmodule` (a `SetLike` with
lattice structure, span, quotients...) and right-`Finsupp`/basis theory: this is
thousands of lines of genuinely duplicated API. The op-encoding gets all of it today for
free as `LinearMap Bᵐᵒᵖ`, `Submodule Bᵐᵒᵖ`.

**Transport (`restrictScalars`-style) — bearable for theorems, bad for structures.**
`RightModule.moduleOp : Module Bᵐᵒᵖ M` (a def) makes any op-encoded *theorem* available
inside a proof at the cost of one `letI`. `Bimodule.smulCommClass_moduleOp` carries the
mixin across. But transporting a *type* (`Submodule Bᵐᵒᵖ M` with a `letI`-instance in
its type) recreates Andrew Yang's type-synonym objection: the instance is part of the
type, and every consumer must carry it. Transport is a per-proof tool, not an API
strategy.

## Tensor products (the #39699 connection)

`FLT/Mathlib/Algebra/Module/Bimodule/TensorProduct.lean`: for `M` an `R`-module and `B`
an `R`-algebra,

```lean
noncomputable instance : RightModule B (M ⊗[R] B)   -- rsmul x b = lTensor M (mulRight R b) x
instance [Module A M] [SMulCommClass R A M] : Bimodule A (M ⊗[R] B) B
```

* The action is `id_M ⊗ (· * b)` — no `TensorProduct.comm`, no `MulOpposite`, and the
  proofs are map-level (`mulRight_mul` + `lTensor_comp` etc.), not induction.
* Unlike `Algebra.TensorProduct.rightAlgebra` (a `def`, because `Algebra B (A ⊗[R] B)`
  collides with `Algebra A (A ⊗[R] B)` at `A = B`), the right-module structure is a
  global **instance**: `RightModule` never competes with `Module`, so the `A = B`
  ambiguity that has blocked #39699-style refactors simply does not arise.
* The `#39699` special case `Bimodule A (A ⊗[R] B) B` is found by `inferInstance`.

## Warts found (the honest list)

1. **The `K = L` diamond — and it fired.** `RightModule (𝔸 K) (𝔸 K)` is inhabited both
   by `Semiring.toRightModule` (right multiplication) and by the base-change instance at
   `L := K` (right multiplication through `baseChange K K`) — propositionally equal,
   presumably not definitionally. This is not hypothetical: the *first* declaration
   mixing the two (`baseChangeRightLinearMap : (𝔸 K) →ᵣ[𝔸 K] (𝔸 L)`, base change as a
   map of right `𝔸 K`-modules) silently picked the base-change action on the domain and
   became unprovable. Declaring the base-change instance at `priority := 900` arbitrates
   it — the self-action wins at `K = L`, so `x <• b` on `𝔸 K` always means `x * b` —
   and the declaration then elaborates with no pinning. Two caveats carry over to any
   real design: priority-based arbitration is global and blunt (an `IsBaseChange`-style
   compatibility class would be principled), and the op-encoding has the *same* problem
   the moment anyone writes the corresponding `Module (𝔸 K)ᵐᵒᵖ (𝔸 K)` instances; it is
   a fact about base change, not about the encoding.
2. **`Bimodule.ofRingHom` needs `letI` in its statement**, because the `Prop` depends on
   which `RightModule` *data* is in scope. Harmless at instance-declaration sites, but
   it is the visible seam of the data/Prop factoring.
3. **`rfl`-transparency discipline.** Sites registering `RightModule.ofRingHom`-built
   instances should restate the action (`rsmul_def : x <• b = x * f b := rfl`);
   `@[instance_reducible]` on the constructors keeps this working.

## Comparison with the alternatives

* **Op-encoding (status quo):** all API exists today; the cost is notational
  (`Module Bᵐᵒᵖ`, `op b • m` — mitigated by the `RightActions` scope) and conceptual.
  Every finding above about *diamonds* applies to it equally.
* **Native right actions (this prototype):** the core and everything additive is cheap;
  linear-map/submodule-level API is a large genuine duplication that someone would have
  to write and maintain. Nothing *breaks* — the two worlds connect by explicit defs —
  but nothing is free either.
* **Type synonyms:** not tested here; Andrew Yang's objection (opaque synonym ⇒ carry an
  equivalence everywhere) resurfaced in this experiment as the transport-of-structures
  problem, which is evidence the objection is fundamental.
* **Anatole's named actions:** still uncosted; the prototype at least sharpens what it
  must beat — the op-encoding's zero-duplication, and the native encoding's readability.

## Verdict

A native right action buys exactly two things: (1) statements that read like
mathematics (`Bimodule L (𝔸 L) (𝔸 K)` as global instances, `(l • x) <• b = l • (x <• b)`),
and (2) an escape from `Module`-instance collisions (the tensor-product right action can
be an instance, where `rightAlgebra` cannot). It costs a full parallel bundled-structure
library, of which this prototype implements only the first hundred metres. If the
bundled tier is out of budget, the op-encoding plus the `RightActions` notation scope
remains the rational choice, and the `lTensor`-style primitive (right multiplication
through a hom) is the piece worth extracting into it — that piece is what unblocks
#39699 either way.
