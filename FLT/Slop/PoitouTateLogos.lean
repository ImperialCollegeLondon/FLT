/-
FOR INTERNAL DEVELOPMENT ONLY.

To compile this Lean file:
  1. Clone LeanService.
  2. cd into the lean-project directory.
  3. Run lake exe logos-cache get.
  4. Run lake build.
  5. Place this file in the directory and open it in your editor.
  6. If it does not work, restart the file.
-/

import LeanProject
SetDefaultOpts


section
-- Natural language: Let $K$ be a number field and let $S$ be a set of finite places of $K$
-- (height-one primes of $\mathcal{O}_K$). The $S$-ramification subgroup $N_S$ is defined to be the
-- topological closure of the normal closure of the union over all finite places $v \notin S$ of the
-- image of the local inertia subgroup $I_v$ under the map $\operatorname{Gal}(\overline{K_v}/K_v)
-- \to G_K$ induced by the algebra map $K \to \widehat{K_v}$.
-- Score: (0 - incorrect, 1 - partially correct, 2 - correct)
-- Comment:
/-- The `S`-ramification subgroup `N_S`: the smallest closed normal subgroup of the
absolute Galois group `G_K` containing, for every finite place `v ∉ S`, the image of
the inertia subgroup `I_v ⊆ Gal(K̄_v/K_v)` under the local-to-global map
`Gal(K̄_v/K_v) → G_K` determined by a choice of embedding `K̄ → K̄_v`. -/
noncomputable def sRamifiedSubgroup (K : Type*) [Field K] [NumberField K]
    (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) :
    Subgroup (Field.absoluteGaloisGroup K) :=
  (Subgroup.normalClosure
    (⋃ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) (_ : v ∉ S),
      ⇑(Field.absoluteGaloisGroup.map
          (algebraMap K (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v))) ''
        ↑(localInertiaGroup v))).topologicalClosure


end

section
-- Natural language: Let $K$ be a number field and $S$ a set of finite places of $K$ (i.e., a set of
-- height-one prime ideals of the ring of integers of $K$). The $S$-ramification subgroup $N_S$ is
-- the topological closure of the normal closure of the union over all finite places $v \notin S$ of
-- the image of the local inertia group $I_v$ under the map $\operatorname{Gal}(\overline{K}_v/K_v)
-- \to G_K$ induced by an embedding $\overline{K} \to \overline{K}_v$. The Galois group $G_S := G_K
-- / N_S$ is defined to be the quotient of the absolute Galois group $G_K$ of $K$ by this subgroup.
-- Score: (0 - incorrect, 1 - partially correct, 2 - correct)
-- Comment:
/-- The Galois group `G_S := G_K / N_S`: the quotient of the absolute Galois group of `K`
by the `S`-ramification subgroup. It is a profinite topological group (the quotient group
and quotient topology instances fire automatically since `N_S` is a closed normal
subgroup), canonically `Gal(K_S/K)` for `K_S` the maximal subextension of `K̄/K` ramified
only at primes in `S`. -/
noncomputable abbrev sGaloisGroup (K : Type*) [Field K] [NumberField K]
    (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) :
    Type _ :=
  Field.absoluteGaloisGroup K ⧸ sRamifiedSubgroup K S


end

section
-- Natural language: For a number field $K$ and a set $S$ of finite places of $K$ (i.e., a set of
-- height‑one primes of the ring of integers of $K$), the $S$-ramification subgroup $N_S$ is a
-- normal (closed) subgroup of the absolute Galois group $G_K$; consequently the quotient $G_S =
-- G_K/N_S$ carries a canonical topological group structure.
-- Score: (0 - incorrect, 1 - partially correct, 2 - correct)
-- Comment:
/-- The `S`-ramification subgroup `N_S` is a normal (closed) subgroup of the absolute
Galois group `G_K`; consequently the quotient `G_S = G_K/N_S` carries canonical
topological group structure. -/
instance sRamifiedSubgroupNormal (K : Type*) [Field K] [NumberField K]
    (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) :
    (sRamifiedSubgroup K S).Normal :=
  Subgroup.is_normal_topologicalClosure _


end

section
-- Natural language: We say that a *Poitou–Tate setup* consists of a prime $p>2$, a finite field $F$
-- of characteristic $p$, a totally real number field $K$, a set $S$ of height‑one primes of the
-- ring of integers of $K$ (which by convention always contains the archimedean places), a finitely
-- generated $F$-module $M$, a continuous representation $\rho : G_S \to \operatorname{Aut}_F(M)$
-- (where $G_S$ is the Galois group of the maximal extension of $K$ unramified outside $S$) such
-- that for every $m\in M$ the stabilizer $\{g\in G_S \mid \rho(g)m=m\}$ is open, and such that the
-- order $\operatorname{Nat.card}(M)$ is a unit in the ring of $S$-integers $R_{K,S}$.
-- Score: (0 - incorrect, 1 - partially correct, 2 - correct)
-- Comment:
/-- The ambient data for the (restrictive) Poitou–Tate setting:
a prime `p > 2`; a finite field `F` of characteristic `p`; a totally real number field
`K`; a set `S` of primes of `K` — following the source's convention `S` always contains
all archimedean places, so (these carrying no data, and making `S` automatically
non-empty) the field `S` below records the *finite* part `S_f ⊆ S` as a set of
height-one primes of `𝓞_K`; and a finitely generated (hence finite) `G_S`-module `M`
over `F` whose order is a unit in the ring of `S`-integers `R_{K,S}`, the action of
`G_S = Gal(K_S/K) = sGaloisGroup K S` being continuous (each point stabilizer is open,
`M` being discrete). All cohomology throughout is continuous cohomology of profinite
groups. -/
structure PoitouTateSetup (F : Type) [Field F] [Fintype F]
    (K : Type) [Field K] [NumberField K]
    (M : Type) [AddCommGroup M] [Module F M] where
  p : ℕ
  hp : p.Prime
  hp_odd : 2 < p
  charP : CharP F p
  totallyReal : NumberField.IsTotallyReal K
  S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
  finiteM : Module.Finite F M
  ρ : Representation F (sGaloisGroup K S) M
  continuous_ρ : ∀ m : M, IsOpen {g : sGaloisGroup K S | ρ g m = m}
  card_isUnit : IsUnit (Nat.card M : ↥(S.integer K))


end

section
-- Natural language: Let $K$ be a number field and $S$ a set of finite places of $K$ (i.e. a set of
-- height-one prime ideals of the ring of integers of $K$). The field $K_S$ is defined to be the
-- fixed field of the $S$-ramification subgroup $N_S$ acting on the algebraic closure
-- $\overline{K}$, viewed as an intermediate field of $\overline{K}/K$.
-- Score: (0 - incorrect, 1 - partially correct, 2 - correct)
-- Comment:
/-- The field `K_S`: the fixed field of the `S`-ramification subgroup `N_S` acting on the
algebraic closure `K̄`, i.e. the maximal subfield of the separable closure of `K` that is
ramified over `K` only at primes in `S`, viewed as an intermediate field of `K̄/K`.
(The group `G_S = G_K/N_S` acts on `K_S`, and hence on `K_Sˣ`, by descent of the natural
`G_K`-action; this action is realised on downstream items via the quotient.) -/
noncomputable def sMaximalExtension (K : Type*) [Field K] [NumberField K]
    (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) :
    IntermediateField K (AlgebraicClosure K) :=
  IntermediateField.fixedField (sRamifiedSubgroup K S)


end

section
-- Natural language: Let $F$ be a finite field, $K$ a number field, and $M$ a finite-dimensional
-- $F$-vector space (hence a finite abelian group). Given a Poitou–Tate setup $P$ over $F$, $K$, and
-- $M$, the *dual module* $M^*$ is defined to be $\operatorname{Hom}_{\mathbb{Z}}(M, K_S^\times)$,
-- the abelian group of group homomorphisms from the additive group $M$ to the multiplicative group
-- of units of the maximal $S$-ramified extension $K_S$ of $K$.
-- Score: (0 - incorrect, 1 - partially correct, 2 - correct)
-- Comment:
/-- The dual module `M^* = Hom_ℤ(M, K_S^×)` (Milne's `M^D`): the group of abelian-group
homomorphisms from the *additive* group `M` to the *multiplicative* unit group `K_S^×`.
In Lean, a homomorphism from an additive group to a multiplicative group is expressed
by transporting the codomain along the type tag `Additive` — `Additive K_S^×` is the
SAME group `K_S^×` with its multiplication written additively — so
`M →+ Additive K_S^×` is literally `Hom_ℤ(M, K_S^×)`: its elements are the maps
`x^* : M → K_S^×` with `x^*(m + m') = x^*(m)·x^*(m')`. No structure is changed.
The natural `G_S`-action `(g·x^*)(x) = g(x^*(g⁻¹x))` is realised by the companion item
`dualModuleRep`. When `M` is finite of order `n`, every homomorphism takes values in
the `n`-th roots of unity, so `M^* = Hom_ℤ(M, μ_n)`. -/
noncomputable abbrev dualModule {F K M : Type} [Field F] [Fintype F] [Field K]
    [NumberField K] [AddCommGroup M] [Module F M] (P : PoitouTateSetup F K M) :
    Type :=
  M →+ Additive (↥(sMaximalExtension K P.S))ˣ


end

section
-- Natural language: Let $F$, $K$, $M$ be types, let $F$ be a field with $F$ finite, let $K$ be a
-- field with $K$ a number field, let $M$ be an additive commutative group with an $F$-module
-- structure, and let $P$ be a Poitou–Tate setup on $F$, $K$, $M$.
-- The action of $G_S$ on the coefficient module $M$ of $P$, repackaged as a monoid homomorphism
-- $G_S \to \operatorname{End}(M)$ of additive endomorphisms (forgetting the $F$-linear structure of
-- $\rho$), is defined by sending $g$ to the additive monoid homomorphism underlying $P.\rho(g)$.
-- Score: (0 - incorrect, 1 - partially correct, 2 - correct)
-- Comment:
/-- The action of `G_S` on the coefficient module `M` of a Poitou–Tate setup,
repackaged as a monoid homomorphism `G_S →* End(M)` of additive endomorphisms
(forgetting the `F`-linear structure of `ρ`). -/
noncomputable def setupRho {F K M : Type} [Field F] [Fintype F] [Field K]
    [NumberField K] [AddCommGroup M] [Module F M] (P : PoitouTateSetup F K M) :
    sGaloisGroup K P.S →* AddMonoid.End M where
  toFun := fun g => (P.ρ g).toAddMonoidHom
  map_one' := by ext m; rw [map_one]; rfl
  map_mul' := by intro g h; ext m; rw [map_mul]; rfl


end

section
-- Natural language: Let $K$ be a number field, let $S$ be a set of finite primes of $K$ (height-one
-- primes of the ring of integers of $K$), and let $v$ be a finite prime of $K$.
-- The *decomposition map* $G_v = \operatorname{Gal}(\overline{K}_v/K_v) \to G_{K,S}$ is defined to
-- be the continuous homomorphism obtained by composing the map
-- $\operatorname{Gal}(\overline{K}_v/K_v) \to G_K$ induced by the embedding $K \hookrightarrow
-- \overline{K}_v$ (determined by a choice of a prime $\tilde{v}$ of $\overline{K}$ above $v$) with
-- the quotient map $G_K \to G_{K,S} = G_K/N_S$.
-- Score: (0 - incorrect, 1 - partially correct, 2 - correct)
-- Comment:
/-- The local-to-global map `G_v = Gal(K̄_v/K_v) → G_{K,S}` for a finite place `v`:
the composition of `Gal(K̄_v/K_v) → G_K` (determined by a choice of prime `ṽ` of `K̄`
above `v`, equivalently an embedding `K̄ → K̄_v`; realised by
`Field.absoluteGaloisGroup.map`) with the projection `G_K → G_S = G_K/N_S`. Such maps
are not canonical: they depend on the choice of `ṽ`. After such a choice one obtains a
decomposition subgroup `D_ṽ = {σ ∈ G_{K,S} : σṽ = ṽ}` as the image, and `G_v ≅ D_ṽ`;
different choices give conjugate decomposition subgroups and have no effect on the
induced maps on `H^i`. The map is a continuous homomorphism. -/
noncomputable def decompositionMap (K : Type*) [Field K] [NumberField K]
    (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    ContinuousMonoidHom
      (Field.absoluteGaloisGroup (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v))
      (sGaloisGroup K S) :=
  { toMonoidHom :=
      (QuotientGroup.mk' (sRamifiedSubgroup K S)).comp
        (Field.absoluteGaloisGroup.map
          (algebraMap K (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v))).toMonoidHom
    continuous_toFun :=
      continuous_quot_mk.comp
        (map_continuous
          (Field.absoluteGaloisGroup.map
            (algebraMap K (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v)))) }


end

section
-- Natural language: Let $F$ be a field, $K$ a number field, $M$ an additive abelian group equipped
-- with an $F$-module structure, and $P$ a Poitou–Tate setup for $F$, $K$, $M$. For each finite
-- place $v$ of $K$ (i.e., each height‑one prime of the ring of integers of $K$), the *local Galois
-- group* $G_v = \operatorname{Gal}(\overline{K_v}/K_v)$ acts on $M$ via the composition of the
-- homomorphism $\operatorname{Gal}(\overline{K_v}/K_v) \to G_S$ (the local‑to‑global map determined
-- by a choice of prime above $v$) with the homomorphism $G_S \to
-- \operatorname{End}_{\mathbb{Z}}(M)$ given by the $G_S$‑action on $M$ (forgetting the $F$‑linear
-- structure). This yields a monoid homomorphism $G_v \to \operatorname{End}_{\mathbb{Z}}(M)$.
-- Score: (0 - incorrect, 1 - partially correct, 2 - correct)
-- Comment:
/-- The action of the local Galois group `G_v = Gal(K̄_v/K_v)` on the coefficient
module `M`: the composition of the `G_S`-action with the local-to-global map
`G_v → G_S`. -/
noncomputable abbrev localRho {F K M : Type} [Field F] [Fintype F] [Field K]
    [NumberField K] [AddCommGroup M] [Module F M] (P : PoitouTateSetup F K M)
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    Field.absoluteGaloisGroup (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v)
      →* AddMonoid.End M :=
  (setupRho P).comp (decompositionMap K P.S v).toMonoidHom


end

section
-- Natural language: Let $F$ be a finite field, $K$ a number field, $M$ a finite-dimensional
-- $F$-vector space, and $P$ a Poitou–Tate setup for $F$, $K$, $M$. For a finite prime $v$ of $K$,
-- we say that $M$ is *unramified* at $v$ if for every $\sigma$ in the inertia subgroup $I_v$ of the
-- local Galois group $G_v$ and every $m \in M$, the local action $\rho_v(\sigma)(m)$ equals $m$.
-- Score: (0 - incorrect, 1 - partially correct, 2 - correct)
-- Comment:
/-- `M` is unramified (at `v`) if `M^{I_v} = M`: every element of the inertia subgroup
`I_v` acts as the identity on `M` (via the local action `localRho`). For unramified
`M`, `H^1(G_v/I_v, M)` makes sense and injects into `H^1(G_v, M)` by inflation; the
companion submodule `M^d = Hom(M, (R^un_v)^×) ⊆ M^*` is `unramifiedDual`. -/
def unramifiedModule {F K M : Type} [Field F] [Fintype F] [Field K]
    [NumberField K] [AddCommGroup M] [Module F M] (P : PoitouTateSetup F K M)
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) : Prop :=
  ∀ σ ∈ localInertiaGroup v, ∀ m : M, localRho P v σ m = m


end

section
-- Natural language: For each finite place $v$ of $K$ there exists a $K$-algebra embedding $\iota_v
-- : \overline{K} \to \overline{K_v}$ compatible with the local-to-global map on Galois groups: for
-- every $\sigma \in \mathrm{Gal}(\overline{K_v}/K_v)$ and every $x \in \overline{K}$,
-- $\iota_v\big((\mathrm{loc}_v\,\sigma)(x)\big) = \sigma(\iota_v(x))$, where $\mathrm{loc}_v :
-- \mathrm{Gal}(\overline{K_v}/K_v) \to G_K$ denotes the local-to-global homomorphism.
-- Score: (0 - incorrect, 1 - partially correct, 2 - correct)
-- Comment:
/-- For each finite place `v` of `K` there exists an embedding
`ι_v : K̄ → K̄_v` of the algebraic closure of `K` into the algebraic closure of the
completion `K_v` which is a `K`-algebra map (it commutes with the structure maps from
`K`) and is compatible with the local-to-global map on Galois groups:
`ι_v((loc_v σ)(x)) = σ(ι_v(x))` for all `σ ∈ Gal(K̄_v/K_v)`, `x ∈ K̄`, where
`loc_v = Field.absoluteGaloisGroup.map (algebraMap K K_v)`. -/
theorem existsCompatibleEmbedding (K : Type*) [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    ∃ ι : AlgebraicClosure K →+*
        AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v),
      (∀ x : K,
          ι (algebraMap K (AlgebraicClosure K) x)
            = algebraMap (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v)
                (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v))
                (algebraMap K (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v) x))
        ∧ ∀ (σ : Field.absoluteGaloisGroup
              (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v))
            (x : AlgebraicClosure K),
            ι ((Field.absoluteGaloisGroup.map
                (algebraMap K (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v))
                σ) x)
              = σ (ι x) :=
  sorry


end

section
-- Natural language: Let $K$ be a number field and $v$ a finite place of $K$.
-- A chosen $K$-algebra embedding $\iota_v : \overline{K} \to \overline{K_v}$ (equivalently, a
-- choice of prime $\tilde v$ of $\overline{K}$ above $v$), compatible with the local-to-global map
-- on Galois groups.
-- Score: (0 - incorrect, 1 - partially correct, 2 - correct)
-- Comment:
/-- A chosen embedding `ι_v : K̄ → K̄_v` (equivalently, a choice of prime `ṽ` of `K̄`
above `v`), compatible with the structure maps from `K` and with the local-to-global
map on Galois groups (see `existsCompatibleEmbedding`). All local restriction maps and
local pairings are taken with respect to this choice; the choices have no effect on the
induced maps on `H^i`. -/
noncomputable def globalToLocalEmbedding (K : Type*) [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    AlgebraicClosure K →+*
      AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v) :=
  Classical.choose (existsCompatibleEmbedding K v)


end

section
-- Natural language: Let $K$ be a number field, $S$ a set of primes of the ring of integers of $K$,
-- and $v$ a prime of the ring of integers of $K$.
-- The coefficient homomorphism $K_S^{\times} \to \overline{K_v}^{\times}$ (on additivised unit
-- groups) is defined to be the map induced by the composition of the inclusion $K_S \hookrightarrow
-- \overline{K}$ with the chosen embedding $\iota_v : \overline{K} \to \overline{K_v}$, applied to
-- units and then converted to additive groups.
-- Score: (0 - incorrect, 1 - partially correct, 2 - correct)
-- Comment:
/-- The coefficient homomorphism `K_S^× → K̄_v^×` (on additivised unit groups) induced
by the chosen embedding `ι_v : K̄ → K̄_v`, restricted to `K_S ⊆ K̄`. -/
noncomputable def coeffKStoLocal (K : Type*) [Field K] [NumberField K]
    (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    Additive (↥(sMaximalExtension K S))ˣ →+
      Additive
        (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v))ˣ :=
  MonoidHom.toAdditive
    (Units.map
      (((globalToLocalEmbedding K v).comp
          ((sMaximalExtension K S).val : ↥(sMaximalExtension K S) →+* AlgebraicClosure K)) :
        ↥(sMaximalExtension K S) →*
          AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v)))


end

section
-- Natural language: Let $K$ be a number field and $v$ a height-one prime of the ring of integers of
-- $K$.
-- The *maximal unramified extension* $K_v^{\mathrm{un}}$ of the local field $K_v$ is defined to be
-- the fixed field of the inertia subgroup $I_v$ acting on the algebraic closure $\overline{K_v}$,
-- viewed as an intermediate field of $\overline{K_v}/K_v$.
-- Score: (0 - incorrect, 1 - partially correct, 2 - correct)
-- Comment:
/-- The maximal unramified extension `K_v^un` of the local field `K_v`: the fixed field
of the inertia subgroup `I_v` acting on `K̄_v`, viewed as an intermediate field of
`K̄_v/K_v`. -/
noncomputable def maxUnramifiedExtension (K : Type*) [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    IntermediateField (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v)
      (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v)) :=
  IntermediateField.fixedField (localInertiaGroup v)


end

section
-- Natural language: Let $F$ be a field, $K$ a number field, $M$ an $F$-vector space, and $P$ a
-- Poitou–Tate setup for $F$, $K$, $M$. For a prime $v$ of $K$, consider the subset of the dual
-- module $M^* = \operatorname{Hom}_{\mathbb{Z}}(M, K_S^\times)$ consisting of those homomorphisms
-- $x$ such that for every $m \in M$, the image of $x(m)$ under the coefficient map $\iota_v :
-- K_S^\times \to \overline{K_v}^\times$ lies in the maximal unramified extension
-- $K_v^{\mathrm{un}}$ of the completion $K_v$, and both this value and its inverse are integral
-- over the valuation ring $\mathcal{O}_v$ of $K_v$ (i.e., are integral elements of $\overline{K_v}$
-- with respect to the composite of the inclusion $\mathcal{O}_v \hookrightarrow K_v$ and the
-- embedding $K_v \hookrightarrow \overline{K_v}$). Then this subset contains the zero homomorphism,
-- is closed under addition, and is closed under negation.
-- Score: (0 - incorrect, 1 - partially correct, 2 - correct)
-- Comment:
/-- The subset of `M^*` of homomorphisms all of whose values, pushed into `K̄_v` via
`ι_v`, lie in `K_v^un` and are units of its ring of integers (both the value and its
inverse are integral over the valuation subring `𝒪_v`), contains `0` and is closed
under addition and negation. Consequently `AddSubgroup.closure` of this set is the set
itself, realising `M^d`. -/
theorem unramifiedDualClosed {F K M : Type} [Field F] [Fintype F] [Field K]
    [NumberField K] [AddCommGroup M] [Module F M] (P : PoitouTateSetup F K M)
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    ((0 : dualModule P) ∈
        {x : dualModule P | ∀ m : M,
          ((Additive.toMul (coeffKStoLocal K P.S v (x m)) :
              (AlgebraicClosure
                (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v))ˣ) :
            AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v))
            ∈ maxUnramifiedExtension K v
          ∧ ((algebraMap (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v)
                (AlgebraicClosure
                  (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v))).comp
              (SubringClass.subtype
                (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers
                  K v))).IsIntegralElem
              ((Additive.toMul (coeffKStoLocal K P.S v (x m)) :
                (AlgebraicClosure
                  (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v))ˣ) :
                AlgebraicClosure
                  (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v))
          ∧ ((algebraMap (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v)
                (AlgebraicClosure
                  (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v))).comp
              (SubringClass.subtype
                (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers
                  K v))).IsIntegralElem
              (((Additive.toMul (coeffKStoLocal K P.S v (x m)) :
                (AlgebraicClosure
                  (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v))ˣ))⁻¹ :
                AlgebraicClosure
                  (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v))})
      ∧ (∀ x y : dualModule P,
          x ∈ {x : dualModule P | ∀ m : M,
            ((Additive.toMul (coeffKStoLocal K P.S v (x m)) :
                (AlgebraicClosure
                  (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v))ˣ) :
              AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v))
              ∈ maxUnramifiedExtension K v
            ∧ ((algebraMap (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v)
                  (AlgebraicClosure
                    (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v))).comp
                (SubringClass.subtype
                  (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers
                    K v))).IsIntegralElem
                ((Additive.toMul (coeffKStoLocal K P.S v (x m)) :
                  (AlgebraicClosure
                    (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v))ˣ) :
                  AlgebraicClosure
                    (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v))
            ∧ ((algebraMap (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v)
                  (AlgebraicClosure
                    (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v))).comp
                (SubringClass.subtype
                  (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers
                    K v))).IsIntegralElem
                (((Additive.toMul (coeffKStoLocal K P.S v (x m)) :
                  (AlgebraicClosure
                    (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v))ˣ))⁻¹ :
                  AlgebraicClosure
                    (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v))} →
          y ∈ {x : dualModule P | ∀ m : M,
            ((Additive.toMul (coeffKStoLocal K P.S v (x m)) :
                (AlgebraicClosure
                  (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v))ˣ) :
              AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v))
              ∈ maxUnramifiedExtension K v
            ∧ ((algebraMap (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v)
                  (AlgebraicClosure
                    (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v))).comp
                (SubringClass.subtype
                  (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers
                    K v))).IsIntegralElem
                ((Additive.toMul (coeffKStoLocal K P.S v (x m)) :
                  (AlgebraicClosure
                    (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v))ˣ) :
                  AlgebraicClosure
                    (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v))
            ∧ ((algebraMap (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v)
                  (AlgebraicClosure
                    (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v))).comp
                (SubringClass.subtype
                  (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers
                    K v))).IsIntegralElem
                (((Additive.toMul (coeffKStoLocal K P.S v (x m)) :
                  (AlgebraicClosure
                    (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v))ˣ))⁻¹ :
                  AlgebraicClosure
                    (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v))} →
          x + y ∈ {x : dualModule P | ∀ m : M,
            ((Additive.toMul (coeffKStoLocal K P.S v (x m)) :
                (AlgebraicClosure
                  (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v))ˣ) :
              AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v))
              ∈ maxUnramifiedExtension K v
            ∧ ((algebraMap (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v)
                  (AlgebraicClosure
                    (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v))).comp
                (SubringClass.subtype
                  (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers
                    K v))).IsIntegralElem
                ((Additive.toMul (coeffKStoLocal K P.S v (x m)) :
                  (AlgebraicClosure
                    (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v))ˣ) :
                  AlgebraicClosure
                    (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v))
            ∧ ((algebraMap (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v)
                  (AlgebraicClosure
                    (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v))).comp
                (SubringClass.subtype
                  (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers
                    K v))).IsIntegralElem
                (((Additive.toMul (coeffKStoLocal K P.S v (x m)) :
                  (AlgebraicClosure
                    (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v))ˣ))⁻¹ :
                  AlgebraicClosure
                    (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v))})
      ∧ ∀ x : dualModule P,
          x ∈ {x : dualModule P | ∀ m : M,
            ((Additive.toMul (coeffKStoLocal K P.S v (x m)) :
                (AlgebraicClosure
                  (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v))ˣ) :
              AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v))
              ∈ maxUnramifiedExtension K v
            ∧ ((algebraMap (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v)
                  (AlgebraicClosure
                    (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v))).comp
                (SubringClass.subtype
                  (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers
                    K v))).IsIntegralElem
                ((Additive.toMul (coeffKStoLocal K P.S v (x m)) :
                  (AlgebraicClosure
                    (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v))ˣ) :
                  AlgebraicClosure
                    (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v))
            ∧ ((algebraMap (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v)
                  (AlgebraicClosure
                    (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v))).comp
                (SubringClass.subtype
                  (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers
                    K v))).IsIntegralElem
                (((Additive.toMul (coeffKStoLocal K P.S v (x m)) :
                  (AlgebraicClosure
                    (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v))ˣ))⁻¹ :
                  AlgebraicClosure
                    (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v))} →
          -x ∈ {x : dualModule P | ∀ m : M,
            ((Additive.toMul (coeffKStoLocal K P.S v (x m)) :
                (AlgebraicClosure
                  (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v))ˣ) :
              AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v))
              ∈ maxUnramifiedExtension K v
            ∧ ((algebraMap (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v)
                  (AlgebraicClosure
                    (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v))).comp
                (SubringClass.subtype
                  (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers
                    K v))).IsIntegralElem
                ((Additive.toMul (coeffKStoLocal K P.S v (x m)) :
                  (AlgebraicClosure
                    (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v))ˣ) :
                  AlgebraicClosure
                    (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v))
            ∧ ((algebraMap (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v)
                  (AlgebraicClosure
                    (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v))).comp
                (SubringClass.subtype
                  (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers
                    K v))).IsIntegralElem
                (((Additive.toMul (coeffKStoLocal K P.S v (x m)) :
                  (AlgebraicClosure
                    (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v))ˣ))⁻¹ :
                  AlgebraicClosure
                    (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v))} :=
  sorry


end

section
-- Natural language: Let $F$ be a field, $K$ a number field, $M$ an $\mathbb{F}$-vector space
-- (viewed as an additive abelian group), and $P$ a Poitou–Tate setup for $F$, $K$, $M$.
-- For a finite place $v$ of $K$ (a height‑one prime of the ring of integers of $K$), the
-- *unramified dual* $M^d$ is defined to be the additive subgroup of the dual module $M^* =
-- \operatorname{Hom}_{\mathbb{Z}}(M, K_S^\times)$ generated by those homomorphisms $x^* \in M^*$
-- such that for every $m \in M$, the image of $x^*(m)$ under the coefficient map
-- $\operatorname{coeffKStoLocal}_{K,P,S,v}$ (which sends $K_S^\times$ into $\overline{K_v}^\times$)
-- lies in the maximal unramified extension $K_v^{\mathrm{un}}$ of the completion $K_v$, and both
-- this element and its inverse are integral over the ring of integers $\mathcal{O}_v$ of $K_v$
-- (i.e. they belong to the integral closure of $\mathcal{O}_v$ inside $\overline{K_v}$).
-- Score: (0 - incorrect, 1 - partially correct, 2 - correct)
-- Comment:
/-- The submodule `M^d ⊆ M^*` of Theorem 1.5: `M^d = Hom(M, (R^un_v)^×)`, the subgroup
of those `x^* ∈ M^*` all of whose values, pushed into `K̄_v` via `ι_v`, lie in `K_v^un`
and are units of its ring of integers (both the value and its inverse integral over
`𝒪_v`). Realised as the subgroup generated by this set — which equals the set itself
by `unramifiedDualClosed`. -/
noncomputable def unramifiedDual {F K M : Type} [Field F] [Fintype F] [Field K]
    [NumberField K] [AddCommGroup M] [Module F M] (P : PoitouTateSetup F K M)
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    AddSubgroup (dualModule P) :=
  AddSubgroup.closure
    {x : dualModule P | ∀ m : M,
      ((Additive.toMul (coeffKStoLocal K P.S v (x m)) :
          (AlgebraicClosure
            (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v))ˣ) :
        AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v))
        ∈ maxUnramifiedExtension K v
      ∧ ((algebraMap (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v)
            (AlgebraicClosure
              (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v))).comp
          (SubringClass.subtype
            (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers
              K v))).IsIntegralElem
          ((Additive.toMul (coeffKStoLocal K P.S v (x m)) :
            (AlgebraicClosure
              (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v))ˣ) :
            AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v))
      ∧ ((algebraMap (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v)
            (AlgebraicClosure
              (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v))).comp
          (SubringClass.subtype
            (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers
              K v))).IsIntegralElem
          (((Additive.toMul (coeffKStoLocal K P.S v (x m)) :
            (AlgebraicClosure
              (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v))ˣ))⁻¹ :
            AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v))}


end

section
-- Natural language: For a topological group $G$ and an abelian group $A$ (regarded as discrete),
-- the group $C^n(G,A)$ of continuous inhomogeneous $n$-cochains is defined to be the set of locally
-- constant functions from $G^n$ (identified with $\operatorname{Fin} n \to G$) to $A$.
-- Score: (0 - incorrect, 1 - partially correct, 2 - correct)
-- Comment:
/-- The group `C^n(G,A)` of continuous inhomogeneous `n`-cochains of a topological
group `G` with values in an abelian group `A` regarded as discrete: locally constant
(equivalently, continuous into the discrete `A`) functions `G^n → A`. This is the
cochain model prescribed by the source: `C^i(G,M) = {f : G^i → M continuous}`. -/
abbrev contCochain (G : Type*) [TopologicalSpace G] (A : Type*) [AddCommGroup A]
    (n : ℕ) : Type _ :=
  LocallyConstant (Fin n → G) A


end

section
-- Natural language: Let $G$ be a topological group, $A$ an abelian group, and $\rho : G \to
-- \operatorname{End}(A)$ a monoid homomorphism such that for every $a \in A$ the set $\{g \in G
-- \mid \rho(g)a = a\}$ is open. For every $n \in \mathbb{N}$ and every locally constant function $f
-- : G^n \to A$, the function $(g_0,\dots,g_n) \mapsto \rho(g_0)\,f(g_1,\dots,g_n) + \sum_{k=0}^{n}
-- (-1)^{k+1} f\bigl(g_0,\dots,g_{k-1},\,g_k g_{k+1},\,g_{k+2},\dots,g_n\bigr)$ (where for $k=n$ the
-- term is $(-1)^{n+1} f(g_0,\dots,g_{n-1})$) is again locally constant.
-- Score: (0 - incorrect, 1 - partially correct, 2 - correct)
-- Comment:
/-- The standard inhomogeneous coboundary formula preserves local constancy, provided
the action `ρ : G →* End(A)` has open point stabilizers.

The formula below is the standard one (identical to Mathlib's
`groupCohomology.inhomogeneousCochains` differential), with all three parts of the
informal formula
`(df)(g₀,…,gₙ) = ρ(g₀)f(g₁,…,gₙ) + ∑_{k=1}^{n} (-1)^k f(g₀,…,g_{k-1}g_k,…,gₙ)
 + (-1)^{n+1} f(g₀,…,g_{n-1})`
present: the first term is `ρ (g 0) (f fun i => g i.succ)`; the sum over `k : Fin (n+1)`
encodes BOTH the middle alternating sum and the final term, after the index shift
`k ↦ k+1`: for `k < n`, `Fin.contractNth k (· * ·) g` is
`(g₀,…,g_{k}·g_{k+1},…,gₙ)` with sign `(-1)^(k+1)` — i.e. the informal term of index
`k+1` — while for `k = n` (the last index), `Fin.contractNth n (· * ·) g` is
`(g₀,…,g_{n-1})` (no product occurs, the last entry is dropped), giving exactly the
final term with sign `(-1)^(n+1)`. -/
theorem contCoboundaryLocallyConstant {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] {A : Type*} [AddCommGroup A]
    (ρ : G →* AddMonoid.End A) (hρ : ∀ a : A, IsOpen {g : G | ρ g a = a})
    {n : ℕ} (f : contCochain G A n) :
    IsLocallyConstant fun g : Fin (n + 1) → G =>
      ρ (g 0) (f fun i => g i.succ)
        + ∑ k : Fin (n + 1),
            ((-1 : ℤ) ^ ((k : ℕ) + 1)) • f (Fin.contractNth k (· * ·) g) :=
  sorry


end

section
-- Natural language: Let $G$ be a topological group, $A$ an abelian group, and $\rho : G \to
-- \operatorname{End}(A)$ a group homomorphism such that for every $a \in A$ the stabilizer $\{g \in
-- G \mid \rho(g)(a) = a\}$ is open. For each $n \in \mathbb{N}$, the coboundary map $d^n : C^n(G,A)
-- \to C^{n+1}(G,A)$ is defined by
-- $$(df)(g_0,\dots,g_n) = \rho(g_0) f(g_1,\dots,g_n) + \sum_{k=1}^{n} (-1)^k
-- f(g_0,\dots,g_{k-1}g_k,\dots,g_n) + (-1)^{n+1} f(g_0,\dots,g_{n-1}),$$
-- where $f \in C^n(G,A)$ is a locally constant function $G^n \to A$ and $g_0,\dots,g_n \in G$.
-- Score: (0 - incorrect, 1 - partially correct, 2 - correct)
-- Comment:
/-- The coboundary map `d^n : C^n(G,A) → C^{n+1}(G,A)` of the continuous inhomogeneous
cochain complex, for a topological group `G` and a discrete `G`-module `(A, ρ)` with
open point stabilizers. The formula is the standard inhomogeneous one (see
`contCoboundaryLocallyConstant` for the term-by-term correspondence with
`(df)(g₀,…,gₙ) = ρ(g₀)f(g₁,…,gₙ) + ∑_{k=1}^n (-1)^k f(g₀,…,g_{k-1}g_k,…,gₙ)
 + (-1)^{n+1} f(g₀,…,g_{n-1})`). -/
noncomputable def contCoboundary {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] {A : Type*} [AddCommGroup A]
    (ρ : G →* AddMonoid.End A) (hρ : ∀ a : A, IsOpen {g : G | ρ g a = a})
    (n : ℕ) (f : contCochain G A n) : contCochain G A (n + 1) :=
  ⟨fun g : Fin (n + 1) → G =>
      ρ (g 0) (f fun i => g i.succ)
        + ∑ k : Fin (n + 1),
            ((-1 : ℤ) ^ ((k : ℕ) + 1)) • f (Fin.contractNth k (· * ·) g),
   contCoboundaryLocallyConstant ρ hρ f⟩


end

section
-- Natural language: Let $G$ be a topological group, $A$ a discrete $G$-module with representation
-- $\rho : G \to \operatorname{AddMonoidEnd}(A)$ such that for every $a \in A$ the stabilizer $\{g
-- \in G \mid \rho(g)(a) = a\}$ is open. For each $n \in \mathbb{N}$, the coboundary map $d^n :
-- C^n(G,A) \to C^{n+1}(G,A)$ is additive: $d^n(f+g) = d^n f + d^n g$ for all $f,g \in C^n(G,A)$,
-- $d^n(0) = 0$, and $d^{n+1}(d^n f) = 0$ for every $f \in C^n(G,A)$.
-- Score: (0 - incorrect, 1 - partially correct, 2 - correct)
-- Comment:
/-- The coboundary map is additive, kills `0`, and squares to zero. -/
theorem contCoboundaryAdd {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] {A : Type*} [AddCommGroup A]
    (ρ : G →* AddMonoid.End A) (hρ : ∀ a : A, IsOpen {g : G | ρ g a = a})
    (n : ℕ) :
    (∀ f g : contCochain G A n,
        contCoboundary ρ hρ n (f + g) = contCoboundary ρ hρ n f + contCoboundary ρ hρ n g)
      ∧ contCoboundary ρ hρ n (0 : contCochain G A n) = 0
      ∧ ∀ f : contCochain G A n,
          contCoboundary ρ hρ (n + 1) (contCoboundary ρ hρ n f) = 0 :=
  sorry


end

section
-- Natural language: Let $G$ be a group equipped with a topology making it a topological group, let
-- $A$ be an additive abelian group, let $\rho : G \to \operatorname{End}_{\mathbb{Z}}(A)$ be a
-- group homomorphism such that for every $a \in A$ the set $\{g \in G \mid \rho(g)(a) = a\}$ is
-- open, and let $n \in \mathbb{N}$.
-- The set $\{f \in C^n(G,A) \mid d^n f = 0\}$, where $d^n$ denotes the continuous inhomogeneous
-- coboundary map $\operatorname{contCoboundary}(\rho, h_\rho, n)$, is an additive subgroup of
-- $C^n(G,A)$; it is called the subgroup of continuous $n$-cocycles and denoted $Z^n(G,A)$.
-- Score: (0 - incorrect, 1 - partially correct, 2 - correct)
-- Comment:
/-- The subgroup `Z^n(G,A) ⊆ C^n(G,A)` of continuous `n`-cocycles: those `f` with
`d^n f = 0`. -/
noncomputable def contCocycles {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] {A : Type*} [AddCommGroup A]
    (ρ : G →* AddMonoid.End A) (hρ : ∀ a : A, IsOpen {g : G | ρ g a = a})
    (n : ℕ) : AddSubgroup (contCochain G A n) where
  carrier := {f | contCoboundary ρ hρ n f = 0}
  zero_mem' := (contCoboundaryAdd ρ hρ n).2.1
  add_mem' := by
    intro a b ha hb
    have h := (contCoboundaryAdd ρ hρ n).1 a b
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [h, ha, hb, add_zero]
  neg_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at ha ⊢
    have h := (contCoboundaryAdd ρ hρ n).1 (-a) a
    rw [neg_add_cancel, (contCoboundaryAdd ρ hρ n).2.1, ha, add_zero] at h
    exact h.symm


end

section
-- Natural language: For a topological group $G$ and a discrete $G$-module $(A,\rho)$ with open
-- point stabilizers (i.e., for every $a\in A$ the set $\{g\in G\mid \rho(g)a=a\}$ is open), the
-- subgroup $B^n(G,A)\subseteq C^n(G,A)$ of continuous $n$-coboundaries is defined by $B^0=0$ and,
-- for $n+1$, $B^{n+1}$ is the additive subgroup of $C^{n+1}(G,A)$ generated by the set-theoretic
-- image of the coboundary map $d^n\colon C^n(G,A)\to C^{n+1}(G,A)$.
-- Score: (0 - incorrect, 1 - partially correct, 2 - correct)
-- Comment:
/-- The subgroup `B^n(G,A) ⊆ C^n(G,A)` of continuous `n`-coboundaries: `B^0 = 0`, and
`B^{n+1}` is the subgroup generated by the image of `d^n` (equal to the set-theoretic
image, since `d` is additive by `contCoboundaryAdd`). -/
noncomputable def contCoboundaries {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] {A : Type*} [AddCommGroup A]
    (ρ : G →* AddMonoid.End A) (hρ : ∀ a : A, IsOpen {g : G | ρ g a = a}) :
    (n : ℕ) → AddSubgroup (contCochain G A n)
  | 0 => ⊥
  | n + 1 => AddSubgroup.closure (Set.range (contCoboundary ρ hρ n))


end

section
-- Natural language: For a topological group $G$ and a discrete $G$-module $(A,\rho)$ (i.e., an
-- abelian group $A$ with a group homomorphism $\rho:G\to\operatorname{End}(A)$ such that for every
-- $a\in A$ the stabilizer $\{g\in G\mid \rho(g)(a)=a\}$ is open), the continuous cohomology group
-- $H^n(G,A)$ is defined for each $n\in\mathbb{N}$ as the quotient of the subgroup $Z^n(G,A)$ of
-- continuous $n$-cocycles by the subgroup $B^n(G,A)$ of continuous $n$-coboundaries, where
-- $Z^n(G,A)$ consists of those continuous inhomogeneous $n$-cochains $f$ whose coboundary $d^n f$
-- vanishes, and $B^n(G,A)$ is the additive subgroup of $C^n(G,A)$ generated by the image of the
-- coboundary operator $d^{n-1}$ (with the convention $B^0(G,A)=0$).
-- Score: (0 - incorrect, 1 - partially correct, 2 - correct)
-- Comment:
/-- The continuous cohomology group `H^n(G,A) = Z^n(G,A)/B^n(G,A)` of a topological
group `G` with coefficients in a discrete `G`-module `(A, ρ)` (action with open point
stabilizers), computed from the complex of continuous inhomogeneous cochains. -/
noncomputable abbrev contCohomologyGrp {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] {A : Type*} [AddCommGroup A]
    (ρ : G →* AddMonoid.End A) (hρ : ∀ a : A, IsOpen {g : G | ρ g a = a})
    (n : ℕ) : Type _ :=
  ↥(contCocycles ρ hρ n) ⧸
    (contCoboundaries ρ hρ n).addSubgroupOf (contCocycles ρ hρ n)


end

section
-- Natural language: Let $G$ be a topological group, $A$, $B$, $C$ abelian groups, $\rho_B : G \to
-- \operatorname{End}(B)$ an action such that for every $b \in B$ the set $\{g \in G \mid \rho_B(g)
-- b = b\}$ is open, and $\phi : A \to B \to C$ a bi-additive pairing. For any $i, j \in \mathbb{N}$
-- and any locally constant functions $f : G^i \to A$ and $g : G^j \to B$, the function
-- $$(x_1,\dots,x_{i+j}) \mapsto \phi\big(f(x_1,\dots,x_i)\big)\big(\rho_B(x_1 \cdots x_i)\,
-- g(x_{i+1},\dots,x_{i+j})\big)$$
-- is locally constant on $G^{i+j}$.
-- Score: (0 - incorrect, 1 - partially correct, 2 - correct)
-- Comment:
/-- The cup-product formula
`(f ∪ g)(g₁,…,g_{i+j}) = φ(f(g₁,…,g_i))(ρ_B(g₁⋯g_i) g(g_{i+1},…,g_{i+j}))`
is locally constant, for locally constant `f, g`, a bi-additive pairing `φ : A → B → C`,
and an action `ρ_B` on `B` with open point stabilizers. (The ordered product `g₁⋯g_i`
is taken as a list product.) -/
theorem contCupLocallyConstant {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] {A B C : Type*} [AddCommGroup A] [AddCommGroup B]
    [AddCommGroup C]
    (ρB : G →* AddMonoid.End B) (hρB : ∀ b : B, IsOpen {g : G | ρB g b = b})
    (φ : A →+ B →+ C) {i j : ℕ}
    (f : contCochain G A i) (g : contCochain G B j) :
    IsLocallyConstant fun x : Fin (i + j) → G =>
      φ (f fun k => x (Fin.castAdd j k))
        (ρB (List.ofFn fun k : Fin i => x (Fin.castAdd j k)).prod
          (g fun k => x (Fin.natAdd i k))) :=
  sorry


end

section
-- Natural language: Let $G$ be a topological group, $A$, $B$, $C$ abelian groups, $\rho_B : G \to
-- \operatorname{End}_{\mathbb{Z}}(B)$ an action with open point stabilizers (i.e. for every $b \in
-- B$ the set $\{g \in G \mid \rho_B(g)(b) = b\}$ is open), and $\phi : A \to
-- \operatorname{Hom}_{\mathbb{Z}}(B, C)$ a bi-additive pairing. For any $i, j \in \mathbb{N}$, any
-- locally constant $f : G^i \to A$ and $g : G^j \to B$, the cochain-level cup product $f \cup g :
-- G^{i+j} \to C$ is defined by
-- \[
-- (f \cup g)(g_1,\dots,g_{i+j}) = \phi\big(f(g_1,\dots,g_i)\big)\big(\rho_B(g_1\cdots g_i)\,
-- g(g_{i+1},\dots,g_{i+j})\big),
-- \]
-- where the ordered product $g_1\cdots g_i$ is taken as the product of the list.
-- Score: (0 - incorrect, 1 - partially correct, 2 - correct)
-- Comment:
/-- The cochain-level cup product `∪ : C^i(G,A) × C^j(G,B) → C^{i+j}(G,C)` associated
to a bi-additive pairing `φ : A → B → C` (with `ρ_B` an action on `B` with open point
stabilizers):
`(f ∪ g)(g₁,…,g_{i+j}) = φ(f(g₁,…,g_i))(ρ_B(g₁⋯g_i) g(g_{i+1},…,g_{i+j}))`. -/
noncomputable def contCupProduct {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] {A B C : Type*} [AddCommGroup A] [AddCommGroup B]
    [AddCommGroup C]
    (ρB : G →* AddMonoid.End B) (hρB : ∀ b : B, IsOpen {g : G | ρB g b = b})
    (φ : A →+ B →+ C) {i j : ℕ}
    (f : contCochain G A i) (g : contCochain G B j) : contCochain G C (i + j) :=
  ⟨fun x : Fin (i + j) → G =>
      φ (f fun k => x (Fin.castAdd j k))
        (ρB (List.ofFn fun k : Fin i => x (Fin.castAdd j k)).prod
          (g fun k => x (Fin.natAdd i k))),
   contCupLocallyConstant ρB hρB φ f g⟩


end

section
-- Natural language: Let $G$ be a topological group, let $A$, $B$, $C$ be additive abelian groups
-- equipped with actions $\rho_A : G \to \operatorname{End}(A)$, $\rho_B : G \to
-- \operatorname{End}(B)$, $\rho_C : G \to \operatorname{End}(C)$ such that for every $a\in A$,
-- $b\in B$, $c\in C$ the stabilizer $\{g\in G \mid \rho_A(g)a=a\}$, $\{g\in G \mid \rho_B(g)b=b\}$,
-- $\{g\in G \mid \rho_C(g)c=c\}$ is open, and let $\phi : A \to B \to C$ be a bi-additive
-- $G$-equivariant pairing, i.e. $\phi(\rho_A(g)a)(\rho_B(g)b) = \rho_C(g)(\phi(a)(b))$ for all
-- $g\in G$, $a\in A$, $b\in B$. Then for any $i,j\in\mathbb{N}$ the cochain-level cup product
-- $\operatorname{contCupProduct}_{\rho_B,\phi}$ is bi-additive: for all $f,f' \in C^i(G,A)$ and
-- $g,g' \in C^j(G,B)$ we have $\operatorname{contCupProduct}_{\rho_B,\phi}(f+f',g) =
-- \operatorname{contCupProduct}_{\rho_B,\phi}(f,g) +
-- \operatorname{contCupProduct}_{\rho_B,\phi}(f',g)$ and
-- $\operatorname{contCupProduct}_{\rho_B,\phi}(f,g+g') =
-- \operatorname{contCupProduct}_{\rho_B,\phi}(f,g) +
-- \operatorname{contCupProduct}_{\rho_B,\phi}(f,g')$; moreover, if $f$ is a cocycle in $Z^i(G,A)$
-- and $g$ is a cocycle in $Z^j(G,B)$ then $\operatorname{contCupProduct}_{\rho_B,\phi}(f,g)$ is a
-- cocycle in $Z^{i+j}(G,C)$; and if $f$ is a cocycle and $g$ is a coboundary in $B^j(G,B)$, or $f$
-- is a coboundary in $B^i(G,A)$ and $g$ is a cocycle, then
-- $\operatorname{contCupProduct}_{\rho_B,\phi}(f,g)$ is a coboundary in $B^{i+j}(G,C)$.
-- Consequently, there exists a map $\cup : H^i(G,A) \times H^j(G,B) \to H^{i+j}(G,C)$ such that for
-- every $f \in Z^i(G,A)$ and $g \in Z^j(G,B)$ with
-- $\operatorname{contCupProduct}_{\rho_B,\phi}(f,g) \in Z^{i+j}(G,C)$, the cup product of the
-- cohomology classes of $f$ and $g$ equals the class of
-- $\operatorname{contCupProduct}_{\rho_B,\phi}(f,g)$.
-- Score: (0 - incorrect, 1 - partially correct, 2 - correct)
-- Comment:
/-- For a bi-additive `G`-equivariant pairing `φ : A → B → C` (all actions with open
stabilizers), the cochain-level cup product is bi-additive, maps cocycle × cocycle to
cocycles, maps cocycle × coboundary and coboundary × cocycle to coboundaries, and hence
descends to a well-defined bi-additive pairing on cohomology classes. -/
theorem contCupCocycle {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] {A B C : Type*} [AddCommGroup A] [AddCommGroup B]
    [AddCommGroup C]
    (ρA : G →* AddMonoid.End A) (hρA : ∀ a : A, IsOpen {g : G | ρA g a = a})
    (ρB : G →* AddMonoid.End B) (hρB : ∀ b : B, IsOpen {g : G | ρB g b = b})
    (ρC : G →* AddMonoid.End C) (hρC : ∀ c : C, IsOpen {g : G | ρC g c = c})
    (φ : A →+ B →+ C)
    (hφ : ∀ (g : G) (a : A) (b : B), φ (ρA g a) (ρB g b) = ρC g (φ a b))
    {i j : ℕ} :
    (∀ (f f' : contCochain G A i) (g : contCochain G B j),
        contCupProduct ρB hρB φ (f + f') g
          = contCupProduct ρB hρB φ f g + contCupProduct ρB hρB φ f' g)
      ∧ (∀ (f : contCochain G A i) (g g' : contCochain G B j),
          contCupProduct ρB hρB φ f (g + g')
            = contCupProduct ρB hρB φ f g + contCupProduct ρB hρB φ f g')
      ∧ (∀ f ∈ contCocycles ρA hρA i, ∀ g ∈ contCocycles ρB hρB j,
          contCupProduct ρB hρB φ f g ∈ contCocycles ρC hρC (i + j))
      ∧ (∀ f ∈ contCocycles ρA hρA i, ∀ g ∈ contCoboundaries ρB hρB j,
          contCupProduct ρB hρB φ f g ∈ contCoboundaries ρC hρC (i + j))
      ∧ (∀ f ∈ contCoboundaries ρA hρA i, ∀ g ∈ contCocycles ρB hρB j,
          contCupProduct ρB hρB φ f g ∈ contCoboundaries ρC hρC (i + j))
      ∧ ∃ cup : contCohomologyGrp ρA hρA i → contCohomologyGrp ρB hρB j →
            contCohomologyGrp ρC hρC (i + j),
          ∀ (f : ↥(contCocycles ρA hρA i)) (g : ↥(contCocycles ρB hρB j))
            (h : contCupProduct ρB hρB φ ↑f ↑g ∈ contCocycles ρC hρC (i + j)),
            cup (QuotientAddGroup.mk f) (QuotientAddGroup.mk g)
              = QuotientAddGroup.mk ⟨contCupProduct ρB hρB φ ↑f ↑g, h⟩ :=
  sorry


end

section
-- Natural language: Given a topological group $G$ (with a group structure and a topology making it
-- a topological group), discrete $G$-modules $A$, $B$, $C$ (with actions $\rho_A$, $\rho_B$,
-- $\rho_C$ having open point stabilizers), and a bi-additive $G$-equivariant pairing $\phi : A \to
-- B \to C$ (so that $\phi(\rho_A(g)(a))(\rho_B(g)(b)) = \rho_C(g)(\phi(a)(b))$ for all $g\in G$,
-- $a\in A$, $b\in B$), the cohomology-level cup product $H^i(G,A) \times H^j(G,B) \to H^{i+j}(G,C)$
-- is defined by descending the cochain-level cup product to cohomology classes.
-- Score: (0 - incorrect, 1 - partially correct, 2 - correct)
-- Comment:
/-- The cohomology-level cup product `H^i(G,A) × H^j(G,B) → H^{i+j}(G,C)` associated to
a bi-additive `G`-equivariant pairing `φ : A → B → C` (all actions with open
stabilizers): the descent of the cochain-level cup product to cohomology classes,
obtained from the well-definedness clause of `contCupCocycle`. -/
noncomputable def contCohomologyCup {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] {A B C : Type*} [AddCommGroup A] [AddCommGroup B]
    [AddCommGroup C]
    (ρA : G →* AddMonoid.End A) (hρA : ∀ a : A, IsOpen {g : G | ρA g a = a})
    (ρB : G →* AddMonoid.End B) (hρB : ∀ b : B, IsOpen {g : G | ρB g b = b})
    (ρC : G →* AddMonoid.End C) (hρC : ∀ c : C, IsOpen {g : G | ρC g c = c})
    (φ : A →+ B →+ C)
    (hφ : ∀ (g : G) (a : A) (b : B), φ (ρA g a) (ρB g b) = ρC g (φ a b))
    (i j : ℕ) :
    contCohomologyGrp ρA hρA i → contCohomologyGrp ρB hρB j →
      contCohomologyGrp ρC hρC (i + j) :=
  Classical.choose
    (contCupCocycle ρA hρA ρB hρB ρC hρC φ hφ (i := i) (j := j)).2.2.2.2.2


end

section
-- Natural language: Let $F$ be a field, $K$ a number field, $M$ an $F$-vector space, and $P$ a
-- Poitou–Tate setup for $F$, $K$, $M$. For a finite place $v$ of $K$, the *local evaluation
-- pairing* is the additive group homomorphism
-- \[
-- M^* \longrightarrow \operatorname{Hom}_{\mathbb{Z}}\!\bigl(M, \overline{K_v}^{\times}\bigr)
-- \]
-- sending $x^* \in M^* = \operatorname{Hom}_{\mathbb{Z}}(M, K_S^{\times})$ to the composition $m
-- \mapsto \iota_v(x^*(m))$, where $\iota_v : K_S^{\times} \hookrightarrow \overline{K_v}^{\times}$
-- is the coefficient homomorphism induced by the chosen embedding of the algebraic closure into the
-- $v$-adic completion.
-- Score: (0 - incorrect, 1 - partially correct, 2 - correct)
-- Comment:
/-- The local evaluation pairing `M^* × M → K̄_v^×`: `(x^*, m) ↦ ι_v(x^*(m))`, the
evaluation `M^* = Hom_ℤ(M, K_S^×) → K_S^×` followed by the chosen embedding into
`K̄_v^×`; bi-additive (curried), and `G_v`-equivariant (see the companion lemma). -/
noncomputable def localEvalPairing {F K M : Type} [Field F] [Fintype F] [Field K]
    [NumberField K] [AddCommGroup M] [Module F M] (P : PoitouTateSetup F K M)
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    dualModule P →+
      (M →+ Additive
        (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v))ˣ) :=
  AddMonoidHom.mk'
    (fun x : dualModule P => (coeffKStoLocal K P.S v).comp x)
    (fun x y => by ext m; simp)


end

section
-- Natural language: Let $K$ be a field with a number field structure, and let $S$ be a set of
-- height‑one primes of the ring of integers of $K$. Then the extension $K_S/K$ is normal, where
-- $K_S$ denotes the fixed field of the $S$-ramification subgroup of the absolute Galois group $G_K$
-- acting on the algebraic closure $\overline{K}$.
-- Score: (0 - incorrect, 1 - partially correct, 2 - correct)
-- Comment:
/-- The extension `K_S/K` is normal, being the fixed field of a normal subgroup of
`G_K` acting on `K̄`. -/
theorem sMaximalExtensionNormal (K : Type*) [Field K] [NumberField K]
    (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) :
    Normal K ↥(sMaximalExtension K S) :=
  sorry


end

section
-- Natural language: For any number field $K$ and any set $S$ of height-one primes of the ring of
-- integers of $K$, the extension $K_S/K$ is normal.
-- Score: (0 - incorrect, 1 - partially correct, 2 - correct)
-- Comment:
/-- The normality of `K_S/K`, registered as a typeclass instance so that restriction of
automorphisms of `K̄` to `K_S` (via `AlgEquiv.restrictNormalHom`) is available. -/
instance sMaximalExtensionNormalInst (K : Type*) [Field K] [NumberField K]
    (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) :
    Normal K ↥(sMaximalExtension K S) :=
  sMaximalExtensionNormal K S


end

section
-- Natural language: Let $K$ be a number field and $S$ a set of finite primes of $K$.
-- The $S$-ramification subgroup $N_S$ is contained in the kernel of the restriction homomorphism
-- $G_K \to \operatorname{Gal}(K_S/K)$; that is, every element of $N_S$ restricts to the identity on
-- $K_S = \overline{K}^{N_S}$.
-- Score: (0 - incorrect, 1 - partially correct, 2 - correct)
-- Comment:
/-- The `S`-ramification subgroup `N_S` is contained in the kernel of the restriction
homomorphism `G_K → Gal(K_S/K)`: every element of `N_S` restricts to the identity on
`K_S = K̄^{N_S}`. -/
theorem sRamifiedActsTriviallyOnKS (K : Type*) [Field K] [NumberField K]
    (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) :
    sRamifiedSubgroup K S
      ≤ (AlgEquiv.restrictNormalHom (F := K) (K₁ := AlgebraicClosure K)
          ↥(sMaximalExtension K S)).ker :=
  sorry


end

section
-- Natural language: Let $K$ be a number field and $S$ a set of height‑one primes of the ring of
-- integers of $K$.
-- The *canonical action of $G_S = G_K/N_S$ on $K_S$* is the homomorphism
-- $G_S \to \operatorname{Gal}(K_S/K)$ obtained by descending the restriction homomorphism
-- $G_K \to \operatorname{Gal}(K_S/K)$ (restriction of automorphisms of $\overline{K}$ to the normal
-- subextension $K_S$) through the quotient by $N_S$.
-- Score: (0 - incorrect, 1 - partially correct, 2 - correct)
-- Comment:
/-- The canonical action of `G_S = G_K/N_S` on `K_S`: the homomorphism
`G_S → Gal(K_S/K)` obtained by descending the restriction homomorphism
`G_K → Gal(K_S/K)` through the quotient by `N_S` (which acts trivially on `K_S`). -/
noncomputable def sGaloisGroupAction (K : Type*) [Field K] [NumberField K]
    (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) :
    sGaloisGroup K S →* (↥(sMaximalExtension K S) ≃ₐ[K] ↥(sMaximalExtension K S)) :=
  QuotientGroup.lift (sRamifiedSubgroup K S)
    (AlgEquiv.restrictNormalHom (F := K) (K₁ := AlgebraicClosure K)
      ↥(sMaximalExtension K S))
    (sRamifiedActsTriviallyOnKS K S)


end

section
-- Natural language: Let $K$ be a number field, let $S$ be a set of height‑one primes of the ring of
-- integers of $K$, and let $G_S$ be the Galois group of the maximal extension of $K$ unramified
-- outside $S$. The canonical action of $G_S$ on the maximal extension $K_S$ of $K$ unramified
-- outside $S$ induces, by restriction to units, a monoid homomorphism $G_S \to
-- \operatorname{End}(K_S^\times)$; composing with the natural isomorphism
-- $\operatorname{End}(K_S^\times) \cong \operatorname{End}_{\operatorname{Add}}(K_S^\times)$ (which
-- views the unit group as an additive group) yields a monoid homomorphism $G_S \to
-- \operatorname{End}_{\operatorname{Add}}(K_S^\times)$.
-- Score: (0 - incorrect, 1 - partially correct, 2 - correct)
-- Comment:
/-- The action of `G_S` on the (additivised) unit group `K_S^×`, as a monoid
homomorphism `G_S →* End(Additive K_S^×)`, induced by the canonical action of `G_S` on
`K_S` (via the Galois action on units). -/
noncomputable def sUnitsRep (K : Type*) [Field K] [NumberField K]
    (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) :
    sGaloisGroup K S →* AddMonoid.End (Additive (↥(sMaximalExtension K S))ˣ) :=
  MonoidHom.comp
    { toFun := fun f : Monoid.End (↥(sMaximalExtension K S))ˣ =>
        (MonoidHom.toAdditive f : AddMonoid.End (Additive (↥(sMaximalExtension K S))ˣ))
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
    (MonoidHom.comp
      (MulDistribMulAction.toMonoidEnd
        (↥(sMaximalExtension K S) ≃ₐ[K] ↥(sMaximalExtension K S))
        (↥(sMaximalExtension K S))ˣ)
      (sGaloisGroupAction K S))


end

section
-- Natural language: Let $F$ be a field, $K$ a number field, and $M$ an additive commutative group
-- equipped with an $F$-module structure. Let $P$ be a Poitou–Tate setup for $F$, $K$, $M$, and let
-- $S$ be the set of places associated to $P$. Write $G_S$ for the Galois group of the maximal
-- extension of $K$ unramified outside $S$, and $K_S^\times$ for the unit group of that maximal
-- extension. The dual module $M^* = \operatorname{Hom}_{\mathbb{Z}}(M, K_S^\times)$ is the abelian
-- group of additive-group homomorphisms from $M$ to the additive group underlying $K_S^\times$. The
-- action of $G_S$ on $M^*$ given by $(g \cdot x^*)(x) = g\big(x^*(g^{-1}x)\big)$ defines a monoid
-- homomorphism $G_S \to \operatorname{End}(M^*)$.
-- Score: (0 - incorrect, 1 - partially correct, 2 - correct)
-- Comment:
/-- The action of `G_S` on the dual module `M^* = Hom_ℤ(M, K_S^×)`, given by
`(g·x^*)(x) = g(x^*(g⁻¹x))`, as a monoid homomorphism `G_S →* End(M^*)`. -/
noncomputable def dualModuleRep {F K M : Type} [Field F] [Fintype F] [Field K]
    [NumberField K] [AddCommGroup M] [Module F M] (P : PoitouTateSetup F K M) :
    sGaloisGroup K P.S →* AddMonoid.End (dualModule P) where
  toFun := fun g =>
    AddMonoidHom.mk'
      (fun x : dualModule P =>
        ((sUnitsRep K P.S g).comp x).comp (setupRho P g⁻¹ : M →+ M))
      (by
        intro x y
        ext m
        simp)
  map_one' := by
    refine AddMonoidHom.ext fun x => ?_
    refine AddMonoidHom.ext fun m => ?_
    change (sUnitsRep K P.S 1) (x ((setupRho P (1 : sGaloisGroup K P.S)⁻¹) m)) = x m
    rw [inv_one, map_one, map_one]
    rfl
  map_mul' := by
    intro g h
    refine AddMonoidHom.ext fun x => ?_
    refine AddMonoidHom.ext fun m => ?_
    change (sUnitsRep K P.S (g * h)) (x ((setupRho P (g * h)⁻¹) m))
        = (sUnitsRep K P.S g)
            ((((sUnitsRep K P.S h).comp x).comp ((setupRho P) h⁻¹ : M →+ M))
              ((setupRho P g⁻¹) m))
    rw [mul_inv_rev, map_mul, map_mul]
    rfl


end

section
-- Natural language: Let $K$ be a number field, let $v$ be a height‑one prime of the ring of
-- integers of $K$, and let $K_v$ denote the $v$-adic completion of $K$.
-- The *local Bar‐units representation* is the monoid homomorphism
-- 
-- \[
-- G_v \longrightarrow \operatorname{End}\bigl(\overline{K_v}^{\times}\bigr)
-- \]
-- 
-- obtained by composing the map that sends a monoid endomorphism of $\overline{K_v}^{\times}$ to
-- the corresponding additive endomorphism of the additivised unit group $\overline{K_v}^{\times}$
-- (i.e. the natural identification $\operatorname{End}_{\mathsf{Mon}}(\overline{K_v}^{\times}) \to
-- \operatorname{End}_{\mathsf{Ab}}(\overline{K_v}^{\times})$ induced by the additive–multiplicative
-- translation) with the canonical action of the absolute Galois group $G_v =
-- \operatorname{Gal}(\overline{K_v}/K_v)$ on the unit group $\overline{K_v}^{\times}$ by
-- multiplication of elements.
-- Score: (0 - incorrect, 1 - partially correct, 2 - correct)
-- Comment:
/-- The natural action of the local Galois group `G_v = Gal(K̄_v/K_v)` on the
(additivised) unit group `K̄_v^×` of the algebraic closure of the completion `K_v`, as
a monoid homomorphism `G_v →* End(Additive K̄_v^×)`. -/
noncomputable def localBarUnitsRep (K : Type*) [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    Field.absoluteGaloisGroup (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v)
      →* AddMonoid.End
        (Additive
          (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v))ˣ) :=
  MonoidHom.comp
    { toFun := fun f : Monoid.End
          (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v))ˣ =>
        (MonoidHom.toAdditive f :
          AddMonoid.End
            (Additive
              (AlgebraicClosure
                (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v))ˣ))
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
    (MulDistribMulAction.toMonoidEnd
      (Field.absoluteGaloisGroup (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v))
      (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v))ˣ)


end

section
-- Natural language: Let $K$ be a number field, $S$ a set of finite places of $K$, and $v$ a finite
-- place of $K$. For every $\sigma \in G_v = \operatorname{Gal}(\overline{K_v}/K_v)$ and every $x
-- \in K_S^\times$ (viewed as an element of the additive group of units), applying $\sigma$ to the
-- image of $x$ under the coefficient homomorphism $K_S^\times \to \overline{K_v}^\times$ yields the
-- same as applying the image of $\sigma$ under the local-to-global map $G_v \to G_S$ to $x$ and
-- then applying the coefficient homomorphism.
-- Score: (0 - incorrect, 1 - partially correct, 2 - correct)
-- Comment:
/-- The coefficient homomorphism `K_S^× → K̄_v^×` induced by `ι_v` is equivariant: for
every `σ ∈ G_v` and `x ∈ K_S^×`, applying `σ` on `K̄_v^×` after the map agrees with
applying the image of `σ` under the local-to-global map `G_v → G_S` before the map. -/
theorem coeffKStoLocalEquivariant (K : Type*) [Field K] [NumberField K]
    (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    ∀ (σ : Field.absoluteGaloisGroup
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v))
      (x : Additive (↥(sMaximalExtension K S))ˣ),
      localBarUnitsRep K v σ (coeffKStoLocal K S v x)
        = coeffKStoLocal K S v (sUnitsRep K S (decompositionMap K S v σ) x) :=
  sorry


end

section
-- Natural language: For all fields $F$ and $K$ with $F$ finite and $K$ a number field, every
-- $F$-module $M$, every Poitou–Tate setup $P$ for $F,K,M$, every prime $v$ of the ring of integers
-- of $K$, every $\sigma$ in the absolute Galois group $G_v$ of the $v$-adic completion of $K$,
-- every $x^*$ in the dual module $M^* = \operatorname{Hom}_{\mathbb{Z}}(M, K_S^\times)$, and every
-- $m$ in $M$, the local evaluation pairing $\langle x^*, m\rangle_v \in \overline{K_v}^{\times}$
-- satisfies $\langle \sigma \cdot x^*, \sigma \cdot m\rangle_v = \sigma \cdot \langle x^*,
-- m\rangle_v$, where $\sigma \cdot x^*$ is the action of $\sigma$ on $M^*$ via the decomposition
-- map $G_v \to G_S$ and the dual module representation, $\sigma \cdot m$ is the action of $\sigma$
-- on $M$ via the same decomposition map and the $G_S$-action, and $\sigma \cdot (\cdot)$ on
-- $\overline{K_v}^{\times}$ is the natural Galois action.
-- Score: (0 - incorrect, 1 - partially correct, 2 - correct)
-- Comment:
/-- The local evaluation pairing `M^* × M → K̄_v^×` is `G_v`-equivariant: for all
`σ ∈ G_v`, `x^* ∈ M^*`, `m ∈ M`, one has `⟨σ·x^*, σ·m⟩ = σ·⟨x^*, m⟩`, where the local
actions on `M^*` and `M` are via the local-to-global map and the action on `K̄_v^×` is
the natural one. -/
theorem localEvalPairingEquivariant {F K M : Type} [Field F] [Fintype F] [Field K]
    [NumberField K] [AddCommGroup M] [Module F M] (P : PoitouTateSetup F K M)
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    ∀ (σ : Field.absoluteGaloisGroup
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v))
      (x : dualModule P) (m : M),
      localEvalPairing P v (dualModuleRep P (decompositionMap K P.S v σ) x)
          (localRho P v σ m)
        = localBarUnitsRep K v σ (localEvalPairing P v x m) :=
  sorry


end

section
-- Natural language: The group $\mathbb{Q}/\mathbb{Z}$ is defined to be the quotient $\mathbb{Q} /
-- \langle 1 \rangle$ of the additive group of rationals by the subgroup generated by $1$.
-- Score: (0 - incorrect, 1 - partially correct, 2 - correct)
-- Comment:
/-- The group `ℚ/ℤ`, realised as the quotient of the additive rationals by the subgroup
generated by `1`. It is the target of all duality pairings and invariant maps; for an
abelian group `A`, the dual `A^∨` denotes `A →+ ratCircle`. -/
abbrev ratCircle : Type :=
  ℚ ⧸ AddSubgroup.zmultiples (1 : ℚ)


end

section
-- Natural language: The map $s : \mathbb{Q}/\mathbb{Z} \to \mathbb{Q}$ is defined by sending a
-- class $x$ to the fractional part $\operatorname{Int.fract}(q)$ of any representative $q$ of $x$
-- (the fractional part is constant on $\mathbb{Z}$-cosets, so the choice of representative is
-- immaterial).
-- Score: (0 - incorrect, 1 - partially correct, 2 - correct)
-- Comment:
/-- The canonical set-theoretic section `s : ℚ/ℤ → ℚ` of the projection: each class is
sent to the fractional part of a(ny) representative — its unique representative in
`[0,1)` (the fractional part is constant on `ℤ`-cosets, so the choice of representative
is immaterial). -/
noncomputable def ratCircleSection : ratCircle → ℚ :=
  fun x => Int.fract (Quotient.out x)


end

section
-- Natural language: Let $G$ be a topological group, and let $f \in C^1(G,\mathbb{Q}/\mathbb{Z})$ be
-- a continuous $1$-cochain. The $\mathbb{Z}$-valued continuous $2$-cochain $\lfloor \delta f\rfloor
-- \in C^2(G,\mathbb{Z})$ is defined by
-- \[
-- \lfloor \delta f\rfloor(g_0,g_1) = \bigl\lfloor s(f(g_0)) + s(f(g_1)) - s(f(g_0g_1))\bigr\rfloor,
-- \]
-- where $s : \mathbb{Q}/\mathbb{Z} \to \mathbb{Q}$ is the canonical section sending each class to
-- its fractional part in $[0,1)$.
-- Score: (0 - incorrect, 1 - partially correct, 2 - correct)
-- Comment:
/-- For a continuous `1`-cochain `f ∈ C^1(G, ℚ/ℤ)`, the `ℤ`-valued continuous
`2`-cochain `⌊δf⌋`, where `δf(g₁,g₂) = s(f(g₁)) + s(f(g₂)) - s(f(g₁g₂))` with `s` the
canonical section. (When `f` is a cocycle, `δf` is integer-valued and `⌊δf⌋ = δf`; the
floor makes the `ℤ`-valued form total. Built from `LocallyConstant` combinators, so
local constancy is automatic.) -/
noncomputable def bocksteinCochain {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (f : contCochain G ratCircle 1) : contCochain G ℤ 2 :=
  LocallyConstant.map (fun q : ℚ => ⌊q⌋)
    ((f.comap ⟨fun g : Fin 2 → G => fun _ : Fin 1 => g 0,
        continuous_pi fun _ => continuous_apply 0⟩).map ratCircleSection
      + (f.comap ⟨fun g : Fin 2 → G => fun _ : Fin 1 => g 1,
          continuous_pi fun _ => continuous_apply 1⟩).map ratCircleSection
      - (f.comap ⟨fun g : Fin 2 → G => fun _ : Fin 1 => g 0 * g 1,
          continuous_pi fun _ =>
            (continuous_apply (0 : Fin 2)).mul (continuous_apply 1)⟩).map
          ratCircleSection)


end

section
-- Natural language: Let $G$ be a topological group, and let $hQZ$ and $hZ$ be the (trivially true)
-- open‑stabilizer witnesses for the trivial actions of $G$ on $\mathbb{Q}/\mathbb{Z}$ and
-- $\mathbb{Z}$ respectively. Then the following four statements hold:
-- 
-- 1. For every continuous $1$-cocycle $f \in Z^1(G,\mathbb{Q}/\mathbb{Z})$ and every $g \in G^2$,
-- the image in $\mathbb{Q}$ of the Bockstein cochain $\lfloor\delta f\rfloor(g)$ equals $s(f(g_0))
-- + s(f(g_1)) - s(f(g_0g_1))$, where $s$ is the canonical section $\mathbb{Q}/\mathbb{Z} \to
-- \mathbb{Q}$.
-- 2. For every continuous $1$-cocycle $f \in Z^1(G,\mathbb{Q}/\mathbb{Z})$, the Bockstein cochain
-- $\lfloor\delta f\rfloor$ is a continuous $2$-cocycle with values in $\mathbb{Z}$.
-- 3. For every pair of continuous $1$-cocycles $f,f' \in Z^1(G,\mathbb{Q}/\mathbb{Z})$ such that $f
-- - f'$ is a continuous $1$-coboundary, the difference $\lfloor\delta f\rfloor - \lfloor\delta
-- f'\rfloor$ is a continuous $2$-coboundary with values in $\mathbb{Z}$.
-- 4. For every pair of continuous $1$-cochains $f,f' \in C^1(G,\mathbb{Q}/\mathbb{Z})$, the cochain
-- $\lfloor\delta(f+f')\rfloor - (\lfloor\delta f\rfloor + \lfloor\delta f'\rfloor)$ is a continuous
-- $2$-coboundary with values in $\mathbb{Z}$.
-- Score: (0 - incorrect, 1 - partially correct, 2 - correct)
-- Comment:
/-- Properties of the `ℤ`-valued Bockstein cochain `⌊δf⌋` (see `bocksteinCochain`):
(1) on cocycles its values coincide (in `ℚ`) with
    `δf(g₁,g₂) = s(f(g₁)) + s(f(g₂)) - s(f(g₁g₂))` — i.e. `δf` is integer-valued;
(2) it sends `1`-cocycles to `2`-cocycles;
(3) if two cocycles differ by a coboundary (i.e. represent the same class in `H^1`),
    their Bockstein cochains differ by a coboundary (equal classes in `H^2`);
(4) `⌊δ(f+f')⌋ - (⌊δf⌋ + ⌊δf'⌋)` is a coboundary (additivity on classes).
Together these say `f ↦ [δf]` descends to a well-defined additive map
`H^1(G,ℚ/ℤ) → H^2(G,ℤ)`, the connecting map of `0 → ℤ → ℚ → ℚ/ℤ → 0`.
(The binders `hQZ`, `hZ` are the — trivially true — open-stabilizer witnesses for the
trivial actions, bound once to name the cocycle/coboundary groups.) -/
theorem bocksteinWellDefined {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G]
    (hQZ : ∀ a : ratCircle,
      IsOpen {g : G | (1 : G →* AddMonoid.End ratCircle) g a = a})
    (hZ : ∀ a : ℤ, IsOpen {g : G | (1 : G →* AddMonoid.End ℤ) g a = a}) :
    (∀ f ∈ contCocycles (1 : G →* AddMonoid.End ratCircle) hQZ 1,
        ∀ g : Fin 2 → G,
        ((bocksteinCochain f g : ℤ) : ℚ)
          = ratCircleSection (f fun _ => g 0) + ratCircleSection (f fun _ => g 1)
            - ratCircleSection (f fun _ => g 0 * g 1))
      ∧ (∀ f ∈ contCocycles (1 : G →* AddMonoid.End ratCircle) hQZ 1,
          bocksteinCochain f ∈ contCocycles (1 : G →* AddMonoid.End ℤ) hZ 2)
      ∧ (∀ f ∈ contCocycles (1 : G →* AddMonoid.End ratCircle) hQZ 1,
          ∀ f' ∈ contCocycles (1 : G →* AddMonoid.End ratCircle) hQZ 1,
          f - f' ∈ contCoboundaries (1 : G →* AddMonoid.End ratCircle) hQZ 1 →
          bocksteinCochain f - bocksteinCochain f'
            ∈ contCoboundaries (1 : G →* AddMonoid.End ℤ) hZ 2)
      ∧ ∀ f f' : contCochain G ratCircle 1,
          bocksteinCochain (f + f') - (bocksteinCochain f + bocksteinCochain f')
            ∈ contCoboundaries (1 : G →* AddMonoid.End ℤ) hZ 2 :=
  sorry


end

section
-- Natural language: Let $G$ be a topological group (with the discrete module structures given by
-- the trivial action).
-- Assume that for every $a\in\mathbb{Q}/\mathbb{Z}$ the set $\{g\in G\mid g\cdot a = a\}$ is open,
-- and similarly for every $a\in\mathbb{Z}$.
-- Then the *Bockstein map* $\delta : H^1(G,\mathbb{Q}/\mathbb{Z}) \to H^2(G,\mathbb{Z})$ is defined
-- as follows:
-- for a class $x\in H^1(G,\mathbb{Q}/\mathbb{Z})$ represented by a continuous $1$-cocycle $f$ (with
-- values in $\mathbb{Q}/\mathbb{Z}$), the image $\delta(x)$ is the class in $H^2(G,\mathbb{Z})$ of
-- the continuous $2$-cochain
-- \[
-- (g_1,g_2) \mapsto s\bigl(f(g_1)\bigr) + s\bigl(f(g_2)\bigr) - s\bigl(f(g_1g_2)\bigr),
-- \]
-- where $s:\mathbb{Q}/\mathbb{Z}\to\mathbb{Q}$ is the canonical set‑theoretic section sending each
-- class to its fractional part in $[0,1)$.
-- The definition is independent of the choice of representative $f$ of $x$ (by the third part of
-- `bocksteinWellDefined`).
-- Score: (0 - incorrect, 1 - partially correct, 2 - correct)
-- Comment:
/-- The connecting (Bockstein) map `δ : H^1(G,ℚ/ℤ) → H^2(G,ℤ)` of the exact sequence
`0 → ℤ → ℚ → ℚ/ℤ → 0` (trivial `G`-actions): on the class of a cocycle `f` it returns
the class of the Bockstein cochain `⌊δf⌋`, `δf(g₁,g₂) = s(f(g₁)) + s(f(g₂)) - s(f(g₁g₂))`
with `s` the canonical section. (Realised on a chosen representative of the class; by
`bocksteinWellDefined` (3) the value does not depend on the representative, so this is
the induced map.) -/
noncomputable def bockstein {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G]
    (hQZ : ∀ a : ratCircle,
      IsOpen {g : G | (1 : G →* AddMonoid.End ratCircle) g a = a})
    (hZ : ∀ a : ℤ, IsOpen {g : G | (1 : G →* AddMonoid.End ℤ) g a = a})
    (x : contCohomologyGrp (1 : G →* AddMonoid.End ratCircle) hQZ 1) :
    contCohomologyGrp (1 : G →* AddMonoid.End ℤ) hZ 2 :=
  QuotientAddGroup.mk
    ⟨bocksteinCochain ↑(Quotient.out x),
      (bocksteinWellDefined hQZ hZ).2.1 ↑(Quotient.out x) (Quotient.out x).2⟩


end

section
-- Natural language: Let $G$ be a topological group (with a topology making it a topological group)
-- acting trivially on an abelian group $A$, and let $hA$ be a proof that for every $a \in A$ the
-- set $\{g \in G \mid 1(g)(a)=a\}$ is open (where $1 : G \to \operatorname{AddMonoid.End}(A)$ is
-- the trivial action). For any $\tau \in G$, the following two statements hold:
-- 
-- (1) For any two continuous $1$-cocycles $f,g$ (with respect to the trivial action and the
-- open-stabilizer condition $hA$), if the classes of $f$ and $g$ in the continuous cohomology group
-- $H^1(G,A)$ (defined as the quotient of the group of continuous $1$-cocycles by the subgroup of
-- continuous $1$-coboundaries) are equal, then $f(\tau,\dots,\tau)=g(\tau,\dots,\tau)$ (where the
-- argument is the constant $1$-tuple $(\tau)$).
-- 
-- (2) For any two such continuous $1$-cocycles $f,g$, the value of the sum $f+g$ (taken in the
-- group of continuous $1$-cochains) at the constant $1$-tuple $(\tau)$ equals
-- $f(\tau,\dots,\tau)+g(\tau,\dots,\tau)$.
-- Score: (0 - incorrect, 1 - partially correct, 2 - correct)
-- Comment:
/-- For the trivial action of `G` on `A` and `τ ∈ G`: (1) cocycles representing the
same class in `H^1(G,A)` take the same value at `τ`; (2) evaluation at `τ` is additive
on cocycles. -/
theorem evalH1WellDefined {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] {A : Type*} [AddCommGroup A]
    (hA : ∀ a : A, IsOpen {g : G | (1 : G →* AddMonoid.End A) g a = a}) (τ : G) :
    (∀ f g : ↥(contCocycles (1 : G →* AddMonoid.End A) hA 1),
        (QuotientAddGroup.mk f :
            contCohomologyGrp (1 : G →* AddMonoid.End A) hA 1)
          = QuotientAddGroup.mk g →
        (f : contCochain G A 1) (fun _ : Fin 1 => τ)
          = (g : contCochain G A 1) (fun _ : Fin 1 => τ))
      ∧ (∀ f g : ↥(contCocycles (1 : G →* AddMonoid.End A) hA 1),
          ((↑(f + g) : contCochain G A 1)) (fun _ : Fin 1 => τ)
            = (f : contCochain G A 1) (fun _ : Fin 1 => τ)
              + (g : contCochain G A 1) (fun _ : Fin 1 => τ)) :=
  sorry


end

section
-- Natural language: For a topological group $G$ acting trivially on an abelian group $A$ and an
-- element $\tau \in G$, the evaluation map $H^1(G,A) \to A$ sending the class of a continuous
-- $1$-cocycle $f$ (i.e. a continuous homomorphism $G \to A$) to $f(\tau)$ is defined as follows:
-- given $x$ in the continuous cohomology group $H^1(G,A)$ (the quotient of the set of continuous
-- $1$-cocycles by the subgroup of continuous $1$-coboundaries), choose a representative cocycle via
-- $\operatorname{Quotient.out}(x)$, evaluate it as a continuous $1$-cochain on the tuple $(\tau)$,
-- and output the resulting element of $A$.
-- Score: (0 - incorrect, 1 - partially correct, 2 - correct)
-- Comment:
/-- For a topological group `G` acting trivially on an abelian group `A` and `τ ∈ G`,
the evaluation map `H^1(G,A) → A`: the class of a continuous `1`-cocycle `f` (i.e. a
continuous homomorphism `G → A`) is sent to `f(τ)`. (Realised on a chosen
representative — `Quotient.out`, which makes the definition noncomputable — but by
`evalH1WellDefined` the value is independent of the choice, so this is the evaluation
map on classes.) -/
noncomputable def evalH1 {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] {A : Type*} [AddCommGroup A]
    (hA : ∀ a : A, IsOpen {g : G | (1 : G →* AddMonoid.End A) g a = a}) (τ : G)
    (x : contCohomologyGrp (1 : G →* AddMonoid.End A) hA 1) : A :=
  (↑(Quotient.out x) : contCochain G A 1) (fun _ : Fin 1 => τ)


end

section
-- Natural language: Let $G$ be a profinite group (a compact, totally disconnected topological
-- group) and let the trivial actions of $G$ on $\mathbb{Q}/\mathbb{Z}$ and on $\mathbb{Z}$ be
-- given, together with the automatically satisfied open point-stabilizer witnesses that for every
-- $a \in \mathbb{Q}/\mathbb{Z}$ the set $\{g \in G \mid g \cdot a = a\}$ is open and for every $a
-- \in \mathbb{Z}$ the set $\{g \in G \mid g \cdot a = a\}$ is open. Then the Bockstein map $\delta
-- : H^1(G,\mathbb{Q}/\mathbb{Z}) \to H^2(G,\mathbb{Z})$ (the connecting map arising from the exact
-- sequence $0 \to \mathbb{Z} \to \mathbb{Q} \to \mathbb{Q}/\mathbb{Z} \to 0$) is bijective, i.e.
-- both injective and surjective.
-- Score: (0 - incorrect, 1 - partially correct, 2 - correct)
-- Comment:
/-- For a profinite group `G` (compact, totally disconnected topological group), the
Bockstein map `δ : H^1(G,ℚ/ℤ) → H^2(G,ℤ)` (trivial actions; open-stabilizer witnesses
bound to name the groups) is bijective — the isomorphism of Milne, Example 1.6(1). -/
theorem bocksteinBijective {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G]
    (hQZ : ∀ a : ratCircle,
      IsOpen {g : G | (1 : G →* AddMonoid.End ratCircle) g a = a})
    (hZ : ∀ a : ℤ, IsOpen {g : G | (1 : G →* AddMonoid.End ℤ) g a = a}) :
    Function.Injective (bockstein hQZ hZ) ∧ Function.Surjective (bockstein hQZ hZ) :=
  sorry


end

section
-- Natural language: Let $H$ be a profinite group (i.e. a topological group that is compact and
-- totally disconnected) and let $\tau \in H$.
-- Assume that for every $a \in \mathbb{Q}/\mathbb{Z}$ the set $\{g \in H \mid 1(g)(a)=a\}$ is open,
-- and similarly for every $a \in \mathbb{Z}$ the set $\{g \in H \mid 1(g)(a)=a\}$ is open (where
-- $1$ denotes the trivial action of $H$ on the respective abelian group).
-- Then the *invariant map* $\operatorname{inv}_{H,\tau} : H^2(H,\mathbb{Z}) \to
-- \mathbb{Q}/\mathbb{Z}$ is defined to be the composition of the inverse of the Bockstein
-- isomorphism $\delta : H^1(H,\mathbb{Q}/\mathbb{Z}) \to H^2(H,\mathbb{Z})$ (which is bijective
-- under the given hypotheses) with the evaluation map $\operatorname{eval}_{H,\tau} :
-- H^1(H,\mathbb{Q}/\mathbb{Z}) \to \mathbb{Q}/\mathbb{Z}$ that sends the class of a continuous
-- $1$-cocycle $f : H \to \mathbb{Q}/\mathbb{Z}$ to $f(\tau)$.
-- Score: (0 - incorrect, 1 - partially correct, 2 - correct)
-- Comment:
/-- For a profinite group `H` with a chosen element `τ ∈ H`, the invariant map
`inv_{H,τ} : H^2(H,ℤ) → ℚ/ℤ` (trivial actions; open-stabilizer witnesses bound to
name the groups): the composition of the inverse of the Bockstein bijection
`δ : H^1(H,ℚ/ℤ) → H^2(H,ℤ)` with evaluation at `τ` of continuous homomorphisms
`H → ℚ/ℤ`. Applied with `H = U`, `τ = σ^m` this yields the map `inv_U` of
Theorem 1.4(1). -/
noncomputable def invOfGen {H : Type*} [Group H] [TopologicalSpace H]
    [IsTopologicalGroup H] [CompactSpace H] [TotallyDisconnectedSpace H]
    (hQZ : ∀ a : ratCircle,
      IsOpen {g : H | (1 : H →* AddMonoid.End ratCircle) g a = a})
    (hZ : ∀ a : ℤ, IsOpen {g : H | (1 : H →* AddMonoid.End ℤ) g a = a})
    (τ : H)
    (x : contCohomologyGrp (1 : H →* AddMonoid.End ℤ) hZ 2) : ratCircle :=
  evalH1 hQZ τ
    ((Equiv.ofBijective (bockstein hQZ hZ) (bocksteinBijective hQZ hZ)).symm x)


end

section
-- Natural language: Let $G$ be a profinite group (i.e. a topological group that is compact and
-- totally disconnected) acting trivially on $\mathbb{Z}$ and on $\mathbb{Q}/\mathbb{Z}$. Choose an
-- element $\sigma \in G$ and a natural number $m$. Let $U$ be an open subgroup of $G$ such that
-- $\sigma^m \in U$, and assume that $U$ is compact (which is automatic for an open subgroup of a
-- compact group) and that the stabiliser of every element of $\mathbb{Q}/\mathbb{Z}$ (resp.
-- $\mathbb{Z}$) under the trivial action of $U$ is open. Then the map $\mathrm{inv}_U :
-- H^2(U,\mathbb{Z}) \to \mathbb{Q}/\mathbb{Z}$ is defined to be the composition of the inverse of
-- the Bockstein isomorphism $H^1(U,\mathbb{Q}/\mathbb{Z}) \to H^2(U,\mathbb{Z})$ with evaluation at
-- $\sigma^m$ of continuous homomorphisms $U \to \mathbb{Q}/\mathbb{Z}$.
-- Score: (0 - incorrect, 1 - partially correct, 2 - correct)
-- Comment:
/-- (Milne, Example 1.6(1).) For a profinite group `G` (e.g. `G ≅ Ẑ`) with a chosen
topological generator `σ`, and an open subgroup `U` of index `m` (so that `σ^m ∈ U`
generates `U` topologically), the invariant map `inv_U : H^2(U,ℤ) → ℚ/ℤ`: the
composition of the inverse of the Bockstein isomorphism
`H^1(U,ℚ/ℤ) → H^2(U,ℤ)` (the boundary map of `0 → ℤ → ℚ → ℚ/ℤ → 0`) with the
evaluation `f ↦ f(σ^m)` of continuous homomorphisms `U → ℚ/ℤ`. It depends on the
choice of `σ`. (Realised as the specialisation of `invOfGen` at `H = U`, `τ = σ^m`;
the compactness of `U` — automatic for an open, hence closed, subgroup of the profinite
`G` — and the trivially-true open-stabilizer witnesses of the trivial actions are
supplied as instance/argument binders in order to name the cohomology groups.) -/
noncomputable def invU {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G]
    (σ : G) (m : ℕ) (U : Subgroup G) (_hUopen : IsOpen (U : Set G))
    (hU : σ ^ m ∈ U) [CompactSpace ↥U]
    (hQZ : ∀ a : ratCircle,
      IsOpen {g : ↥U | (1 : ↥U →* AddMonoid.End ratCircle) g a = a})
    (hZ : ∀ a : ℤ, IsOpen {g : ↥U | (1 : ↥U →* AddMonoid.End ℤ) g a = a})
    (x : contCohomologyGrp (1 : ↥U →* AddMonoid.End ℤ) hZ 2) : ratCircle :=
  invOfGen hQZ hZ (⟨σ ^ m, hU⟩ : ↥U) x


end

section
-- Natural language: Let $K$ be a number field and $v$ a finite place of $K$, with completion $K_v$.
-- The inertia subgroup $I_v \subseteq G_v = \mathrm{Gal}(\overline{K_v}/K_v)$ is closed under
-- conjugation: for every $\sigma \in G_v$ and every $\tau \in I_v$, one has $\sigma\tau\sigma^{-1}
-- \in I_v$.
-- Score: (0 - incorrect, 1 - partially correct, 2 - correct)
-- Comment:
/-- The inertia subgroup `I_v = Gal(K̄_v/K_v^un)` is a normal subgroup of the local
Galois group `G_v = Gal(K̄_v/K_v)`. Here `localInertiaGroup v` is the library's inertia
subgroup of `Gal(K̄_v/K_v)` at the prime `v` (the inertia subgroup for the maximal
ideal of the ring of integers of the algebraic closure of the `v`-adic completion),
i.e. exactly `I_v`. -/
theorem localInertiaNormal (K : Type*) [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    ∀ σ : Field.absoluteGaloisGroup
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v),
      ∀ τ ∈ localInertiaGroup v, σ * τ * σ⁻¹ ∈ localInertiaGroup v :=
  sorry


end

section
-- Natural language: For a number field $K$ and a prime ideal $v$ of the ring of integers of $K$,
-- the inertia subgroup $I_v$ (denoted `localInertiaGroup v`) is a normal subgroup of the local
-- Galois group $G_v = \operatorname{Gal}(\overline{K}_v/K_v)$; that is, for every $\sigma \in G_v$
-- and every $\tau \in I_v$, the conjugate $\sigma \tau \sigma^{-1}$ lies in $I_v$. This fact is
-- registered as a typeclass instance so that the unramified quotient $g_v = G_v/I_v$ inherits a
-- canonical topological group structure.
-- Score: (0 - incorrect, 1 - partially correct, 2 - correct)
-- Comment:
/-- The normality of the inertia subgroup `I_v ⊴ G_v` (from its closure under
conjugation), registered as a typeclass instance so that the unramified quotient
`g_v = G_v/I_v` carries canonical topological group structure. -/
instance localInertiaNormalInst (K : Type*) [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    (localInertiaGroup v).Normal :=
  ⟨fun τ hτ σ => localInertiaNormal K v σ τ hτ⟩


end

section
-- Natural language: Let $K$ be a field with a number field structure, and let $v$ be a height-one
-- prime of the ring of integers of $K$. The *unramified quotient* $g_v := G_v/I_v =
-- \operatorname{Gal}(k(v)^s/k(v))$ of the local Galois group by the inertia subgroup is defined to
-- be the quotient of the absolute Galois group of the $v$-adic completion of $K$ by the local
-- inertia subgroup $I_v$; it is a profinite topological group.
-- Score: (0 - incorrect, 1 - partially correct, 2 - correct)
-- Comment:
/-- The unramified quotient `g_v := G_v/I_v = Gal(k(v)^s/k(v))` of the local Galois
group by the inertia subgroup; a profinite topological group (the quotient group and
quotient topology instances fire automatically since `I_v` is normal). -/
noncomputable abbrev localUnramifiedQuotient (K : Type*) [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    Type _ :=
  Field.absoluteGaloisGroup (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v)
    ⧸ localInertiaGroup v


end

section
-- Natural language: Let $K$ be a number field and let $v$ be a height-one prime of the ring of
-- integers of $K$.
-- Then the unramified quotient $g_v = G_v/I_v$ has a topological generator: there exists $\tau \in
-- g_v$ such that the closure of the cyclic subgroup generated by $\tau$ is all of $g_v$.
-- Score: (0 - incorrect, 1 - partially correct, 2 - correct)
-- Comment:
/-- The unramified quotient `g_v = G_v/I_v ≅ Ẑ` has a topological generator (the
Frobenius): there exists `τ ∈ g_v` such that the closure of the subgroup generated by
`τ` is all of `g_v`. -/
theorem existsFrobeniusGen (K : Type*) [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    ∃ τ : localUnramifiedQuotient K v,
      (Subgroup.zpowers τ).topologicalClosure = ⊤ :=
  sorry


end

section
-- Natural language: For each number field $K$ and each height-one prime $v$ of the ring of integers
-- of $K$, we choose a topological generator $\sigma$ of the unramified quotient $g_v = G_v/I_v
-- \cong \hat{\mathbb{Z}}$ (the Frobenius).
-- Score: (0 - incorrect, 1 - partially correct, 2 - correct)
-- Comment:
/-- A chosen topological generator `σ` of the unramified quotient `g_v = G_v/I_v ≅ Ẑ`
(the Frobenius). The invariant map depends on this choice, as noted in the source. -/
noncomputable def frobeniusGen (K : Type*) [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    localUnramifiedQuotient K v :=
  Classical.choose (existsFrobeniusGen K v)


end

section
-- Natural language: Let $K$ be a number field and $v$ a height-one prime of the ring of integers of
-- $K$. Then the extension $K_v^{\mathrm{un}}/K_v$ is normal, where $K_v$ denotes the $v$-adic
-- completion of $K$ and $K_v^{\mathrm{un}}$ is the maximal unramified extension of $K_v$.
-- Score: (0 - incorrect, 1 - partially correct, 2 - correct)
-- Comment:
/-- The extension `K_v^un/K_v` is normal, being the fixed field of the normal subgroup
`I_v ⊴ G_v`. -/
theorem maxUnramifiedNormal (K : Type*) [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    Normal (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v)
      ↥(maxUnramifiedExtension K v) :=
  sorry


end

section
-- Natural language: For any number field $K$ and any height-one prime $v$ of the ring of integers
-- of $K$, the extension $K_v^{\mathrm{un}}/K_v$ is normal, where $K_v$ denotes the $v$-adic
-- completion of $K$ and $K_v^{\mathrm{un}}$ denotes the maximal unramified extension of $K_v$.
-- Score: (0 - incorrect, 1 - partially correct, 2 - correct)
-- Comment:
/-- The normality of `K_v^un/K_v`, registered as a typeclass instance so that
restriction of automorphisms of `K̄_v` to `K_v^un` (via `AlgEquiv.restrictNormalHom`)
is available. -/
instance maxUnramifiedNormalInst (K : Type*) [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    Normal (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v)
      ↥(maxUnramifiedExtension K v) :=
  maxUnramifiedNormal K v


end

section
-- Natural language: Let $K$ be a number field and $v$ a height-one prime of the ring of integers of
-- $K$. Then the inertia subgroup $I_v$ is contained in the kernel of the restriction homomorphism
-- $G_v \to \operatorname{Gal}(K_v^{\mathrm{un}}/K_v)$; that is, every element of $I_v$ restricts to
-- the identity on $K_v^{\mathrm{un}} = \overline{K_v}^{\,I_v}$.
-- Score: (0 - incorrect, 1 - partially correct, 2 - correct)
-- Comment:
/-- The inertia subgroup `I_v` is contained in the kernel of the restriction
homomorphism `G_v → Gal(K_v^un/K_v)`: every element of `I_v` restricts to the identity
on `K_v^un = K̄_v^{I_v}`. -/
theorem inertiaActsTriviallyOnUnramified (K : Type*) [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    localInertiaGroup v
      ≤ (AlgEquiv.restrictNormalHom
          (F := IsDedekindDomain.HeightOneSpectrum.adicCompletion K v)
          (K₁ := AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v))
          ↥(maxUnramifiedExtension K v)).ker :=
  sorry


end

section
-- Natural language: Let $K$ be a number field and $v$ a height‑one prime of the ring of integers of
-- $K$.
-- The *unramified quotient* $g_v = G_v / I_v$ (where $G_v$ is the absolute Galois group of the
-- completion $K_v$ and $I_v$ is the inertia subgroup) acts canonically on the maximal unramified
-- extension $K_v^{\mathrm{un}}$: the map $g_v \to \operatorname{Gal}(K_v^{\mathrm{un}}/K_v)$
-- obtained by descending the restriction homomorphism $G_v \to
-- \operatorname{Gal}(K_v^{\mathrm{un}}/K_v)$ through the quotient by $I_v$ is a group homomorphism.
-- Score: (0 - incorrect, 1 - partially correct, 2 - correct)
-- Comment:
/-- The canonical action of the unramified quotient `g_v = G_v/I_v` on `K_v^un`: the
homomorphism `g_v → Gal(K_v^un/K_v)` obtained by descending the restriction
homomorphism `G_v → Gal(K_v^un/K_v)` through the quotient by `I_v` (which acts
trivially on `K_v^un`). -/
noncomputable def unramifiedGaloisAction (K : Type*) [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    localUnramifiedQuotient K v →*
      (↥(maxUnramifiedExtension K v)
        ≃ₐ[IsDedekindDomain.HeightOneSpectrum.adicCompletion K v]
        ↥(maxUnramifiedExtension K v)) :=
  QuotientGroup.lift (localInertiaGroup v)
    (AlgEquiv.restrictNormalHom
      (F := IsDedekindDomain.HeightOneSpectrum.adicCompletion K v)
      (K₁ := AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v))
      ↥(maxUnramifiedExtension K v))
    (inertiaActsTriviallyOnUnramified K v)


end

section
-- Natural language: Let $K$ be a number field and $v$ a height-one prime of the ring of integers of
-- $K$.
-- Let $g_v$ denote the unramified quotient $G_v/I_v$ (the local unramified quotient).
-- The *unramified units representation* is the monoid homomorphism
-- $g_v \to \operatorname{End}\bigl(\operatorname{Additive}((K_v^{\mathrm{un}})^{\times})\bigr)$
-- obtained by composing the canonical action $g_v \to \operatorname{Gal}(K_v^{\mathrm{un}}/K_v)$
-- (given by `unramifiedGaloisAction`) with the natural map
-- $\operatorname{Gal}(K_v^{\mathrm{un}}/K_v) \to
-- \operatorname{End}\bigl((K_v^{\mathrm{un}})^{\times}\bigr)$
-- induced by the Galois action on the unit group, and then converting the resulting monoid
-- endomorphism of $(K_v^{\mathrm{un}})^{\times}$ into an additive monoid endomorphism of
-- $\operatorname{Additive}((K_v^{\mathrm{un}})^{\times})$ via the canonical
-- additive‑to‑multiplicative identification.
-- Score: (0 - incorrect, 1 - partially correct, 2 - correct)
-- Comment:
/-- The action of `g_v = G_v/I_v` on the (additivised) unit group `(K_v^un)^×`, as a
monoid homomorphism `g_v →* End(Additive (K_v^un)^×)`, induced by the canonical action
of `g_v` on `K_v^un`. -/
noncomputable def unramifiedUnitsRep (K : Type*) [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    localUnramifiedQuotient K v
      →* AddMonoid.End (Additive (↥(maxUnramifiedExtension K v))ˣ) :=
  MonoidHom.comp
    { toFun := fun f : Monoid.End (↥(maxUnramifiedExtension K v))ˣ =>
        (MonoidHom.toAdditive f :
          AddMonoid.End (Additive (↥(maxUnramifiedExtension K v))ˣ))
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
    (MonoidHom.comp
      (MulDistribMulAction.toMonoidEnd
        (↥(maxUnramifiedExtension K v)
          ≃ₐ[IsDedekindDomain.HeightOneSpectrum.adicCompletion K v]
          ↥(maxUnramifiedExtension K v))
        (↥(maxUnramifiedExtension K v))ˣ)
      (unramifiedGaloisAction K v))


end

section
-- Natural language: Let $K$ be a number field and $v$ a height-one prime of the ring of integers of
-- $K$.
-- There exists a group homomorphism $\operatorname{ord} : (K_v^{\mathrm{un}})^{\times} \to
-- \mathbb{Z}$ (where $K_v^{\mathrm{un}}$ denotes the maximal unramified extension of the completion
-- $K_v$) such that
-- 
-- (i) $\operatorname{ord}$ is surjective;
-- 
-- (ii) for every unit $\pi$ of the adic completion $K_v$ with $\operatorname{Valued.v}(\pi) =
-- \operatorname{ofAdd}(-1)$ (i.e. a uniformizer of $K_v$), we have
-- $\operatorname{ord}\bigl(\operatorname{Additive.ofMul}(\operatorname{Units.map}(\operatorname{algebraMap}_{K_v
-- \to K_v^{\mathrm{un}}})\,\pi)\bigr) = 1$;
-- 
-- (iii) for every unit $x$ of $(K_v^{\mathrm{un}})^{\times}$ such that both $x$ and $x^{-1}$ are
-- integral over the valuation ring $\mathcal{O}_v$ via the composition $\mathcal{O}_v
-- \hookrightarrow K_v \xrightarrow{\operatorname{algebraMap}} K_v^{\mathrm{un}}$, we have
-- $\operatorname{ord}(\operatorname{Additive.ofMul}\,x) = 0$;
-- 
-- (iv) for every $\sigma$ in the Galois group $g_v = G_v/I_v$ and every $x$ in
-- $(K_v^{\mathrm{un}})^{\times}$ (additivised), we have
-- $\operatorname{ord}(\operatorname{unramifiedUnitsRep}(K,v,\sigma,x)) = \operatorname{ord}(x)$.
-- Score: (0 - incorrect, 1 - partially correct, 2 - correct)
-- Comment:
/-- There exists a surjective homomorphism `ord : (K_v^un)^× → ℤ` extending the
normalized valuation of `K_v`: (i) `ord` is surjective; (ii) `ord` takes the value `1`
on images of uniformizers of `K_v` (units `π` with `Valued.v π = ofAdd(-1)` for the
canonical normalized valuation of the completion); (iii) `ord` takes the value `0` on
units of the ring of integers of `K_v^un` (both `x` and `x⁻¹` integral over `𝒪_v`, via
`RingHom.IsIntegralElem` for the canonical map `𝒪_v → K_v^un`); (iv) `ord` is
`g_v`-equivariant for the trivial action on `ℤ`. -/
theorem existsUnramifiedOrd (K : Type*) [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    ∃ ord : Additive (↥(maxUnramifiedExtension K v))ˣ →+ ℤ,
      Function.Surjective ⇑ord
        ∧ (∀ π : (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v)ˣ,
            Valued.v (π : IsDedekindDomain.HeightOneSpectrum.adicCompletion K v)
                = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) :
                    WithZero (Multiplicative ℤ)) →
            ord (Additive.ofMul
              (Units.map
                ((algebraMap (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v)
                    ↥(maxUnramifiedExtension K v)) :
                  IsDedekindDomain.HeightOneSpectrum.adicCompletion K v
                    →* ↥(maxUnramifiedExtension K v)) π)) = 1)
        ∧ (∀ x : (↥(maxUnramifiedExtension K v))ˣ,
            ((algebraMap (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v)
                ↥(maxUnramifiedExtension K v)).comp
              (SubringClass.subtype
                (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers
                  K v))).IsIntegralElem (x : ↥(maxUnramifiedExtension K v)) →
            ((algebraMap (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v)
                ↥(maxUnramifiedExtension K v)).comp
              (SubringClass.subtype
                (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers
                  K v))).IsIntegralElem
              ((x⁻¹ : (↥(maxUnramifiedExtension K v))ˣ) :
                ↥(maxUnramifiedExtension K v)) →
            ord (Additive.ofMul x) = 0)
        ∧ ∀ (σ : localUnramifiedQuotient K v)
            (x : Additive (↥(maxUnramifiedExtension K v))ˣ),
            ord (unramifiedUnitsRep K v σ x) = ord x :=
  sorry


end

section
-- Natural language: Let $K$ be a number field and $v$ a height‑one prime of the ring of integers of
-- $K$.
-- The *unramified order homomorphism* $\operatorname{ord} : (K_v^{\mathrm{un}})^{\times} \to
-- \mathbb{Z}$ is defined to be a chosen surjective, $g_v$-equivariant homomorphism extending the
-- normalized valuation of $K_v$ (unique with these properties; obtained from the existence
-- statement $\operatorname{existsUnramifiedOrd}$).
-- Score: (0 - incorrect, 1 - partially correct, 2 - correct)
-- Comment:
/-- The valuation homomorphism `ord : (K_v^un)^× → ℤ`: a chosen surjective,
`g_v`-equivariant homomorphism extending the normalized valuation of `K_v` (unique with
these properties; obtained from `existsUnramifiedOrd`). -/
noncomputable def unramifiedOrd (K : Type*) [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    Additive (↥(maxUnramifiedExtension K v))ˣ →+ ℤ :=
  Classical.choose (existsUnramifiedOrd K v)


end

section
-- Natural language: Let $G$, $G'$ be topological groups, $A$ an additive abelian group, and
-- $\varphi : G' \to G$ a continuous group homomorphism. For each $n \in \mathbb{N}$, the pullback
-- of continuous cochains along $\varphi$ is the map $C^n(G,A) \to C^n(G',A)$ sending a continuous
-- $n$-cochain $f$ to $f \circ \varphi^n$, i.e. the restriction of functions on $G^n$ to functions
-- on $G'^n$ via $\varphi$.
-- Score: (0 - incorrect, 1 - partially correct, 2 - correct)
-- Comment:
/-- Pullback of continuous cochains along a continuous group homomorphism
`φ : G' → G`: the map `C^n(G,A) → C^n(G',A)`, `f ↦ f ∘ φ^n` — the restriction of
functions on `G^n` to functions on `G'^n` via `φ` (for `φ` an inclusion this is the
cochain-level restriction map of the source, Section 2(i)). -/
noncomputable def contCochainComap {G G' : Type*} [Group G] [TopologicalSpace G]
    [Group G'] [TopologicalSpace G'] {A : Type*} [AddCommGroup A]
    (φ : G' →* G) (hφ : Continuous ⇑φ) (n : ℕ)
    (f : contCochain G A n) : contCochain G' A n :=
  f.comap ⟨fun g : Fin n → G' => (⇑φ) ∘ g,
    continuous_pi fun i => hφ.comp (continuous_apply i)⟩


end

section
-- Natural language: Let $G$, $G'$ be topological groups, $A$ an additive abelian group, $\rho : G
-- \to \operatorname{End}(A)$ a homomorphism such that $\{g \in G \mid \rho(g)(a) = a\}$ is open for
-- every $a \in A$, and $\varphi : G' \to G$ a continuous group homomorphism. Then for every $n \in
-- \mathbb{N}$ the pullback map $\varphi^* : C^n(G,A) \to C^n(G',A)$ (given by $f \mapsto f \circ
-- \varphi^n$) is additive, commutes with the coboundary maps in the sense that
-- $d^{n}_{G'}(\varphi^* f) = \varphi^*(d^{n}_{G} f)$ for all $f \in C^n(G,A)$, and sends
-- $n$-cocycles (elements of $Z^n(G,A)$) to $n$-cocycles of $G'$ and $n$-coboundaries (elements of
-- $B^n(G,A)$) to $n$-coboundaries of $G'$.
-- Score: (0 - incorrect, 1 - partially correct, 2 - correct)
-- Comment:
/-- Cochain pullback along a continuous homomorphism `φ : G' → G` is additive,
commutes with the coboundaries (target action `ρ ∘ φ`), and maps cocycles to cocycles
and coboundaries to coboundaries. -/
theorem contComapCompat {G G' : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [Group G'] [TopologicalSpace G'] [IsTopologicalGroup G']
    {A : Type*} [AddCommGroup A]
    (ρ : G →* AddMonoid.End A) (hρ : ∀ a : A, IsOpen {g : G | ρ g a = a})
    (φ : G' →* G) (hφ : Continuous ⇑φ) (n : ℕ) :
    (∀ f g : contCochain G A n,
        contCochainComap φ hφ n (f + g)
          = contCochainComap φ hφ n f + contCochainComap φ hφ n g)
      ∧ (∀ f : contCochain G A n,
          contCoboundary (ρ.comp φ) (fun a => (hρ a).preimage hφ) n
              (contCochainComap φ hφ n f)
            = contCochainComap φ hφ (n + 1) (contCoboundary ρ hρ n f))
      ∧ (∀ f ∈ contCocycles ρ hρ n,
          contCochainComap φ hφ n f
            ∈ contCocycles (ρ.comp φ) (fun a => (hρ a).preimage hφ) n)
      ∧ (∀ f ∈ contCoboundaries ρ hρ n,
          contCochainComap φ hφ n f
            ∈ contCoboundaries (ρ.comp φ) (fun a => (hρ a).preimage hφ) n) :=
  sorry


end

section
-- Natural language: Let $G$, $G'$ be topological groups, $A$ an additive abelian group, $\rho : G
-- \to \operatorname{End}_{\mathbb{Z}}(A)$ a continuous action with open point stabilizers (i.e.,
-- for every $a \in A$, $\{g \in G \mid \rho(g)(a) = a\}$ is open), and $\varphi : G' \to G$ a
-- continuous group homomorphism. For each $n \in \mathbb{N}$, pullback of cochains along $\varphi$
-- induces an additive group homomorphism $H^n(G,A) \to H^n(G',A)$ (where the coefficient action on
-- $G'$ is $\rho \circ \varphi$), defined by sending the class of a cocycle $f$ to the class of the
-- pulled-back cocycle $f \circ \varphi^n$.
-- Score: (0 - incorrect, 1 - partially correct, 2 - correct)
-- Comment:
/-- The map on continuous cohomology `H^n(G,A) → H^n(G',A)` induced by pullback of
cochains along a continuous group homomorphism `φ : G' → G` (target coefficient action
`ρ ∘ φ`). For `φ` the inclusion of a (decomposition) subgroup this is the restriction
map; for `φ` a quotient projection it is the inflation map. It is an additive group
homomorphism. -/
noncomputable def contCohomologyRes {G G' : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [Group G'] [TopologicalSpace G'] [IsTopologicalGroup G']
    {A : Type*} [AddCommGroup A]
    (ρ : G →* AddMonoid.End A) (hρ : ∀ a : A, IsOpen {g : G | ρ g a = a})
    (φ : G' →* G) (hφ : Continuous ⇑φ) (n : ℕ) :
    contCohomologyGrp ρ hρ n →+
      contCohomologyGrp (ρ.comp φ) (fun a => (hρ a).preimage hφ) n :=
  QuotientAddGroup.map _ _
    (AddMonoidHom.mk'
      (fun z => (⟨contCochainComap φ hφ n ↑z,
          (contComapCompat ρ hρ φ hφ n).2.2.1 ↑z z.2⟩ :
            ↥(contCocycles (ρ.comp φ) (fun a => (hρ a).preimage hφ) n)))
      (fun a b => Subtype.ext ((contComapCompat ρ hρ φ hφ n).1 ↑a ↑b)))
    (by
      intro z hz
      simp only [AddSubgroup.mem_addSubgroupOf, AddSubgroup.mem_comap,
        AddMonoidHom.mk'_apply] at hz ⊢
      exact (contComapCompat ρ hρ φ hφ n).2.2.2 ↑z hz)


end

section
-- Natural language: Let $G$ be a topological group, $A$ and $B$ abelian groups, $\rho_A : G \to
-- \operatorname{End}(A)$ and $\rho_B : G \to \operatorname{End}(B)$ actions such that for every $a
-- \in A$ the set $\{g \in G \mid \rho_A(g)(a) = a\}$ is open and similarly for $B$, and let $u : A
-- \to B$ be an additive $G$-equivariant map (i.e. $u(\rho_A(g)(a)) = \rho_B(g)(u(a))$ for all $g
-- \in G$, $a \in A$). Then for every $n \in \mathbb{N}$, postcomposition with $u$ sends $C^n(G,A)$
-- to $C^n(G,B)$ additively, commutes with the coboundary map $d^n$, maps cocycles to cocycles, and
-- maps coboundaries to coboundaries.
-- Score: (0 - incorrect, 1 - partially correct, 2 - correct)
-- Comment:
/-- Postcomposition of cochains with an additive `G`-equivariant map `u : A → B`
(both coefficient actions with open stabilizers) is additive, commutes with the
coboundaries, and maps cocycles to cocycles and coboundaries to coboundaries. -/
theorem contCoeffMapCompat {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    (ρA : G →* AddMonoid.End A) (hρA : ∀ a : A, IsOpen {g : G | ρA g a = a})
    (ρB : G →* AddMonoid.End B) (hρB : ∀ b : B, IsOpen {g : G | ρB g b = b})
    (u : A →+ B) (hu : ∀ (g : G) (a : A), u (ρA g a) = ρB g (u a)) (n : ℕ) :
    (∀ f g : contCochain G A n,
        LocallyConstant.map ⇑u (f + g)
          = LocallyConstant.map ⇑u f + LocallyConstant.map ⇑u g)
      ∧ (∀ f : contCochain G A n,
          contCoboundary ρB hρB n (LocallyConstant.map ⇑u f)
            = LocallyConstant.map ⇑u (contCoboundary ρA hρA n f))
      ∧ (∀ f ∈ contCocycles ρA hρA n,
          LocallyConstant.map ⇑u f ∈ contCocycles ρB hρB n)
      ∧ (∀ f ∈ contCoboundaries ρA hρA n,
          LocallyConstant.map ⇑u f ∈ contCoboundaries ρB hρB n) :=
  sorry


end

section
-- Natural language: Given a topological group $G$, two additive $G$-modules $A$ and $B$ (with
-- actions $\rho_A$ and $\rho_B$ such that every element of $A$ and $B$ has open stabilizer), an
-- additive $G$-equivariant homomorphism $u : A \to B$, and a natural number $n$, the map on
-- continuous cohomology $H^n(G,A) \to H^n(G,B)$ induced by postcomposition of cochains with $u$ is
-- an additive group homomorphism.
-- Score: (0 - incorrect, 1 - partially correct, 2 - correct)
-- Comment:
/-- The map on continuous cohomology `H^n(G,A) → H^n(G,B)` induced by postcomposition
of cochains with an additive `G`-equivariant map `u : A → B` (both coefficient actions
with open stabilizers). It is an additive group homomorphism. -/
noncomputable def contCohomologyCoeffMap {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    (ρA : G →* AddMonoid.End A) (hρA : ∀ a : A, IsOpen {g : G | ρA g a = a})
    (ρB : G →* AddMonoid.End B) (hρB : ∀ b : B, IsOpen {g : G | ρB g b = b})
    (u : A →+ B) (hu : ∀ (g : G) (a : A), u (ρA g a) = ρB g (u a)) (n : ℕ) :
    contCohomologyGrp ρA hρA n →+ contCohomologyGrp ρB hρB n :=
  QuotientAddGroup.map _ _
    (AddMonoidHom.mk'
      (fun z => (⟨LocallyConstant.map ⇑u ↑z,
          (contCoeffMapCompat ρA hρA ρB hρB u hu n).2.2.1 ↑z z.2⟩ :
            ↥(contCocycles ρB hρB n)))
      (fun a b => Subtype.ext ((contCoeffMapCompat ρA hρA ρB hρB u hu n).1 ↑a ↑b)))
    (by
      intro z hz
      simp only [AddSubgroup.mem_addSubgroupOf, AddSubgroup.mem_comap,
        AddMonoidHom.mk'_apply] at hz ⊢
      exact (contCoeffMapCompat ρA hρA ρB hρB u hu n).2.2.2 ↑z hz)


end

section
-- Natural language: Let $K$ be a number field and $v$ a finite place of $K$. For every $\sigma \in
-- G_v = \operatorname{Gal}(\overline{K_v}/K_v)$ and every $x \in K_v^{\mathrm{un}}$, we have
-- $\sigma(x) = \bar\sigma(x)$ inside $\overline{K_v}$, where $\bar\sigma$ denotes the action on
-- $K_v^{\mathrm{un}}$ of the image of $\sigma$ in $g_v = G_v/I_v$ via the homomorphism
-- $\operatorname{unramifiedGaloisAction}$.
-- Score: (0 - incorrect, 1 - partially correct, 2 - correct)
-- Comment:
/-- The field inclusion `K_v^un ⊆ K̄_v` is equivariant for the Galois actions: for every
`σ ∈ G_v` and `x ∈ K_v^un`, `σ(x) = σ̄(x)` inside `K̄_v`, where `σ̄` is the action on
`K_v^un` of the image of `σ` in `g_v = G_v/I_v` (via `unramifiedGaloisAction`).
Consequently the induced additive homomorphism of additivised unit groups is
equivariant as well. -/
theorem unramifiedInclusionEquivariant (K : Type*) [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    ∀ (σ : Field.absoluteGaloisGroup
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v))
      (x : ↥(maxUnramifiedExtension K v)),
      σ ((maxUnramifiedExtension K v).val x)
        = (maxUnramifiedExtension K v).val
            (unramifiedGaloisAction K v (QuotientGroup.mk σ) x) :=
  sorry


end

section
-- Natural language: Let $K$ be a number field and $v$ a prime ideal of its ring of integers. For
-- every $a \in (K_v^{\mathrm{un}})^{\times}$, the stabilizer $\{\sigma \in g_v \mid \sigma a = a\}$
-- is open in $g_v$, where $g_v = G_v/I_v$ carries the quotient of the Krull topology.
-- Score: (0 - incorrect, 1 - partially correct, 2 - correct)
-- Comment:
/-- The action of `g_v` on `(K_v^un)^×` has open point stabilizers: for every
`a ∈ (K_v^un)^×` the stabilizer `{σ ∈ g_v | σ·a = a}` is open (in the quotient of the
Krull topology, which `g_v = G_v ⧸ I_v` carries as an instance). Open point stabilizers
is what "discrete `g_v`-module" means throughout this blueprint. -/
theorem unramifiedUnitsRepSmooth (K : Type*) [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    ∀ a : Additive (↥(maxUnramifiedExtension K v))ˣ,
      IsOpen {g : localUnramifiedQuotient K v | unramifiedUnitsRep K v g a = a} :=
  sorry


end

section
-- Natural language: Let $K$ be a number field, $v$ a finite place of $K$, $K_v$ the completion,
-- $\overline{K}_v$ an algebraic closure, and $G_v = \operatorname{Gal}(\overline{K}_v/K_v)$ its
-- absolute Galois group endowed with the Krull topology. For every $a \in \overline{K}_v^{\times}$
-- (viewed as an element of the additive group of the unit group), the stabilizer $\{\sigma \in G_v
-- \mid \sigma \cdot a = a\}$ is open in $G_v$, where the action is the natural one given by the
-- representation $\operatorname{localBarUnitsRep}(K,v)$.
-- Score: (0 - incorrect, 1 - partially correct, 2 - correct)
-- Comment:
/-- The action of `G_v` on `K̄_v^×` has open point stabilizers: for every `a ∈ K̄_v^×`
the stabilizer `{σ ∈ G_v | σ·a = a}` is open. (`Field.absoluteGaloisGroup` carries the
Krull topology as its canonical `TopologicalSpace` instance in the library, and `IsOpen`
below refers to that instance. Open point stabilizers is what "discrete `G_v`-module"
means throughout this blueprint.) -/
theorem localBarUnitsRepSmooth (K : Type*) [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    ∀ a : Additive
        (AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v))ˣ,
      IsOpen {g : Field.absoluteGaloisGroup
          (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v) |
        localBarUnitsRep K v g a = a} :=
  sorry


end

section
-- Natural language: Let $K$ be a number field and $v$ a finite place of $K$.
-- The *inflation map*
-- \[
-- H^2(G_v/I_v, (K_v^{\mathrm{un}})^{\times}) \longrightarrow H^2(G_v, \overline{K_v}^{\times})
-- \]
-- is defined to be the composition of the pullback of cochains along the projection $G_v \to
-- G_v/I_v$ with the coefficient map induced by the equivariant inclusion
-- $(K_v^{\mathrm{un}})^{\times} \hookrightarrow \overline{K_v}^{\times}$.
-- Score: (0 - incorrect, 1 - partially correct, 2 - correct)
-- Comment:
/-- The inflation map `H^2(G_v/I_v, (K_v^un)^×) → H^2(G_v, K̄_v^×)`: the composition of
pullback of cochains along the projection `G_v → G_v/I_v` with the coefficient map
induced by the equivariant inclusion `(K_v^un)^× ↪ K̄_v^×`. -/
noncomputable def inflationKvUn (K : Type*) [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    contCohomologyGrp (unramifiedUnitsRep K v) (unramifiedUnitsRepSmooth K v) 2
      →+ contCohomologyGrp (localBarUnitsRep K v) (localBarUnitsRepSmooth K v) 2 :=
  (contCohomologyCoeffMap
      ((unramifiedUnitsRep K v).comp (QuotientGroup.mk' (localInertiaGroup v)))
      (fun a => (unramifiedUnitsRepSmooth K v a).preimage continuous_quot_mk)
      (localBarUnitsRep K v) (localBarUnitsRepSmooth K v)
      (MonoidHom.toAdditive
        (Units.map ((maxUnramifiedExtension K v).val :
          ↥(maxUnramifiedExtension K v) →*
            AlgebraicClosure (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v))))
      (by
        intro σ a
        refine Units.ext ?_
        exact (unramifiedInclusionEquivariant K v σ (Additive.toMul a : _)).symm)
      2).comp
    (contCohomologyRes (unramifiedUnitsRep K v) (unramifiedUnitsRepSmooth K v)
      (QuotientGroup.mk' (localInertiaGroup v)) continuous_quot_mk 2)


end

section
-- Natural language: Let $K$ be a field that is a number field, and let $v$ be a height-one prime of
-- the ring of integers of $K$. Then the inflation map $H^2(G_v/I_v, (K_v^{\mathrm{un}})^{\times})
-- \to H^2(G_v, \overline{K_v}^{\times})$ — a homomorphism between the continuous cohomology groups
-- computed from continuous inhomogeneous cochains — is bijective, i.e. injective and surjective.
-- Score: (0 - incorrect, 1 - partially correct, 2 - correct)
-- Comment:
/-- The inflation map `H^2(G_v/I_v, (K_v^un)^×) → H^2(G_v, K̄_v^×)` is bijective, i.e.
injective and surjective (Milne, Example 1.6(2)). Here `contCohomologyGrp ρ hρ 2` IS
`H^2` in the sense of this blueprint: by the definition item `contCohomologyGrp`, it is
the cohomology `Z^2/B^2` of the complex of continuous (locally constant) inhomogeneous
cochains, i.e. exactly the continuous group cohomology used throughout, applied here to
the coefficient modules `(K_v^un)^×` (for `g_v = G_v/I_v`) and `K̄_v^×` (for `G_v`). -/
theorem inflationKvUnBijective (K : Type*) [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    Function.Injective ⇑(inflationKvUn K v)
      ∧ Function.Surjective ⇑(inflationKvUn K v) :=
  sorry


end

section
-- Natural language: For the trivial action of a topological group $G$ on an abelian group $A$, for
-- every $a \in A$ the stabilizer $\{g \in G : g \cdot a = a\}$ is equal to the whole group $G$ and
-- therefore is open.
-- Score: (0 - incorrect, 1 - partially correct, 2 - correct)
-- Comment:
/-- The open-stabilizer witness for trivial coefficient modules: for the trivial action
of a topological group `G` on an abelian group `A`, every point stabilizer equals the
whole group and is therefore open. Used to instantiate the cohomology of trivial
modules (`ℤ`, `ℚ/ℤ`). -/
def trivialActionSmooth (G : Type*) [Group G] [TopologicalSpace G]
    (A : Type*) [AddCommGroup A] :
    ∀ a : A, IsOpen {g : G | (1 : G →* AddMonoid.End A) g a = a} :=
  fun a => by
    have h : {g : G | (1 : G →* AddMonoid.End A) g a = a} = Set.univ :=
      Set.eq_univ_of_forall fun g => rfl
    rw [h]
    exact isOpen_univ


end

section
-- Natural language: For every subset $s$ of the unramified quotient $g_v = G_v/I_v$: if $s$ is
-- preconnected, then $s$ is a subsingleton (contains at most one point).
-- Score: (0 - incorrect, 1 - partially correct, 2 - correct)
-- Comment:
/-- Every preconnected subset of the unramified quotient `g_v = G_v/I_v` is a
subsingleton (i.e. `g_v` is totally disconnected; together with compactness this makes
`g_v` profinite). -/
theorem localUnramifiedQuotientTD (K : Type*) [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    ∀ s : Set (localUnramifiedQuotient K v), IsPreconnected s → s.Subsingleton :=
  sorry


end

section
-- Natural language: For any field $K$ that is a number field and any height-one prime $v$ of the
-- ring of integers of $K$, the quotient $g_v = G_v/I_v$ (the local unramified quotient) is totally
-- disconnected: every preconnected subset of $g_v$ is a subsingleton.
-- Score: (0 - incorrect, 1 - partially correct, 2 - correct)
-- Comment:
/-- The total disconnectedness of `g_v = G_v/I_v` (from the subsingleton property of
preconnected subsets), registered as a typeclass instance so that `g_v` is recognised
as profinite where the invariant map requires it. -/
instance localUnramifiedQuotientTDInst (K : Type*) [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    TotallyDisconnectedSpace (localUnramifiedQuotient K v) :=
  ⟨fun t _ ht => localUnramifiedQuotientTD K v t ht⟩


end

section
-- Natural language: Let $K$ be a number field and $v$ a finite prime of $K$ (a height‑one prime of
-- the ring of integers).
-- Let $G_v$ be the absolute Galois group of the completion $K_v$, $I_v$ its inertia subgroup, and
-- $g_v = G_v/I_v$ the unramified quotient.
-- Choose a topological generator $\sigma$ of $g_v$ (the Frobenius).
-- Let $\operatorname{ord} : (K_v^{\mathrm{un}})^\times \to \mathbb{Z}$ be a surjective,
-- $g_v$-equivariant homomorphism extending the normalized valuation of $K_v$ (such an
-- $\operatorname{ord}$ exists).
-- Let $\operatorname{inv}_{g_v} : H^2(g_v, \mathbb{Z}) \to \mathbb{Q}/\mathbb{Z}$ be the invariant
-- map defined with respect to $\sigma$ (the composition of the inverse of the Bockstein isomorphism
-- $H^1(g_v, \mathbb{Q}/\mathbb{Z}) \to H^2(g_v, \mathbb{Z})$ with evaluation at $\sigma$).
-- The inflation map $H^2(g_v, (K_v^{\mathrm{un}})^\times) \to H^2(G_v, \overline{K}_v^\times)$ is
-- bijective.
-- Then the *local invariant map* $\varphi : H^2(G_v, \overline{K}_v^\times) \to
-- \mathbb{Q}/\mathbb{Z}$ is defined to be the composition of the inverse of that inflation
-- isomorphism with the map $H^2(g_v, (K_v^{\mathrm{un}})^\times) \xrightarrow{\operatorname{ord}_*}
-- H^2(g_v, \mathbb{Z}) \xrightarrow{\operatorname{inv}_{g_v}} \mathbb{Q}/\mathbb{Z}$.
-- Score: (0 - incorrect, 1 - partially correct, 2 - correct)
-- Comment:
/-- (Milne, Example 1.6(2).) The local invariant map
`φ = inv_{G_v} : H^2(G_v, K̄_v^×) → ℚ/ℤ`: the composition of the inverse of the
inflation isomorphism `H^2(G_v/I_v, (K_v^un)^×) → H^2(G_v, K̄_v^×)` with the
coefficient map `ord_* : H^2(G_v/I_v, (K_v^un)^×) → H^2(G_v/I_v, ℤ)` induced by the
valuation `ord`, followed by the invariant map `inv_{G_v/I_v}` of Theorem 1.4(1) (i.e.
`invOfGen` at the chosen Frobenius topological generator of `g_v = G_v/I_v`). -/
noncomputable def invGv (K : Type*) [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (x : contCohomologyGrp (localBarUnitsRep K v) (localBarUnitsRepSmooth K v) 2) :
    ratCircle :=
  invOfGen (trivialActionSmooth (localUnramifiedQuotient K v) ratCircle)
    (trivialActionSmooth (localUnramifiedQuotient K v) ℤ)
    (frobeniusGen K v)
    (contCohomologyCoeffMap (unramifiedUnitsRep K v) (unramifiedUnitsRepSmooth K v)
      (1 : localUnramifiedQuotient K v →* AddMonoid.End ℤ)
      (trivialActionSmooth (localUnramifiedQuotient K v) ℤ)
      (unramifiedOrd K v)
      (fun σ a => (Classical.choose_spec (existsUnramifiedOrd K v)).2.2.2 σ a)
      2
      ((Equiv.ofBijective ⇑(inflationKvUn K v)
        (inflationKvUnBijective K v)).symm x))


end

section
-- Natural language: Let $F$, $K$, $M$ be types, let $F$ be a field with $F$ finite, let $K$ be a
-- number field, let $M$ be an additive commutative group with an $F$-module structure, and let $P$
-- be a Poitou–Tate setup for $F$, $K$, $M$. Then for every $x$ in the dual module $M^* =
-- \operatorname{Hom}_{\mathbb{Z}}(M, K_S^\times)$, the set $\{g \in G_S \mid g \cdot x = x\}$ is
-- open in the quotient topology on $G_S = G_K / N_S$.
-- Score: (0 - incorrect, 1 - partially correct, 2 - correct)
-- Comment:
/-- The action of `G_S` on `M^* = Hom_ℤ(M, K_S^×)` has open point stabilizers: for
every `x^* ∈ M^*` the stabilizer `{g ∈ G_S | g·x^* = x^*}` is open. (`sGaloisGroup K S`
is by definition the quotient `G_K ⧸ N_S`, which carries the quotient of the Krull
topology as an instance — `IsOpen` below refers to that canonical topology. Open point
stabilizers is what "discrete `G_S`-module" means throughout this blueprint.) -/
theorem dualModuleRepSmooth {F K M : Type} [Field F] [Fintype F] [Field K]
    [NumberField K] [AddCommGroup M] [Module F M] (P : PoitouTateSetup F K M) :
    ∀ x : dualModule P, IsOpen {g : sGaloisGroup K P.S | dualModuleRep P g x = x} :=
  sorry


end

section
-- Natural language: Let $F$ be a field, $K$ a number field, $M$ an $F$-module, and $P$ a
-- Poitou–Tate setup for $F$, $K$, $M$.
-- For a finite place $v$ of $K$ and an integer $i \le 2$, the *local Tate pairing* is the map
-- \[
-- H^i\bigl(G_v,\, M^*\bigr) \times H^{2-i}\bigl(G_v,\, M\bigr) \longrightarrow
-- \mathbb{Q}/\mathbb{Z}
-- \]
-- defined by taking the cup product (with respect to the local evaluation pairing $M^* \times M \to
-- \overline{K_v}^{\times}$) of a class $x$ in the first group and a class $y$ in the second group
-- to obtain a class in $H^2(G_v,\, \overline{K_v}^{\times})$, and then applying the local invariant
-- map $\operatorname{inv}_{G_v}$.
-- Here $G_v$ denotes the absolute Galois group of the completion $K_v$, the action on $M^*$ is the
-- restriction of the $G_S$-action via the local-to-global map, the action on $M$ is given by
-- $\rho_v$ (the composition of the $G_S$-action with the local-to-global map), and the action on
-- $\overline{K_v}^{\times}$ is the natural one; all actions are assumed to have open point
-- stabilizers.
-- Score: (0 - incorrect, 1 - partially correct, 2 - correct)
-- Comment:
/-- The local Tate duality pairing
`H^i(G_v, M^*) × H^{2-i}(G_v, M) → ℚ/ℤ` (for `i ≤ 2`, matching the truncated
subtraction `2 - i`): the cup product with respect to the local evaluation pairing
`M^* × M → K̄_v^×`, landing in `H^2(G_v, K̄_v^×)`, followed by the invariant map
`φ = inv_{G_v}`. The local actions on `M^*` and `M` are via the local-to-global map. -/
noncomputable def localTatePairing {F K M : Type} [Field F] [Fintype F] [Field K]
    [NumberField K] [AddCommGroup M] [Module F M] (P : PoitouTateSetup F K M)
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (i : ℕ) (hi : i ≤ 2)
    (x : contCohomologyGrp
      ((dualModuleRep P).comp (decompositionMap K P.S v).toMonoidHom)
      (fun a => (dualModuleRepSmooth P a).preimage
        (map_continuous (decompositionMap K P.S v))) i)
    (y : contCohomologyGrp (localRho P v)
      (fun m => (P.continuous_ρ m).preimage
        (map_continuous (decompositionMap K P.S v))) (2 - i)) : ratCircle :=
  invGv K v
    ((show i + (2 - i) = 2 by omega) ▸
      contCohomologyCup
        ((dualModuleRep P).comp (decompositionMap K P.S v).toMonoidHom)
        (fun a => (dualModuleRepSmooth P a).preimage
          (map_continuous (decompositionMap K P.S v)))
        (localRho P v)
        (fun m => (P.continuous_ρ m).preimage
          (map_continuous (decompositionMap K P.S v)))
        (localBarUnitsRep K v) (localBarUnitsRepSmooth K v)
        (localEvalPairing P v)
        (localEvalPairingEquivariant P v)
        i (2 - i) x y)


end

section
-- Natural language: Let $F$ be a field, $K$ a number field, and $M$ an additive commutative group
-- equipped with an $F$-module structure.
-- Fix a Poitou–Tate setup $P$ for $F$, $K$, $M$ and a finite place $v$ of $K$ (a height‑one prime
-- of the ring of integers).
-- Let $G_v = \operatorname{Gal}(\overline{K}_v/K_v)$ be the absolute Galois group of the $v$-adic
-- completion of $K$, and let $g_v = G_v/I_v$ be its unramified quotient.
-- The *subgroup of unramified classes* in $H^1(G_v, M)$ (the continuous cohomology group with
-- respect to the action $\rho_v$ obtained by composing the global $G_S$-action with the
-- decomposition map) is defined to be the additive subgroup generated by the set of those classes
-- $a$ for which there exists a continuous $1$-cocycle $z$ (i.e. an element of $Z^1(G_v, M)$) such
-- that $a = [z]$ in $H^1(G_v, M)$ and, for all tuples $g, g' \colon \operatorname{Fin} 1 \to G_v$,
-- if the componentwise images of $g$ and $g'$ in $g_v$ coincide, then $z(g) = z(g')$ (i.e. $z$ is
-- constant on the fibres of the projection $G_v \to g_v$).
-- Score: (0 - incorrect, 1 - partially correct, 2 - correct)
-- Comment:
/-- The subgroup of unramified classes in `H^1(G_v, M)`: generated by the classes
represented by a continuous `1`-cocycle `z` (a locally constant function on the
one-fold product `G_v^1`) that is constant on the fibres of the projection
`G_v → g_v = G_v/I_v`: `z g = z g'` whenever the tuples `g, g'` have the same image in
`g_v` componentwise. -/
noncomputable def unramifiedClasses {F K M : Type} [Field F] [Fintype F] [Field K]
    [NumberField K] [AddCommGroup M] [Module F M] (P : PoitouTateSetup F K M)
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    AddSubgroup (contCohomologyGrp (localRho P v)
      (fun m => (P.continuous_ρ m).preimage
        (map_continuous (decompositionMap K P.S v))) 1) :=
  AddSubgroup.closure
    {a | ∃ z : ↥(contCocycles (localRho P v)
        (fun m => (P.continuous_ρ m).preimage
          (map_continuous (decompositionMap K P.S v))) 1),
      QuotientAddGroup.mk z = a
        ∧ ∀ g g' : Fin 1 →
            Field.absoluteGaloisGroup
              (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v),
          (fun k => (QuotientGroup.mk (g k) : localUnramifiedQuotient K v))
              = (fun k => QuotientGroup.mk (g' k)) →
          (z : contCochain
            (Field.absoluteGaloisGroup
              (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v)) M 1) g
            = (z : contCochain
              (Field.absoluteGaloisGroup
                (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v)) M 1) g'}


end

section
-- Natural language: Let $F$ be a field, $K$ a number field, $M$ an $F$-vector space, and $P$ a
-- Poitou–Tate setup for $F$, $K$, $M$.
-- Let $v$ be a finite place of $K$ (a height‑one prime of the ring of integers of $K$).
-- The *set of $M^d$-classes in $H^1(G_v, M^*)$* is defined to be the set of those elements $c$ of
-- the continuous cohomology group $H^1\bigl(G_v, M^*\bigr)$ (where $G_v$ is the absolute Galois
-- group of the completion $K_v$, acting on $M^*$ via the local‑to‑global map $G_v \to G_S$) for
-- which there exists a continuous $1$-cocycle $z$ (i.e. an element of the group of continuous
-- $1$-cocycles for that action) such that $c$ is the class of $z$, and such that for all $g, g'
-- \colon \operatorname{Fin} 1 \to G_v$ with the property that for every $k \in \operatorname{Fin}
-- 1$ the images of $g(k)$ and $g'(k)$ in the unramified quotient $g_v = G_v/I_v$ coincide, the
-- values $z(g)$ and $z(g')$ (taken in $M^*$) are equal, and moreover for every $g \colon
-- \operatorname{Fin} 1 \to G_v$ the value $z(g)$ lies in the submodule $M^d \subseteq M^*$ (the
-- unramified dual submodule).
-- Score: (0 - incorrect, 1 - partially correct, 2 - correct)
-- Comment:
/-- The set of `M^d`-classes in `H^1(G_v, M^*)`, where `G_v` denotes (as throughout
this blueprint) the absolute Galois group of the completion `K_v`, acting on `M^*`
through the local-to-global map `G_v → G_S`: the set of those cohomology classes
represented by a continuous `1`-cocycle `z` — in our cochain model, a locally constant
function on one-component tuples `Fin 1 → G_v`, encoding `G_v^1` — such that
`z g = z g'` whenever for every component `k` the images of `g k` and `g' k` in
`g_v = G_v/I_v` agree (constancy on the fibres of the projection), and all of whose
values lie in the submodule `M^d ⊆ M^*`. -/
noncomputable def unramifiedDualClasses {F K M : Type} [Field F] [Fintype F] [Field K]
    [NumberField K] [AddCommGroup M] [Module F M] (P : PoitouTateSetup F K M)
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    Set (contCohomologyGrp
      ((dualModuleRep P).comp (decompositionMap K P.S v).toMonoidHom)
      (fun x => (dualModuleRepSmooth P x).preimage
        (map_continuous (decompositionMap K P.S v))) 1) :=
  {c | ∃ z : ↥(contCocycles
      ((dualModuleRep P).comp (decompositionMap K P.S v).toMonoidHom)
      (fun x => (dualModuleRepSmooth P x).preimage
        (map_continuous (decompositionMap K P.S v))) 1),
    QuotientAddGroup.mk z = c
      ∧ (∀ g g' : Fin 1 →
            Field.absoluteGaloisGroup
              (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v),
          (∀ k : Fin 1, (QuotientGroup.mk (g k) : localUnramifiedQuotient K v)
              = QuotientGroup.mk (g' k)) →
          (z : contCochain
            (Field.absoluteGaloisGroup
              (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v))
            (dualModule P) 1) g
            = (z : contCochain
              (Field.absoluteGaloisGroup
                (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v))
              (dualModule P) 1) g')
      ∧ ∀ g : Fin 1 →
            Field.absoluteGaloisGroup
              (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v),
          (z : contCochain
            (Field.absoluteGaloisGroup
              (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v))
            (dualModule P) 1) g ∈ unramifiedDual P v}


end

section
-- Natural language: Let $F$ be a finite field, $K$ a number field, $M$ a finite $F[G_S]$-module,
-- and $P$ a Poitou–Tate setup for these data. For a finite prime $v$ of $K$, let $G_v$ be the
-- absolute Galois group of the completion $K_v$, let $I_v \subseteq G_v$ be the inertia subgroup,
-- and let $g_v = G_v/I_v$ be the unramified quotient. Write $H^1(G_v, M)$ and $H^1(G_v, M^*)$ for
-- the continuous cohomology groups, where $M^* = \operatorname{Hom}_{\mathbb{Z}}(M, K_S^\times)$ is
-- the dual module with its natural $G_S$-action, and let $\langle \cdot, \cdot \rangle : H^1(G_v,
-- M^*) \times H^1(G_v, M) \to \mathbb{Q}/\mathbb{Z}$ be the local Tate duality pairing in degree
-- $1$. Define the *unramified classes* $\operatorname{unramifiedClasses}(P, v) \subseteq H^1(G_v,
-- M)$ to be the subgroup generated by classes represented by a continuous $1$-cocycle that is
-- constant on the fibres of the projection $G_v \to g_v$, and define the *$M^d$-classes*
-- $\operatorname{unramifiedDualClasses}(P, v) \subseteq H^1(G_v, M^*)$ to be the set of classes
-- represented by a continuous $1$-cocycle that is constant on the fibres of $G_v \to g_v$ and whose
-- values lie in the submodule $M^d \subseteq M^*$ (where $M^d$ is the subgroup of $x^* \in M^*$
-- such that for every $m \in M$, the image of $x^*(m)$ in an algebraic closure of $K_v$ lies in the
-- maximal unramified extension $K_v^{\mathrm{un}}$ and is integral together with its inverse over
-- the ring of integers of $K_v$). Then the following four statements hold: (1) for every $b \in
-- \operatorname{unramifiedDualClasses}(P, v)$ and every $a \in \operatorname{unramifiedClasses}(P,
-- v)$, we have $\langle b, a \rangle = 0$; (2) for every $b \in H^1(G_v, M^*)$, if $\langle b, a
-- \rangle = 0$ for all $a \in \operatorname{unramifiedClasses}(P, v)$, then $b \in
-- \operatorname{unramifiedDualClasses}(P, v)$; (3) for every $a \in
-- \operatorname{unramifiedClasses}(P, v)$ and every $b \in \operatorname{unramifiedDualClasses}(P,
-- v)$, we have $\langle b, a \rangle = 0$; (4) for every $a \in H^1(G_v, M)$, if $\langle b, a
-- \rangle = 0$ for all $b \in \operatorname{unramifiedDualClasses}(P, v)$, then $a \in
-- \operatorname{unramifiedClasses}(P, v)$.
-- Score: (0 - incorrect, 1 - partially correct, 2 - correct)
-- Comment:
/-- (Milne, Theorem 1.5(b) / Example 2.6.) In the local Tate duality pairing
`H^1(G_v, M^*) × H^1(G_v, M) → ℚ/ℤ` (`localTatePairing` in degree `i = 1`), the
unramified classes (`unramifiedClasses`) and the `M^d`-classes
(`unramifiedDualClasses`) are the exact annihilators of each other, as the
conjunction of four universally quantified implications: (1) every `M^d`-class `b`
pairs to `0` with every unramified class `a`; (2) if a class `b ∈ H^1(G_v, M^*)`
pairs to `0` with every unramified class, then `b` is an `M^d`-class; (3) restating
(1): every unramified class `a` pairs to `0` with every `M^d`-class `b`; (4) if a
class `a ∈ H^1(G_v, M)` pairs to `0` with every `M^d`-class, then `a` is
unramified. -/
theorem unramifiedAnnihilators {F K M : Type} [Field F] [Fintype F] [Field K]
    [NumberField K] [AddCommGroup M] [Module F M] (P : PoitouTateSetup F K M)
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    (∀ b, b ∈ unramifiedDualClasses P v →
        ∀ a, a ∈ unramifiedClasses P v →
          localTatePairing P v 1 (by omega) b a = 0)
      ∧ (∀ b : contCohomologyGrp
            ((dualModuleRep P).comp (decompositionMap K P.S v).toMonoidHom)
            (fun x => (dualModuleRepSmooth P x).preimage
              (map_continuous (decompositionMap K P.S v))) 1,
          (∀ a, a ∈ unramifiedClasses P v →
              localTatePairing P v 1 (by omega) b a = 0) →
            b ∈ unramifiedDualClasses P v)
      ∧ (∀ a, a ∈ unramifiedClasses P v →
          ∀ b, b ∈ unramifiedDualClasses P v →
            localTatePairing P v 1 (by omega) b a = 0)
      ∧ ∀ a : contCohomologyGrp (localRho P v)
          (fun m => (P.continuous_ρ m).preimage
            (map_continuous (decompositionMap K P.S v))) 1,
        (∀ b, b ∈ unramifiedDualClasses P v →
            localTatePairing P v 1 (by omega) b a = 0) →
          a ∈ unramifiedClasses P v :=
  sorry


end

section
-- Natural language: For a Poitou–Tate setup $P$ over fields $F$, $K$, $M$ as above, a finite place
-- $v$ of $K$, and any $i \in \mathbb{N}$, the restriction map $\operatorname{res}^i_v : H^i(G_S, M)
-- \to H^i(G_v, M)$ is defined to be the additive group homomorphism induced by pulling back
-- continuous cochains along the continuous homomorphism $\operatorname{decompositionMap} K P.S v :
-- G_v \to G_S$, where $G_S$ acts on $M$ via $P.\rho$ and $G_v$ acts on $M$ via the composition of
-- that map with $P.\rho$.
-- Score: (0 - incorrect, 1 - partially correct, 2 - correct)
-- Comment:
/-- The restriction map `res^i_v : H^i(G_S, M) → H^i(G_v, M)`, induced by the
local-to-global map `G_v → G_S`. On cochains it is exactly the pullback (restriction)
of continuous functions on `G_S^i` to functions on `G_v^i` along the map — see
`contCochainComap` (the cochain complex computing `H^i` is the complex of continuous
functions `C^i(G,M) = {f : G^i → M}`, as prescribed by the source). -/
noncomputable abbrev resIV {F K M : Type} [Field F] [Fintype F] [Field K]
    [NumberField K] [AddCommGroup M] [Module F M] (P : PoitouTateSetup F K M)
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) (i : ℕ) :
    contCohomologyGrp (setupRho P) P.continuous_ρ i →+
      contCohomologyGrp (localRho P v)
        (fun m => (P.continuous_ρ m).preimage
          (map_continuous (decompositionMap K P.S v))) i :=
  contCohomologyRes (setupRho P) P.continuous_ρ
    (decompositionMap K P.S v).toMonoidHom
    (map_continuous (decompositionMap K P.S v)) i


end

section
-- Natural language: For any discrete $G_S$-module $A$ (an abelian group with a $G_S$-action $\rho$
-- such that every $a \in A$ has open stabilizer), the product-restriction homomorphism $H^i(G_S, A)
-- \to \prod_{v \in S} H^i(G_v, A)$, whose $v$-component is the restriction map induced by the
-- local-to-global homomorphism $G_v \to G_S$, is defined as the additive group homomorphism sending
-- a cohomology class $x$ to the function $v \mapsto \operatorname{res}_{G_v}^{G_S}(x)$, where
-- $\operatorname{res}_{G_v}^{G_S}$ is the map on continuous cohomology induced by pullback along
-- the decomposition map $G_v \to G_S$.
-- Score: (0 - incorrect, 1 - partially correct, 2 - correct)
-- Comment:
/-- For any discrete `G_S`-module `(A, ρ)`, the product-restriction homomorphism
`H^i(G_S, A) → ∏_{v ∈ S} H^i(G_v, A)`, whose `v`-component is the restriction map
induced by the local-to-global homomorphism `G_v → G_S`. (Applied to `A = M` this is
the map `α_i`; applied to `A = M^*` it yields the kernels `Ker^i(G_S, M^*)`.) -/
noncomputable def sAlpha (K : Type*) [Field K] [NumberField K]
    (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
    {A : Type*} [AddCommGroup A]
    (ρ : sGaloisGroup K S →* AddMonoid.End A)
    (hρ : ∀ a : A, IsOpen {g : sGaloisGroup K S | ρ g a = a}) (i : ℕ) :
    contCohomologyGrp ρ hρ i →+
      ((v : ↥S) → contCohomologyGrp
        (ρ.comp (decompositionMap K S ↑v).toMonoidHom)
        (fun a => (hρ a).preimage (map_continuous (decompositionMap K S ↑v))) i) :=
  AddMonoidHom.mk'
    (fun x v =>
      contCohomologyRes ρ hρ (decompositionMap K S ↑v).toMonoidHom
        (map_continuous (decompositionMap K S ↑v)) i x)
    (fun x y => funext fun _ => map_add _ x y)


end

section
-- Natural language: Let $F$ be a finite field of characteristic $p>2$, let $K$ be a totally real
-- number field, let $S$ be a set of height-one primes of the ring of integers of $K$ (containing
-- all archimedean places), and let $M$ be a finitely generated $F[G_S]$-module with continuous
-- action $\rho$ such that $\operatorname{Nat.card}(M)$ is a unit in the ring of $S$-integers. For
-- each $i\ge 0$, the map $\alpha_i : H^i(G_S, M) \to \prod_{v\in S} H^i(G_v, M)$ is defined to be
-- the product over $v\in S$ of the restriction maps $\operatorname{res}^i_v$ induced by the
-- local-to-global homomorphism $G_v\to G_S$.
-- Score: (0 - incorrect, 1 - partially correct, 2 - correct)
-- Comment:
/-- The map `α_i : H^i(G_S, M) → ∏_{v ∈ S} H^i(G_v, M)` induced by the restriction
maps `res^i_v` (the specialisation of `sAlpha` to the coefficient module `M`). Since
`p > 2`, the Tate cohomology `Ĥ^i(G_v, M)` vanishes for every archimedean `v ∈ S_∞`,
so the product effectively runs over the finite places `v ∈ S_f` only — which is what
the index set `S` (the finite part of the set of primes) records. (These maps are
denoted `β^r` in Milne, p. 55.) -/
noncomputable abbrev alphaI {F K M : Type} [Field F] [Fintype F] [Field K]
    [NumberField K] [AddCommGroup M] [Module F M] (P : PoitouTateSetup F K M)
    (i : ℕ) :
    contCohomologyGrp (setupRho P) P.continuous_ρ i →+
      ((v : ↥P.S) → contCohomologyGrp
        ((setupRho P).comp (decompositionMap K P.S ↑v).toMonoidHom)
        (fun m => (P.continuous_ρ m).preimage
          (map_continuous (decompositionMap K P.S ↑v))) i) :=
  sAlpha K P.S (setupRho P) P.continuous_ρ i


end

section
-- Natural language: Let $F$ be a finite field of characteristic $p>2$, let $K$ be a totally real
-- number field, let $S$ be a set of finite primes of $K$, and let $M$ be a finite $F[G_S]$-module
-- whose order is a unit in the ring of $S$-integers of $K$ and whose $G_S$-action is continuous.
-- For $i \le 2$, the map $\beta_i : \prod_{v \in S} H^i(G_v, M) \to H^{2-i}(G_S, M^*)^{\vee}$ is
-- defined as follows: given $x = (x_v)_{v \in S}$ with $x_v \in H^i(G_v, M)$ and given $y \in
-- H^{2-i}(G_S, M^*)$, the value $\beta_i(x)(y)$ is the finitely-supported sum $\sum_{v \in S}
-- \langle \operatorname{res}_v y, x_v \rangle_v$, where $\langle\,,\,\rangle_v$ is the local Tate
-- pairing $H^{2-i}(G_v, M^*) \times H^i(G_v, M) \to \mathbb{Q}/\mathbb{Z}$; if the support of the
-- sum is infinite, the value is $0$. The map $\beta_i$ is realised as a function from $\prod_{v \in
-- S} H^i(G_v, M)$ to the group of functions $H^{2-i}(G_S, M^*) \to \mathbb{Q}/\mathbb{Z}$, and on
-- arguments for which the local terms have finite support the value is additive, i.e. lies in the
-- dual $H^{2-i}(G_S, M^*)^{\vee}$.
-- Score: (0 - incorrect, 1 - partially correct, 2 - correct)
-- Comment:
/-- The map `β_i : ∏_{v ∈ S} H^i(G_v, M) → H^{2-i}(G_S, M^*)^∨` (for `i ≤ 2`),
obtained by dualizing the restriction map for `M^*` through local Tate duality:
explicitly, `β_i(x)(ȳ) = Σᶠ_{v ∈ S} ⟨res_v ȳ, x_v⟩_v`, the finitely-supported sum of
the local Tate pairings (`0` if the support is infinite). Realised as a function into
maps `H^{2-i}(G_S, M^*) → ℚ/ℤ`; on arguments with finite local support the value is
additive, i.e. lies in the dual. (Denoted `γ^r` in Milne, p. 56.) -/
noncomputable def betaI {F K M : Type} [Field F] [Fintype F] [Field K]
    [NumberField K] [AddCommGroup M] [Module F M] (P : PoitouTateSetup F K M)
    (i : ℕ) (hi : i ≤ 2)
    (x : (v : ↥P.S) → contCohomologyGrp
      ((setupRho P).comp (decompositionMap K P.S ↑v).toMonoidHom)
      (fun m => (P.continuous_ρ m).preimage
        (map_continuous (decompositionMap K P.S ↑v))) i)
    (y : contCohomologyGrp (dualModuleRep P) (dualModuleRepSmooth P) (2 - i)) :
    ratCircle :=
  finsum fun v : ↥P.S =>
    localTatePairing P ↑v (2 - i) (by omega)
      (sAlpha K P.S (dualModuleRep P) (dualModuleRepSmooth P) (2 - i) y v)
      ((show i = 2 - (2 - i) by omega) ▸ x v)


end

section
-- Natural language: Let $F$ be a finite field, $K$ a number field, and $M$ a finitely generated
-- $F[G_S]$-module with continuous action, where $G_S = \operatorname{Gal}(K_S/K)$. For a
-- Poitou–Tate setup $P$ over $F,K,M$ and any $i \in \mathbb{N}$, $\operatorname{Ker}^i(G_S, M)$ is
-- defined to be the kernel of the product-restriction map $\alpha_i : H^i(G_S, M) \to \prod_{v \in
-- S} H^i(G_v, M)$, i.e. the subgroup of $H^i(G_S, M)$ consisting of those classes whose restriction
-- to every decomposition group $G_v$ ($v \in S$) is trivial.
-- Score: (0 - incorrect, 1 - partially correct, 2 - correct)
-- Comment:
/-- `Ker^i(G_S, M) = ker α_i`: the kernel of the product-restriction map
`α_i : H^i(G_S, M) → ∏_{v ∈ S} H^i(G_v, M)`, as a subgroup of `H^i(G_S, M)`. (In
Sections 4–5 the coefficient module `M` of the setup is finite, being a finitely
generated module over the finite field `F`.) -/
noncomputable abbrev KerI {F K M : Type} [Field F] [Fintype F] [Field K]
    [NumberField K] [AddCommGroup M] [Module F M] (P : PoitouTateSetup F K M)
    (i : ℕ) :
    AddSubgroup (contCohomologyGrp (setupRho P) P.continuous_ρ i) :=
  (alphaI P i).ker


end

section
-- Natural language: Let $F$ be a field, $K$ a number field, $M$ an $\text{AddCommGroup}$ with an
-- $F$-module structure, and $P$ a $\text{PoitouTateSetup}$ over $F$, $K$, $M$. For any topological
-- group $G$ and any $n \in \mathbb{N}$, the group $C^n(G, M^*)$ of continuous $n$-cochains of $G$
-- with values in the dual module $M^*$ (pointwise addition) carries an $\text{AddCommGroup}$
-- structure, given by the canonical instance derived from the general cochain construction.
-- Score: (0 - incorrect, 1 - partially correct, 2 - correct)
-- Comment:
/-- Shortcut typeclass instance: the abelian group structure on the group
`C^n(G, M^*)` of continuous `n`-cochains of a topological group `G` with values in
the dual module `M^*` (pointwise addition). This is exactly the canonical instance
Lean derives from the general cochain construction (the body is instance inference);
it is registered explicitly because the derivation chain for
`M^* = Hom_ℤ(M, K_S^×)` is deep enough that nested instance searches (e.g. for the
group structure on the cohomology quotient `H^n(G, M^*)`) fail without this
shortcut. No new mathematical content. -/
noncomputable instance dualCochainAddCommGroupInst {F K M : Type} [Field F]
    [Fintype F] [Field K] [NumberField K] [AddCommGroup M] [Module F M]
    (P : PoitouTateSetup F K M) (G : Type) [TopologicalSpace G] (n : ℕ) :
    AddCommGroup (contCochain G (dualModule P) n) :=
  inferInstance


end

section
-- Natural language: Let $F$ be a field, $K$ a number field, $M$ an $\text{AddCommGroup}$ with an
-- $F$-module structure, and $P$ a Poitou–Tate setup for $F$, $K$, $M$.
-- For any additive homomorphism $\varphi : H^2(G_S, M^*) \to \mathbb{Q}/\mathbb{Z}$, the map
-- $\iota^\vee(\varphi) = \varphi \circ \iota$ is an additive homomorphism from
-- $\operatorname{Ker}^2(G_S, M^*)$ to $\mathbb{Q}/\mathbb{Z}$, where $\iota :
-- \operatorname{Ker}^2(G_S, M^*) \hookrightarrow H^2(G_S, M^*)$ is the inclusion of the kernel of
-- the product‑restriction map on $H^2(G_S, M^*)$ as an additive subgroup.
-- Score: (0 - incorrect, 1 - partially correct, 2 - correct)
-- Comment:
/-- The dual of the inclusion `ι : Ker^2(G_S, M^*) ↪ H^2(G_S, M^*)`: the (surjective)
map `ι^∨ : H^2(G_S, M^*)^∨ → (Ker^2(G_S, M^*))^∨` given by precomposition with the
subgroup inclusion, `φ ↦ φ ∘ ι`. Here `Ker^2(G_S, M^*)` is the kernel of the
product-restriction map on `H^2(G_S, M^*)` as an additive subgroup, and `(-)^∨`
denotes additive homomorphisms into `ℚ/ℤ`. -/
noncomputable def iotaDual {F K M : Type} [Field F] [Fintype F] [Field K]
    [NumberField K] [AddCommGroup M] [Module F M] (P : PoitouTateSetup F K M)
    (φ : contCohomologyGrp (dualModuleRep P) (dualModuleRepSmooth P) 2 →+ ratCircle) :
    ↥((sAlpha K P.S (dualModuleRep P) (dualModuleRepSmooth P) 2).ker) →+ ratCircle :=
  φ.comp ((sAlpha K P.S (dualModuleRep P) (dualModuleRepSmooth P) 2).ker.subtype)


end

section
-- Natural language: Let $K$ be a number field, $S$ a set of finite places of $K$, $K_S$ the maximal
-- extension of $K$ unramified outside $S$, and $G_S = \operatorname{Gal}(K_S/K)$. For every unit $a
-- \in K_S^{\times}$, the stabilizer $\{g \in G_S : g \cdot a = a\}$ is an open subset of $G_S$
-- (with respect to the Krull topology).
-- Score: (0 - incorrect, 1 - partially correct, 2 - correct)
-- Comment:
/-- The action of `G_S` on `K_S^×` has open point stabilizers: each element of `K_S`
lies in a finite subextension, whose pointwise stabilizer is open in the Krull
topology. Hence `K_S^×` is a discrete `G_S`-module. -/
theorem sUnitsRepSmooth (K : Type*) [Field K] [NumberField K]
    (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) :
    ∀ a : Additive (↥(sMaximalExtension K S))ˣ,
      IsOpen {g : sGaloisGroup K S | sUnitsRep K S g a = a} :=
  sorry


end

section
-- Natural language: Let $K$ be a number field, $S$ a set of finite places of $K$, and $A$, $B$
-- discrete $G_S$-modules with continuous actions $\rho_A$, $\rho_B$ (i.e. each stabiliser is open).
-- Let $\phi : A \to B \to K_S^\times$ be a bi-additive $G_S$-equivariant pairing. Let $\bar f \in
-- Z^2(G_S,A)$ and $\bar g \in Z^1(G_S,B)$ be cocycles whose classes vanish under the
-- product-restriction maps $\alpha_2$ and $\alpha_1$ respectively, and assume that the cup product
-- $\bar f \cup \bar g$ is a global coboundary (i.e. there exists $h_0$ such that $d h_0 = \bar f
-- \cup \bar g$). Then for each $v \in S$, the following three statements hold: (a) there exists a
-- continuous $1$-cochain $\phi_v \in C^1(G_v,A)$ with $d^1\phi_v = \operatorname{res}_v \bar f$;
-- (b) there exists $\psi_v \in B$ such that $d^0\psi_v = \operatorname{res}_v \bar g$ (where
-- $\psi_v$ is regarded as a constant $0$-cochain); and (c) there exists a global $2$-cochain $h \in
-- C^2(G_S,K_S^\times)$ with $dh = \bar f \cup \bar g$.
-- Score: (0 - incorrect, 1 - partially correct, 2 - correct)
-- Comment:
/-- (Section 4.2 choices, per place.) Let `A, B` be discrete `G_S`-modules and
`φ : A → B → K_S^×` a bi-additive `G_S`-equivariant pairing. Let `fbar ∈ Z^2(G_S, A)`
and `gbar ∈ Z^1(G_S, B)` be cocycles whose classes lie in `Ker^2(G_S, A)` resp.
`Ker^1(G_S, B)` (vanishing under `sAlpha`), and assume `fbar ∪ gbar` is a global
coboundary (`hcup`). Then for each `v ∈ S`, as a conjunction of three existence
clauses: (a) there is a continuous `1`-cochain `φ_v ∈ C^1(G_v, A)` with
`d¹φ_v = res_v fbar`; (b) there is `ψ_v ∈ B` with `d⁰ψ_v = res_v gbar` (`ψ_v`
regarded as a constant `0`-cochain); (c) there is `h ∈ C^2(G_S, K_S^×)` with
`dh = fbar ∪ gbar`. -/
theorem kernelPairingChoices (K : Type*) [Field K] [NumberField K]
    (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
    {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    (ρA : sGaloisGroup K S →* AddMonoid.End A)
    (hρA : ∀ a : A, IsOpen {g : sGaloisGroup K S | ρA g a = a})
    (ρB : sGaloisGroup K S →* AddMonoid.End B)
    (hρB : ∀ b : B, IsOpen {g : sGaloisGroup K S | ρB g b = b})
    (φ : A →+ B →+ Additive (↥(sMaximalExtension K S))ˣ)
    (hφ : ∀ (g : sGaloisGroup K S) (a : A) (b : B),
      φ (ρA g a) (ρB g b) = sUnitsRep K S g (φ a b))
    (fbar : ↥(contCocycles ρA hρA 2)) (gbar : ↥(contCocycles ρB hρB 1))
    (hf : sAlpha K S ρA hρA 2 (QuotientAddGroup.mk fbar) = 0)
    (hg : sAlpha K S ρB hρB 1 (QuotientAddGroup.mk gbar) = 0)
    (hcup : ∃ h₀, contCoboundary (sUnitsRep K S) (sUnitsRepSmooth K S) 2 h₀
      = contCupProduct ρB hρB φ ↑fbar ↑gbar)
    (v : ↥S) :
    (∃ φv, contCoboundary (ρA.comp (decompositionMap K S ↑v).toMonoidHom)
        (fun a => (hρA a).preimage (map_continuous (decompositionMap K S ↑v)))
        1 φv
      = contCochainComap (decompositionMap K S ↑v).toMonoidHom
          (map_continuous (decompositionMap K S ↑v)) 2 ↑fbar)
      ∧ (∃ ψv : B,
          contCoboundary (ρB.comp (decompositionMap K S ↑v).toMonoidHom)
              (fun b => (hρB b).preimage (map_continuous (decompositionMap K S ↑v)))
              0 (LocallyConstant.const _ ψv)
            = contCochainComap (decompositionMap K S ↑v).toMonoidHom
                (map_continuous (decompositionMap K S ↑v)) 1 ↑gbar)
      ∧ ∃ h, contCoboundary (sUnitsRep K S) (sUnitsRepSmooth K S) 2 h
          = contCupProduct ρB hρB φ ↑fbar ↑gbar :=
  sorry


end

section
-- Natural language: Given a Poitou–Tate setup $P$ over fields $F$ and $K$ (with $F$ finite and $K$
-- a number field) and an $F$-module $M$, the global evaluation pairing is the bi-additive map $M
-- \times M^* \to K_S^\times$ sending $(m, x^*)$ to $x^*(m)$, curried as an additive homomorphism $M
-- \to \operatorname{Hom}_{\mathbb{Z}}(M^*, \operatorname{Additive}(K_S^\times)^\times)$.
-- Score: (0 - incorrect, 1 - partially correct, 2 - correct)
-- Comment:
/-- The global evaluation pairing `M × M^* → K_S^×`: `(m, x^*) ↦ x^*(m)`, bi-additive
(curried as an additive homomorphism into homomorphisms). -/
noncomputable def globalEvalPairing {F K M : Type} [Field F] [Fintype F] [Field K]
    [NumberField K] [AddCommGroup M] [Module F M] (P : PoitouTateSetup F K M) :
    M →+ (dualModule P →+ Additive (↥(sMaximalExtension K P.S))ˣ) :=
  AddMonoidHom.mk'
    (fun m => AddMonoidHom.mk' (fun x : dualModule P => x m) (fun _ _ => rfl))
    (fun m m' => AddMonoidHom.ext fun x => map_add x m m')


end

section
-- Natural language: Let $F$ be a field, $K$ a number field, and $M$ an additive commutative group
-- equipped with an $F$-module structure. Let $P$ be a Poitou–Tate setup for $F$, $K$, and $M$, and
-- denote by $G_S$ the Galois group of $K$ relative to the set $P.S$. For every $g \in G_S$, every
-- $m \in M$, and every $x^*$ in the dual module $M^* = \operatorname{Hom}_{\mathbb{Z}}(M,
-- K_S^\times)$, the global evaluation pairing $\langle \cdot, \cdot \rangle \colon M \times M^* \to
-- K_S^\times$ satisfies $\langle \rho(g)(m), g \cdot x^* \rangle = g \cdot \langle m, x^* \rangle$,
-- where $\rho(g)$ is the action of $g$ on $M$, $g \cdot x^*$ is the dual action on $M^*$, and $g
-- \cdot (\cdot)$ is the natural action of $G_S$ on $K_S^\times$.
-- Score: (0 - incorrect, 1 - partially correct, 2 - correct)
-- Comment:
/-- The global evaluation pairing `M × M^* → K_S^×` is `G_S`-equivariant:
`⟨g·m, g·x^*⟩ = g·⟨m, x^*⟩` for all `g ∈ G_S` (actions: `ρ` on `M`, the dual action on
`M^*`, the natural action on `K_S^×`). -/
theorem globalEvalPairingEquivariant {F K M : Type} [Field F] [Fintype F] [Field K]
    [NumberField K] [AddCommGroup M] [Module F M] (P : PoitouTateSetup F K M) :
    ∀ (g : sGaloisGroup K P.S) (m : M) (x : dualModule P),
      globalEvalPairing P (setupRho P g m) (dualModuleRep P g x)
        = sUnitsRep K P.S g (globalEvalPairing P m x) :=
  sorry


end

section
-- Natural language: Let $F$ be a finite field, $K$ a totally real number field, $S$ a set of primes
-- of $K$ containing all archimedean places, and $M$ a finite $F[G_S]$-module whose order is a unit
-- in the ring of $S$-integers of $K$, where $G_S = \operatorname{Gal}(K_S/K)$ acts continuously on
-- $M$ with open point stabilizers. If $n = |M|$, then for every element $x$ of the continuous
-- cohomology group $H^3(G_S, K_S^\times)$ whose additive order equals $n$, we have $x = 0$.
-- Score: (0 - incorrect, 1 - partially correct, 2 - correct)
-- Comment:
/-- (Lemma 4.3.) Let `n = |M|` (the order of the finite module `M`). There is no
non-zero element of (additive) order `n` in `H^3(G_S, K_S^×)`: every element whose
order equals `n` is zero. -/
theorem noTorsionH3 {F K M : Type} [Field F] [Fintype F] [Field K]
    [NumberField K] [AddCommGroup M] [Module F M] (P : PoitouTateSetup F K M) :
    ∀ x : contCohomologyGrp (sUnitsRep K P.S) (sUnitsRepSmooth K P.S) 3,
      addOrderOf x = Nat.card M → x = 0 :=
  sorry


end

section
-- Natural language: Let $F$ be a finite field, $K$ a totally real number field, $M$ a finite
-- $F[G_S]$-module, and $P$ the associated Poitou–Tate setup.
-- For every $f$ belonging to $\operatorname{Ker}^2(G_S,M)$ (the kernel of $\alpha_2$) and for every
-- $g$ in $H^1(G_S,M^*)$ such that $\operatorname{sAlpha}_K(P.S, M^*, M^*_{\text{smooth}},1)(g)=0$
-- (i.e. $g$ lies in $\operatorname{Ker}^1(G_S,M^*)$), the cup product $f\cup g$ with respect to the
-- global evaluation pairing $M\times M^*\to K_S^\times$ vanishes in $H^3(G_S,K_S^\times)$.
-- Score: (0 - incorrect, 1 - partially correct, 2 - correct)
-- Comment:
/-- (Claim 4.4.) Fix `f ∈ Ker²(G_S, M)` (the kernel of `α_2`) and
`g ∈ Ker¹(G_S, M^*)` (the kernel of the product-restriction map on `H^1(G_S, M^*)`,
expressed by the vanishing equation `sAlpha … g = 0`). Then the cup product
`f ∪ g = 0` in `H^3(G_S, K_S^×)`, the cup product being taken with respect to the
global evaluation pairing `M × M^* → K_S^×` in degrees `2 + 1 = 3`. -/
theorem cupProductZero {F K M : Type} [Field F] [Fintype F] [Field K]
    [NumberField K] [AddCommGroup M] [Module F M] (P : PoitouTateSetup F K M) :
    ∀ f, f ∈ KerI P 2 →
      ∀ g : contCohomologyGrp (dualModuleRep P) (dualModuleRepSmooth P) 1,
        sAlpha K P.S (dualModuleRep P) (dualModuleRepSmooth P) 1 g = 0 →
          contCohomologyCup (setupRho P) P.continuous_ρ
            (dualModuleRep P) (dualModuleRepSmooth P)
            (sUnitsRep K P.S) (sUnitsRepSmooth K P.S)
            (globalEvalPairing P) (globalEvalPairingEquivariant P) 2 1 f g = 0 :=
  sorry


end

section
-- Natural language: Let $A$ and $B$ be abelian groups equipped with continuous $G_S$-actions
-- $\rho_A$, $\rho_B$ having open point stabilizers, and let $\phi : A \times B \to K_S^\times$ be a
-- bi-additive $G_S$-equivariant pairing.
-- Let $\bar f \in Z^2(G_S, A)$ and $\bar g \in Z^1(G_S, B)$ be continuous cocycles whose classes
-- lie in $\operatorname{Ker}^2(G_S, A)$ and $\operatorname{Ker}^1(G_S, B)$ respectively, fix a
-- place $v \in S$, choose $\psi_v \in B$ such that $d^0\psi_v = \operatorname{res}_v \bar g$ (as
-- constant $0$-cochains), and choose $h \in C^2(G_S, K_S^\times)$ such that $dh = \bar f \cup \bar
-- g$.
-- Then the local $2$-cochain $\operatorname{res}_v \bar f \cup \psi_v - \operatorname{res}_v h$,
-- pushed forward to $\overline{K}_v^\times$ via the natural map $\iota_v$, is a continuous
-- $2$-cocycle for the $G_v$-action on $\overline{K}_v^\times$.
-- Score: (0 - incorrect, 1 - partially correct, 2 - correct)
-- Comment:
/-- (Claim 4.5; stated for a general bi-additive `G_S`-equivariant pairing
`φ : A → B → K_S^×` — the source's case is the evaluation pairing with `A = M`,
`B = M^*`.) Let `fbar ∈ Z^2(G_S, A)` and `gbar ∈ Z^1(G_S, B)` have classes in
`Ker^2(G_S, A)` resp. `Ker^1(G_S, B)`, and fix `v ∈ S`, `ψ_v ∈ B` with
`d⁰ψ_v = res_v gbar`, and `h ∈ C^2(G_S, K_S^×)` with `dh = fbar ∪ gbar`. Set
`x_v = res_v fbar ∪ ψ_v - res_v h` (values pushed into `K̄_v^×` along `ι_v`). Then
`x_v` is a `2`-cocycle for the `G_v`-action on `K̄_v^×`. (Part (ii) of Claim 4.5 is
the separate item `cocycleClaimDiff`.) -/
theorem cocycleClaim (K : Type*) [Field K] [NumberField K]
    (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
    {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    (ρA : sGaloisGroup K S →* AddMonoid.End A)
    (hρA : ∀ a : A, IsOpen {g : sGaloisGroup K S | ρA g a = a})
    (ρB : sGaloisGroup K S →* AddMonoid.End B)
    (hρB : ∀ b : B, IsOpen {g : sGaloisGroup K S | ρB g b = b})
    (φ : A →+ B →+ Additive (↥(sMaximalExtension K S))ˣ)
    (hφ : ∀ (g : sGaloisGroup K S) (a : A) (b : B),
      φ (ρA g a) (ρB g b) = sUnitsRep K S g (φ a b))
    (fbar : ↥(contCocycles ρA hρA 2)) (gbar : ↥(contCocycles ρB hρB 1))
    (hf : sAlpha K S ρA hρA 2 (QuotientAddGroup.mk fbar) = 0)
    (hg : sAlpha K S ρB hρB 1 (QuotientAddGroup.mk gbar) = 0)
    (v : ↥S) (ψv : B)
    (hψ : contCoboundary (ρB.comp (decompositionMap K S ↑v).toMonoidHom)
        (fun b => (hρB b).preimage (map_continuous (decompositionMap K S ↑v)))
        0 (LocallyConstant.const _ ψv)
      = contCochainComap (decompositionMap K S ↑v).toMonoidHom
          (map_continuous (decompositionMap K S ↑v)) 1 ↑gbar)
    (h : contCochain (sGaloisGroup K S) (Additive (↥(sMaximalExtension K S))ˣ) 2)
    (hh : contCoboundary (sUnitsRep K S) (sUnitsRepSmooth K S) 2 h
      = contCupProduct ρB hρB φ ↑fbar ↑gbar) :
    (LocallyConstant.map ⇑(coeffKStoLocal K S ↑v)
        (contCupProduct (ρB.comp (decompositionMap K S ↑v).toMonoidHom)
            (fun b => (hρB b).preimage (map_continuous (decompositionMap K S ↑v)))
            φ (i := 2) (j := 0)
            (contCochainComap (decompositionMap K S ↑v).toMonoidHom
              (map_continuous (decompositionMap K S ↑v)) 2 ↑fbar)
            (LocallyConstant.const _ ψv)
          - contCochainComap (decompositionMap K S ↑v).toMonoidHom
              (map_continuous (decompositionMap K S ↑v)) 2 h)
      ∈ contCocycles (localBarUnitsRep K ↑v) (localBarUnitsRepSmooth K ↑v) 2)
  :=
  sorry


end

section
-- Natural language: Let $K$ be a number field, $S$ a set of finite primes of $K$, and $A,B$
-- discrete $G_S$-modules with continuous actions $\rho_A,\rho_B$ and a bi-additive
-- $G_S$-equivariant pairing $\phi : A \to B \to K_S^\times$.
-- Let $\bar f \in Z^2(G_S,A)$ and $\bar g \in Z^1(G_S,B)$ be continuous cocycles whose classes lie
-- in $\operatorname{Ker}^2(G_S,A)$ and $\operatorname{Ker}^1(G_S,B)$ respectively (i.e.
-- $sAlpha(\bar f)=0$ and $sAlpha(\bar g)=0$), and assume that the cup product $\bar f \cup \bar g$
-- is a global coboundary.
-- For each $v\in S$, choose (via the choices lemma) a continuous $1$-cochain $\phi_v$ with
-- $d^1\phi_v = \operatorname{res}_v\bar f$, an element $\psi_v\in B$ with $d^0\psi_v =
-- \operatorname{res}_v\bar g$, and a $2$-cochain $h$ with $dh = \bar f\cup\bar g$; then set $x_v =
-- \operatorname{res}_v\bar f \cup \psi_v - \operatorname{res}_v h$, which is a local $2$-cocycle
-- valued in $\overline{K}_v^\times$.
-- The *kernel pairing* $\langle\bar f,\bar g\rangle$ is defined to be the (finitely supported) sum
-- over $v\in S$ of $\operatorname{inv}_{G_v}(x_v) \in \mathbb{Q}/\mathbb{Z}$, where
-- $\operatorname{inv}_{G_v}$ is the local invariant map.
-- Score: (0 - incorrect, 1 - partially correct, 2 - correct)
-- Comment:
/-- The generic kernel pairing, at the level of representing cocycles: for discrete
`G_S`-modules `A, B` with a bi-additive `G_S`-equivariant pairing `φ : A → B → K_S^×`,
given cocycles `fbar ∈ Z^2(G_S, A)`, `gbar ∈ Z^1(G_S, B)` whose classes lie in
`Ker^2(G_S, A)` resp. `Ker^1(G_S, B)` and with `fbar ∪ gbar` a global coboundary, the
value `⟨fbar, gbar⟩ := ∑ᶠ_{v ∈ S} inv_{G_v}(x_v) ∈ ℚ/ℤ`, where for choice data
`(ψ_v, h)` from the choices lemma (via `Classical.choose`),
`x_v = res_v fbar ∪ ψ_v - res_v h` is a local `2`-cocycle valued in `K̄_v^×`
(Claim 4.5(i)), and `inv_{G_v}` is the local invariant map. -/
noncomputable def kernelPairing (K : Type*) [Field K] [NumberField K]
    (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
    {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    (ρA : sGaloisGroup K S →* AddMonoid.End A)
    (hρA : ∀ a : A, IsOpen {g : sGaloisGroup K S | ρA g a = a})
    (ρB : sGaloisGroup K S →* AddMonoid.End B)
    (hρB : ∀ b : B, IsOpen {g : sGaloisGroup K S | ρB g b = b})
    (φ : A →+ B →+ Additive (↥(sMaximalExtension K S))ˣ)
    (hφ : ∀ (g : sGaloisGroup K S) (a : A) (b : B),
      φ (ρA g a) (ρB g b) = sUnitsRep K S g (φ a b))
    (fbar : ↥(contCocycles ρA hρA 2)) (gbar : ↥(contCocycles ρB hρB 1))
    (hf : sAlpha K S ρA hρA 2 (QuotientAddGroup.mk fbar) = 0)
    (hg : sAlpha K S ρB hρB 1 (QuotientAddGroup.mk gbar) = 0)
    (hcup : ∃ h₀, contCoboundary (sUnitsRep K S) (sUnitsRepSmooth K S) 2 h₀
      = contCupProduct ρB hρB φ ↑fbar ↑gbar) : ratCircle :=
  ∑ᶠ v : ↥S, invGv K ↑v (QuotientAddGroup.mk
    ⟨_, cocycleClaim K S ρA hρA ρB hρB φ hφ fbar gbar hf hg v
      (Classical.choose
        ((kernelPairingChoices K S ρA hρA ρB hρB φ hφ fbar gbar hf hg hcup v).2.1))
      (Classical.choose_spec
        ((kernelPairingChoices K S ρA hρA ρB hρB φ hφ fbar gbar hf hg hcup v).2.1))
      (Classical.choose hcup)
      (Classical.choose_spec hcup)⟩)


end

section
-- Natural language: Let $F$ be a finite field, $K$ a totally real number field, $M$ a finite
-- $F[G_S]$-module, and $P$ a Poitou–Tate setup for $F$, $K$, $M$.
-- For classes $f \in \operatorname{Ker}^2(G_S, M)$ and $g \in \operatorname{Ker}^1(G_S, M^*)$ such
-- that $hf$ witnesses $f$ lying in the kernel of $\alpha_2$ and $hg$ witnesses $g$ lying in the
-- kernel of $\alpha_1$ (i.e. $sAlpha(K, P.S, \text{dualModuleRep } P, \text{dualModuleRepSmooth }
-- P, 1, g) = 0$), and such that there exists a $2$-cochain $h_0$ whose coboundary equals the cup
-- product of the chosen representing cocycles $\operatorname{Quotient.out}(f)$ and
-- $\operatorname{Quotient.out}(g)$ under the global evaluation pairing, the *explicit pairing*
-- $\langle f, g \rangle$ is defined to be the value in $\mathbb{Q}/\mathbb{Z}$ obtained by applying
-- the generic kernel pairing (with the evaluation pairing $M \times M^* \to K_S^\times$) to those
-- representatives together with the given hypotheses.
-- Score: (0 - incorrect, 1 - partially correct, 2 - correct)
-- Comment:
/-- (Section 4.2 explicit pairing.) The explicit pairing
`Ker^2(G_S, M) × Ker^1(G_S, M^*) → ℚ/ℤ`, `⟨f, g⟩ := ∑_{v ∈ S} inv_{G_v}(x_v)`: the
instance of the generic kernel pairing `kernelPairing` for the evaluation pairing
`M × M^* → K_S^×`, applied to the chosen representing cocycles `Quotient.out f`,
`Quotient.out g` of the classes `f ∈ Ker^2(G_S, M)`, `g ∈ Ker^1(G_S, M^*)` (the
hypothesis `hcup` — that the cup product of these representatives is a global
coboundary — is supplied by Claim 4.4). -/
noncomputable def explicitPairing {F K M : Type} [Field F] [Fintype F] [Field K]
    [NumberField K] [AddCommGroup M] [Module F M] (P : PoitouTateSetup F K M)
    (f : contCohomologyGrp (setupRho P) P.continuous_ρ 2)
    (g : contCohomologyGrp (dualModuleRep P) (dualModuleRepSmooth P) 1)
    (hf : f ∈ KerI P 2)
    (hg : sAlpha K P.S (dualModuleRep P) (dualModuleRepSmooth P) 1 g = 0)
    (hcup : ∃ h₀, contCoboundary (sUnitsRep K P.S) (sUnitsRepSmooth K P.S) 2 h₀
      = contCupProduct (dualModuleRep P) (dualModuleRepSmooth P)
          (globalEvalPairing P) ↑(Quotient.out f) ↑(Quotient.out g)) : ratCircle :=
  kernelPairing K P.S (setupRho P) P.continuous_ρ
    (dualModuleRep P) (dualModuleRepSmooth P)
    (globalEvalPairing P) (globalEvalPairingEquivariant P)
    (Quotient.out f) (Quotient.out g)
    (by
      have h1 : QuotientAddGroup.mk (Quotient.out f) = f := Quotient.out_eq f
      rw [h1]
      exact AddMonoidHom.mem_ker.mp hf)
    (by
      have h2 : QuotientAddGroup.mk (Quotient.out g) = g := Quotient.out_eq g
      rw [h2]
      exact hg)
    hcup


end

section
-- Natural language: Let $F$ be a finite field, $K$ a totally real number field, $M$ a finite
-- $F[G_S]$-module, and $P$ a Poitou–Tate setup for these data.
-- Then there exists a map $\Phi$ from $\operatorname{Ker}^2(G_S,M)$ to the additive group of
-- homomorphisms $\operatorname{Ker}^1(G_S,M^*)\to\mathbb{Q}/\mathbb{Z}$ (where
-- $\operatorname{Ker}^1(G_S,M^*)$ is the kernel of the product‑restriction map on $H^1(G_S,M^*)$)
-- such that
-- 
-- 1. for every $f\in\operatorname{Ker}^2(G_S,M)$, every $x\in\operatorname{Ker}^1(G_S,M^*)$, and
-- every witness $h_{\text{cup}}$ that the cup product of the representing cocycles is a global
-- coboundary, we have $\Phi(f)(x)=\langle f,x\rangle$, where $\langle\cdot,\cdot\rangle$ is the
-- explicit pairing of Section 4.2;
-- 2. $\Phi$ is injective; and
-- 3. $\Phi$ is surjective.
-- Score: (0 - incorrect, 1 - partially correct, 2 - correct)
-- Comment:
/-- (Proposition 4.8.) The explicit pairing `Ker^2(G_S, M) × Ker^1(G_S, M^*) → ℚ/ℤ`
is non-degenerate, and in fact perfect (`M` being finite): there is a map `Φ` sending
each class `f ∈ Ker^2(G_S, M)` to an additive functional on `Ker^1(G_S, M^*)` (the
kernel of the product-restriction map on `H^1(G_S, M^*)`, as an additive subgroup),
such that: (1) `Φ` agrees with the explicit pairing `⟨f, g⟩` whenever a witness that
the cup product of the representing cocycles is a global coboundary is supplied
(such a witness always exists, by Claim 4.4 — this clause pins `Φ` uniquely); (2) `Φ`
is injective — this is non-degeneracy in `f`; and (3) `Φ` is surjective onto the
dual, i.e. the pairing is perfect. -/
theorem pairingNonDegenerate {F K M : Type} [Field F] [Fintype F] [Field K]
    [NumberField K] [AddCommGroup M] [Module F M] (P : PoitouTateSetup F K M) :
    ∃ Φ : ↥(KerI P 2) →
        (↥((sAlpha K P.S (dualModuleRep P) (dualModuleRepSmooth P) 1).ker)
          →+ ratCircle),
      (∀ (f : ↥(KerI P 2))
        (x : ↥((sAlpha K P.S (dualModuleRep P) (dualModuleRepSmooth P) 1).ker))
        (hcup : ∃ h₀,
          contCoboundary (sUnitsRep K P.S) (sUnitsRepSmooth K P.S) 2 h₀
            = contCupProduct (dualModuleRep P) (dualModuleRepSmooth P)
                (globalEvalPairing P) ↑(Quotient.out (↑f :
                  contCohomologyGrp (setupRho P) P.continuous_ρ 2))
                ↑(Quotient.out (↑x :
                  contCohomologyGrp (dualModuleRep P) (dualModuleRepSmooth P) 1))),
        Φ f x = explicitPairing P ↑f ↑x f.2 (AddMonoidHom.mem_ker.mp x.2) hcup)
      ∧ Function.Injective Φ ∧ Function.Surjective Φ :=
  sorry


end

section
-- Natural language: Let $F$ be a field, $K$ a number field, and $M$ an $F$-vector space (viewed as
-- an additive group with $F$-module structure). Fix a Poitou–Tate setup $P$ for $F,K,M$ (so in
-- particular a finite set $S$ of places of $K$). Let $f$ be an element of the continuous cohomology
-- group $H^2(G_S, M^*)$ and $g$ an element of $H^1(G_S, M)$ (where $M^* =
-- \operatorname{Hom}_{\mathbb{Z}}(M, K_S^\times)$ and $G_S$ acts on $M$ via $\rho$ and on $M^*$ via
-- the dual action). Assume that $f$ lies in the kernel of the product‑restriction map $\alpha_2$,
-- i.e. $\alpha_2(f)=0$ (hypothesis $hf$), that $g$ belongs to $\operatorname{Ker}^1(G_S,M)$
-- (hypothesis $hg$), and that there exists a $2$-cochain $h_0$ such that the coboundary of $h_0$
-- equals the cup product (with respect to the flipped evaluation pairing $M^*\times M\to
-- K_S^\times$) of the chosen representing cocycles $\operatorname{out}(f)$ and
-- $\operatorname{out}(g)$ (hypothesis $hcup$). Then the value of the generic kernel pairing
-- (applied to the flipped evaluation pairing, the equivariance data provided by the global
-- evaluation pairing, and the representatives $\operatorname{out}(f),\operatorname{out}(g)$) yields
-- an element of $\mathbb{Q}/\mathbb{Z}$. This element is denoted
-- $\operatorname{explicitPairingDual}(f,g,hf,hg,hcup)$.
-- Score: (0 - incorrect, 1 - partially correct, 2 - correct)
-- Comment:
/-- The explicit pairing with the roles of `M` and `M^*` exchanged:
`Ker^2(G_S, M^*) × Ker^1(G_S, M) → ℚ/ℤ` — the instance of the generic kernel pairing
`kernelPairing` for the flipped evaluation pairing `M^* × M → K_S^×`
(`(globalEvalPairing P).flip`), applied to the representing cocycles `Quotient.out f`,
`Quotient.out g` of classes `f ∈ Ker^2(G_S, M^*)` (hypothesis `hf`, vanishing under
the product-restriction map) and `g ∈ Ker^1(G_S, M)` (hypothesis `hg`); the
hypothesis `hcup` states that the cup product of these representatives is a global
coboundary. -/
noncomputable def explicitPairingDual {F K M : Type} [Field F] [Fintype F] [Field K]
    [NumberField K] [AddCommGroup M] [Module F M] (P : PoitouTateSetup F K M)
    (f : contCohomologyGrp (dualModuleRep P) (dualModuleRepSmooth P) 2)
    (g : contCohomologyGrp (setupRho P) P.continuous_ρ 1)
    (hf : sAlpha K P.S (dualModuleRep P) (dualModuleRepSmooth P) 2 f = 0)
    (hg : g ∈ KerI P 1)
    (hcup : ∃ h₀, contCoboundary (sUnitsRep K P.S) (sUnitsRepSmooth K P.S) 2 h₀
      = contCupProduct (setupRho P) P.continuous_ρ
          ((globalEvalPairing P).flip) ↑(Quotient.out f) ↑(Quotient.out g)) :
    ratCircle :=
  kernelPairing K P.S (dualModuleRep P) (dualModuleRepSmooth P)
    (setupRho P) P.continuous_ρ
    ((globalEvalPairing P).flip)
    (fun σ x m => globalEvalPairingEquivariant P σ m x)
    (Quotient.out f) (Quotient.out g)
    (by
      have h1 : QuotientAddGroup.mk (Quotient.out f) = f := Quotient.out_eq f
      rw [h1]
      exact hf)
    (by
      have h2 : QuotientAddGroup.mk (Quotient.out g) = g := Quotient.out_eq g
      rw [h2]
      exact AddMonoidHom.mem_ker.mp hg)
    hcup


end

section
-- Natural language: Let $F$ be a field, $K$ a number field, $M$ an $\operatorname{AddCommGroup}$
-- with an $F$-module structure, and $P$ a Poitou–Tate setup for $F$, $K$, $M$.
-- Fix $g \in \operatorname{Ker}^1(G_S, M)$ (hypothesis $hg$) and classes $f, f' \in
-- \operatorname{Ker}^2(G_S, M^*)$ (hypotheses $hf$, $hf'$, and $hff'$ for the sum $f+f'$).
-- Assume there exist witnesses $hcup$, $hcup'$, $hcup''$ such that the cup product of the
-- representing cocycles of $(f,g)$, $(f',g)$, and $(f+f',g)$ are global coboundaries.
-- Then the exchanged explicit pairing satisfies
-- \[
-- \langle f + f', g \rangle = \langle f, g \rangle + \langle f', g \rangle .
-- \]
-- Score: (0 - incorrect, 1 - partially correct, 2 - correct)
-- Comment:
/-- The exchanged explicit pairing `Ker^2(G_S, M^*) × Ker^1(G_S, M) → ℚ/ℤ` is additive
in its first argument: for fixed `g ∈ Ker^1(G_S, M)` and classes `f, f'` in
`Ker^2(G_S, M^*)` (hypotheses `hf`, `hf'`, and `hff'` for the sum — the latter follows
from the former two), and any witnesses `hcup`, `hcup'`, `hcup''` that the relevant
cup products of representing cocycles are global coboundaries, the pairing satisfies
`⟨f + f', g⟩ = ⟨f, g⟩ + ⟨f', g⟩`. -/
theorem dualPairingAdditive {F K M : Type} [Field F] [Fintype F] [Field K]
    [NumberField K] [AddCommGroup M] [Module F M] (P : PoitouTateSetup F K M)
    (g : contCohomologyGrp (setupRho P) P.continuous_ρ 1) (hg : g ∈ KerI P 1)
    (f f' : contCohomologyGrp (dualModuleRep P) (dualModuleRepSmooth P) 2)
    (hf : sAlpha K P.S (dualModuleRep P) (dualModuleRepSmooth P) 2 f = 0)
    (hf' : sAlpha K P.S (dualModuleRep P) (dualModuleRepSmooth P) 2 f' = 0)
    (hff' : sAlpha K P.S (dualModuleRep P) (dualModuleRepSmooth P) 2 (f + f') = 0)
    (hcup : ∃ h₀, contCoboundary (sUnitsRep K P.S) (sUnitsRepSmooth K P.S) 2 h₀
      = contCupProduct (setupRho P) P.continuous_ρ
          ((globalEvalPairing P).flip) ↑(Quotient.out f) ↑(Quotient.out g))
    (hcup' : ∃ h₀, contCoboundary (sUnitsRep K P.S) (sUnitsRepSmooth K P.S) 2 h₀
      = contCupProduct (setupRho P) P.continuous_ρ
          ((globalEvalPairing P).flip) ↑(Quotient.out f') ↑(Quotient.out g))
    (hcup'' : ∃ h₀, contCoboundary (sUnitsRep K P.S) (sUnitsRepSmooth K P.S) 2 h₀
      = contCupProduct (setupRho P) P.continuous_ρ
          ((globalEvalPairing P).flip) ↑(Quotient.out (f + f')) ↑(Quotient.out g)) :
    explicitPairingDual P (f + f') g hff' hg hcup''
      = explicitPairingDual P f g hf hg hcup
        + explicitPairingDual P f' g hf' hg hcup' :=
  sorry


end

section
-- Natural language: Let $F$ be a field with $F$ finite, let $K$ be a number field, let $M$ be an
-- additive commutative group with an $F$-module structure, and let $P$ be a Poitou–Tate setup for
-- $F$, $K$, $M$. Then there exists a map $\Psi : \operatorname{Ker}^1(G_S,M) \to
-- \big(\ker(\alpha^2_{K,S}(M^*))\big)^{\vee}$ (where $\alpha^2_{K,S}(M^*)$ is the
-- product-restriction map on $H^2(G_S,M^*)$ and $(-)^{\vee}$ denotes
-- $\operatorname{Hom}_{\mathbb{Z}}(-,\mathbb{Q}/\mathbb{Z})$) such that for every $g \in
-- \operatorname{Ker}^1(G_S,M)$ and every $x \in \ker(\alpha^2_{K,S}(M^*))$, if there exists an
-- $h_0$ for which the coboundary of $h_0$ equals the cup product (with respect to the flipped
-- evaluation pairing) of the representing cocycles of $x$ and $g$, then $\Psi(g)(x)$ equals the
-- exchanged explicit pairing $\langle x,g\rangle$; moreover $\Psi$ is injective and surjective.
-- Score: (0 - incorrect, 1 - partially correct, 2 - correct)
-- Comment:
/-- The exchanged explicit pairing `Ker^2(G_S, M^*) × Ker^1(G_S, M) → ℚ/ℤ` is perfect:
the induced map `Ψ : Ker^1(G_S, M) → (Ker^2(G_S, M^*))^∨`, `g ↦ ⟨·, g⟩`, is injective
and surjective. `Ψ` is pinned by the property that it agrees with the exchanged
explicit pairing `⟨f, g⟩` whenever a witness that the cup product of the representing
cocycles is a global coboundary is supplied (such a witness always exists). (This is
the instance of Proposition 4.8 used to define the connecting map `ψ`.) -/
theorem dualPairingPerfect {F K M : Type} [Field F] [Fintype F] [Field K]
    [NumberField K] [AddCommGroup M] [Module F M] (P : PoitouTateSetup F K M) :
    ∃ Ψ : ↥(KerI P 1) →
        (↥((sAlpha K P.S (dualModuleRep P) (dualModuleRepSmooth P) 2).ker)
          →+ ratCircle),
      (∀ (g : ↥(KerI P 1))
        (x : ↥((sAlpha K P.S (dualModuleRep P) (dualModuleRepSmooth P) 2).ker))
        (hcup : ∃ h₀,
          contCoboundary (sUnitsRep K P.S) (sUnitsRepSmooth K P.S) 2 h₀
            = contCupProduct (setupRho P) P.continuous_ρ
                ((globalEvalPairing P).flip)
                ↑(Quotient.out (↑x :
                  contCohomologyGrp (dualModuleRep P) (dualModuleRepSmooth P) 2))
                ↑(Quotient.out (↑g :
                  contCohomologyGrp (setupRho P) P.continuous_ρ 1))),
        Ψ g x = explicitPairingDual P ↑x ↑g (AddMonoidHom.mem_ker.mp x.2) g.2 hcup)
      ∧ Function.Injective Ψ ∧ Function.Surjective Ψ :=
  sorry


end

section
-- Natural language: Given a Poitou–Tate setup $P$ over fields $F$, $K$ and a finite $F[G_S]$-module
-- $M$, the map $\psi$ is defined to be the inverse of the bijection $\Psi :
-- \operatorname{Ker}^1(G_S, M) \to (\operatorname{Ker}^2(G_S, M^*))^\vee$, $g \mapsto \langle
-- \cdot, g\rangle$, provided by the theorem `dualPairingPerfect` (chosen via choice); concretely,
-- $\psi$ sends a functional $\varphi : \operatorname{Ker}^2(G_S, M^*) \to \mathbb{Q}/\mathbb{Z}$ to
-- the unique class $g \in \operatorname{Ker}^1(G_S, M)$ such that $\langle f, g\rangle =
-- \varphi(f)$ for all $f \in \operatorname{Ker}^2(G_S, M^*)$.
-- Score: (0 - incorrect, 1 - partially correct, 2 - correct)
-- Comment:
/-- (Section 4.2 connecting maps (ii).) The map
`ψ : (Ker^2(G_S, M^*))^∨ → Ker^1(G_S, M)`: the inverse of the bijection
`Ψ : Ker^1(G_S, M) → (Ker^2(G_S, M^*))^∨`, `g ↦ ⟨·, g⟩`, provided by
`dualPairingPerfect` (chosen via choice). Concretely, `ψ` takes a functional
`φ : Ker^2(G_S, M^*) → ℚ/ℤ` to the unique class `g ∈ Ker^1(G_S, M)` with
`⟨f, g⟩ = φ(f)` for all `f ∈ Ker^2(G_S, M^*)`. -/
noncomputable def psiMap {F K M : Type} [Field F] [Fintype F] [Field K]
    [NumberField K] [AddCommGroup M] [Module F M] (P : PoitouTateSetup F K M) :
    (↥((sAlpha K P.S (dualModuleRep P) (dualModuleRepSmooth P) 2).ker)
      →+ ratCircle) → ↥(KerI P 1) :=
  (Equiv.ofBijective (Classical.choose (dualPairingPerfect P))
    ⟨(Classical.choose_spec (dualPairingPerfect P)).2.1,
      (Classical.choose_spec (dualPairingPerfect P)).2.2⟩).symm


end

section
-- Natural language: Let $F$ be a finite field, $K$ a number field, and $M$ a finite-dimensional
-- $F$-vector space (viewed as an additive abelian group with an $F$-module structure). For a
-- Poitou–Tate setup $P$ over $F$, $K$, $M$, the map $\Phi : \operatorname{Ker}^2(G_S, M) \to
-- (\operatorname{Ker}^1(G_S, M^*))^\vee$ given by $f \mapsto \langle f, \cdot \rangle$ is a
-- bijection (by Proposition 4.8). The map $\operatorname{phiMap}_P$ is defined to be the inverse of
-- this bijection; that is, it sends a homomorphism $\varphi : \operatorname{Ker}^1(G_S, M^*) \to
-- \mathbb{Q}/\mathbb{Z}$ to the unique class $f \in \operatorname{Ker}^2(G_S, M)$ such that
-- $\langle f, x \rangle = \varphi(x)$ for all $x \in \operatorname{Ker}^1(G_S, M^*)$.
-- Score: (0 - incorrect, 1 - partially correct, 2 - correct)
-- Comment:
/-- The inverse isomorphism `(Ker^1(G_S, M^*))^∨ → Ker^2(G_S, M)` of the bijection
`Φ : Ker^2(G_S, M) → (Ker^1(G_S, M^*))^∨`, `f ↦ ⟨f, ·⟩`, provided by
`pairingNonDegenerate` (chosen via choice). Concretely, it takes a functional
`φ : Ker^1(G_S, M^*) → ℚ/ℤ` to the unique class `f ∈ Ker^2(G_S, M)` with
`⟨f, x⟩ = φ(x)` for all `x`. (Mirror of `psiMap`; used for the connecting map
`H^1(G_S, M^*)^∨ → H^2(G_S, M)` of the nine-term sequence.) -/
noncomputable def phiMap {F K M : Type} [Field F] [Fintype F] [Field K]
    [NumberField K] [AddCommGroup M] [Module F M] (P : PoitouTateSetup F K M) :
    (↥((sAlpha K P.S (dualModuleRep P) (dualModuleRepSmooth P) 1).ker)
      →+ ratCircle) → ↥(KerI P 2) :=
  (Equiv.ofBijective (Classical.choose (pairingNonDegenerate P))
    ⟨(Classical.choose_spec (pairingNonDegenerate P)).2.1,
      (Classical.choose_spec (pairingNonDegenerate P)).2.2⟩).symm


end

section
-- Natural language: Let $F$ be a finite field of characteristic $p>2$, let $K$ be a totally real
-- number field, let $S$ be a set of finite primes of $K$ (the index set of the setup), and let $M$
-- be a finite $G_S$-module over $F$ whose order is a unit in the ring of $S$-integers.
-- For $i=0,1,2$ let $\alpha_i : H^i(G_S,M) \to \prod_{v\in S} H^i(G_v,M)$ be the product of the
-- restriction maps (item `alphaI`), and let $\beta_i : \prod_{v\in S} H^i(G_v,M) \to
-- H^{2-i}(G_S,M^*)^{\vee}$ be the map (item `betaI`) defined by $\beta_i(x)(y) = \sum_{v\in S}
-- \langle \operatorname{res}_v y, x_v\rangle_v$, where $\langle\cdot,\cdot\rangle_v$ is the local
-- Tate pairing and $(-)^{\vee}$ denotes $\operatorname{Hom}_{\mathbb{Z}}(-,\mathbb{Q}/\mathbb{Z})$.
-- Let $\iota^{\vee} : H^2(G_S,M^*)^{\vee} \to (\operatorname{Ker}^2(G_S,M^*))^{\vee}$ be the dual
-- of the inclusion (item `iotaDual`), and let $\psi : (\operatorname{Ker}^2(G_S,M^*))^{\vee} \to
-- \operatorname{Ker}^1(G_S,M)$ be the inverse of the perfect pairing $\Psi :
-- \operatorname{Ker}^1(G_S,M) \to (\operatorname{Ker}^2(G_S,M^*))^{\vee}$ (item `psiMap`); define
-- $\delta_0 = \psi \circ \iota^{\vee}$.
-- Let $\Phi : \operatorname{Ker}^2(G_S,M) \to (\operatorname{Ker}^1(G_S,M^*))^{\vee}$ be the
-- perfect pairing (item `pairingNonDegenerate`), and let $\phi :
-- (\operatorname{Ker}^1(G_S,M^*))^{\vee} \to \operatorname{Ker}^2(G_S,M)$ be its inverse (item
-- `phiMap`); define $\delta_1 = \phi \circ (\text{restriction to }\operatorname{Ker}^1(G_S,M^*))$,
-- where the restriction is precomposition with the kernel inclusion.
-- Then the following nine-term sequence is exact:
-- 
-- \[
-- 0 \to H^0(G_S,M) \xrightarrow{\alpha_0} \prod_{v\in S} \hat{H}^0(G_v,M) \xrightarrow{\beta_0}
-- H^2(G_S,M^*)^{\vee}
-- \xrightarrow{\delta_0} H^1(G_S,M) \xrightarrow{\alpha_1} \prod_{v\in S} H^1(G_v,M)
-- \xrightarrow{\beta_1} H^1(G_S,M^*)^{\vee}
-- \xrightarrow{\delta_1} H^2(G_S,M) \xrightarrow{\alpha_2} \prod_{v\in S} H^2(G_v,M)
-- \xrightarrow{\beta_2} H^0(G_S,M^*)^{\vee} \to 0.
-- \]
-- 
-- Exactness is expressed by the following nine clauses:
-- 
-- 1. $\alpha_0$ is injective.
-- 2. For every $x \in \prod_{v\in S} \hat{H}^0(G_v,M)$, $\beta_0(x)(y)=0$ for all $y\in
-- H^2(G_S,M^*)$ if and only if there exists $a\in H^0(G_S,M)$ such that $x = \alpha_0(a)$.
-- 3. For every additive functional $\varphi : H^2(G_S,M^*) \to \mathbb{Q}/\mathbb{Z}$,
-- $\delta_0(\varphi)=0$ in $H^1(G_S,M)$ if and only if there exists $x\in \prod_{v\in S}
-- \hat{H}^0(G_v,M)$ such that $\beta_0(x)(y)=\varphi(y)$ for all $y\in H^2(G_S,M^*)$.
-- 4. For every $a\in H^1(G_S,M)$, $\alpha_1(a)=0$ if and only if there exists $\varphi :
-- H^2(G_S,M^*) \to \mathbb{Q}/\mathbb{Z}$ such that $a = \delta_0(\varphi)$.
-- 5. For every $x\in \prod_{v\in S} H^1(G_v,M)$, $\beta_1(x)(y)=0$ for all $y\in H^1(G_S,M^*)$ if
-- and only if there exists $a\in H^1(G_S,M)$ such that $x = \alpha_1(a)$.
-- 6. For every additive functional $\varphi : H
-- Score: (0 - incorrect, 1 - partially correct, 2 - correct)
-- Comment:
/-- (Poitou–Tate; Theorem 5.1.) The nine-term sequence
`0 → H^0(G_S,M) →α₀→ ∏_{v∈S_f} Ĥ^0(G_v,M) →β₀→ H^2(G_S,M^*)^∨`
`  →δ₀→ H^1(G_S,M) →α₁→ ∏_{v∈S_f} H^1(G_v,M) →β₁→ H^1(G_S,M^*)^∨`
`  →δ₁→ H^2(G_S,M) →α₂→ ∏_{v∈S_f} H^2(G_v,M) →β₂→ H^0(G_S,M^*)^∨ → 0`
is exact. (For `p > 2`, `Ĥ^0(G_v,M) = 0` for all archimedean `v`, so the products run
over the finite places `S_f` only — the index set `P.S`; at finite places `Ĥ^0 = H^0`.)
The connecting maps are `δ₀ = ψ ∘ ι^∨` (`psiMap`, `iotaDual`) and
`δ₁ = Φ⁻¹ ∘ (restriction to Ker^1(G_S,M^*))` (`phiMap`, with the restriction given by
precomposition with the kernel inclusion). Exactness is stated by nine clauses:
(1) `α₀` injective; (2) `ker β₀ = im α₀` (`β₀ x` vanishes means `β₀ x y = 0` for all
`y`); (3) `ker δ₀ = im β₀` on additive functionals; (4) `ker α₁ = im δ₀`;
(5) `ker β₁ = im α₁`; (6) `ker δ₁ = im β₁`; (7) `ker α₂ = im δ₁`;
(8) `ker β₂ = im α₂`; (9) `β₂` surjective onto `H^0(G_S,M^*)^∨`. -/
theorem poitouTate {F K M : Type} [Field F] [Fintype F] [Field K]
    [NumberField K] [AddCommGroup M] [Module F M] (P : PoitouTateSetup F K M) :
    Function.Injective ⇑(alphaI P 0)
      ∧ (∀ x, (∀ y, betaI P 0 (by omega) x y = 0) ↔ ∃ a, alphaI P 0 a = x)
      ∧ (∀ φ : contCohomologyGrp (dualModuleRep P) (dualModuleRepSmooth P) 2
            →+ ratCircle,
          (↑(psiMap P (iotaDual P φ)) :
              contCohomologyGrp (setupRho P) P.continuous_ρ 1) = 0
            ↔ ∃ x, ∀ y, betaI P 0 (by omega) x y = φ y)
      ∧ (∀ a : contCohomologyGrp (setupRho P) P.continuous_ρ 1,
          alphaI P 1 a = 0
            ↔ ∃ φ : contCohomologyGrp (dualModuleRep P) (dualModuleRepSmooth P) 2
                →+ ratCircle,
              (↑(psiMap P (iotaDual P φ)) :
                contCohomologyGrp (setupRho P) P.continuous_ρ 1) = a)
      ∧ (∀ x, (∀ y, betaI P 1 (by omega) x y = 0) ↔ ∃ a, alphaI P 1 a = x)
      ∧ (∀ φ : contCohomologyGrp (dualModuleRep P) (dualModuleRepSmooth P) 1
            →+ ratCircle,
          (↑(phiMap P (φ.comp
              (AddMonoidHom.ker
                (sAlpha K P.S (dualModuleRep P) (dualModuleRepSmooth P) 1)).subtype)) :
              contCohomologyGrp (setupRho P) P.continuous_ρ 2) = 0
            ↔ ∃ x, ∀ y, betaI P 1 (by omega) x y = φ y)
      ∧ (∀ a : contCohomologyGrp (setupRho P) P.continuous_ρ 2,
          alphaI P 2 a = 0
            ↔ ∃ φ : contCohomologyGrp (dualModuleRep P) (dualModuleRepSmooth P) 1
                →+ ratCircle,
              (↑(phiMap P (φ.comp
                  (AddMonoidHom.ker (sAlpha K P.S (dualModuleRep P)
                    (dualModuleRepSmooth P) 1)).subtype)) :
                contCohomologyGrp (setupRho P) P.continuous_ρ 2) = a)
      ∧ (∀ x, (∀ y, betaI P 2 (by omega) x y = 0) ↔ ∃ a, alphaI P 2 a = x)
      ∧ ∀ ψ₀ : contCohomologyGrp (dualModuleRep P) (dualModuleRepSmooth P) 0
          →+ ratCircle,
        ∃ x, ∀ y, betaI P 2 (by omega) x y = ψ₀ y :=
  sorry


end

section
-- Natural language: Let $F$ be a finite field, $K$ a totally real number field, $M$ a finite
-- $F[G_S]$-module (with continuous action) whose order is a unit in the ring of $S$-integers, and
-- $v$ a finite prime of $K$ not in $S$. Then the following hold:
-- 
-- (c) $H^i(G_v, M) = 0$ for all $i \ge 3$;
-- (d) $H^i(G_v, M^*) = 0$ for all $i \ge 3$;
-- (a) for every $i \le 2$ and every $x \in H^i(G_v, M^*)$, the map $\langle x, \cdot \rangle \colon
-- H^{2-i}(G_v, M) \to \mathbb{Q}/\mathbb{Z}$ is additive;
-- (b) for every $i \le 2$, the map $x \mapsto \langle x, \cdot \rangle$ from $H^i(G_v, M^*)$ to
-- $\operatorname{Hom}(H^{2-i}(G_v, M), \mathbb{Q}/\mathbb{Z})$ is injective and surjective.
-- Score: (0 - incorrect, 1 - partially correct, 2 - correct)
-- Comment:
/-- (Local Tate duality; Milne, Corollary 2.3.) Clauses (c),(d) first, then (a),(b):
(c) `H^i(G_v, M) = 0` (subsingleton) for `i ≥ 3`; (d) `H^i(G_v, M^*) = 0` for `i ≥ 3`
(for `i > 2` the index `2-i` is negative and negative-degree cohomology vanishes, so
the duality isomorphism in those degrees is exactly this vanishing); (a) for `i ≤ 2`
each `⟨x, ·⟩` (via `localTatePairing`) is additive — an element of the dual; (b) for
`i ≤ 2` the assignment `x ↦ ⟨x,·⟩` is injective and surjective onto the dual
`H^{2-i}(G_v, M)^∨`. -/
theorem localTateDuality {F K M : Type} [Field F] [Fintype F] [Field K]
    [NumberField K] [AddCommGroup M] [Module F M] (P : PoitouTateSetup F K M)
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    (∀ i : ℕ, 3 ≤ i →
        Subsingleton (contCohomologyGrp (localRho P v)
          (fun m => (P.continuous_ρ m).preimage
            (map_continuous (decompositionMap K P.S v))) i))
      ∧ (∀ i : ℕ, 3 ≤ i →
          Subsingleton (contCohomologyGrp
            ((dualModuleRep P).comp (decompositionMap K P.S v).toMonoidHom)
            (fun a => (dualModuleRepSmooth P a).preimage
              (map_continuous (decompositionMap K P.S v))) i))
      ∧ ∀ (i : ℕ) (hi : i ≤ 2),
          (∀ x, ∀ y y',
              localTatePairing P v i hi x (y + y')
                = localTatePairing P v i hi x y + localTatePairing P v i hi x y')
            ∧ (∀ x x',
                (∀ y, localTatePairing P v i hi x y = localTatePairing P v i hi x' y)
                  → x = x')
            ∧ ∀ φ : contCohomologyGrp (localRho P v)
                  (fun m => (P.continuous_ρ m).preimage
                    (map_continuous (decompositionMap K P.S v))) (2 - i)
                    →+ ratCircle,
                ∃ x, ∀ y, localTatePairing P v i hi x y = φ y :=
  sorry


end

section
-- Natural language: Let $F$ be a finite field, $K$ a number field, and $M$ a finitely generated
-- $F$-module (hence finite) that is part of a Poitou–Tate setup $P$ over $F$ and $K$. For any
-- height-one prime $v$ of the ring of integers of $K$, let $G_v$ denote the absolute Galois group
-- of the $v$-adic completion of $K$, and let $\rho_v$ be the action of $G_v$ on $M$ obtained by
-- composing the global action $P.\rho$ with the decomposition map $G_v \to G_S$. Then for every $i
-- \in \mathbb{N}$, the continuous cohomology group $H^i(G_v, M)$ (computed from the complex of
-- continuous inhomogeneous cochains with respect to the action $\rho_v$, which has open point
-- stabilizers) is finite.
-- Score: (0 - incorrect, 1 - partially correct, 2 - correct)
-- Comment:
/-- (Milne, Theorem 2.1, in the setting of the setup, where the coefficient module `M`
is finitely generated over the finite field `F`, hence finite.) The local cohomology
groups `H^i(G_v, M)` are finite for all `i`. -/
theorem localFiniteness {F K M : Type} [Field F] [Fintype F] [Field K]
    [NumberField K] [AddCommGroup M] [Module F M] (P : PoitouTateSetup F K M)
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    ∀ i : ℕ, Finite (contCohomologyGrp (localRho P v)
      (fun m => (P.continuous_ρ m).preimage
        (map_continuous (decompositionMap K P.S v))) i) :=
  sorry


end

section
-- Natural language: Let $G$ be a topological group, $H \trianglelefteq G$ a normal subgroup, $A$ an
-- abelian group with $G$-action $\rho$, and let $g \in G$ and $\varphi \in C^1(H, A)$ be a
-- continuous (locally constant) $1$-cochain of $H$. Then the conjugated function $t \mapsto
-- \rho(g)\,\varphi\big(k \mapsto g^{-1}\, t(k)\, g\big)$ (on one-component tuples $t :
-- \operatorname{Fin} 1 \to H$; the conjugate $g^{-1} t(k) g$ lies in $H$ by normality) is locally
-- constant.
-- Score: (0 - incorrect, 1 - partially correct, 2 - correct)
-- Comment:
/-- Let `G` be a topological group, `H ⊴ G` a normal subgroup, `A` an abelian group
with `G`-action `ρ`, `g ∈ G`, and `φ ∈ C^1(H, A)` a continuous (locally constant)
`1`-cochain of `H`. Then the conjugated function
`t ↦ ρ g (φ (fun k => g⁻¹ * t k * g))` (on one-component tuples `t : Fin 1 → H`; the
conjugate lies in `H` by normality) is locally constant. -/
theorem conjCochainLocallyConstant {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (H : Subgroup G) [hN : H.Normal] {A : Type*}
    [AddCommGroup A] (ρ : G →* AddMonoid.End A) (g : G)
    (φ : contCochain ↥H A 1) :
    IsLocallyConstant (fun t : Fin 1 → ↥H =>
      ρ g (φ (fun k =>
        (⟨g⁻¹ * ↑(t k) * g, by simpa using hN.conj_mem ↑(t k) (t k).2 g⁻¹⟩ :
          ↥H)))) :=
  sorry


end

section
-- Natural language: Let $G$ be a topological group, $H \trianglelefteq G$ a normal subgroup, $A$ an
-- abelian group with $G$-action $\rho$, and $g \in G$. The conjugation operator on continuous
-- $1$-cochains is the map $C^1(H,A) \to C^1(H,A)$ sending $\varphi$ to ${}^{g}\varphi : t \mapsto
-- \rho(g)\,\varphi\big(k \mapsto g^{-1}\, t(k)\, g\big)$, which is locally constant by the lemma
-- conjCochainLocallyConstant.
-- Score: (0 - incorrect, 1 - partially correct, 2 - correct)
-- Comment:
/-- The conjugation operator on continuous `1`-cochains: for a topological group `G`,
a normal subgroup `H ⊴ G`, an abelian group `A` with `G`-action `ρ`, and `g ∈ G`, the
map `C^1(H,A) → C^1(H,A)` sending `φ` to
`ᵍφ : t ↦ ρ g (φ (fun k => g⁻¹ * t k * g))` (locally constant by
`conjCochainLocallyConstant`). -/
noncomputable def conjCochain {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (H : Subgroup G) [hN : H.Normal] {A : Type*}
    [AddCommGroup A] (ρ : G →* AddMonoid.End A) (g : G)
    (φ : contCochain ↥H A 1) : contCochain ↥H A 1 :=
  ⟨fun t : Fin 1 → ↥H =>
      ρ g (φ (fun k =>
        (⟨g⁻¹ * ↑(t k) * g, by simpa using hN.conj_mem ↑(t k) (t k).2 g⁻¹⟩ :
          ↥H))),
    conjCochainLocallyConstant H ρ g φ⟩


end

section
-- Natural language: Let $G$ be a topological group, $H \trianglelefteq G$ a normal subgroup, and
-- $A$ a discrete $G$-module with action $\rho$ such that for every $a \in A$ the stabilizer $\{g
-- \in G \mid \rho(g)(a) = a\}$ is open; $H$ acts on $A$ by restriction. The conjugation operator
-- ${}^{g}\varphi$ defined by $({}^{g}\varphi)(t) = \rho(g)\,\varphi\bigl(k \mapsto g^{-1}\, t(k)\,
-- g\bigr)$ satisfies, as a conjunction of seven clauses: (1) for every $g \in G$ and every
-- $\varphi$ in the set of continuous $1$-cocycles of $H$ with values in $A$, ${}^{g}\varphi$ also
-- lies in that set; (2) for every $g \in G$ and every pair $\varphi,\psi$ of continuous
-- $1$-cochains of $H$, ${}^{g}(\varphi+\psi) = {}^{g}\varphi + {}^{g}\psi$; (3) for every $g \in G$
-- and every $\varphi$ in the subgroup of continuous $1$-coboundaries of $H$, ${}^{g}\varphi$ also
-- lies in that subgroup; (4) for every $g \in G$, every $h \in H$, and every $\varphi$ in the set
-- of continuous $1$-cocycles of $H$, the difference ${}^{g h}\varphi - {}^{g}\varphi$ lies in the
-- subgroup of continuous $1$-coboundaries; (5) for every $g,g' \in G$ and every continuous
-- $1$-cochain $\varphi$, ${}^{g g'}\varphi = {}^{g}({}^{g'}\varphi)$; (6) for every continuous
-- $1$-cochain $\varphi$, ${}^{1}\varphi = \varphi$; and hence (7) there exists a map
-- $\operatorname{act} \colon G/H \to H^1(H,A) \to H^1(H,A)$ such that for every $g \in G$, every
-- $\varphi$ in the set of continuous $1$-cocycles of $H$, and every proof that ${}^{g}\varphi$ is
-- also a continuous $1$-cocycle, $\operatorname{act}([g])([\varphi]) = [{}^{g}\varphi]$.
-- Score: (0 - incorrect, 1 - partially correct, 2 - correct)
-- Comment:
/-- Let `G` be a topological group, `H ⊴ G` a normal subgroup, and `(A, ρ)` a discrete
`G`-module; `H` acts on `A` by restriction. The conjugation operator `conjCochain`
`ᵍφ : t ↦ ρ g (φ (fun k => g⁻¹ * t k * g))`: (1) maps continuous `1`-cocycles of `H`
to `1`-cocycles; (2) is additive in `φ`; (3) maps coboundaries to coboundaries (so the
induced map on `H^1(H,A)` depends only on the class of `φ`); (4) changes a cocycle by
a coboundary when `g` is multiplied on the right by an element of `H`; (5) is
compatible with multiplication (`ᵍᵍ'φ = ᵍ(ᵍ'φ)`) and (6) trivial for `g = 1`; hence
(7) there exists an induced action map `G/H → H^1(H,A) → H^1(H,A)` sending the class
of `g` and the class of a cocycle `φ` to the class of `ᵍφ`. -/
theorem h1ConjActionWellDefined {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (H : Subgroup G) [hN : H.Normal] {A : Type*}
    [AddCommGroup A] (ρ : G →* AddMonoid.End A)
    (hρ : ∀ a : A, IsOpen {g : G | ρ g a = a}) :
    (∀ g : G, ∀ φ ∈ contCocycles (ρ.comp H.subtype)
        (fun a => (hρ a).preimage continuous_subtype_val) 1,
      conjCochain H ρ g φ ∈ contCocycles (ρ.comp H.subtype)
        (fun a => (hρ a).preimage continuous_subtype_val) 1)
      ∧ (∀ (g : G) (φ ψ : contCochain ↥H A 1),
          conjCochain H ρ g (φ + ψ) = conjCochain H ρ g φ + conjCochain H ρ g ψ)
      ∧ (∀ g : G, ∀ φ ∈ contCoboundaries (ρ.comp H.subtype)
            (fun a => (hρ a).preimage continuous_subtype_val) 1,
          conjCochain H ρ g φ ∈ contCoboundaries (ρ.comp H.subtype)
            (fun a => (hρ a).preimage continuous_subtype_val) 1)
      ∧ (∀ (g : G) (h : ↥H), ∀ φ ∈ contCocycles (ρ.comp H.subtype)
            (fun a => (hρ a).preimage continuous_subtype_val) 1,
          conjCochain H ρ (g * ↑h) φ - conjCochain H ρ g φ
            ∈ contCoboundaries (ρ.comp H.subtype)
              (fun a => (hρ a).preimage continuous_subtype_val) 1)
      ∧ (∀ (g g' : G) (φ : contCochain ↥H A 1),
          conjCochain H ρ (g * g') φ = conjCochain H ρ g (conjCochain H ρ g' φ))
      ∧ (∀ φ : contCochain ↥H A 1, conjCochain H ρ 1 φ = φ)
      ∧ ∃ act : G ⧸ H →
            contCohomologyGrp (ρ.comp H.subtype)
              (fun a => (hρ a).preimage continuous_subtype_val) 1 →
            contCohomologyGrp (ρ.comp H.subtype)
              (fun a => (hρ a).preimage continuous_subtype_val) 1,
          ∀ (g : G) (φ : ↥(contCocycles (ρ.comp H.subtype)
              (fun a => (hρ a).preimage continuous_subtype_val) 1))
            (hmem : conjCochain H ρ g ↑φ ∈ contCocycles (ρ.comp H.subtype)
              (fun a => (hρ a).preimage continuous_subtype_val) 1),
            act (QuotientGroup.mk g) (QuotientAddGroup.mk φ)
              = QuotientAddGroup.mk ⟨conjCochain H ρ g ↑φ, hmem⟩ :=
  sorry


end

section
-- Natural language: Let $G$ be a topological group, $H \trianglelefteq G$ a normal subgroup, and
-- $(A,\rho)$ a discrete $G$-module (so that for each $a \in A$ the set $\{g \in G \mid \rho(g)a =
-- a\}$ is open).
-- The conjugation action of $G/H$ on $H^1(H,A)$ is defined to be the map
-- \[
-- G/H \to \operatorname{End}\bigl(H^1(H,A)\bigr)
-- \]
-- that sends the class of $g$ to the map $[\varphi] \mapsto [h \mapsto \rho(g)\varphi(g^{-1}hg)]$,
-- where $H^1(H,A)$ denotes the continuous cohomology group
-- $\operatorname{contCohomologyGrp}(\rho\circ H.\text{subtype}, \dots, 1)$.
-- Score: (0 - incorrect, 1 - partially correct, 2 - correct)
-- Comment:
/-- The conjugation action of `G/H` on `H^1(H,A)`, for a normal subgroup `H ⊴ G` and
a discrete `G`-module `A`: the class of `g` acts by `[φ] ↦ [ᵍφ]` (the descent to
cohomology classes provided by the last clause of `h1ConjActionWellDefined`). Its
fixed points are the invariants `H^1(H,A)^{G/H}`. -/
noncomputable def h1ConjAction {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (H : Subgroup G) [hN : H.Normal] {A : Type*}
    [AddCommGroup A] (ρ : G →* AddMonoid.End A)
    (hρ : ∀ a : A, IsOpen {g : G | ρ g a = a}) :
    G ⧸ H →
      contCohomologyGrp (ρ.comp H.subtype)
        (fun a => (hρ a).preimage continuous_subtype_val) 1 →
      contCohomologyGrp (ρ.comp H.subtype)
        (fun a => (hρ a).preimage continuous_subtype_val) 1 :=
  Classical.choose (h1ConjActionWellDefined H ρ hρ).2.2.2.2.2.2


end

section
-- Natural language: Let $G$ be a topological group, $H \trianglelefteq G$ a normal subgroup, and
-- $A$ a discrete $G$-module with action $\rho$ such that for every $a \in A$ the stabilizer $\{g
-- \in G \mid \rho(g)a = a\}$ is open. Let $N = A^H$ be the subgroup of $H$-invariants (hypothesis:
-- $a \in N$ iff $\rho(h)a = a$ for all $h \in H$), equipped with a discrete $G/H$-action $\sigma$
-- such that for every $a \in N$ the stabilizer $\{q \in G/H \mid \sigma(q)a = a\}$ is open and such
-- that for all $g \in G$ and $a \in N$ we have $(\sigma(\overline{g})a : A) = \rho(g)(a : A)$ in
-- $A$. Then there exist additive group homomorphisms $\mathrm{infl}_1 : H^1(G/H, N) \to H^1(G, A)$,
-- $\mathrm{res}_1 : H^1(G, A) \to H^1(H, A)$, $\mathrm{infl}_2 : H^2(G/H, N) \to H^2(G, A)$, and
-- $\mathrm{tg} : H^1(H, A) \to H^2(G/H, N)$ such that: $\mathrm{infl}_1$ equals the composition of
-- the pullback along $G \to G/H$ with the coefficient map induced by the inclusion $N
-- \hookrightarrow A$ in degree $1$; $\mathrm{res}_1$ equals the pullback along $H \hookrightarrow
-- G$ in degree $1$; $\mathrm{infl}_2$ equals the analogous composition in degree $2$;
-- $\mathrm{infl}_1$ is injective; for every $x \in H^1(G, A)$, $\mathrm{res}_1(x) = 0$ if and only
-- if there exists $y$ such that $\mathrm{infl}_1(y) = x$; for every $x \in H^1(G, A)$ and every $q
-- \in G/H$, the conjugation action of $q$ on $\mathrm{res}_1(x)$ (given by the map
-- $\mathrm{h1ConjAction}$) equals $\mathrm{res}_1(x)$; for all $z, z' \in H^1(H, A)$ that are
-- invariant under the conjugation action for all $q \in G/H$, we have $\mathrm{tg}(z+z') =
-- \mathrm{tg}(z) + \mathrm{tg}(z')$; for every $z \in H^1(H, A)$ that is invariant under the
-- conjugation action for all $q \in G/H$, $\mathrm{tg}(z) = 0$ if and only if there exists $x$ such
-- that $\mathrm{res}_1(x) = z$; and for every $w \in H^2(G/H, N)$, $\mathrm{infl}_2(w) = 0$ if and
-- only if there exists $z \in H^1(H, A)$ that is invariant under the conjugation action for all $q
-- \in G/H$ such that $\mathrm{tg}(z) = w$.
-- Score: (0 - incorrect, 1 - partially correct, 2 - correct)
-- Comment:
/-- (Proposition 1.1; inflation–restriction.) Let `G` be a topological group,
`H ⊴ G` a normal subgroup, and `(A, ρ)` a discrete `G`-module. Let `N ⊆ A` be the
subgroup of `H`-invariants (clause `hN`), equipped with a discrete `G/H`-action `σ`
compatible with `ρ` (clause `hσc`). Then there exist maps: the inflation
`infl₁ : H^1(G/H, A^H) → H^1(G, A)` and `infl₂` in degree `2` (each pinned to be the
composition of pullback along `G → G/H` with the coefficient map of the inclusion
`A^H ↪ A`), the restriction `res₁ : H^1(G, A) → H^1(H, A)` (pinned to be pullback
along `H ↪ G`), and a transgression `tg : H^1(H, A) → H^2(G/H, A^H)`, such that the
sequence `0 → H^1(G/H, A^H) → H^1(G, A) → H^1(H, A)^{G/H} → H^2(G/H, A^H) → H^2(G, A)`
is exact: (1) `infl₁` is injective; (2) `ker res₁ = im infl₁`; (3) `res₁` lands in the
`G/H`-invariants of `H^1(H, A)` (conjugation action `h1ConjAction`); (4) `tg` is
additive on invariant classes; (5) for invariant `z`, `tg z = 0` iff `z` is in the
image of `res₁`; (6) `ker infl₂` is the image under `tg` of the invariant classes. -/
theorem inflationRestriction {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (H : Subgroup G) [hn : H.Normal] {A : Type*}
    [AddCommGroup A] (ρ : G →* AddMonoid.End A)
    (hρ : ∀ a : A, IsOpen {g : G | ρ g a = a})
    (N : AddSubgroup A) (hN : ∀ a : A, a ∈ N ↔ ∀ h : ↥H, ρ ↑h a = a)
    (σ : G ⧸ H →* AddMonoid.End ↥N)
    (hσ : ∀ a : ↥N, IsOpen {q : G ⧸ H | σ q a = a})
    (hσc : ∀ (g : G) (a : ↥N),
      (↑(σ (QuotientGroup.mk g) a) : A) = ρ g ↑a) :
    ∃ (infl1 : contCohomologyGrp σ hσ 1 →+ contCohomologyGrp ρ hρ 1)
      (res1 : contCohomologyGrp ρ hρ 1 →+
        contCohomologyGrp (ρ.comp H.subtype)
          (fun a => (hρ a).preimage continuous_subtype_val) 1)
      (infl2 : contCohomologyGrp σ hσ 2 →+ contCohomologyGrp ρ hρ 2)
      (tg : contCohomologyGrp (ρ.comp H.subtype)
          (fun a => (hρ a).preimage continuous_subtype_val) 1 →
        contCohomologyGrp σ hσ 2),
      infl1 = (contCohomologyCoeffMap (σ.comp (QuotientGroup.mk' H))
          (fun a => (hσ a).preimage continuous_quot_mk)
          ρ hρ N.subtype hσc 1).comp
        (contCohomologyRes σ hσ (QuotientGroup.mk' H) continuous_quot_mk 1)
      ∧ res1 = contCohomologyRes ρ hρ H.subtype continuous_subtype_val 1
      ∧ infl2 = (contCohomologyCoeffMap (σ.comp (QuotientGroup.mk' H))
            (fun a => (hσ a).preimage continuous_quot_mk)
            ρ hρ N.subtype hσc 2).comp
          (contCohomologyRes σ hσ (QuotientGroup.mk' H) continuous_quot_mk 2)
      ∧ Function.Injective infl1
      ∧ (∀ x : contCohomologyGrp ρ hρ 1, res1 x = 0 ↔ ∃ y, infl1 y = x)
      ∧ (∀ (x : contCohomologyGrp ρ hρ 1) (q : G ⧸ H),
          h1ConjAction H ρ hρ q (res1 x) = res1 x)
      ∧ (∀ z z', (∀ q, h1ConjAction H ρ hρ q z = z) →
          (∀ q, h1ConjAction H ρ hρ q z' = z') → tg (z + z') = tg z + tg z')
      ∧ (∀ z, (∀ q, h1ConjAction H ρ hρ q z = z) →
          (tg z = 0 ↔ ∃ x, res1 x = z))
      ∧ ∀ w : contCohomologyGrp σ hσ 2,
          infl2 w = 0 ↔ ∃ z, (∀ q, h1ConjAction H ρ hρ q z = z) ∧ tg z = w :=
  sorry


end

section
-- Natural language: Let $F$ be a finite field, $K$ a totally real number field, and $M$ a finitely
-- generated $F$-module.
-- For a Poitou–Tate setup $P$ over $F$, $K$, and $M$, the dual module $M^* =
-- \operatorname{Hom}_{\mathbb{Z}}(M, K_S^\times)$ is finite, and for every $g$ in the Galois group
-- $G_S = \operatorname{Gal}(K_S/K)$, every $x^* \in M^*$, and every $m \in M$, the action satisfies
-- $(g \cdot x^*)(m) = g\bigl(x^*(g^{-1}m)\bigr)$.
-- Score: (0 - incorrect, 1 - partially correct, 2 - correct)
-- Comment:
/-- (Lemma 4.1.) For `M` finite (as it is in the setup: a finitely generated module
over the finite field `F`), the dual `M^* = Hom_ℤ(M, K_S^×)` is also finite; and the
`G_S`-action on `M^*` is given by `(g·x^*)(x) = g(x^*(g⁻¹x))` (the second conjunct,
which holds by definition of `dualModuleRep`). -/
theorem dualFinite {F K M : Type} [Field F] [Fintype F] [Field K]
    [NumberField K] [AddCommGroup M] [Module F M] (P : PoitouTateSetup F K M) :
    Finite (dualModule P)
      ∧ ∀ (g : sGaloisGroup K P.S) (x : dualModule P) (m : M),
        dualModuleRep P g x m = sUnitsRep K P.S g (x (setupRho P g⁻¹ m)) :=
  sorry


end

section
-- Natural language: Let $K$ be a number field, $S$ a set of finite places of $K$, and $A,B$ abelian
-- groups equipped with continuous $G_S$-actions $\rho_A,\rho_B$ having open point stabilizers. Let
-- $\phi:A\times B\to K_S^\times$ be a bi-additive $G_S$-equivariant pairing. Let $\bar f\in
-- Z^2(G_S,A)$ and $\bar g\in Z^1(G_S,B)$ be continuous cocycles whose classes vanish under the
-- product‑restriction maps $\alpha_2$ and $\alpha_1$ respectively. Fix a place $v\in S$, an element
-- $\psi_v\in B$ such that $d^0\psi_v=\operatorname{res}_v\bar g$, and a continuous $2$-cochain
-- $h\in C^2(G_S,K_S^\times)$ satisfying $dh=\bar f\cup\bar g$. Then for every continuous
-- $1$-cochain $\varphi_v\in C^1(G_v,A)$ with $d^1\varphi_v=\operatorname{res}_v\bar f$, the
-- difference
-- \[
-- \bigl(\operatorname{res}_v\bar f\cup\psi_v-\operatorname{res}_v h\bigr)
-- \;-\;
-- \bigl(\varphi_v\cup\operatorname{res}_v\bar g-\operatorname{res}_v h\bigr),
-- \]
-- with values pushed forward to $\overline{K_v}^\times$ via the coefficient map $\iota_v$, lies in
-- the subgroup of continuous $2$-coboundaries for the $G_v$-action on $\overline{K_v}^\times$.
-- Score: (0 - incorrect, 1 - partially correct, 2 - correct)
-- Comment:
/-- (Claim 4.5(ii); general pairing — the source's case is the evaluation pairing
with `A = M`, `B = M^*`. All cochains/cocycles are continuous.) With hypotheses as in
`cocycleClaim` (discrete actions `hρA`, `hρB`; equivariant pairing `hφ`; cocycles
`fbar`, `gbar` with classes killed by the product-restriction maps `hf`, `hg`;
`ψ_v ∈ B` with `d⁰ψ_v = res_v gbar`; `h` with `dh = fbar ∪ gbar`): for every
continuous `1`-cochain `φ_v ∈ C^1(G_v, A)` with `d¹φ_v = res_v fbar`, the difference
`x_v - y_v` of `x_v = res_v fbar ∪ ψ_v - res_v h` and `y_v = φ_v ∪ res_v gbar - res_v h`
(values pushed into `K̄_v^×` along `ι_v`) is a continuous `2`-coboundary for the
`G_v`-action on `K̄_v^×` — hence the classes of `x_v` and `y_v` in `H^2(G_v, K̄_v^×)`
agree. -/
theorem cocycleClaimDiff (K : Type*) [Field K] [NumberField K]
    (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
    {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    (ρA : sGaloisGroup K S →* AddMonoid.End A)
    (hρA : ∀ a : A, IsOpen {g : sGaloisGroup K S | ρA g a = a})
    (ρB : sGaloisGroup K S →* AddMonoid.End B)
    (hρB : ∀ b : B, IsOpen {g : sGaloisGroup K S | ρB g b = b})
    (φ : A →+ B →+ Additive (↥(sMaximalExtension K S))ˣ)
    (hφ : ∀ (g : sGaloisGroup K S) (a : A) (b : B),
      φ (ρA g a) (ρB g b) = sUnitsRep K S g (φ a b))
    (fbar : ↥(contCocycles ρA hρA 2)) (gbar : ↥(contCocycles ρB hρB 1))
    (hf : sAlpha K S ρA hρA 2 (QuotientAddGroup.mk fbar) = 0)
    (hg : sAlpha K S ρB hρB 1 (QuotientAddGroup.mk gbar) = 0)
    (v : ↥S) (ψv : B)
    (hψ : contCoboundary (ρB.comp (decompositionMap K S ↑v).toMonoidHom)
        (fun b => (hρB b).preimage (map_continuous (decompositionMap K S ↑v)))
        0 (LocallyConstant.const _ ψv)
      = contCochainComap (decompositionMap K S ↑v).toMonoidHom
          (map_continuous (decompositionMap K S ↑v)) 1 ↑gbar)
    (h : contCochain (sGaloisGroup K S) (Additive (↥(sMaximalExtension K S))ˣ) 2)
    (hh : contCoboundary (sUnitsRep K S) (sUnitsRepSmooth K S) 2 h
      = contCupProduct ρB hρB φ ↑fbar ↑gbar) :
    ∀ φv, contCoboundary (ρA.comp (decompositionMap K S ↑v).toMonoidHom)
          (fun a => (hρA a).preimage (map_continuous (decompositionMap K S ↑v)))
          1 φv
        = contCochainComap (decompositionMap K S ↑v).toMonoidHom
            (map_continuous (decompositionMap K S ↑v)) 2 ↑fbar →
      LocallyConstant.map ⇑(coeffKStoLocal K S ↑v)
          (contCupProduct (ρB.comp (decompositionMap K S ↑v).toMonoidHom)
              (fun b => (hρB b).preimage (map_continuous (decompositionMap K S ↑v)))
              φ (i := 2) (j := 0)
              (contCochainComap (decompositionMap K S ↑v).toMonoidHom
                (map_continuous (decompositionMap K S ↑v)) 2 ↑fbar)
              (LocallyConstant.const _ ψv)
            - contCochainComap (decompositionMap K S ↑v).toMonoidHom
                (map_continuous (decompositionMap K S ↑v)) 2 h)
        - LocallyConstant.map ⇑(coeffKStoLocal K S ↑v)
          (contCupProduct (ρB.comp (decompositionMap K S ↑v).toMonoidHom)
              (fun b => (hρB b).preimage (map_continuous (decompositionMap K S ↑v)))
              φ (i := 1) (j := 1) φv
              (contCochainComap (decompositionMap K S ↑v).toMonoidHom
                (map_continuous (decompositionMap K S ↑v)) 1 ↑gbar)
            - contCochainComap (decompositionMap K S ↑v).toMonoidHom
                (map_continuous (decompositionMap K S ↑v)) 2 h)
      ∈ contCoboundaries (localBarUnitsRep K ↑v) (localBarUnitsRepSmooth K ↑v) 2 :=
  sorry


end

section
-- Natural language: Let $F$ be a finite field, $K$ a totally real number field, $M$ a finite
-- $F[G_S]$-module (with $G_S = \operatorname{Gal}(K_S/K)$ acting continuously, i.e. each point
-- stabilizer is open), and $M^* = \operatorname{Hom}_{\mathbb{Z}}(M, K_S^\times)$ the dual module
-- with the contragredient $G_S$-action. Then the continuous cohomology groups $H^2(G_S, M)$ and
-- $H^1(G_S, M^*)$ are finite.
-- Score: (0 - incorrect, 1 - partially correct, 2 - correct)
-- Comment:
/-- (Lemma 4.2.) `M` being finite, the continuous cohomology groups `H^2(G_S, M)`
and `H^1(G_S, M^*)` are finite. -/
theorem H2H1Finite {F K M : Type} [Field F] [Fintype F] [Field K]
    [NumberField K] [AddCommGroup M] [Module F M] (P : PoitouTateSetup F K M) :
    Finite (contCohomologyGrp (setupRho P) P.continuous_ρ 2)
      ∧ Finite (contCohomologyGrp (dualModuleRep P) (dualModuleRepSmooth P) 1) :=
  sorry


end


