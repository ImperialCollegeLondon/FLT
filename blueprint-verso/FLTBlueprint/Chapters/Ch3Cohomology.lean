import Verso
import VersoManual
import VersoBlueprint

open Verso.Genre
open Verso.Genre.Manual
open Informal

/-
Blueprint chapter: continuous Galois cohomology and the Selmer (mapping-cone) complex.

This is the accuracy-critical chapter. Gee (pp. 90–91) and Clozel–Harris–Taylor (§2.2) both
define the objects of the Selmer complex but leave its differentials, the chain-map property,
and the sign in the short exact sequence of complexes implicit; CHT even flag parenthetically
that "this is a special case of a cone construction". We make the cone construction explicit
and prove every omitted step. We follow Gee's `ad⁰`/fixed-determinant convention (so the
degree-0 term is the full `ad`, encoding scalar automorphisms), and supply the differential
across the `ad → ad⁰` seam that Gee omits.

Provenance: the homogeneous `ad r̄` form is CHT Def. 2.2.7; we specialise to `ad⁰` and repair
the seam. All cohomology is continuous cohomology of a profinite group on a finite discrete
module (Mathlib `continuousCohomology`); the cochain complex `C^•(G, M)` below is the
inhomogeneous continuous cochain complex computing it.
-/

#doc (Manual) "Galois cohomology and the Selmer complex" =>

We construct the complex whose cohomology $`H^i_{\mathcal{S},T}` controls framed
deformations, as the mapping cone of a restriction map, and derive its long exact sequence.
The construction is uniform, but two points need the standing hypothesis $`p \nmid n`: the
splitting $`\mathrm{ad} = \mathrm{ad}^0 \oplus \mathbb{F}`, and (later) the nondegeneracy of
the trace pairing on $`\mathrm{ad}^0`.

:::author "ch3coh_author" (name := "Chapter 3 Blueprint")
:::

:::group "cohomology"
Continuous Galois cohomology, the adjoint module, and the Selmer mapping cone.
:::

# The cochain complex and the adjoint module

:::definition "cochain_complex" (parent := "cohomology")
For a profinite group $`G` and a finite discrete $`\mathbb{F}[G]`-module $`M`, let
$`C^i(G, M)` be the group of continuous maps $`G^i \to M` ($`C^0(G,M) = M`), with the
inhomogeneous coboundary $`\partial^i : C^i(G,M) \to C^{i+1}(G,M)`,
$$`(\partial^0 m)(g) = g\cdot m - m, \quad (\partial^1 f)(g,h) = g\cdot f(h) - f(gh) + f(g),\ \dots`
Then $`\partial \circ \partial = 0`, and $`H^i(G,M)` is the cohomology of $`(C^\bullet(G,M),
\partial)`. We write $`Z^i = \ker \partial^i`, $`B^i = \mathrm{im}\,\partial^{i-1}`,
$`h^i = \dim_{\mathbb{F}} H^i`.
:::

:::definition "adjoint" (parent := "cohomology")
$`\mathrm{ad}\,\bar\rho = M_n(\mathbb{F}) = \mathfrak{gl}_n(\mathbb{F})` with the conjugation
action $`g \cdot X = \bar\rho(g)\, X\, \bar\rho(g)^{-1}`; $`\mathrm{ad}^0\bar\rho =
\{X : \mathrm{tr}\,X = 0\}`, a $`G`-submodule (trace is conjugation-invariant). The scalar
matrices $`\mathbb{F}\cdot 1_n` form a trivial $`G`-submodule.
:::

:::lemma_ "ad0_split" (parent := "cohomology") (owner := "ch3coh_author")
If $`p \nmid n` then $`\mathrm{ad}\,\bar\rho = \mathrm{ad}^0\bar\rho \oplus \mathbb{F}\cdot 1_n`
as $`\mathbb{F}[G]`-modules, and the projection $`\mathrm{pr} : \mathrm{ad} \to
\mathrm{ad}^0`, $`X \mapsto X - \tfrac{\mathrm{tr}\,X}{n} 1_n`, is $`G`-equivariant. In
particular $`\partial^0 : C^0(G, \mathrm{ad}) \to C^1(G, \mathrm{ad})` carries
$`C^0(G,\mathrm{ad})` into $`C^1(G, \mathrm{ad}^0)` and kills the scalars.
:::

:::proof "ad0_split"
Since $`p \nmid n`, $`n` is invertible in $`\mathbb{F}`, so $`X \mapsto
\tfrac{\mathrm{tr}\,X}{n} 1_n` is a well-defined projection onto $`\mathbb{F}\cdot 1_n` with
kernel $`\mathrm{ad}^0`, giving the direct sum. Both summands are $`G`-stable
({uses "adjoint"}[$`\mathrm{ad}^0`] by trace-invariance, scalars being central hence fixed by
conjugation), so $`\mathrm{pr}` is $`G`-equivariant. For the last claim: scalars are
$`G`-invariant, so $`\partial^0(s 1_n) = 0`; and for $`X \in \mathrm{ad}^0`,
$`(\partial^0 X)(g) = g\cdot X - X \in \mathrm{ad}^0` as $`\mathrm{ad}^0` is a submodule. By
linearity $`\partial^0(C^0(G,\mathrm{ad})) \subseteq C^1(G,\mathrm{ad}^0)`.
:::

# The modified global complex

:::definition "modified_global" (parent := "cohomology")
The *modified global complex* $`C_0^\bullet` has $`C_0^0 = C^0(\Gamma, \mathrm{ad})` and
$`C_0^i = C^i(\Gamma, \mathrm{ad}^0)` for $`i \geq 1`, with differential
$`d^0 = \mathrm{pr}\circ\partial^0 : C^0(\Gamma,\mathrm{ad}) \to C^1(\Gamma,\mathrm{ad}^0)`
and $`d^i = \partial^i` for $`i \geq 1`. (The degree-0 term is the full $`\mathrm{ad}`: it
records that infinitesimal automorphisms of a deformation are scalars.)
:::

:::lemma_ "modified_global_complex" (parent := "cohomology") (owner := "ch3coh_author")
$`(C_0^\bullet, d)` is a cochain complex, and $`H^0(C_0^\bullet) = H^0(\Gamma,
\mathrm{ad}\,\bar\rho)`, $`H^i(C_0^\bullet) = H^i(\Gamma, \mathrm{ad}^0\bar\rho)` for
$`i \geq 1`.
:::

:::proof "modified_global_complex"
Only $`d^1 \circ d^0 = 0` is non-automatic. By {uses "ad0_split"}[the splitting lemma]
$`\partial^0` already lands in $`C^1(\Gamma,\mathrm{ad}^0)`, so $`\mathrm{pr}\circ\partial^0 =
\partial^0` there, whence $`d^1 d^0 = \partial^1\partial^0 = 0`. For the cohomology:
$`H^0(C_0^\bullet) = \ker d^0 = \ker(\mathrm{pr}\,\partial^0)`; since $`\partial^0` is already
$`\mathrm{ad}^0`-valued and injective on $`\mathrm{ad}^0`-coboundaries, $`\ker d^0 =
\ker \partial^0 = H^0(\Gamma, \mathrm{ad})`. In degrees $`\geq 1` the complex agrees with
$`C^\bullet(\Gamma,\mathrm{ad}^0)` (the incoming $`d^0` has the same image as $`\partial^0` on
$`\mathrm{ad}^0`), giving $`H^i = H^i(\Gamma,\mathrm{ad}^0)`.
:::

# Local conditions and the local complex

:::definition "local_subcomplex" (parent := "cohomology")
For $`v \in S` let $`L(\mathcal{D}_v) \subseteq H^1(G_{F_v}, \mathrm{ad}^0\bar\rho)` be the
local condition (defined in the Local Conditions chapter) and $`\widetilde{L}_v \subseteq
Z^1(G_{F_v}, \mathrm{ad}^0)` its preimage in cocycles, so $`B^1 \subseteq \widetilde{L}_v
\subseteq Z^1`. The *local complex* $`C^\bullet_{\mathcal{S},T,\mathrm{loc}}` is
$$`\bigoplus_{v\in T} C^0(G_{F_v},\mathrm{ad}) \ (\text{degree }0);\quad \bigoplus_{v\in T} C^1(G_{F_v},\mathrm{ad}^0)\ \oplus\ \bigoplus_{v\in S\setminus T} C^1(G_{F_v},\mathrm{ad}^0)/\widetilde{L}_v\ (\text{degree }1);\quad \bigoplus_{v\in S} C^i(G_{F_v},\mathrm{ad}^0)\ (i\geq 2),`
with differential induced by $`\mathrm{pr}\circ\partial` in degree 0 and $`\partial`
(descended to the quotient in degree 1) above.
:::

:::lemma_ "local_complex" (parent := "cohomology") (owner := "ch3coh_author")
$`C^\bullet_{\mathcal{S},T,\mathrm{loc}}` is a cochain complex.
:::

:::proof "local_complex"
At each $`v` the degree-0 differential is a complex by the argument of
{uses "modified_global_complex"}[the global lemma]. The only extra point is that the
degree-1 differential descends to the quotient by $`\widetilde{L}_v` ($`v \in S\setminus T`):
this needs $`\partial^1(\widetilde{L}_v) = 0`, i.e. $`\widetilde{L}_v \subseteq Z^1`, which
holds by {uses "local_subcomplex"}[definition]. The induced map
$`C^1/\widetilde{L}_v \to C^2` then satisfies $`d^1_{\mathrm{quot}} d^0 = \partial^1
\partial^0 \bmod \widetilde{L}_v = 0`. (Equivalently: the degrees $`(C^0, \widetilde{L}_v, 0,
\dots)` form a subcomplex $`M^\bullet_v` of $`C^\bullet(G_{F_v},\mathrm{ad}^0)` — using
$`B^1 \subseteq \widetilde{L}_v \subseteq Z^1` — and the local complex is the quotient
$`C^\bullet/M^\bullet_v`, manifestly a complex.)
:::

# The mapping cone and its cohomology

:::definition "restriction" (parent := "cohomology")
The *restriction map* $`\mathrm{res} : C_0^\bullet \to
C^\bullet_{\mathcal{S},T,\mathrm{loc}}` sends a global cochain $`\varphi` to
$`(\varphi|_{G_{F_v}})_{v}` (restricted along $`G_{F_v}\hookrightarrow\Gamma`, composed with
the projection to $`\mathrm{ad}^0` in degree 0 over $`T` and with the quotient by
$`\widetilde{L}_v` in degree 1 over $`S\setminus T`).
:::

:::lemma_ "res_chain_map" (parent := "cohomology") (owner := "ch3coh_author")
$`\mathrm{res}` is a morphism of complexes: $`\mathrm{res}\circ d = d \circ \mathrm{res}`.
:::

:::proof "res_chain_map"
Restriction of cochains along the continuous homomorphism $`G_{F_v}\hookrightarrow\Gamma`
commutes with the inhomogeneous coboundary, $`(\partial\varphi)|_{G_{F_v}} =
\partial(\varphi|_{G_{F_v}})`. The seam projection $`\mathrm{pr}` is $`G`-equivariant and
restriction is computed pointwise, so $`\mathrm{pr}` commutes with restriction; likewise the
degree-1 quotient is applied after restriction. Combining these in each degree gives
$`\mathrm{res}^{i+1}\circ d^i = d^i \circ \mathrm{res}^i`.
:::

:::definition "cone" (parent := "cohomology")
The *Selmer complex* is the shifted mapping cone of {uses "restriction"}[$`\mathrm{res}`]:
$$`C^i_{\mathcal{S},T}(\Gamma,\mathrm{ad}^0\bar\rho) := C_0^i \oplus C^{i-1}_{\mathcal{S},T,\mathrm{loc}}, \qquad d(\varphi, \psi) = (d\varphi,\ \mathrm{res}(\varphi) - d\psi).`
Its cohomology is $`H^i_{\mathcal{S},T}(\Gamma, \mathrm{ad}^0\bar\rho)`.
:::

:::lemma_ "cone_complex" (parent := "cohomology") (owner := "ch3coh_author")
$`d^2 = 0` on $`C^\bullet_{\mathcal{S},T}`; equivalently, the cone differential squares to
zero precisely because {uses "res_chain_map"}[$`\mathrm{res}` is a chain map].
:::

:::proof "cone_complex"
For $`(\varphi,\psi) \in C_0^i \oplus C^{i-1}_{\mathrm{loc}}`,
$$`d^2(\varphi,\psi) = d(d\varphi,\ \mathrm{res}\,\varphi - d\psi) = (d^2\varphi,\ \mathrm{res}(d\varphi) - d(\mathrm{res}\,\varphi - d\psi)) = (0,\ \mathrm{res}(d\varphi) - d(\mathrm{res}\,\varphi) + d^2\psi).`
The first slot vanishes as $`C_0^\bullet` is a {uses "modified_global_complex"}[complex] and
$`d^2\psi = 0` as $`C^\bullet_{\mathrm{loc}}` is a {uses "local_complex"}[complex]; the middle
term is $`(\mathrm{res}\, d - d\,\mathrm{res})\varphi = 0` by
{uses "res_chain_map"}[the chain-map property]. Hence $`d^2 = 0`.
:::

# The defining short exact sequence and the long exact sequence

:::lemma_ "ses" (parent := "cohomology") (owner := "ch3coh_author")
Let $`C^{\bullet-1}_{\mathcal{S},T,\mathrm{loc}}` denote the local complex shifted by $`-1`,
*with the shifted differential $`-d`*. Then
$$`0 \longrightarrow C^{\bullet-1}_{\mathcal{S},T,\mathrm{loc}} \xrightarrow{\ \iota\ } C^\bullet_{\mathcal{S},T} \xrightarrow{\ \pi\ } C_0^\bullet \longrightarrow 0,\qquad \iota(\psi) = (0,\psi),\ \ \pi(\varphi,\psi)=\varphi,`
is a short exact sequence of complexes.
:::

:::proof "ses"
Termwise the sequence is the split-exact $`0 \to C^{i-1}_{\mathrm{loc}} \to C_0^i \oplus
C^{i-1}_{\mathrm{loc}} \to C_0^i \to 0`. It remains to check $`\iota, \pi` are chain maps.
For $`\pi`: $`\pi(d(\varphi,\psi)) = \pi(d\varphi, \mathrm{res}\,\varphi - d\psi) = d\varphi =
d(\pi(\varphi,\psi))`. For $`\iota`:
$`d(\iota\psi) = d(0,\psi) = (d\,0,\ \mathrm{res}\,0 - d\psi) = (0, -d\psi)`, while
$`\iota` applied to the shifted differential $`-d` of $`\psi` is $`(0, -d\psi)` — equal.
$`(⚠`\ this is exactly the point Gee elides: with the *unshifted* $`+d` on the subcomplex,
$`\iota` would fail to commute with $`d`, so the standard shift sign $`-d` is forced.$`)`
:::

:::theorem "les" (parent := "cohomology") (owner := "ch3coh_author")
There is a long exact sequence (Gee p. 91; Clozel–Harris–Taylor p. 22), with connecting map
the restriction $`\mathrm{res}^* `:
$$`\cdots \to H^i_{\mathcal{S},T} \to H^i(C_0^\bullet) \xrightarrow{\mathrm{res}^*} H^i(C^\bullet_{\mathcal{S},T,\mathrm{loc}}) \to H^{i+1}_{\mathcal{S},T} \to \cdots`
Concretely $`H^i(C_0^\bullet)` is $`H^0(\Gamma,\mathrm{ad})` then $`H^i(\Gamma,\mathrm{ad}^0)`
($`i\geq 1`), and $`H^i(C^\bullet_{\mathcal{S},T,\mathrm{loc}})` is
$`\bigoplus_{v\in T} H^i(G_{F_v},\mathrm{ad}^{(0)}) \oplus \bigoplus_{v\in S\setminus T} H^i(G_{F_v},\mathrm{ad}^0)/L(\mathcal{D}_v)`
in the relevant degrees.
:::

:::proof "les"
Apply the cohomology long exact sequence to the {uses "ses"}[short exact sequence of
complexes]. The cohomology of the shifted subcomplex $`C^{\bullet-1}_{\mathrm{loc}}` is
$`H^{i}(C^\bullet_{\mathcal{S},T,\mathrm{loc}})` in cone-degree $`i+1` (the sign $`-d` does
not change cohomology, the map $`x \mapsto -x` being an isomorphism of complexes
$`(C_{\mathrm{loc}}, d) \cong (C_{\mathrm{loc}}, -d)`). The connecting homomorphism of the
cone SES is induced by $`\mathrm{res}` — this is the standard identification of the cone's
boundary map with the map it is the cone of. Reading off the cohomologies of $`C_0^\bullet`
({uses "modified_global_complex"}[computed above]) and of $`C^\bullet_{\mathrm{loc}}` (the
cohomology of the local condition quotient complexes) gives the stated terms.
:::

:::corollary "h0_selmer" (parent := "cohomology") (owner := "ch3coh_author")
From the {uses "les"}[long exact sequence],
$$`H^0_{\mathcal{S},T}(\Gamma, \mathrm{ad}^0\bar\rho) = \ker\Big(H^0(\Gamma, \mathrm{ad}\,\bar\rho) \xrightarrow{\ \mathrm{res}\ } \bigoplus_{v\in T} H^0(G_{F_v}, \mathrm{ad}\,\bar\rho)\Big).`
If $`\bar\rho` is absolutely irreducible then $`H^0(\Gamma,\mathrm{ad}\,\bar\rho) =
\mathbb{F}` (the scalars), and
$$`H^0_{\mathcal{S},T}(\Gamma, \mathrm{ad}^0\bar\rho) = \begin{cases}\mathbb{F} & T = \varnothing,\\ 0 & T \neq \varnothing.\end{cases}`

⚠ *Correction to the source.* Gee p. 92 states "$`H^0(\Gamma,\mathrm{ad}) = \mathbb{F}`, so
$`H^0_{\mathcal{S},T} = \mathbb{F}`". The implication holds only for the unframed count
$`T = \varnothing`; for $`T \neq \varnothing` the restriction of the scalars to the local
invariants is injective, so $`H^0_{\mathcal{S},T} = 0`. Both cases must be carried separately
in the Euler-characteristic bookkeeping (the global/framed split of Prop. 3.24(2)(3)).
:::

:::proof "h0_selmer"
The {uses "ses"}[cone short exact sequence] begins
$`0 \to H^0_{\mathcal{S},T} \to H^0(C_0^\bullet) \xrightarrow{\mathrm{res}^*} H^0(C^\bullet_{\mathrm{loc}})`,
so $`H^0_{\mathcal{S},T} = \ker(\mathrm{res}^*)`. By
{uses "modified_global_complex"}[the global computation] $`H^0(C_0^\bullet) =
H^0(\Gamma,\mathrm{ad})`, and the degree-0 local cohomology is $`\bigoplus_{v\in T}
H^0(G_{F_v},\mathrm{ad})` (the $`S\setminus T` part is zero in degree 0). By
{uses "adjoint"}[Schur], $`H^0(\Gamma,\mathrm{ad}) =
\mathrm{End}_{\mathbb{F}[\Gamma]}(\mathbb{F}^n) = \mathbb{F}\cdot 1_n`. A scalar restricts to
the same nonzero scalar in each $`H^0(G_{F_v},\mathrm{ad})`, so $`\mathrm{res}^*` is injective
when $`T \neq \varnothing` (giving kernel $`0`) and is the zero map into the empty sum when
$`T = \varnothing` (giving kernel $`\mathbb{F}`).
:::
