import Verso
import VersoManual
import VersoBlueprint

open Verso.Genre
open Verso.Genre.Manual
open Informal

/-
Blueprint chapter: the imported black boxes for the road to Gee's Proposition 3.24.

Everything in this chapter is *stated precisely and used without proof*: each node is a
theorem we consume from class field theory, Galois cohomology, or the representability of
deformation functors, with a precise external reference. No `:::proof` blocks appear here by
design. Conventions are pinned at the top so that downstream chapters (which DO carry full
proofs) inherit unambiguous statements.

Standing notation (fixed throughout the blueprint, defined in the Setup chapter):
`p > 2` prime; `𝓞` the integers of a finite extension `L/ℚ_p`, uniformizer `λ`, finite
residue field `𝔽 = 𝓞/λ` of characteristic `p`; `n ≥ 1` with `p ∤ n`; `F` a number field;
`S` a finite set of places of `F` containing all `v ∣ p∞`; `Γ = G_{F,S}` the Galois group of
the maximal extension of `F` unramified outside `S`; for `v ∈ S`, `G_{F_v} ↪ Γ` a
decomposition subgroup; `ρ̄ : Γ → GLₙ(𝔽)` continuous, absolutely irreducible, with fixed
determinant `χ`; `ad ρ̄ = 𝔤𝔩ₙ(𝔽)` and `ad⁰ρ̄ = 𝔰𝔩ₙ(𝔽)` (trace zero) under conjugation by `ρ̄`;
`ad⁰ρ̄(1)` its mod-`p` cyclotomic Tate twist. All cohomology `Hⁱ(−,−)` is continuous
cohomology of a profinite group on a finite discrete module, and `hⁱ := dim_𝔽 Hⁱ`.
-/

#doc (Manual) "Assumptions: class field theory and representability" =>

This chapter collects the results we take as black boxes. Each is a deep theorem with a
precise external reference; none is proved here. They fall into two families: the Euler
characteristic and duality theorems of Galois cohomology (Tate, Poitou–Tate), and the
representability of the deformation functors. Everything _downstream_ of this chapter is
proved in full.

:::author "cht_gee_author" (name := "Chapter 3 Blueprint")
:::

:::group "assumptions"
The imported black boxes. Conventions follow the standing notation above. In particular the
Euler characteristic is the standard alternating sum of cohomology dimensions, degree zero
minus degree one plus degree two. Gee negates this convention; we use the standard sign
throughout and convert once, where Gee's formulas are reproduced.
:::

# Representability of the deformation functors

We do not construct the deformation rings; we assume they exist with their universal
property, and only ever *evaluate* the functor at explicit small rings (above all at the dual
numbers $`\mathbb{F}[\epsilon]/(\epsilon^2)`) through the description of the functor. This is
the single structural input from deformation theory.

:::definition "def_functor" (parent := "assumptions")
For an object $`R` of the category $`\mathcal{C}_{\mathcal{O}}` of complete local Noetherian
$`\mathcal{O}`-algebras with residue field $`\mathbb{F}`, a *lifting* of $`\bar\rho` to $`R`
is a continuous $`r : \Gamma \to GL_n(R)` with $`r \bmod \mathfrak{m}_R = \bar\rho` and
$`\det r = \chi`. For $`T \subseteq S`, a *$`T`-framed lifting* is a tuple
$`(r, (\alpha_v)_{v \in T})` with $`\alpha_v \in 1 + M_n(\mathfrak{m}_R)`, two being
equivalent if simultaneously conjugate by some $`\beta \in 1 + M_n(\mathfrak{m}_R)` acting as
$`r \mapsto \beta r \beta^{-1}`, $`\alpha_v \mapsto \beta \alpha_v`. With a local deformation
problem $`\mathcal{D}_v` imposed at each $`v \in S`, this defines the $`T`-framed deformation
functor $`\mathrm{Def}^{\square_T}_{\mathcal{S}} : \mathcal{C}_{\mathcal{O}} \to
\mathbf{Set}`.
:::

:::theorem "rep_framed" (parent := "assumptions") (owner := "cht_gee_author")
*(Representability.)* Suppose $`\bar\rho` is {uses "def_functor"}[Schur] (e.g. absolutely
irreducible). Then $`\mathrm{Def}^{\square_T}_{\mathcal{S}}` is represented by an object
$`R^{\square_T}_{\mathcal{S}}` of $`\mathcal{C}_{\mathcal{O}}`; the unframed functor
($`T = \varnothing`) by $`R^{\mathrm{univ}}_{\mathcal{S}}`. Likewise, for each $`v \in S` the
unrestricted local lifting functor of $`\bar\rho|_{G_{F_v}}` (with $`\det = \chi`) is
represented by a complete local Noetherian $`\mathcal{O}`-algebra $`R^{\mathrm{loc}}_v`, and
each local deformation problem $`\mathcal{D}_v` corresponds to a
$`(1 + M_n(\mathfrak{m}))`-invariant ideal $`\mathcal{I}_v \trianglelefteq R^{\mathrm{loc}}_v`.

*Reference.* Clozel–Harris–Taylor, Prop. 2.2.9 and Lemma 2.2.3; Gee, Lemmas 3.2, 3.5, 3.22;
Mazur, *Deforming Galois representations*. (Proof omitted by assumption.)
:::

# Galois cohomology: Euler characteristics

:::theorem "euler_local" (parent := "assumptions") (owner := "cht_gee_author")
*(Local Euler characteristic formula, Tate.)* Let $`v` be a finite place of $`F` and $`M` a
finite $`\mathbb{F}[G_{F_v}]`-module. Then
$$`h^0(G_{F_v}, M) - h^1(G_{F_v}, M) + h^2(G_{F_v}, M) = \begin{cases} -[F_v : \mathbb{Q}_p]\,\dim_{\mathbb{F}} M & v \mid p,\\ 0 & v \nmid p.\end{cases}`

*Reference.* Milne, *Arithmetic Duality Theorems*, Thm. I.2.8; Neukirch–Schmidt–Wingberg,
*Cohomology of Number Fields*, Thm. 7.3.1.
:::

:::theorem "euler_global" (parent := "assumptions") (owner := "cht_gee_author")
*(Global Euler characteristic formula, Tate.)* Let $`M` be a finite
$`\mathbb{F}[\Gamma]`-module ($`p \in S`). Then
$$`h^0(\Gamma, M) - h^1(\Gamma, M) + h^2(\Gamma, M) = \sum_{v \mid \infty} h^0(G_{F_v}, M) - [F : \mathbb{Q}]\,\dim_{\mathbb{F}} M.`
(Since $`p > 2`, at each real place the archimedean term is the ordinary
$`h^0(G_{F_v}, M)`.)

*Reference.* Tate; Milne, *Arithmetic Duality Theorems*, Thm. I.5.1; Neukirch–Schmidt–Wingberg,
Thm. 8.7.4.
:::

# Galois cohomology: duality

:::theorem "tate_local_duality" (parent := "assumptions") (owner := "cht_gee_author")
*(Tate local duality.)* Let $`v` be a finite place of $`F` and $`M` a finite
$`\mathbb{F}[G_{F_v}]`-module with Cartier dual $`M^{*}(1) = \mathrm{Hom}(M, \mu_{p^\infty})`.
Cup product and the invariant map give a perfect pairing of finite groups
$$`H^i(G_{F_v}, M) \times H^{2-i}(G_{F_v}, M^{*}(1)) \longrightarrow H^2(G_{F_v}, \mu) = \mathbb{Q}/\mathbb{Z},`
for $`i = 0, 1, 2`; in particular $`h^i(G_{F_v}, M) = h^{2-i}(G_{F_v}, M^{*}(1))`. For
$`M = \mathrm{ad}^0\bar\rho` the trace pairing $`(x,y) \mapsto \mathrm{tr}(xy)` identifies
$`(\mathrm{ad}^0\bar\rho)^{*}(1) \cong \mathrm{ad}^0\bar\rho(1)` (nondegenerate on
$`\mathrm{ad}^0` exactly because $`p \nmid n`).

*Reference.* Milne, *Arithmetic Duality Theorems*, Cor. I.2.3; Neukirch–Schmidt–Wingberg,
Thm. 7.2.6.
:::

:::theorem "poitou_tate" (parent := "assumptions") (owner := "cht_gee_author")
*(Poitou–Tate.)* Let $`M` be a finite $`\mathbb{F}[\Gamma]`-module. There is a nine-term
exact sequence relating the global cohomology $`H^i(\Gamma, M)`, the products of local
cohomology $`\prod_v H^i(G_{F_v}, M)`, and the dual global cohomology
$`H^{2-i}(\Gamma, M^{*}(1))^{\vee}`, for $`i = 0, 1, 2`. Consequently, for the Selmer
conditions $`L(\mathcal{D}_v)` and their annihilators $`L(\mathcal{D}_v)^{\perp}` under
{uses "tate_local_duality"}[local duality], the Selmer and dual-Selmer groups satisfy
$$`H^2_{\mathcal{S},T}(\Gamma, \mathrm{ad}^0\bar\rho) \cong H^1_{\mathcal{L}^{\perp}, T}(\Gamma, \mathrm{ad}^0\bar\rho(1))^{\vee}, \qquad H^3_{\mathcal{S},T}(\Gamma, \mathrm{ad}^0\bar\rho) \cong H^0(\Gamma, \mathrm{ad}^0\bar\rho(1))^{\vee}.`

*Reference.* Milne, *Arithmetic Duality Theorems*, Thm. I.4.10; Neukirch–Schmidt–Wingberg,
Thm. 8.6.10 and 8.6.13; the Selmer reformulation follows Clozel–Harris–Taylor, §2.3 and Gee,
§3.23. (The groups $`H^i_{\mathcal{S},T}` and $`H^1_{\mathcal{L}^\perp,T}` are defined in the
cohomology chapter.)
:::
