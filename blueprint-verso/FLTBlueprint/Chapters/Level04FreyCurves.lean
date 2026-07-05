import Verso
import VersoManual
import VersoBlueprint
import FLT.FreyCurve.FreyPackage
import FLT.FreyCurve.Basic
import FLT.EllipticCurve.Torsion
import FLT.FreyCurve.Mazur
import FLT.Proof

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Level 4: Frey curves" =>

The story so far: Fermat's Last Theorem has been reduced to statement $`B_3`,
the claim that there are no Frey packages. In this level
we make the big reveal of the whole game. To a Frey package we attach an
_elliptic curve_ — the _Frey curve_ — and we extract from it a _Galois
representation_. The boss of this level, statement $`B_4`, is a statement purely
about this Galois representation, and beating it will follow from a deep theorem
of Mazur.

A word on the numbering. In the accompanying 2026 lecture notes the boss of this
level is called $`B_3`, because there the levels are numbered from zero. Here the
levels are numbered from one, so every statement is shifted by one: the notes'
$`B_3` is our $`B_4`. Apart from this bookkeeping the mathematics is identical.

One remark before we begin. Wiles' work is often advertised as a profound link
between elliptic curves and _modular forms_. The proof we are formalizing will
never mention modular forms: they are present in the background, but they appear
in no statement we make and every fact we need about them was known in the
1980s. Elliptic curves, on the other hand, we cannot avoid.

# Elliptic curves

Let $`K` be a field. The definition of an elliptic curve over $`K` that we use
avoids all algebraic geometry: an elliptic curve is simply a tuple of five field
elements, subject to one inequality.

:::group "curves"
Elliptic curves, their Galois representations, and the Frey curve.
:::

:::definition "weierstrass_curve" (parent := "curves") (lean := "WeierstrassCurve")
A *Weierstrass curve* over a field $`K` is an ordered tuple
$`(a_1, a_2, a_3, a_4, a_6)` of five elements of $`K`.

To such a tuple we associate its *defining polynomial*

$$`f_E := Y^2 + a_1 X Y + a_3 Y - (X^3 + a_2 X^2 + a_4 X + a_6) \in K[X, Y],`

which we think of as cutting out the curve $`f_E = 0` in the plane.
:::

The indices $`1,2,3,4,6` look strange, but they encode a grading: if we declare
$`a_n` to have "degree $`n`" and the variables $`X`, $`Y` to have degrees $`2`
and $`3`, then $`f_E` is homogeneous of degree $`6`. With this convention there
is a distinguished degree-$`12` polynomial in the $`a_i`, the *discriminant*
$`\Delta_E`, and an elliptic curve is a Weierstrass curve whose discriminant does
not vanish.

:::definition "elliptic_curve" (parent := "curves") (lean := "WeierstrassCurve.IsElliptic") (uses := "weierstrass_curve")
A {uses "weierstrass_curve"}[Weierstrass curve] $`E = (a_1, a_2, a_3, a_4, a_6)`
over a field $`K` is an *elliptic curve* if its *discriminant* $`\Delta_E` is
nonzero, where

$$`\Delta_E = -(a_1^2 + 4a_2)^2(a_1^2 a_6 + 4a_2 a_6 - a_1 a_3 a_4 + a_2 a_3^2 - a_4^2) - 8(2a_4 + a_1 a_3)^3 - 27(a_3^2 + 4a_6)^2 + 9(a_1^2 + 4a_2)(2a_4 + a_1 a_3)(a_3^2 + 4a_6).`

:::

The virtue of this definition is that it works in every characteristic and needs
no geometry. Geometrically, the non-vanishing of $`\Delta_E` says precisely that
the polynomials $`f_E`, $`\partial f_E / \partial X` and $`\partial f_E /
\partial Y` have no common zero, i.e. that the curve $`f_E = 0` is *smooth*.

It also drives home the point that the *underlying definition* of a mathematical
object barely matters; what matters is its *interface*. In Lean a Weierstrass
curve is a structure bundling the five coefficients, and being an elliptic curve
is a typeclass asserting that the discriminant is a unit.

## A family of examples

Fix a field $`K` and three elements $`\alpha, \beta, \gamma \in K`. Let us look
for an elliptic curve whose defining polynomial is $`Y^2 - (X - \alpha)(X -
\beta)(X - \gamma)`. Multiplying out and comparing with the general shape of
$`f_E`, we must take

$$`a_1 = a_3 = 0, \quad a_2 = -(\alpha + \beta + \gamma), \quad a_4 = \alpha\beta + \beta\gamma + \gamma\alpha, \quad a_6 = -\alpha\beta\gamma.`

Substituting into the formula for the discriminant, the monstrous expression
collapses to

$$`\Delta_E = 16\,(\alpha - \beta)^2 (\beta - \gamma)^2 (\gamma - \alpha)^2.`

So provided $`K` does not have characteristic $`2` and $`\alpha, \beta, \gamma`
are pairwise distinct, this data defines an elliptic curve. The Frey curve below
will be a member of exactly this family.

## Points, and the group law

Say $`E` is an elliptic curve over $`K`. Its set of *$`K`-points* $`E(K)` is the
set of solutions $`(x, y) \in K^2` to $`f_E(x, y) = 0`, together with one extra
point, the *point at infinity*, which we choose to call $`0`.

:::definition "points" (parent := "curves") (lean := "WeierstrassCurve.Affine.Point") (uses := "elliptic_curve")
The *$`K`-points* $`E(K)` of an {uses "elliptic_curve"}[elliptic curve] $`E` over
$`K` are the solutions in $`K^2` of $`f_E = 0`, together with a distinguished
extra point $`0`.
:::

If $`L` is any field equipped with a field homomorphism $`K \to L`, then applying
that homomorphism to the five coefficients produces an elliptic curve $`E_L` over
$`L` (the discriminant stays nonzero because field homomorphisms are injective),
and we write $`E(L) := E_L(L)`. A $`K`-algebra homomorphism $`\phi : L \to M`
between $`K`-fields induces a map $`\phi_* : E(L) \to E(M)`, $`(x, y) \mapsto
(\phi(x), \phi(y))`, sending $`0` to $`0`; this construction is functorial.

The reason elliptic curves are so useful is that their points form a group.

:::theorem "group_law" (parent := "curves") (uses := "points")
Let $`E` be an {uses "elliptic_curve"}[elliptic curve] over a field $`K`. There is
one and only one abelian group structure on {uses "points"}[$`E(K)`] with the
following properties:
* $`0` is the identity element;
* three distinct nonzero points sum to zero exactly when they are collinear.
:::

:::proof "group_law"
The existence of such a group law was known in the 1980s (the delicate point is
associativity, which amounts to a large algebraic identity). Uniqueness is
formal: collinearity determines $`P + Q` for all $`P \neq Q`, and then $`P + P`
is forced as the unique point not of the form $`P + Q` for some other $`Q`.
:::

Because $`\phi_*` sends collinear triples to collinear triples, each induced map
$`\phi_* : E(L) \to E(M)` is a group homomorphism. In particular a $`K`-algebra
automorphism of a $`K`-field $`L` acts on $`E(L)` by group automorphisms.

# Galois representations

We now let the symmetries of the field act on the points of the curve. Fix a
field $`K` and a separable closure $`\overline{K}` of $`K` (for $`K = \mathbb{Q}`
one may take the algebraic numbers inside $`\mathbb{C}`). Unlike the natural
numbers, $`\overline{K}` is generally only unique up to non-unique isomorphism,
and its self-symmetries are the object of interest.

:::definition "galois_group" (parent := "curves") (lean := "Field.absoluteGaloisGroup")
The *absolute Galois group* $`\mathrm{Gal}(\overline{K}/K)` of $`K` is the group
of $`K`-algebra automorphisms of the $`K`-field $`\overline{K}`.
:::

By functoriality, $`\mathrm{Gal}(\overline{K}/K)` acts on the abelian group
$`E(\overline{K})` by group automorphisms. Restricting this action to the
$`n`-torsion gives the object we care about.

:::definition "torsion" (parent := "curves") (lean := "WeierstrassCurve.nTorsion") (uses := "points")
For a natural number $`n`, the *$`n`-torsion* $`E(\overline{K})[n]` is the
subgroup of {uses "points"}[points] $`P` with $`nP = 0`.
:::

:::definition "galois_rep" (parent := "curves") (lean := "WeierstrassCurve.galoisRep") (uses := "elliptic_curve, galois_group, torsion")
The action of {uses "galois_group"}[$`\mathrm{Gal}(\overline{K}/K)`] on
$`E(\overline{K})` preserves the {uses "torsion"}[$`n`-torsion], giving *the mod
$`n` Galois representation* attached to $`E/K`, an action of
$`\mathrm{Gal}(\overline{K}/K)` on $`E(\overline{K})[n]`.
:::

Why "representation"? When $`n = p` is prime, $`E(\overline{K})[p]` is naturally a
vector space over the field $`\mathbb{Z}/p\mathbb{Z}`, and the Galois action is by
$`\mathbb{Z}/p\mathbb{Z}`-linear automorphisms. So $`E(\overline{K})[p]` really is
a representation of $`\mathrm{Gal}(\overline{K}/K)` in the sense of undergraduate
algebra. (One can show this vector space is two-dimensional whenever $`p \neq 0`
in $`K`.) Note that the representation depends on the chosen $`\overline{K}`, so
it is slightly less canonical than one might hope.

Recall that a representation of a group $`G` on a vector space $`V` is
*reducible* if there is a subspace $`0 < W < V`, neither zero nor everything,
which is $`G`-stable; it is *irreducible* otherwise. In Lean we phrase
reducibility as the negation of irreducibility.

# The Frey curve

We can now attach an elliptic curve to a Frey package. Recall a Frey package is a
prime $`p \geq 5` together with pairwise
coprime nonzero integers $`a, b, c` with $`a \equiv 3 \pmod 4`, $`b` even, and
$`a^p + b^p = c^p`.

:::definition "frey_curve" (parent := "curves") (lean := "FreyPackage.freyCurve") (uses := "frey_package, elliptic_curve")
The *Frey curve* associated to a {uses "frey_package"}[Frey package]
$`(a, b, c, p)` is the {uses "elliptic_curve"}[elliptic curve] over
$`\mathbb{Q}` with defining polynomial

$$`Y^2 - X(X - a^p)(X + b^p).`

:::

This is the member of our example family with $`\alpha = 0`, $`\beta = a^p` and
$`\gamma = -b^p`. We had better check that it really is an elliptic curve.

:::lemma_ "frey_curve_elliptic" (parent := "curves") (lean := "FreyCurve.Δ") (uses := "frey_curve")
The {uses "frey_curve"}[Frey curve] of a Frey package is an
{uses "elliptic_curve"}[elliptic curve]; its discriminant is
$`(abc)^{2p}/2^8`, which is nonzero.
:::

:::proof "frey_curve_elliptic"
By the discriminant computation for our example family, and using $`2 \neq 0` in
$`\mathbb{Q}`, being an elliptic curve amounts to checking that $`0`, $`a^p` and
$`-b^p` are three distinct rational numbers. Since $`a, b \neq 0` we have
$`a^p \neq 0` and $`-b^p \neq 0`; and $`a^p - (-b^p) = a^p + b^p = c^p \neq 0`, so
$`a^p \neq -b^p`. Hence the three roots are distinct and the discriminant is
nonzero.

A technical remark on the Lean formalization: rather than the naive model above,
`FreyPackage.freyCurve` records an isomorphic model obtained by the change of
variables $`X = 4x`, $`Y = 8y + 4x`. The congruences $`a \equiv 3 \pmod 4` and
$`b` even (together with $`p` odd) guarantee this model has *integer*
coefficients and is semistable at $`2`; this is why a Frey package demands those
otherwise mysterious congruences. The discriminant is unchanged up to the units
introduced by the substitution, and works out to $`(abc)^{2p}/2^8`.
:::

# The boss: reducibility of the Frey representation

We are ready to state the boss of level 4. Fix a Frey package and its Frey curve
$`E`, choose a separable closure $`\overline{\mathbb{Q}}` of $`\mathbb{Q}`, and
let $`\rho` be the mod $`p` Galois representation of $`E`, so $`p` is the prime of
the Frey package.

:::definition "Statement_B4_reducible" (parent := "curves") (lean := "FLT.Bosses.B4") (uses := "frey_curve, galois_rep")
$`B_4` is the statement that for every {uses "frey_package"}[Frey package], the
mod $`p` {uses "galois_rep"}[Galois representation] $`\rho` attached to the
{uses "frey_curve"}[Frey curve] is *reducible* — equivalently, not irreducible.
(This is the statement called $`B_3` in the lecture notes.)
:::

The reason $`B_4` is exactly what we need is a beautiful and deep theorem, which
by the rules of the game we are entitled to assume: it was proved in the 1980s.

:::theorem "mazur_serre_irreducible" (parent := "curves") (lean := "FreyPackage.mazur") (uses := "frey_curve, galois_rep")
For every {uses "frey_package"}[Frey package], the mod $`p`
{uses "galois_rep"}[Galois representation] attached to the
{uses "frey_curve"}[Frey curve] is *irreducible*.
:::

:::proof "mazur_serre_irreducible"
This is Proposition 6 of Serre's 1987 Duke paper *Sur les représentations
modulaires de degré 2 de* $`\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})`. By a
delicate arithmetic argument, if $`\rho` were reducible one could manipulate the
Frey curve into a curve $`Y^2 = (X-\alpha)(X-\beta)(X-\gamma)` over $`\mathbb{Q}`
whose $`p`-torsion contains a *nonzero point* fixed by the whole Galois group;
Galois theory then forces this point to have rational coordinates, i.e. to be a
$`\mathbb{Q}`-point of order $`p`.

But Mazur's landmark 1977 paper shows that no elliptic curve over $`\mathbb{Q}`
can possess a $`\mathbb{Q}`-point of prime order $`p \geq 5`. This is a
contradiction, so $`\rho` is irreducible. Mazur's paper — longer than the Wiles
and Taylor–Wiles papers combined, and drawing on a large chunk of Grothendieck's
1960s machinery — is one of several deep inputs that every known proof of Fermat's
Last Theorem relies on. Formalizing it is not part of the present project, so we
assume it.
:::

Beating the boss is now a one-line contradiction.

:::theorem "B4_implies_B3" (parent := "curves") (lean := "FLT.Bosses.B4_implies_B3") (uses := "Statement_B4_reducible, Statement_B3_no_Frey_Package")
Statement $`B_4` implies statement $`B_3`: if the Frey representation is always
reducible, then there are no {uses "frey_package"}[Frey packages].
:::

:::proof "B4_implies_B3" (uses := "mazur_serre_irreducible")
We prove the contrapositive is vacuous by deriving a contradiction from the
existence of a Frey package. Suppose $`P` is a {uses "frey_package"}[Frey package]
and let $`\rho` be the mod $`p` {uses "galois_rep"}[representation] of its
{uses "frey_curve"}[Frey curve].

Statement {uses "Statement_B4_reducible"}[$`B_4`] tells us $`\rho` is reducible,
i.e. *not* irreducible. But {uses "mazur_serre_irreducible"}[Serre and Mazur] tell
us $`\rho` *is* irreducible. These directly contradict each other, so no Frey
package exists — which is precisely statement
{uses "Statement_B3_no_Frey_Package"}[$`B_3`].
:::

Assuming the boss for now, we can record the payoff of the level.

:::theorem "B3_proof" (parent := "curves") (lean := "FLT.Bosses.B3_proof") (uses := "Statement_B3_no_Frey_Package")
Statement $`B_3` is true: there are no Frey packages.
:::

:::proof "B3_proof"
Immediate from {uses "B4_implies_B3"}[the boss theorem], assuming statement
$`B_4`.
:::

This is a genuine milestone. Combined with the earlier levels, it reduces Fermat's
Last Theorem to a single statement about the reducibility of one explicit family
of Galois representations. Everything from here on is about proving statement
$`B_4`. The corresponding "main spine" in Lean lives in `FLT/Proof.lean`, where
`B4_implies_B3` and the deduction of `flt` from it are assembled; the
mathematics of this level is formalized in `FLT/FreyCurve/Basic.lean` (the Frey
curve), `FLT/EllipticCurve/Torsion.lean` (torsion and Galois representations) and
`FLT/FreyCurve/Mazur.lean` (irreducibility).
