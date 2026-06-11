import Verso
import VersoManual
import VersoBlueprint
import FLT.Basic.FreyPackage

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Level 2: Frey packages" =>

In the previous level we reduced Fermat's Last Theorem to the case of a prime
exponent $`p \geq 5` (this was {uses "flt_prime_ge_5"}[Statement $`B_1`]).
The boss of this level repackages a hypothetical counterexample to $`B_1` as a
single, highly structured object which we call a *Frey package*. The boss theorem
will then assert that the mere non-existence of Frey packages is enough to recover
Fermat's Last Theorem.

As promised at the end of Level 1, we now grant ourselves a powerful upgrade: from
here on we freely use the standard results of an undergraduate mathematics degree,
all of which were known well before the 1990s. In particular we will happily talk
about the integers and their arithmetic without reproving everything from the axioms.

To even *state* the definition of a Frey package we need two ingredients which we
have so far managed to avoid: the integers, and the notion of congruence.

:::group "frey"
The integers, congruences, and the definition of a Frey package, leading to the
second boss theorem.
:::

:::definition "integers" (parent := "frey") (lean := "Int")
The *integers* $`\mathbb{Z}` are obtained from the {uses "natural_numbers"}[natural
numbers] by adjoining additive inverses: formally, $`\mathbb{Z}` is the additive
localization (the Grothendieck group) of the additive monoid $`(\mathbb{N}, +)`.
The integers carry a natural commutative ring structure, extending
{uses "addition"}[addition] and {uses "multiplication"}[multiplication] on
$`\mathbb{N}`.

Because $`\mathbb{Z}` is built from $`\mathbb{N}`, there is a canonical ring
homomorphism $`\mathbb{N} \to \mathbb{Z}`. The traditional mathematical notation for
this map is *no notation at all*: we silently regard a natural number as an integer.
But the map is there.
:::

:::definition "congruence" (parent := "frey") (lean := "Int.ModEq")
Let $`x` and $`y` be {uses "integers"}[integers] and let $`n` be a natural number.
We say that $`x` and $`y` are *congruent modulo* $`n`, written $`x \equiv y \pmod n`,
if $`n` — regarded as an integer through the invisible map — divides the difference
$`x - y`.
:::

:::definition "coprime_integers" (parent := "frey") (lean := "Int.gcd")
Two {uses "integers"}[integers] are *coprime* if no prime number divides both of them;
equivalently, their greatest common divisor is $`1`. Three integers $`a`, $`b`, $`c` are *pairwise coprime* if each of the
three pairs $`(a, b)`, $`(b, c)` and $`(a, c)` is coprime.
:::

We can now assemble all of these pieces into the central definition of this level.

:::definition "frey_package" (parent := "frey") (lean := "FreyPackage")
A *Frey package* is the following data:
* three nonzero, {uses "coprime_integers"}[pairwise coprime] {uses "integers"}[integers]
  $`a`, $`b`, $`c`;
* a prime number $`p` with {uses "small_numbers"}[$`p \geq 5`];

subject to the requirements that
* $`a \equiv 3 \pmod 4` and $`b \equiv 0 \pmod 2` (that is, {uses "congruence"}[$`b` is even]);
* $`a^p + b^p = c^p`.

The somewhat mysterious congruence conditions are exactly what is needed to ensure
that the elliptic curve $`Y^2 = X(X - a^p)(X + b^p)` — the *Frey curve* of the
package, which we will meet in the next level — has all the good properties required
by Serre's analysis.
:::

With the definition in hand, here is the statement that this level reduces to.

:::theorem "no_frey_package" (parent := "frey")
*(Statement $`B_2`.)* There is no {uses "frey_package"}[Frey package].
:::

Our task is to show that Statement $`B_2` implies Fermat's Last Theorem. As in the
previous level, the heart of the argument is a construction, which we isolate first.

:::lemma_ "frey_package_of_solution" (parent := "frey") (lean := "FreyPackage.of_not_FermatLastTheorem_p_ge_5")
Suppose $`a`, $`b`, $`c` are nonzero {uses "integers"}[integers] and $`p \geq 5` is a
prime with $`a^p + b^p = c^p`. Then there exists a {uses "frey_package"}[Frey package].
:::

:::proof "frey_package_of_solution"
We massage the given solution into one satisfying all the extra conditions.

*Coprimality.* First we make $`a` and $`b` coprime. If some prime $`q` divides both
$`a` and $`b`, then $`q` divides $`a^p + b^p = c^p`, and hence (as $`q` is prime)
$`q` divides $`c`. Dividing $`a`, $`b` and $`c` all through by $`q` produces a smaller
solution, and repeating finitely often we may assume $`\gcd(a, b) = 1`. The relation
$`a^p + b^p = c^p` then forces $`a`, $`b`, $`c` to be
{uses "coprime_integers"}[pairwise coprime]: any prime dividing $`a` and $`c` would
also divide $`b^p = c^p - a^p` and hence $`b`, contradicting $`\gcd(a,b)=1`, and
similarly for $`b` and $`c`.

*Parity.* Since $`a`, $`b`, $`c` are pairwise coprime and $`a^p + b^p = c^p`, exactly
one of them is even. We arrange for it to be $`b`:
* if $`a` is the even one, swap the roles of $`a` and $`b`;
* if $`c` is the even one, replace $`(a, b, c)` by $`(a, -c, -b)`. This keeps the
  equation valid because $`p` is odd (being a prime at least $`5`), so
  $`a^p + (-c)^p = a^p - c^p = -(b^p) = (-b)^p`.

After this step $`b` is even and $`a`, $`c` are both odd.

*Congruence mod $`4`.* As $`a` is odd, we have $`a \equiv 1` or $`a \equiv 3 \pmod 4`.
If $`a \equiv 1 \pmod 4`, replace $`(a, b, c)` by $`(-a, -b, -c)`; this is again
legitimate because $`p` is odd, and it flips $`a` to $`-a \equiv 3 \pmod 4` while
preserving the equation, the nonvanishing, the coprimality, and the parity of $`b`.

The resulting data $`(a, b, c, p)` is a {uses "frey_package"}[Frey package].
:::

:::theorem "flt_of_no_frey_package" (parent := "frey") (lean := "FreyPackage.of_not_FermatLastTheorem")
*(Level boss.)* {uses "no_frey_package"}[Statement $`B_2`] implies
{uses "flt"}[Fermat's Last Theorem].
:::

:::proof "flt_of_no_frey_package"
By the {uses "flt_of_prime_ge_5"}[boss of Level 1] it is enough to deduce
{uses "flt_prime_ge_5"}[Statement $`B_1`] from Statement $`B_2`. We argue by
contraposition: suppose $`B_1` fails, so there is a prime $`p \geq 5` together with
positive natural numbers $`a`, $`b`, $`c` satisfying $`a^p + b^p = c^p`.

Viewing $`a`, $`b`, $`c` as nonzero {uses "integers"}[integers] through the invisible
map, the {uses "frey_package_of_solution"}[construction above] manufactures a
{uses "frey_package"}[Frey package]. This contradicts Statement $`B_2`. Hence $`B_2`
implies $`B_1`, and therefore $`B_2` implies Fermat's Last Theorem.
:::

This completes the level. Notice how much more comfortable life has become now that
we are allowed to assume undergraduate mathematics: a step which would have been an
enormous undertaking from the axioms alone is now a short and natural argument. In the
next level we will breathe geometric life into the congruence conditions of a Frey
package by attaching to it an elliptic curve.
