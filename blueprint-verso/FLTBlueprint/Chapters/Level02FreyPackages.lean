import Verso
import VersoManual
import VersoBlueprint
import FLT.FreyCurve.FreyPackage

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Level 2: Frey packages" =>

In this level, we define a _Frey package_ to be, basically, a counterexample to
Fermat's Last Theorem satisfying certain extra criteria. The boss of this level
is the reduction of Fermat's Last Theorem to the non-existence of a Frey package.

It is at this point in the argument where we need the concept of negative numbers.
So let's assume familiarity with the integers $`\Z` and the concept of
subtraction. Let's identify
$`\mathbb{N}` with the corresponding subset of $`\Z`. Let's also assume
familiarity with the concept of divisibility: an integer $`a` divides an integer $`b`
(we write $`a \mid b`) if there's an integer $`c` such that $`b=ac`.
Let's assume familiarity with the concept of congruence: two integers $`x` and $`y`
are congruent modulo an integer $`n` if $`n` divides $`x-y` (we write $`x \equiv y \pmod n`).
Finally, let's say
that two integers are _coprime_ if no natural number greater than one divides both of them;
this is equivalent to no prime number dividing both of them. We can now define a Frey package.

:::group "frey"
The integers, congruences, and the definition of a Frey package, leading to the
second boss theorem.
:::

:::definition "frey_package" (parent := "frey") (lean := "FreyPackage")
A *Frey package* is the following data:
* three nonzero, pairwise coprime integers
  $`a`, $`b`, $`c`;
* a prime number $`p \geq 5`;

subject to the requirements that
* $`a \equiv 3 \pmod 4` and $`b \equiv 0 \pmod 2` (that is, $`b` is even);
* $`a^p + b^p = c^p`.

The somewhat mysterious congruence conditions will be clarified when we introduce
the concept of a Frey curve in the next level.
:::

With the definition in hand, here is statement $`B_2`.

:::theorem "no_frey_package" (parent := "frey")
*(Statement $`B_2`.)* There is no {uses "frey_package"}[Frey package].
:::

The boss of this level is to show that statement $`B_2` implies Fermat's Last Theorem.
By the main result of the previous level, it suffices to show that statement $`B_2`
implies statement $`B_1`.

:::lemma_ "fermatLastTheoremFor_p_ge_5_of_no_Frey_package" (parent := "frey") (lean := "FreyPackage.fermatLastTheoremFor_p_ge_5")
Suppose that there is no {uses "no_frey_package"}[no Frey package]. Then Fermat's Last Theorem is true
for all primes $`p \geq 5`.
:::

:::proof "fermatLastTheoremFor_p_ge_5_of_no_Frey_package"
We prove the contrapositive. Suppose that we have a counterexample to FLT with positive
integers $`a,` $`b` and $`c` and a prime $`p \geq 5.`
We massage the counterexample into one satisfying all the extra conditions for
a Frey package.

*Coprimality.* First we make $`a` and $`b` coprime. If some prime $`q` divides both
$`a` and $`b`, then $`q` divides $`a^p + b^p = c^p`, and hence (as $`q` is prime)
$`q` divides $`c`. Dividing $`a`, $`b` and $`c` all through by $`q` produces a smaller
solution. We repeat this trick until $`a` and $`b` are coprime.
The relation
$`a^p + b^p = c^p` then forces $`a`, $`b`, $`c` to be
pairwise coprime: any prime dividing $`a` and $`c` would
also divide $`b^p = c^p - a^p` and hence $`b`, contradicting $`\gcd(a,b)=1`, and
similarly for $`b` and $`c`.

*Parity.* Since $`a`, $`b`, $`c` are pairwise coprime and $`a^p + b^p = c^p`, exactly
one of them is even. We can arrange for it to be $`b`. Indeed:
* if $`a` is the even one, swap $`a` and $`b`;
* if $`c` is the even one, replace $`(a, b, c)` by $`(a, -c, -b)`. This keeps the
  Fermat equation valid because $`p` is odd (being a prime at least $`5`), so
  $`a^p + (-c)^p = a^p - c^p = -(b^p) = (-b)^p`.

After this step $`b` is even and $`a`, $`c` are both odd.

*Congruence mod $`4`.* As $`a` is odd, we have $`a \equiv 1` or $`a \equiv 3 \pmod 4`.
If $`a \equiv 1 \pmod 4`, replace $`(a, b, c)` by $`(-a, -b, -c)`; we still
have $`(-a)^p+(-b)^p=(-c)^p`, $`-b` is still even, and $`-a` is now 3 mod 4.

The resulting data $`(a, b, c, p)` is a {uses "frey_package"}[Frey package].
:::
