import Verso
import VersoManual
import VersoBlueprint
import FLT.FreyCurve.FreyPackage
import FLT.Proof

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Level 3: Frey packages" =>

The story so far: we have reduced Fermat's Last Theorem to proving statement $`B_2`.
In this level, we define a _Frey package_ to be, basically, a counterexample to
Fermat's Last Theorem satisfying certain extra conditions. Statement $`B_3` is the
statement that there are no Frey packages. The boss of this level will be to prove
that $`B_3` implies $`B_2`.

It is at this point in the argument where we need the concept of negative numbers.
So let's assume familiarity with the integers $`\Z={}\ldots,-2,-1,0,1,2,\ldots\}`
and the concept of subtraction. Let's identify
$`\mathbb{N}` with the corresponding subset of $`\Z`. Let's also assume
familiarity with the concept of divisibility: an integer $`a` divides an integer $`b`
(we write $`a \mid b`) if there's an integer $`c` such that $`b=ac`.
Let's assume familiarity with the concept of congruence: two integers $`x` and $`y`
are congruent modulo an integer $`n` if $`n` divides $`x-y` (we write $`x \equiv y \pmod n`).
Finally, let's say
that two integers are _coprime_ if no natural number greater than one divides both of them;
this is equivalent to no prime number dividing both of them. We can now define a Frey package.

:::group "frey"
Frey packages.
:::

:::definition "frey_package" (parent := "frey") (lean := "FreyPackage")
A *Frey package* is the following data:
* three nonzero, pairwise coprime integers
  $`a`, $`b`, $`c`;
* and a prime number $`p \geq 5`,

subject to the requirements that
* $`a \equiv 3 \pmod 4` and $`b \equiv 0 \pmod 2` (that is, $`b` is even);
* and $`a^p + b^p = c^p`.
:::


The somewhat mysterious congruence conditions will be clarified when we introduce
the concept of a Frey curve in the next level.

Now we've made the definition, we can write down statement $`B_3`:
:::definition "Statement_B3_no_Frey_Package" (parent := "frey") (lean := "FLT.Bosses.B3")
There are no {uses "frey_package"}[Frey packages].
:::

Recall that we've reduced Fermat's Last Theorem to theorem $`B_2`:
Fermat's Last Theorem is true for $`n=p\geq5` prime. We will now
show that this statement follows from theorem $`B_3`, the nonexistence of
Frey packages.

:::lemma_ "B_3_no_Frey_Package_implies_B_2_FLT_for_p_geq_5" (parent := "frey") (lean := "FreyPackage.fermatLastTheoremFor_p_ge_5")
Suppose that there are {uses "Statement_B3_no_Frey_Package"}[no Frey packages].
Then Fermat's Last Theorem is true for all primes $`p \geq 5`.
:::

:::proof "B_3_no_Frey_Package_implies_B_2_FLT_for_p_geq_5"
We prove the contrapositive. Suppose that we have a counterexample to FLT with positive
integers $`a,` $`b` and $`c` and a prime $`p \geq 5.`
We massage the counterexample into one satisfying all the extra conditions of
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

The resulting data $`(a, b, c, p)` is a {uses "frey_package"}[Frey package],
which was what we were required to construct.
:::

In the next level, we will begin the proof of $`B_3`. Assuming it for now,
we can deduce

:::theorem "B2_proof" (parent := "frey") (lean := "FLT.Bosses.B2_proof")
Statement $`B_2` is true. In other words, FLT is true for $`p\geq5` prime.
:::

:::proof "B2_proof"
Follows from {uses "B_3_no_Frey_Package_implies_B_2_FLT_for_p_geq_5"}[the above argument],
assuming {uses "B3_proof"}[$`B_3.`]
:::

It remains to prove statement $`B_3`.
