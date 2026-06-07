import Verso
import VersoManual
import VersoBlueprint
import Mathlib.NumberTheory.FLT.Basic
import Mathlib.NumberTheory.FLT.Three
import Mathlib.NumberTheory.FLT.Four
import FLT.Basic.Lemmas
import FLT.Basic.Reductions

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Level 1: First reductions" =>

Our ultimate goal is to prove that there are no solutions to $`x^n + y^n = z^n` in positive
integers when $`n \geq 3`. Our first step is to reduce to the case where $`n`
is prime and at least $`5`. Before we start, we should observe that even this
relatively straightforward task would be _extremely_ long and tedious assuming
only the axioms of mathematics. For example, although we have defined addition
and multiplication, we have not yet established any of the basic facts about
them such as $`a + b = b + a` or $`ab=ba` (as they were not needed to state Fermat's Last Theorem).
The reader interested in seeing what it really means to do mathematics from the axioms
is encouraged to play the [Natural Number Game](https://adam.math.hhu.de/#/g/leanprover-community/nng4).

In this exposition of Fermat's Last Theorem we shall now make the pragmatic assumption
that the reader knows what things like $`5` and "prime" mean, and
furthermore that they are happy with basic properties of the natural numbers
such as factoring numbers into primes.

We recall what we're trying to prove.

-- TODO error: FLTBlueprint/Blueprint.lean:23:0: Duplicate imported blueprint node label 'flt'
:::theorem "flt2_this_is_flt" (parent := "definitions") (lean := "Wiles_Taylor_Wiles")
Fermat's Last Theorem is a simple relationship between {uses "addition"}[addition]
and {uses "exponentiation"}[exponentiation]. TODO remove these links.
Let $`a`, $`b` and $`c` be {uses "leq"}[positive] natural numbers
and let $`n` be a natural number with {uses "small_numbers"}[$`3 \leq n`]. Then
$`a ^ n + b ^ n \neq c ^ n`.
:::

We're going to start the proof by making a reduction. That is, we will
write down another mathematical statement, Theorem B1.
Then the boss of this level (i.e., the main objective of this chapter)
will be to prove Fermat's Last Theorem *assuming* theorem B1.

:::group "reductions"
The reduction of Fermat's Last Theorem to the case of prime exponent at least
five.
:::

Consider the following statement, which we'll call B1.

:::theorem "flt_prime_ge_5" (parent := "reductions")
*(Statement $`B_1`.* )For every prime number $`p \geq 5`,
Fermat's Last Theorem holds for the exponent $`p`: there are no positive natural
numbers $`a, b, c` with $`a^p + b^p = c^p`.
:::

The theorem we shall prove in this section is that statement $`B_1` implies
Fermat's Last Theorem. We will do this, assuming two old theorems which
date back centuries.

:::theorem "fermatLastTheoremThree" (parent := "reductions") (lean := "fermatLastTheoremThree")
*(Euler.)* There are no positive natural numbers $`a, b, c` with
$`a^3 + b^3 = c^3`.
:::

:::proof "fermatLastTheoremThree"
This is a theorem of Euler. It is already in Lean's mathematics library — it was
formalized by a team at the 2024 *Lean for the Curious Mathematician* meeting in
Luminy.
:::

:::theorem "fermatLastTheoremFour" (parent := "reductions") (lean := "fermatLastTheoremFour")
*(Fermat.)* There are no positive natural numbers $`a, b, c` with
$`a^4 + b^4 = c^4`.
:::

:::proof "fermatLastTheoremFour"
This one is even older: it is essentially Fermat's own argument by infinite
descent, and it is also in Lean's mathematics library.

Here is a sketch proof. WLOG $`a`, $`b` and $`c` are pairwise coprime.
It thus suffices to show that there are no pairwise coprime positive integer
solutions to $`X^4+Y^4=Z^2`. By switching $`X` and $`Y` if necessary, we may
assume that $`X` is odd, so $`Y` is even and $`Z` is even by considerations modulo 4.

We now use the theorem that if $`r`, $`s`, $`t` are pairwise
coprime positive integers satisfying $`r^2+s^2=t^2`, and with $`r`, $`t` odd and $`s` even,
then there are pairwise
coprime positive integers $`m>n`, one even and one odd, with $`r=m^2-n^2`, $`s=2mn` and
$`t=m^2+n^2`. Applying this to $`X^4+Y^4=Z^2` we deduce that $`X^2=m^2-n^2` and $`Y^2=2mn`.
Now $`m`, $`n` are coprime and the second equation tells us that their product is twice a square.
We cannot have $`m=2a^2` and `n=b^2` (the first equation becomes insolvable mod 4) so we must
have $`m=a^2` and $`n=2b^2`, meaning that $`X^2=a^4-4b^4`.

The conclusion so far: if we have a solution to $`X^4+Y^4=Z^2` then we have
a smaller solution to $`V^4-4W^4=X^2`.

We now do the same trick again. We have $`(2W^2)^2+X^2=(V^2)^2` and we know $`X` is odd,
meaning that there are pairwise coprime $`p`, and $`q` (one even and one odd) with
$`2W^2=2pq` (thus $`p=\alpha^2` and $`q=\beta^2` are both squares) and
$`V^2=p^2+q^2=\alpha^4+\beta^4`. In particular, if we have a solution to `$V^4-4W^4=X^2`,
we have a smaller solution to $`X^4+Y^4=Z^2`.

The upshot: if there is a solution in positive integers, then there is an infinitely long
sequence of solutions, each smaller than the one before. But this cannot happen for
positive integer solutions.

:::

Modulo these results, the proof is not too difficult. We explain the details.

:::lemma_ "descent" (parent := "reductions") (lean := "FermatLastTheoremFor.mono")
If $`d` divides $`n` and Fermat's Last Theorem holds for the exponent $`d`, then it
also holds for the exponent $`n`.
:::

:::proof "descent"
Write $`n = d m`. Suppose, for contradiction, that there were positive naturals
with $`a^n + b^n = c^n`. Since $`a^n = a^{d m} = (a^m)^d`, and likewise for $`b`
and $`c`, the numbers $`a^m, b^m, c^m` would be a positive solution for the
exponent $`d` — and a power of a positive number is positive. That contradicts
Fermat's Last Theorem for $`d`.
:::

:::lemma_ "three_dvd_or_four_dvd_or_prime_dvd" (parent := "reductions") (lean := "Nat.three_dvd_or_four_dvd_or_prime_dvd")
Every natural number $`n` with $`3 \leq n` is a multiple of $`3`, a multiple of
$`4`, or a multiple of some prime $`p \geq 5`.
:::


:::proof "three_dvd_or_four_dvd_or_prime_dvd"
Write $`n` as a product of primes. If $`2` is the only
prime that appears, then $`n=2^t` is a power of $`2`; since $`3 \leq n` we have $`t \geq 2`
and hence $`4 \mid n`. Otherwise some odd prime $`p` divides $`n`.
Such a $`p` is at least $`3`; if $`p = 3` then $`3 \mid n`, and if not then $`p`
is an odd prime other than $`3`, hence $`p \geq 5`.
:::

:::theorem "flt_of_prime_ge_5" (parent := "reductions")
*(The boss of the chapter.)* {uses "flt_prime_ge_5"}[Statement $`B_1`] implies
{uses "flt"}[Fermat's Last Theorem].
:::

:::proof "flt_of_prime_ge_5"
Let's assume Fermat's Last Theorem is false, so we have $`n \geq 3` and a solution
to $`x^n+y^n=z^n` in positive integers, and let's construct a counterexample to statement $`B_1`.

By {uses "three_dvd_or_four_dvd_or_prime_dvd"}[the previous lemma], $`n` is a multiple
of $`3`, of $`4`, or of a prime $`p \geq 5`.

By {uses "descent"}[the descent lemma], Fermat's Last Theorem must be false for
$`n=3`, $`n=4` or for some prime $`p \geq 5.`

However, we have just seen that Fermat's Last Theorem is true
for {uses "fermatLastTheoremThree"}[$`n=3`] and {uses "fermatLastTheoremFour"}[$`n=4`].
The only possibility
left is that it is false for some prime $`p \geq 5`. Hence statement $`B_1` is
false, which is what we wanted to prove.
:::

So all we have to do now is to prove Theorem $`B_1`. In the next level, we will further reduce
$`B_1` to the theorem that there is no Frey package.
