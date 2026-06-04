import Verso
import VersoManual
import VersoBlueprint
import Mathlib.NumberTheory.FLT.Basic
import Mathlib.NumberTheory.FLT.Three
import Mathlib.NumberTheory.FLT.Four

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Reduction to the prime case" =>

In the previous chapter we were painfully careful. We built the natural numbers
out of nothing, we defined addition, multiplication and exponentiation one
successor at a time, and we made a point of the fact that even an utterly mundane
statement such as $`2 \neq 48573486 \times 3586358934658` is *not* given to us for
free: somebody, somewhere, has to prove it.

That was, in part, a joke, and it is a joke that does not improve with repetition.
So we now retire it. From this chapter onwards we grant ourselves the ordinary
mathematics of the school classroom, and we use it without apology. In particular
we help ourselves to:

* the usual laws of arithmetic — that $`+` and $`\times` are commutative and
  associative, and that multiplication distributes over addition (in the jargon,
  that the natural numbers form a *commutative semiring*);
* the usual facts about $`\leq` and about divisibility;
* and, crucially, *unique factorization*: every positive natural number is a
  product of prime numbers, in essentially only one way.

None of this is deep, but all of it is genuine work when done from first
principles — which is precisely why we now decline to do it. We will cheerfully
believe that $`2` is prime, and we will never again worry about ruling out
$`2 = 373234827364 \times 243823482768`.

The goal of this chapter is the first real theorem of the course, and it is a
*reduction*. We show that, in order to prove Fermat's Last Theorem in full, it is
enough to prove it one prime exponent at a time, and moreover only for primes that
are at least $`5`. The two small exponents left over, $`n = 3` and $`n = 4`, are
old theorems of Euler and Fermat; both were formalized in Lean's mathematics
library long ago, so we will simply quote them.

:::group "reductions"
The reduction of Fermat's Last Theorem to the case of prime exponents at least
five.
:::

:::definition "prime" (parent := "reductions") (lean := "Nat.Prime")
A natural number $`p` is *prime* if $`2 \leq p` and the only way to write it as a
product is the obvious one: if $`p = a b` then $`a = 1` or $`b = 1`. The first few
primes are $`2, 3, 5, 7, \ldots`, and we take their elementary properties for
granted.
:::

:::definition "flt_prime_ge_5" (parent := "reductions")
*Statement $`B_1`.* For every {uses "prime"}[prime] number $`p` with $`5 \leq p`,
Fermat's Last Theorem holds for the exponent $`p`: there are no positive natural
numbers $`a, b, c` with $`a^p + b^p = c^p`. This is the statement we will spend the
rest of the course proving; for now we simply give it a name and treat it as a
hypothesis.
:::

:::theorem "flt_three" (parent := "reductions") (lean := "fermatLastTheoremThree")
*(Euler.)* There are no positive natural numbers $`a, b, c` with
$`a^3 + b^3 = c^3`.
:::

:::proof "flt_three"
This is a theorem of Euler. It is already in Lean's mathematics library — it was
formalized by a team at the 2024 *Lean for the Curious Mathematician* meeting in
Luminy — so, by the rules of our game, we may simply cite it.
:::

:::theorem "flt_four" (parent := "reductions") (lean := "fermatLastTheoremFour")
*(Fermat.)* There are no positive natural numbers $`a, b, c` with
$`a^4 + b^4 = c^4`.
:::

:::proof "flt_four"
This one is even older: it is essentially Fermat's own argument by infinite
descent, and it too lives in Lean's mathematics library, so we quote it as well.
:::

:::lemma_ "descent" (parent := "reductions") (lean := "FermatLastTheoremFor.mono")
If $`d` divides $`n` and Fermat's Last Theorem holds for the exponent $`d`, then it
also holds for the exponent $`n`.
:::

:::proof "descent"
Write $`n = d m`. Suppose, for contradiction, that there were positive naturals
with $`a^n + b^n = c^n`. Since $`a^n = a^{d m} = (a^m)^d`, and likewise for $`b`
and $`c`, the numbers $`a^m, b^m, c^m` would be a positive solution for the
exponent $`d` — and a power of a positive number is positive. That contradicts
Fermat's Last Theorem for $`d`. This is `FermatLastTheoremFor.mono` in mathlib.
:::

:::lemma_ "divisibility" (parent := "reductions")
Every natural number $`n` with $`3 \leq n` is a multiple of $`3`, a multiple of
$`4`, or a multiple of some {uses "prime"}[prime] $`p` with $`5 \leq p`.
:::

:::proof "divisibility"
By unique factorization, write $`n` as a product of primes. If $`2` is the only
prime that appears, then $`n` is a power of $`2`; since $`3 \leq n`, this power is
at least the second, so $`4 \mid n`. Otherwise some odd prime $`p` divides $`n`.
Such a $`p` is at least $`3`; if $`p = 3` then $`3 \mid n`, and if not then $`p`
is an odd prime other than $`3`, hence $`p \geq 5`. In Lean we lean on the library
lemma `Nat.four_dvd_or_exists_odd_prime_and_dvd_of_two_lt`, which packages exactly
this "power of two versus odd prime factor" dichotomy.
:::

```lean "divisibility"
theorem dvd_three_four_or_prime_ge_five
    {n : ℕ} (hn : 3 ≤ n) :
    3 ∣ n ∨ 4 ∣ n ∨ ∃ p, p.Prime ∧ 5 ≤ p ∧ p ∣ n := by
  have key :=
    Nat.four_dvd_or_exists_odd_prime_and_dvd_of_two_lt hn
  rcases key with h4 | ⟨p, hp, hdvd, hodd⟩
  · exact Or.inr (Or.inl h4)
  · rcases eq_or_ne p 3 with rfl | hp3
    · exact Or.inl hdvd
    · have hp5 : 5 ≤ p := by
        have h2 := hp.two_le
        obtain ⟨k, rfl⟩ := hodd
        omega
      exact Or.inr (Or.inr ⟨p, hp, hp5, hdvd⟩)
```

:::theorem "flt_of_prime_ge_5" (parent := "reductions")
*(The boss of the chapter.)* {uses "flt_prime_ge_5"}[Statement $`B_1`] implies
Fermat's Last Theorem: if Fermat's Last Theorem holds for every prime exponent
$`p \geq 5`, then it holds for every exponent $`n \geq 3`.
:::

:::proof "flt_of_prime_ge_5"
Let $`n \geq 3`. By {uses "divisibility"}[the previous lemma], $`n` is a multiple
of $`3`, of $`4`, or of a prime $`p \geq 5`.

* If $`3 \mid n`, then {uses "flt_three"}[Euler's theorem], pushed up by
  {uses "descent"}[the descent lemma], gives Fermat's Last Theorem for the
  exponent $`n`.
* If $`4 \mid n`, then {uses "flt_four"}[Fermat's theorem] and the descent lemma
  do the same.
* If a prime $`p \geq 5` divides $`n`, then {uses "flt_prime_ge_5"}[our hypothesis
  $`B_1`] gives Fermat's Last Theorem for the exponent $`p`, and the descent lemma
  promotes it to the exponent $`n`.

In every case Fermat's Last Theorem holds for the exponent $`n`, as required.
:::

```lean "flt_of_prime_ge_5"
theorem fermatLastTheorem_of_prime_ge_five
    (H : ∀ p ≥ 5, p.Prime → FermatLastTheoremFor p) :
    FermatLastTheorem := by
  intro n hn
  rcases dvd_three_four_or_prime_ge_five hn with
    h3 | h4 | ⟨p, hp, hp5, hdvd⟩
  · exact fermatLastTheoremThree.mono h3
  · exact fermatLastTheoremFour.mono h4
  · exact (H p hp5 hp).mono hdvd
```

The moral of this chapter mirrors the last one, but in reverse. *Stating* Fermat's
Last Theorem needed nothing beyond the axioms of mathematics. *Reducing* it to the
prime case needed only school mathematics — and yet already we have had to call on
unique factorization, on the arithmetic of $`\leq` and divisibility, and on two
hard theorems of Euler and Fermat. The real battle has begun.
