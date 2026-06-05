import Verso
import VersoManual
import VersoBlueprint
import Mathlib.NumberTheory.FLT.Basic
import Mathlib.NumberTheory.FLT.Three
import Mathlib.NumberTheory.FLT.Four

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "First reductions" =>

Our goal is to prove that there are no solutions to $`x^n + y^n = z^n` in positive
integers when $`n \geq 3`. Our first step is to reduce to the case where $`n`
is prime and at least $`5`. Before we start, we should observe that even this
relatively straightforward task would be _extremely_ long and tedious assuming
only the axioms of mathematics. For example, although we have defined addition
and multiplication, we have not yet established any of the basic facts about
them such as $`a + b = b + a` or $`ab=ba` (as they were not needed to state Fermat's Last Theorem).
The reader interested in seeing what it really means to do mathematics from the axioms
is encouraged to play the Natural Number Game.

In this exposition of Fermat's Last Theorem we shall now make the pragmatic assumption
that the reader knows what things like $`5` and "prime" mean, and
furthermore that they are happy with basic properties of the natural numbers
such as factoring numbers into primes.

:::group "reductions"
The reduction of Fermat's Last Theorem to the case of prime exponent at least
five.
:::

Consider the following statement.

:::definition "flt_prime_ge_5" (parent := "reductions")
*Statement $`B_1`.* For every prime number $`p \geq 5`,
Fermat's Last Theorem holds for the exponent $`p`: there are no positive natural
numbers $`a, b, c` with $`a^p + b^p = c^p`.
:::

The theorem we shall prove in this section is that statement $`B_1` implies
Fermat's Last Theorem. We will do this, assuming two theorems which
date back centuries and which we will now state.

:::theorem "flt_three" (parent := "reductions") (lean := "fermatLastTheoremThree")
*(Euler.)* There are no positive natural numbers $`a, b, c` with
$`a^3 + b^3 = c^3`.
:::

:::proof "flt_three"
This is a theorem of Euler. It is already in Lean's mathematics library — it was
formalized by a team at the 2024 *Lean for the Curious Mathematician* meeting in
Luminy.
:::

:::theorem "flt_four" (parent := "reductions") (lean := "fermatLastTheoremFour")
*(Fermat.)* There are no positive natural numbers $`a, b, c` with
$`a^4 + b^4 = c^4`.
:::

:::proof "flt_four"
This one is even older: it is essentially Fermat's own argument by infinite
descent, and it is also in Lean's mathematics library.
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

:::lemma_ "divisibility" (parent := "reductions") (lean := "dvd_three_four_or_prime_ge_five")
Every natural number $`n` with $`3 \leq n` is a multiple of $`3`, a multiple of
$`4`, or a multiple of some prime $`p \geq 5`.
:::


:::proof "divisibility"
Write $`n` as a product of primes. If $`2` is the only
prime that appears, then $`n=2^t` is a power of $`2`; since $`3 \leq n` we have $`t \geq 2`
and hence $`4 \mid n`. Otherwise some odd prime $`p` divides $`n`.
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
