import Verso
import VersoManual
import VersoBlueprint
import FLT.Proof

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Stating Fermat's Last Theorem" =>

Welcome to the first level of the Fermat's Last Theorem game.

Let's start at the beginning, by defining the natural numbers
$`\mathbb{N}=\{0,1,2,3,\ldots\}`. Our convention will be that they start at zero.
Indeed, this will be the first of the rules which we use
to define the natural numbers.

:::group "definitions"
The definitions needed to state Fermat's Last Theorem.
:::

:::author "flt_author" (name := "FLT Project")
:::

:::definition "natural_numbers" (parent := "definitions") (lean := "Nat")
The *natural numbers* are defined by these rules:
 * $`0` is a natural number;
 * If $`n` is a natural number, then its *successor* $`S(n)` is again a natural number;
 * That's it.
:::


The _successor_ of a number means the one that comes after it — for example,
the successor of 37 is 38. But we're getting ahead of ourselves, we didn't
name any numbers yet other than zero. Using successors,
let's name some more numbers.

:::definition "small_numbers" (parent := "definitions") (lean := "One.one")
We name the following {uses "natural_numbers"}[natural numbers].
We define $`1` to be $`S(0)` (the successor of zero), we let $`2` be $`S(1)` and
we define $`3` to be $`S(2)`.
:::

There are numbers beyond three, but we don't need any of them to state
Fermat's Last Theorem. We do however need to talk about the third rule
defining natural numbers, namely "That's it". The meaning of this rule
is that if we want to define something for all numbers, then it suffices
to do the following:

* Define it for $`0`;
* Assuming we've already defined it for $`n`, define it for $`S(n)`.

Our third rule then guarantees that we've covered all numbers.
For example, let's define addition using this strategy.
Given a number $`x`, how are we going to add it to another number $`y`?
Let's apply the "that's it" rule to $`y`.

:::definition "addition" (parent := "definitions") (lean := "Nat.add") (uses := "natural_numbers")
We define *addition* $`x + y` by the following rules:
* $`x + 0` is defined to be $`x`;
* If we have already defined $`x + n`, then we define $`x + S(n)` to be $`S(x + n)`.
:::

The explanation of the second part of the definition is: if we already
know how to add $`n` to a number, then we can add the number after $`n` to it as well,
by first adding $`n`, and then taking the number after the result. Combined
with the fact that adding $`0` to a number is easy, we have just defined addition.

Multiplication $`x \times y` and exponentiation $`x^y` can be dealt with
in the same way:

:::definition "multiplication" (parent := "definitions") (lean := "Nat.mul") (uses := "natural_numbers, addition")
*Multiplication* $`x \times y` is defined
by the following rules:
* $`x \times 0` is defined to be $`0`;
* If we know $`x \times n`, we define $`x \times S(n)` to be $`(x \times n) + n`.
:::

:::definition "exponentiation" (parent := "definitions") (lean := "Nat.pow") (uses := "small_numbers, multiplication")
*Exponentiation* $`x^y` is defined by these rules:
* $`a ^ 0` is defined to be  $`1`;
* $`a ^ {S(n)}` is defined to be $`a ^ n \times a`.
:::

The last thing we need in this section is the concept of an inequality
between two natural numbers, which is a way of saying who was born first.

:::definition "leq" (parent := "definitions") (lean := "Nat.le")
We define $`x \leq y`
to mean that there exists a natural number $`a` such that {uses "addition"}[$`y = x + a`].
A natural number $`n` is called *positive* when
$`1 \leq n`.
:::

We are now ready to achieve the goal of this level, which is to state
Fermat's Last Theorem!

:::definition "Statement_B1_FLT" (parent := "definitions") (owner := "flt_author") (lean := "FLT.Bosses.B1")
Let $`a`, $`b` and $`c` be
{uses "leq"}[positive] natural numbers
and let $`n` be a natural number with {uses "small_numbers"}[$`3 \leq n`]. Then
{uses "addition"}[$`a ^ n + b ^ n`]$`\;\neq\;`{uses "exponentiation"}[$`c ^ n`].
:::

The moral of the story so far is that a rigorous statement of Fermat's Last
Theorem fits comfortably on one side of a sheet of paper, assuming nothing
more than the axioms of mathematics and the rules of logic. It is an
extraordinary fact that every proof of this statement known to humanity runs to
thousands of pages and involves developing many new definitions and results.
In the next level, we begin the proof of the theorem by making some
preliminary reductions.
