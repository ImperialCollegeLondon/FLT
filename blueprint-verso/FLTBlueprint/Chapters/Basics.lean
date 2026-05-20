import Verso
import VersoManual
import VersoBlueprint

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Basics" =>

This placeholder chapter exists so the FLT Verso blueprint has rendered content
while the real material is still being chosen.

:::group "basics_core"
Placeholder arithmetic facts for the FLT Verso blueprint.
:::

:::author "flt_author" (name := "FLT Project")
:::

:::definition "addition_spec" (parent := "basics_core")
We write $`a + b` for the sum of the natural numbers $`a` and $`b`.
:::

:::theorem "two_plus_two" (parent := "basics_core") (owner := "flt_author") (tags := "placeholder")
We have $`2 + 2 = 4`.
:::

:::proof "two_plus_two"
Obvious: the claim is a direct computation with {uses "addition_spec"}[].
:::

```lean "two_plus_two"
theorem two_plus_two : 2 + 2 = 4 := by rfl
```
