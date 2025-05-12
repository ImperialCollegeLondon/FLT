import Mathlib.GroupTheory.Torsion
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

/-!

# Bounds for the torsion of elliptic curves over the rationals.

Let `E` be an elliptic curve over the rational numbers. It is well-known
that the rational points `E(ℚ)` on the curve form a finitely-generated
abelian group, and thus `E(ℚ) ≃ ℤʳ × T` where `r` is the algebraic
rank of the curve and `T`, a finite group, is the torsion subgroup.

Our understanding of the possibilities for the algebraic rank `r` is
not at all complete. The Birch and Swinnerton-Dyer conjecture claims
that `r` is the order of vanishing of the L-function `L(E,s)` of `E`
at `s = 1` (the so-called analytic rank of the curve); this remains open.
It was certainly my impression in the 1990s that the general belief was
that `r` should be unbounded (I asked both Rubin and Bombieri this
question in 1995 and they both seemed to believe it), but since then
Poonen has given evidence that this might not be the case. Every now
and then a new elliptic curve is discovered which breaks the world
record for the highest known rank; at the time of writing, the current
record-holder is Elkies and Klagsbrun with a curve of algebraic rank
at least 29 (and modulo GRH, rank exactly 29).

However the status of the torsion subgroup `T` is very different;
it is completely understood. Indeed a 1977 theorem of Mazur, proving a 1908
conjecture of Beppo Levi, completely classifies which finite abelian groups
can occur as torsion subgroups of elliptic curves; they are the cyclic
groups of order `n` for `1 ≤ n ≤ 10` and `n = 12`, and the groups `ℤ/2ℤ × ℤ/nℤ` for
`n = 2, 4, 6, 8`. In particular the size of `T` is at most `16`. Every known
proof of Fermat's Last Theorem uses this result of Mazur.

Mazur's 154-page paper was a tour de force, using the full force of Grothendieck's
theory of schemes and the cohomology theories which had been introduced
by the Grothendieck school ten years earlier. Mazur performs a descent
on what he called the Eisenstein quotient of the Jacobian of a modular
curve of prime level; nowadays one can instead use the winding quotient
and invoke known partial results towards the Birch and Swinnerton-Dyer
conjecture by Bump--Friedberg--Hoffstein and Murty--Murty; this simplification
was crucial in Merel's 1995 extension of Mazur's results to elliptic curves
over general number fields.

Mazur's paper is

Mazur, Barry (1977). "Modular curves and the Eisenstein ideal".
Publications Mathématiques de l'IHÉS. 47 (1): 33–186. doi:10.1007/BF02684339.
MR 0488287. S2CID 122609075.

## Why do we need this?

Given a counterexample `x^p+y^p=z^p` to Fermat's Last Theorem, with `p ≥ 5`
a prime, the first step is to construct an elliptic curve `E` called the Frey
curve. It was observed by Frey that the p-torsion `E[p]` of `E` was a
Galois representation which was unramified away from `2` and `p`, and whose
ramification at `2` and `p` was also highly controlled. One way for this
to happen would be for the representation to be reducible (for example it
could be the sum of the trivial character and the mod `p` cyclotomic character).
However, Mazur's theorem rules this out; if the trivial representation were
a subrepresentation of `E[p]` then `E` would have a point of order `p ≥ 5`
and this, combined with the fact that the 2-torsion in the Frey curve
has size 4, would give us a torsion subgroup of size `4p > 16`, contradicting
Mazur's theorem.

More generally, Mazur's theorem and the fact that `E` is semistable can be
used to deduce that the Galois representation `E[p]` is irreducible, a hypothesis
which is crucial for applying the modularity lifting results in the proof that
we are formalizing in this project. Historically the irreducibility was used
in a different way; Wiles proved that the Frey curve was modular by arguing
at 3 and 5 rather than at p, and this was known to imply FLT by earlier work
of Ribet which relied on `E[p]` being irreducible. Our proof will avoid Ribet's
work completely by applying Wiles's techniques at `p` rather than at small primes.

## References

- [Barry Mazur, Modular curves and the Eisenstein ideal][mazur_torsion]

At the time of writing, the article is available here
https://www.numdam.org/item/?id=PMIHES_1977__47__33_0

The github tracking issue for this assumption is #477 on the FLT github repository.

-/

open scoped WeierstrassCurve.Affine -- E⟮ℚ⟯ notation

-- Implementation note: The `ncard` function used in the axiom returns the junk
-- value 0 if it is fed an infinite set, so the axiom as it stands actually
-- says "the size of the torsion subgroup is either at most 16, or infinite".
-- However it is well-known (and much much much easier than Mazur's theorem)
-- that the torsion subgroup is finite, so the axiom as stated will suffice
-- for the application to FLT.

/-- Mazur's bound for the size of the torsion subgroup of an elliptic curve
over the rationals . -/
axiom Mazur_statement (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    (AddCommGroup.torsion E⟮ℚ⟯ : Set E⟮ℚ⟯).ncard ≤ 16
