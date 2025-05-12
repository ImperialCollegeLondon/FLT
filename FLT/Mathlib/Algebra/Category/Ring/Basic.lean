import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.RingTheory.Ideal.Quotient.Defs

open CategoryTheory

section CommRingCat

def CommRingCat.quotient {A : CommRingCat} (a : Ideal A) : CommRingCat := of (A ⧸ a)

end CommRingCat
