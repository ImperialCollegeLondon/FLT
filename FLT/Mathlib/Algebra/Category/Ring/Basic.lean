import Mathlib
import FLT.Mathlib.CategoryTheory.Comma.Over

open CategoryTheory

section CommRingCat

def CommRingCat.quotient {A : CommRingCat} (a : Ideal A) : CommRingCat := of (A ⧸ a)

end CommRingCat

