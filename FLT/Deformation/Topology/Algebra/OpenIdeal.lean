import Mathlib

variable (A : Type*) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]

def OpenIdeal := {a : Ideal A // IsOpen a.carrier}

instance : CoeOut (OpenIdeal A) (Ideal A) where
  coe a := a.1

instance : Min (OpenIdeal A) where
  min a b := ⟨
    a.1 ⊓ b.1,
    IsOpen.inter a.2 b.2
  ⟩
