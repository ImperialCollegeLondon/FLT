import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
import Mathlib.NumberTheory.NumberField.Basic

universe u v

def AdeleRing (R : Type u) [CommRing R] [IsDedekindDomain R]
    (K : Type v) [Field K] [NumberField K]
    [Algebra R K] [IsFractionRing R K]  : Type (max u v) := sorry
