import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing

variable (K : Type*) [Field K] [NumberField K]

open NumberField

open IsDedekindDomain

noncomputable instance : MeasurableSpace (FiniteAdeleRing (𝓞 K) K) := borel _

instance : BorelSpace (FiniteAdeleRing (𝓞 K) K) := ⟨rfl⟩
