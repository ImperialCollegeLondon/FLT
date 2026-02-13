-- can't upstream because this first import imports too much
import FLT.Mathlib.NumberTheory.NumberField.FiniteAdeleRing
import FLT.Mathlib.NumberTheory.NumberField.InfiniteAdeleRing

/-!

# Topological facts about adele rings

This should be enough to deduce that they're Polish.

-/
variable {K : Type*} [Field K]

namespace NumberField.AdeleRing

variable {R : Type*} [CommRing R] [IsDedekindDomain R] [Algebra R K] [IsFractionRing R K]
  (x y : AdeleRing R K)

@[simp] lemma add_fst (x y : AdeleRing R K) : (x + y).1 = x.1 + y.1 := rfl
@[simp] lemma add_snd (x y : AdeleRing R K) : (x + y).2 = x.2 + y.2 := rfl

@[simp] lemma mul_fst (x y : AdeleRing R K) : (x * y).1 = x.1 * y.1 := rfl
@[simp] lemma mul_snd (x y : AdeleRing R K) : (x * y).2 = x.2 * y.2 := rfl

@[simp] lemma zero_fst : (0 : AdeleRing R K).1 = 0 := rfl
@[simp] lemma zero_snd : (0 : AdeleRing R K).2 = 0 := rfl

@[simp] lemma one_fst : (1 : AdeleRing R K).1 = 1 := rfl
@[simp] lemma one_snd : (1 : AdeleRing R K).2 = 1 := rfl

variable [NumberField K]

section topology_stuff

open IsDedekindDomain.HeightOneSpectrum in
instance locallyCompactSpace : LocallyCompactSpace (AdeleRing (𝓞 K) K) :=
  inferInstanceAs <| LocallyCompactSpace (_ × _)

instance : T2Space (AdeleRing (𝓞 K) K) :=
  inferInstanceAs <| T2Space (_ × _)

instance : SecondCountableTopology (AdeleRing (𝓞 K) K) :=
  inferInstanceAs <| SecondCountableTopology (_ × _)

end topology_stuff

end NumberField.AdeleRing
