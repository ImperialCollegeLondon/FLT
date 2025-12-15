import FLT.NumberField.FiniteAdeleRing
import FLT.NumberField.InfiniteAdeleRing

/-!

# Topological facts about adele rings

This should be enough to deduce that they're Polish.

-/
variable (K : Type*) [Field K] [NumberField K]

open NumberField

section topology_stuff

open IsDedekindDomain.HeightOneSpectrum in
instance NumberField.AdeleRing.locallyCompactSpace : LocallyCompactSpace (AdeleRing (𝓞 K) K) :=
  inferInstanceAs <| LocallyCompactSpace (_ × _)

instance : T2Space (AdeleRing (𝓞 K) K) :=
  inferInstanceAs <| T2Space (_ × _)

instance : SecondCountableTopology (AdeleRing (𝓞 K) K) :=
  inferInstanceAs <| SecondCountableTopology (_ × _)

end topology_stuff
