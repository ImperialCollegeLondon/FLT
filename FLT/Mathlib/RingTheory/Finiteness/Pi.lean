import Mathlib.RingTheory.Finiteness.Basic

-- Converse to `Module.Finite.pi`
theorem Module.Finite.of_pi {R : Type*} [Semiring R] {ι : Type*} (M : ι → Type*)
    [(i : ι) → AddCommMonoid (M i)] [(i : ι) → Module R (M i)]
    [Module.Finite R ((i : ι) → M i)] (i : ι) : Module.Finite R (M i) :=
  Module.Finite.of_surjective _ <| LinearMap.proj_surjective i
