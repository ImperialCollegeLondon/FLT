import Mathlib

/-- The twisted representation `ρ^s` attached to `s : G`, in the setting of injective
homomorphisms `φ : H →* G`, `χ : L →* G`. The subgroup is
`L_s = φ.range.comap ((MulAut.conj s).toMonoidHom.comp χ) ≤ L`, i.e.
`{a : L | s * χ a * s⁻¹ ∈ φ(H)}` (for subgroup inclusions this is the source's
`H_s = s⁻¹Hs ⊓ L`), and `ρ^s` is `ρ` composed with the homomorphism `L_s →* H` sending `a`
to the unique `h : H` with `φ h = s * χ a * s⁻¹` — `MonoidHom.subgroupComap` followed by
`(MonoidHom.ofInjective hφ).symm`. Its type `Representation k ↥L_s V` carries the fact that
it is a `k`-linear representation of `L_s` on `V` (the module `V` with this action is
`V^s`). -/
noncomputable def twistedRep {k G H L : Type*} [CommRing k] [Group G] [Group H] [Group L]
    {φ : H →* G} (hφ : Function.Injective φ) (χ : L →* G)
    {V : Type*} [AddCommGroup V] [Module k V] (ρ : Representation k H V) (s : G) :
    Representation k ↥(φ.range.comap ((MulAut.conj s).toMonoidHom.comp χ)) V :=
  ρ.comp
    ((MonoidHom.ofInjective hφ).symm.toMonoidHom.comp
      (((MulAut.conj s).toMonoidHom.comp χ).subgroupComap φ.range))
