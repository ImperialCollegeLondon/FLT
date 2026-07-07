import Mathlib

#check Representation.ind


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


#check MulAut
def twistedRep' {k G : Type*} [CommRing k] [Group G] {H : Subgroup G} (L : Subgroup G)
    {V : Type*} [AddCommGroup V] [Module k V] (ρ : Representation k H V) (s : G) :
    Representation k ↥(H.comap (MulAut.conj s).toMonoidHom ⊓ L) V :=
  ρ.comp (((MulAut.conj s).toMonoidHom.subgroupComap H).comp (Subgroup.inclusion inf_le_left))


  /-- The Mackey direct sum `W = ⨁_{D ∈ φ(H)\G/χ(L)} Ind_{L_{σ(D)}}^L (V^{σ(D)})` as an
`L`-representation with componentwise action: `Representation.directSum` of the family of
induced twisted representations `D ↦ Representation.ind (L_{σ(D)}).subtype ρ^{σ(D)}`. -/
noncomputable def mackeyDirectSum {k G H L : Type*} [CommRing k] [Group G] [Group H]
    [Group L] {φ : H →* G} (hφ : Function.Injective φ) (χ : L →* G)
    {V : Type*} [AddCommGroup V] [Module k V] (ρ : Representation k H V)
    (σ : DoubleCoset.Quotient (↑φ.range : Set G) (↑χ.range : Set G) → G) :=
  letI fam : DoubleCoset.Quotient (↑φ.range : Set G) (↑χ.range : Set G) → Type _ :=
    fun D =>
      Representation.IndV
        (φ.range.comap ((MulAut.conj (σ D)).toMonoidHom.comp χ)).subtype
        (twistedRep hφ χ ρ (σ D))
  letI : (D : DoubleCoset.Quotient (↑φ.range : Set G) (↑χ.range : Set G)) →
      AddCommGroup (fam D) := fun _ => inferInstance
  letI : (D : DoubleCoset.Quotient (↑φ.range : Set G) (↑χ.range : Set G)) →
      Module k (fam D) := fun _ => inferInstance
  Representation.directSum (fun D =>
    Representation.ind
      (φ.range.comap ((MulAut.conj (σ D)).toMonoidHom.comp χ)).subtype
      (twistedRep hφ χ ρ (σ D)))

/-- Universal property of the presentation of the induced representation along a group
homomorphism `φ : H →* G`. Given a family of `k`-linear maps `f g : V →ₗ[k] W` indexed by
`g : G` satisfying the compatibility `f (φ h * g) ∘ ρ h = f g`, there is a unique `k`-linear
map `F̄ : Representation.IndV φ ρ →ₗ[k] W` with `F̄ [g, v] = f g v`. Conversely, for every
`k`-linear map `F̄`, the family `f g := F̄ ∘ [g, ·]` satisfies the compatibility. -/
theorem universal_property {k G H : Type*} [CommRing k] [Group G] [Group H] (φ : H →* G)
    {V : Type*} [AddCommGroup V] [Module k V] (ρ : Representation k H V)
    {W : Type*} [AddCommGroup W] [Module k W] (f : G → (V →ₗ[k] W))
    (hf : ∀ (h : H) (g : G), (f (φ h * g)) ∘ₗ (ρ h : V →ₗ[k] V) = f g) :
    (∃! F : Representation.IndV φ ρ →ₗ[k] W,
      ∀ (g : G) (v : V), F (Representation.IndV.mk φ ρ g v) = f g v) ∧
    (∀ (F : Representation.IndV φ ρ →ₗ[k] W) (h : H) (g : G),
      (F ∘ₗ Representation.IndV.mk φ ρ (φ h * g)) ∘ₗ (ρ h : V →ₗ[k] V)
        = F ∘ₗ Representation.IndV.mk φ ρ g) := sorry

/-- If the image of the injective homomorphism `κ : K →* G` has index `2` and the image of
`ι : J →* G` is not contained in it, then the double-coset space `κ(K)\G/ι(J)` is a
`Subsingleton` (it is inhabited, hence a singleton); equivalently `κ(K) ι(J) = G` (every
`g : G` factors as `g = κ x * ι y`). -/
theorem index_two_singleton {G K J : Type*} [Group G] [Group K] [Group J]
    (κ : K →* G) (ι : J →* G)
    (hκ : Function.Injective κ) (hι : Function.Injective ι)
    (hK : κ.range.index = 2) (hJ : ¬ ι.range ≤ κ.range) :
    Subsingleton (DoubleCoset.Quotient (↑κ.range : Set G) (↑ι.range : Set G)) ∧
    (∀ g : G, ∃ (x : K) (y : J), g = κ x * ι y) := sorry

/-- Stability of double cosets: if `g ∈ φ(H) s χ(L)`, then `φ(b) * g ∈ φ(H) s χ(L)` for all
`b : H`, and `g * χ(λ)⁻¹ ∈ φ(H) s χ(L)` for all `λ : L`. Here the double coset is
`DoubleCoset.doubleCoset s ↑φ.range ↑χ.range`. -/
theorem double_coset_closure {G H L : Type*} [Group G] [Group H] [Group L]
    (φ : H →* G) (χ : L →* G) (s g : G)
    (hg : g ∈ DoubleCoset.doubleCoset s (↑φ.range : Set G) (↑χ.range : Set G)) :
    (∀ b : H, φ b * g ∈ DoubleCoset.doubleCoset s (↑φ.range : Set G) (↑χ.range : Set G)) ∧
    (∀ l : L, g * (χ l)⁻¹ ∈ DoubleCoset.doubleCoset s (↑φ.range : Set G) (↑χ.range : Set G))
    := sorry

/-- The formula `ℓ • (φ(H)g) := φ(H)(g * χ(ℓ)⁻¹)` defines a left action of `L` on the set
`φ(H)\G` of right cosets of `φ.range`: there is a well-defined map on the right-coset
quotient sending `⟦g⟧ ↦ ⟦g * χ(ℓ)⁻¹⟧`, satisfying the two left-action axioms. -/
theorem L_action_cosets {G H L : Type*} [Group G] [Group H] [Group L]
    (φ : H →* G) (χ : L →* G) :
    ∃ act : L → Quotient (QuotientGroup.rightRel φ.range) →
        Quotient (QuotientGroup.rightRel φ.range),
      (∀ (ℓ : L) (g : G), act ℓ (Quotient.mk'' g) = Quotient.mk'' (g * (χ ℓ)⁻¹)) ∧
      (∀ x : Quotient (QuotientGroup.rightRel φ.range), act 1 x = x) ∧
      (∀ (ℓ ℓ' : L) (x : Quotient (QuotientGroup.rightRel φ.range)),
        act (ℓ * ℓ') x = act ℓ (act ℓ' x)) := sorry

/-- The twisted action is a representation with the prescribed values: for
`a ∈ L_s = φ.range.comap ((MulAut.conj s).toMonoidHom.comp χ)` and any `h : H` with
`φ h = s * χ a * s⁻¹`, the twisted representation `ρ^s = twistedRep hφ χ ρ s` (a `k`-linear
representation of `L_s` on `V` by its type) satisfies `ρ^s a = ρ h` as `k`-linear maps. -/
theorem twisted_rep {k G H L : Type*} [CommRing k] [Group G] [Group H] [Group L]
    {φ : H →* G} (hφ : Function.Injective φ) (χ : L →* G)
    {V : Type*} [AddCommGroup V] [Module k V] (ρ : Representation k H V) (s : G)
    (a : ↥(φ.range.comap ((MulAut.conj s).toMonoidHom.comp χ)))
    (h : H) (hh : φ h = s * χ (↑a : L) * s⁻¹) :
    twistedRep hφ χ ρ s a = ρ h := sorry

/-- Uniqueness of the `G`-action on the induced representation: any `k`-linear
`G`-representation `π` on `Representation.IndV φ ρ` satisfying `π x [g, v] = [g * x⁻¹, v]`
equals `Representation.ind φ ρ`. (The value formula for `Representation.ind` itself is
Mathlib's `Representation.ind_mk` and is not restated.) -/
theorem G_action {k G H : Type*} [CommRing k] [Group G] [Group H] (φ : H →* G)
    {V : Type*} [AddCommGroup V] [Module k V] (ρ : Representation k H V)
    (π : Representation k G (Representation.IndV φ ρ))
    (hπ : ∀ (x g : G) (v : V),
      π x (Representation.IndV.mk φ ρ g v)
        = Representation.IndV.mk φ ρ (g * x⁻¹) v) :
    π = Representation.ind φ ρ := sorry

/-- Existence and values of `Θ_s`. The presentation applies verbatim to the triple
`(L, L_s, ρ^s)`: the induced representation `Ind_{L_s}^L(V^s)` is
`Representation.IndV L_s.subtype (twistedRep hφ χ ρ s)` where
`L_s = φ.range.comap ((MulAut.conj s).toMonoidHom.comp χ)`. For each `s : G` there is a
unique `k`-linear map `Θ_s : Ind_{L_s}^L(V^s) →ₗ[k] Representation.IndV φ ρ` with
`Θ_s [ℓ, v]_s = [s * χ ℓ, v]`. -/
theorem theta_def {k G H L : Type*} [CommRing k] [Group G] [Group H] [Group L]
    {φ : H →* G} (hφ : Function.Injective φ) (χ : L →* G)
    {V : Type*} [AddCommGroup V] [Module k V] (ρ : Representation k H V) (s : G) :
    ∃! Θ : Representation.IndV
        (φ.range.comap ((MulAut.conj s).toMonoidHom.comp χ)).subtype
        (twistedRep hφ χ ρ s) →ₗ[k] Representation.IndV φ ρ,
      ∀ (l : L) (v : V),
        Θ (Representation.IndV.mk
            (φ.range.comap ((MulAut.conj s).toMonoidHom.comp χ)).subtype
            (twistedRep hφ χ ρ s) l v)
          = Representation.IndV.mk φ ρ (s * χ l) v := sorry

/-- The assembled comparison map `Θ : ⨁_{D} Ind_{L_{σ(D)}}^L (V^{σ(D)}) →ₗ[k] Ind_φ(V)`,
built by the universal property of the direct sum (`DirectSum.toModule`) with `D`-th
component the unique map `Θ_{σ(D)}` provided by `theta_def` (the witness of its
unique-existence statement), so `Θ (ι_D [ℓ, v]_{σ(D)}) = [σ(D) * χ ℓ, v]`. -/
noncomputable def thetaSum {k G H L : Type*} [CommRing k] [Group G] [Group H] [Group L]
    {φ : H →* G} (hφ : Function.Injective φ) (χ : L →* G)
    [DecidableEq (DoubleCoset.Quotient (↑φ.range : Set G) (↑χ.range : Set G))]
    {V : Type*} [AddCommGroup V] [Module k V] (ρ : Representation k H V)
    (σ : DoubleCoset.Quotient (↑φ.range : Set G) (↑χ.range : Set G) → G) :=
  letI fam : DoubleCoset.Quotient (↑φ.range : Set G) (↑χ.range : Set G) → Type _ :=
    fun D =>
      Representation.IndV
        (φ.range.comap ((MulAut.conj (σ D)).toMonoidHom.comp χ)).subtype
        (twistedRep hφ χ ρ (σ D))
  letI : (D : DoubleCoset.Quotient (↑φ.range : Set G) (↑χ.range : Set G)) →
      AddCommGroup (fam D) := fun _ => inferInstance
  letI : (D : DoubleCoset.Quotient (↑φ.range : Set G) (↑χ.range : Set G)) →
      Module k (fam D) := fun _ => inferInstance
  DirectSum.toModule k (DoubleCoset.Quotient (↑φ.range : Set G) (↑χ.range : Set G))
    (Representation.IndV φ ρ)
    (fun D => (theta_def hφ χ ρ (σ D)).choose)

/-- `L`-equivariance of `Θ_s`: any `k`-linear map `Θ : Ind_{L_s}^L(V^s) → Ind_φ(V)`
satisfying the value formula `Θ [ℓ, v]_s = [s * χ ℓ, v]` intertwines the `L`-action of
`Representation.ind L_s.subtype (twistedRep hφ χ ρ s)` on the source with the restricted
`L`-action `(Representation.ind φ ρ) (χ λ)` on the target. -/
theorem theta_equivariant {k G H L : Type*} [CommRing k] [Group G] [Group H] [Group L]
    {φ : H →* G} (hφ : Function.Injective φ) (χ : L →* G)
    {V : Type*} [AddCommGroup V] [Module k V] (ρ : Representation k H V) (s : G)
    (Θ : Representation.IndV
        (φ.range.comap ((MulAut.conj s).toMonoidHom.comp χ)).subtype
        (twistedRep hφ χ ρ s) →ₗ[k] Representation.IndV φ ρ)
    (hΘ : ∀ (l : L) (v : V),
      Θ (Representation.IndV.mk
          (φ.range.comap ((MulAut.conj s).toMonoidHom.comp χ)).subtype
          (twistedRep hφ χ ρ s) l v)
        = Representation.IndV.mk φ ρ (s * χ l) v) :
    ∀ lam : L,
      Θ ∘ₗ ((Representation.ind
          (φ.range.comap ((MulAut.conj s).toMonoidHom.comp χ)).subtype
          (twistedRep hφ χ ρ s)) lam)
        = ((Representation.ind φ ρ) (χ lam)) ∘ₗ Θ := sorry

/-- Independence lemma. Fix `s : G`. If `φ h * s * χ l = φ h' * s * χ l'` with `h h' : H`
and `l l' : L`, then for every `v : V`,
`[l, ρ(h)⁻¹ v]_s = [l', ρ(h')⁻¹ v]_s` in `Ind_{L_s}^L(V^s)` (with `ρ(h)⁻¹ = ρ(h⁻¹)`). -/
theorem independence {k G H L : Type*} [CommRing k] [Group G] [Group H] [Group L]
    {φ : H →* G} (hφ : Function.Injective φ) (χ : L →* G)
    {V : Type*} [AddCommGroup V] [Module k V] (ρ : Representation k H V) (s : G)
    (h h' : H) (l l' : L)
    (heq : φ h * s * χ l = φ h' * s * χ l') (v : V) :
    Representation.IndV.mk
        (φ.range.comap ((MulAut.conj s).toMonoidHom.comp χ)).subtype
        (twistedRep hφ χ ρ s) l (ρ h⁻¹ v)
      = Representation.IndV.mk
          (φ.range.comap ((MulAut.conj s).toMonoidHom.comp χ)).subtype
          (twistedRep hφ χ ρ s) l' (ρ h'⁻¹ v) := sorry

/-- Existence and values of the global inverse `Π`. Given a representative section `σ` of
the double-coset quotient (`hσ : DoubleCoset.mk φ.range χ.range (σ D) = D`), let
`W := ⨁_{D ∈ φ(H)\G/χ(L)} Ind_{L_{σ(D)}}^L (V^{σ(D)})` with inclusions
`ι_D = DirectSum.of _ D`. There is a unique `k`-linear map
`Π : Representation.IndV φ ρ →ₗ[k] W` such that for every `g : G`, every factorization
`g = φ h * σ(D_g) * χ l` (where `D_g = DoubleCoset.mk φ.range χ.range g`), and every
`v : V`, `Π [g, v] = ι_{D_g} [l, ρ(h)⁻¹ v]_{σ(D_g)}`. -/
theorem pi_def {k G H L : Type*} [CommRing k] [Group G] [Group H] [Group L]
    {φ : H →* G} (hφ : Function.Injective φ) (χ : L →* G)
    [DecidableEq (DoubleCoset.Quotient (↑φ.range : Set G) (↑χ.range : Set G))]
    {V : Type*} [AddCommGroup V] [Module k V] (ρ : Representation k H V)
    (σ : DoubleCoset.Quotient (↑φ.range : Set G) (↑χ.range : Set G) → G)
    (hσ : ∀ D, DoubleCoset.mk φ.range χ.range (σ D) = D) :
    letI fam : DoubleCoset.Quotient (↑φ.range : Set G) (↑χ.range : Set G) → Type _ :=
      fun D =>
        Representation.IndV
          (φ.range.comap ((MulAut.conj (σ D)).toMonoidHom.comp χ)).subtype
          (twistedRep hφ χ ρ (σ D))
    letI : (D : DoubleCoset.Quotient (↑φ.range : Set G) (↑χ.range : Set G)) →
        AddCommGroup (fam D) := fun D => inferInstance
    letI : (D : DoubleCoset.Quotient (↑φ.range : Set G) (↑χ.range : Set G)) →
        Module k (fam D) := fun D => inferInstance
    ∃! P : Representation.IndV φ ρ →ₗ[k]
        DirectSum (DoubleCoset.Quotient (↑φ.range : Set G) (↑χ.range : Set G)) fam,
      ∀ (g : G) (h : H) (l : L),
        g = φ h * σ (DoubleCoset.mk φ.range χ.range g) * χ l →
        ∀ v : V,
          P (Representation.IndV.mk φ ρ g v)
            = DirectSum.of fam (DoubleCoset.mk φ.range χ.range g)
                (Representation.IndV.mk
                  (φ.range.comap
                    ((MulAut.conj
                        (σ (DoubleCoset.mk φ.range χ.range g))).toMonoidHom.comp χ)).subtype
                  (twistedRep hφ χ ρ (σ (DoubleCoset.mk φ.range χ.range g)))
                  l (ρ h⁻¹ v)) := sorry


/-- The global inverse map `Π : Ind_φ(V) →ₗ[k] ⨁_{D} Ind_{L_{σ(D)}}^L (V^{σ(D)})`: the
unique map provided by `pi_def` (the witness of its unique-existence statement),
characterized by `Π [g, v] = ι_{D_g} [ℓ, ρ(h)⁻¹ v]_{σ(D_g)}` for every factorization
`g = φ h * σ(D_g) * χ ℓ`. -/
noncomputable def piMap {k G H L : Type*} [CommRing k] [Group G] [Group H] [Group L]
    {φ : H →* G} (hφ : Function.Injective φ) (χ : L →* G)
    [DecidableEq (DoubleCoset.Quotient (↑φ.range : Set G) (↑χ.range : Set G))]
    {V : Type*} [AddCommGroup V] [Module k V] (ρ : Representation k H V)
    (σ : DoubleCoset.Quotient (↑φ.range : Set G) (↑χ.range : Set G) → G)
    (hσ : ∀ D, DoubleCoset.mk φ.range χ.range (σ D) = D) :=
  (pi_def hφ χ ρ σ hσ).choose


/-- `Π ∘ Θ = id_W`: the global inverse `piMap` is a left inverse of the assembled
comparison map `thetaSum`. -/
theorem pi_theta {k G H L : Type*} [CommRing k] [Group G] [Group H] [Group L]
    {φ : H →* G} (hφ : Function.Injective φ) (χ : L →* G)
    [DecidableEq (DoubleCoset.Quotient (↑φ.range : Set G) (↑χ.range : Set G))]
    {V : Type*} [AddCommGroup V] [Module k V] (ρ : Representation k H V)
    (σ : DoubleCoset.Quotient (↑φ.range : Set G) (↑χ.range : Set G) → G)
    (hσ : ∀ D, DoubleCoset.mk φ.range χ.range (σ D) = D) :
    Function.LeftInverse ⇑(piMap hφ χ ρ σ hσ) ⇑(thetaSum hφ χ ρ σ) := sorry


/-- `Θ ∘ Π = id` on `Ind_φ(V)`: the global inverse `piMap` is a right inverse of the
assembled comparison map `thetaSum`. -/
theorem theta_pi {k G H L : Type*} [CommRing k] [Group G] [Group H] [Group L]
    {φ : H →* G} (hφ : Function.Injective φ) (χ : L →* G)
    [DecidableEq (DoubleCoset.Quotient (↑φ.range : Set G) (↑χ.range : Set G))]
    {V : Type*} [AddCommGroup V] [Module k V] (ρ : Representation k H V)
    (σ : DoubleCoset.Quotient (↑φ.range : Set G) (↑χ.range : Set G) → G)
    (hσ : ∀ D, DoubleCoset.mk φ.range χ.range (σ D) = D) :
    Function.RightInverse ⇑(piMap hφ χ ρ σ hσ) ⇑(thetaSum hφ χ ρ σ) := sorry

/-- Mackey's restriction formula: for injective `φ : H →* G`, `χ : L →* G` and a
representative section `σ` of the double-coset quotient, the assembled comparison map
`Θ = thetaSum` from the Mackey direct sum `W = mackeyDirectSum` to `Res_χ Ind_φ(V)` is an
isomorphism of `L`-representations with inverse `Π = piMap`: (i) `Θ` is `L`-equivariant;
(ii) `Π` is a left inverse of `Θ`; (iii) `Π` is a right inverse of `Θ`; (iv) `Θ` is
bijective. -/
theorem mackey {k G H L : Type*} [CommRing k] [Group G] [Group H] [Group L]
    {φ : H →* G} (hφ : Function.Injective φ) (χ : L →* G)
    [DecidableEq (DoubleCoset.Quotient (↑φ.range : Set G) (↑χ.range : Set G))]
    {V : Type*} [AddCommGroup V] [Module k V] (ρ : Representation k H V)
    (σ : DoubleCoset.Quotient (↑φ.range : Set G) (↑χ.range : Set G) → G)
    (hσ : ∀ D, DoubleCoset.mk φ.range χ.range (σ D) = D) :
    (∀ (lam : L) w,
      thetaSum hφ χ ρ σ (mackeyDirectSum hφ χ ρ σ lam w)
        = (Representation.ind φ ρ) (χ lam) (thetaSum hφ χ ρ σ w)) ∧
    Function.LeftInverse ⇑(piMap hφ χ ρ σ hσ) ⇑(thetaSum hφ χ ρ σ) ∧
    Function.RightInverse ⇑(piMap hφ χ ρ σ hσ) ⇑(thetaSum hφ χ ρ σ) ∧
    Function.Bijective ⇑(thetaSum hφ χ ρ σ) := sorry

/-- Index-two Mackey corollary, general coefficients, for injective homomorphisms
`κ : K →* G` and `ι : J →* G`. If `κ.range` has index `2`, `ι.range` is not contained in
`κ.range`, and `ρV` is any `k`-linear representation of `K` on `V`, then with
`P := κ.range.comap ι` (the pullback of `κ(K)` along `ι`, playing the role of `K ∩ J`) and
`r : ↥P →* K` the homomorphism with `κ (r a) = ι a` (assembled from
`MonoidHom.subgroupComap` and `MonoidHom.ofInjective`), there is an isomorphism of
`J`-representations `Res_ι Ind_κ(V) ≅ Ind_P^J (ρV ∘ r)` (a `Representation.Equiv`). -/
theorem index_two {k G K J : Type*} [CommRing k] [Group G] [Group K] [Group J]
    {κ : K →* G} (hκ : Function.Injective κ) (ι : J →* G)
    (hK : κ.range.index = 2) (hJ : ¬ ι.range ≤ κ.range)
    {V : Type*} [AddCommGroup V] [Module k V] (ρV : Representation k K V) :
    Nonempty (Representation.Equiv
      ((Representation.ind κ ρV).comp ι :
        Representation k J (Representation.IndV κ ρV))
      (Representation.ind (κ.range.comap ι).subtype
        (ρV.comp
          ((MonoidHom.ofInjective hκ).symm.toMonoidHom.comp (ι.subgroupComap κ.range)) :
          Representation k ↥(κ.range.comap ι) V))) := sorry


/-- Index-two Mackey corollary, rank-one form (rephrased in terms of representations: the
source's character `ψ : K →* kˣ` is replaced by an arbitrary `k`-linear representation
`ρψ` of `K` on the module `k` itself). If `κ : K →* G` is injective with `κ.range` of index
`2`, `ι : J →* G` injective with `ι.range` not contained in `κ.range`, then with
`P := κ.range.comap ι` and `r : ↥P →* K` as in `index_two`, there is an isomorphism of
`J`-representations `Res_ι Ind_κ(ρψ) ≅ Ind_P^J (ρψ ∘ r)` (a `Representation.Equiv`). -/
theorem index_two_character {k G K J : Type*} [CommRing k] [Group G] [Group K] [Group J]
    {κ : K →* G} (hκ : Function.Injective κ) (ι : J →* G)
    (hK : κ.range.index = 2) (hJ : ¬ ι.range ≤ κ.range)
    (ρψ : Representation k K k) :
    Nonempty (Representation.Equiv
      ((Representation.ind κ ρψ).comp ι :
        Representation k J (Representation.IndV κ ρψ))
      (Representation.ind (κ.range.comap ι).subtype
        (ρψ.comp
          ((MonoidHom.ofInjective hκ).symm.toMonoidHom.comp (ι.subgroupComap κ.range)) :
          Representation k ↥(κ.range.comap ι) k))) := sorry

/-
/- Mackey's restriction formula for injective homomorphisms `φ : H →* G`, `χ : L →* G`:
the map `Θ : ⨁_{D ∈ φ(H)\G/χ(L)} Ind_{L_{σ(D)}}^L (V^{σ(D)}) → Res_χ Ind_φ(V)` — assembled
by the universal property of the direct sum (`DirectSum.toModule`) from the unique maps
`Θ_{σ(D)}` of `theta_def` — is an isomorphism of `L`-representations with inverse the
unique map `Π` of `pi_def`: (i) `Θ` intertwines the componentwise `L`-action of the
summand representations with the restricted `L`-action `(Representation.ind φ ρ) (χ λ)`;
(ii) `Π ∘ Θ = id`; (iii) `Θ ∘ Π = id`; (iv) hence there is an equivalence of
representations (`Representation.Equiv`) with underlying map `Θ`. -/
theorem mackey' {k G H L : Type*} [CommRing k] [Group G] [Group H] [Group L]
    {φ : H →* G} (hφ : Function.Injective φ) (χ : L →* G)
    [DecidableEq (DoubleCoset.Quotient (↑φ.range : Set G) (↑χ.range : Set G))]
    {V : Type*} [AddCommGroup V] [Module k V] (ρ : Representation k H V)
    (c : Choices φ χ) :
    letI fam : DoubleCoset.Quotient (↑φ.range : Set G) (↑χ.range : Set G) → Type _ :=
      fun D =>
        Representation.IndV
          (φ.range.comap ((MulAut.conj (c.σ D)).toMonoidHom.comp χ)).subtype
          (twistedRep hφ χ ρ (c.σ D))
    letI : (D : DoubleCoset.Quotient (↑φ.range : Set G) (↑χ.range : Set G)) →
        AddCommGroup (fam D) := fun D => inferInstance
    letI : (D : DoubleCoset.Quotient (↑φ.range : Set G) (↑χ.range : Set G)) →
        Module k (fam D) := fun D => inferInstance
    (∀ lam : L,
      DirectSum.toModule k (DoubleCoset.Quotient (↑φ.range : Set G) (↑χ.range : Set G))
          (Representation.IndV φ ρ)
          (fun D => (theta_def hφ χ ρ (c.σ D)).choose) ∘ₗ
        ((Representation.directSum (fun D =>
            Representation.ind
              (φ.range.comap ((MulAut.conj (c.σ D)).toMonoidHom.comp χ)).subtype
              (twistedRep hφ χ ρ (c.σ D)))) lam)
        = ((Representation.ind φ ρ) (χ lam)) ∘ₗ
            DirectSum.toModule k
              (DoubleCoset.Quotient (↑φ.range : Set G) (↑χ.range : Set G))
              (Representation.IndV φ ρ)
              (fun D => (theta_def hφ χ ρ (c.σ D)).choose)) ∧
    ((pi_def hφ χ ρ c).choose ∘ₗ
        DirectSum.toModule k (DoubleCoset.Quotient (↑φ.range : Set G) (↑χ.range : Set G))
          (Representation.IndV φ ρ)
          (fun D => (theta_def hφ χ ρ (c.σ D)).choose)
      = LinearMap.id) ∧
    (DirectSum.toModule k (DoubleCoset.Quotient (↑φ.range : Set G) (↑χ.range : Set G))
        (Representation.IndV φ ρ)
        (fun D => (theta_def hφ χ ρ (c.σ D)).choose) ∘ₗ
      (pi_def hφ χ ρ c).choose
      = LinearMap.id) ∧
    (Function.Bijective
      ⇑(DirectSum.toModule k (DoubleCoset.Quotient (↑φ.range : Set G) (↑χ.range : Set G))
          (Representation.IndV φ ρ)
          (fun D => (theta_def hφ χ ρ (c.σ D)).choose))) := sorry
-/
