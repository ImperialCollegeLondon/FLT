import Mathlib

/-!
# Mackey's restriction–induction formula — readable statement skeleton

This file restates `Mackey.lean` in a form meant to be *checked by a human* against the
informal lemmas, and now also **proves every statement** (the file is `sorry`-free).
The statement layer is organised for auditability: a small fixed vocabulary of
definitions, each with a definitional (`rfl`) or derived characterisation lemma, and one
theorem per informal lemma.

## Setting

`G` is a group with subgroups `H L : Subgroup G`. The original file's injective
homomorphisms `φ : H →* G`, `χ : L →* G` are replaced by the subgroup inclusions
`H.subtype`, `L.subtype`; this removes every `Function.Injective` hypothesis and every use
of `MonoidHom.ofInjective`. `k` is a commutative ring and `ρ : Representation k H V`.

## Mathlib's induced representation (conventions)

For a group hom `φ : Γ →* Δ` and `τ : Representation k Γ V`, mathlib defines
`Representation.IndV φ τ` (the module) and `Representation.ind φ τ` (the `Δ`-action).
Writing `[g, v]` for `IndV.mk φ τ g v` (`g : Δ`, `v : V`):

* defining relation: `[φ h * g, τ h v] = [g, v]` (so classes are indexed by *right* cosets);
* action: `x • [g, v] = [g * x⁻¹, v]` (`Representation.ind_mk`).

## Dictionary

For a fixed `s : G`, and `D` ranging over the double cosets `H\G/L`:

* `L_s = s⁻¹Hs ⊓ L`, as a subgroup of `L`      ↝ `Mackey.inter H L s : Subgroup L`
* `ρ^s : L_s → GL(V)`, `ρ^s(a) = ρ(s a s⁻¹)`   ↝ `Mackey.twisted H L ρ s`
* the module `Ind_{L_s}^L (V^s)`               ↝ `Mackey.TwistedIndV H L ρ s`
* its generators `[l, v]` (`l ∈ L`)            ↝ `Mackey.twistedMk H L ρ s l v`
* the `L`-action on it                         ↝ `Mackey.indTwisted H L ρ s`
* the double-coset space `H\G/L`               ↝ `Mackey.Cosets H L`
* a chosen representative `s_D` of `D`         ↝ `D.out` (see `DoubleCoset.out_eq'`)
* `W = ⨁_D Ind_{L_{s_D}}^L (V^{s_D})`          ↝ `⨁ D, Mackey.Summand H L ρ D`,
  with `L`-action `Mackey.mackeySum H L ρ`
* `Res_L Ind_H^G (V, ρ)`                       ↝ `Mackey.resInd H L ρ`

**Main statement** (`Mackey.mackey`): there is an equivalence of `L`-representations
`e : ⨁_D Ind_{L_{s_D}}^L (V^{s_D}) ≃ Res_L Ind_H^G V` with `e (ι_D [l, v]) = [s_D * l, v]`.

**Pen-and-paper form** (`Mackey.mackey_equiv`): the same equivalence for an *arbitrary*
choice of representatives `σ`, with no map named. `index_two` is proved from it
(choose `σ D = 1` once `K\G/J` is a singleton), together with the glue equivalences
`directSum_unique_equiv` and `indTwisted_one`.

## Correspondence with `Mackey.lean`

| `Mackey.lean` | here | change |
| --- | --- | --- |
| `twistedRep` | `twisted` | explicit, computable; no `hφ`, no `ofInjective` |
| `twisted_rep` (sorried) | `twisted_apply` | now true by `rfl` |
| `mackeyDirectSum` | `mackeySum` | no `letI` block, no section `σ` |
| `universal_property` | `existsUnique_indLift`, `indV_mk_eq` | conjunction split; converse half restated on generators (it was the `F = id` case quantified over all `F`) |
| `index_two_singleton` | `subsingleton_cosets_of_index_two`, `exists_mul_eq_of_index_two` | conjunction split |
| `double_coset_closure` | `mul_mem_doubleCoset`, `mul_inv_mem_doubleCoset` | conjunction split |
| `L_action_cosets` | `exists_rightCosetAction` | action packaged as `L →* Equiv.Perm _` |
| `G_action` | `ind_ext` | |
| `theta_def` | `existsUnique_theta` | |
| `thetaSum` | `theta` | value lemma `theta_of` is proved, not sorried |
| `theta_equivariant` | `theta_component_equivariant` | |
| `independence` | `independence` | |
| `pi_def` | `existsUnique_pi` | no `letI`, no `(σ, hσ)` |
| `piMap` | `pi` | value lemma `pi_mk` is proved, not sorried |
| `pi_theta` / `theta_pi` | `pi_comp_theta` / `theta_comp_pi` | as `LinearMap` equalities |
| `mackey` | `theta_intertwines` + `mackey` | final form: a `Representation.Equiv` with prescribed values (bijectivity conjunct subsumed) |
| `index_two`, `index_two_character` | same names | now both *proved*; `P = K ⊓ J` |

Everywhere, the section `σ : H\G/L → G` with `hσ : ∀ D, ⟦σ D⟧ = D` is replaced by the
canonical representative `Quotient.out`, so those two arguments disappear from every
signature — except in `mackey_equiv`, whose pen-and-paper statement deliberately
quantifies over all representative systems (that generality is what `index_two` uses).
-/

open Representation DirectSum

namespace Mackey

variable {k G : Type*} [CommRing k] [Group G] (H L : Subgroup G)
    {V : Type*} [AddCommGroup V] [Module k V] (ρ : Representation k H V)

/-! ## The twisted representation `ρ^s` -/

/-- `L_s`: the subgroup of `L` of elements `a` with `s * a * s⁻¹ ∈ H`. Informally
`L_s = s⁻¹Hs ⊓ L`, here packaged as a subgroup of `L`. -/
def inter (s : G) : Subgroup L := (H.comap (MulAut.conj s).toMonoidHom).subgroupOf L

@[simp]
lemma mem_inter {s : G} {a : L} : a ∈ inter H L s ↔ s * (a : G) * s⁻¹ ∈ H := Iff.rfl

/-- The twisted representation `ρ^s` of `L_s` on `V`: `a ∈ L_s` acts by `ρ (s * a * s⁻¹)`.
(Was `twistedRep`; now with no injectivity hypothesis and no use of choice.) -/
def twisted (s : G) : Representation k (inter H L s) V :=
  ρ.comp (((MulAut.conj s).toMonoidHom.subgroupComap H).comp
    (L.subtype.subgroupComap (H.comap (MulAut.conj s).toMonoidHom)))

/-- `ρ^s a = ρ (s * a * s⁻¹)`, definitionally. (Was the sorried `twisted_rep`.) -/
@[simp]
lemma twisted_apply (s : G) (a : inter H L s) :
    twisted H L ρ s a = ρ ⟨s * ((a : L) : G) * s⁻¹, a.2⟩ := rfl

/-! ## Double cosets, the Mackey direct sum, the restricted induced representation -/

/-- The double-coset space `H\G/L`. -/
abbrev Cosets := DoubleCoset.Quotient (H : Set G) (L : Set G)

/-- The `k`-module `Ind_{L_s}^L (V^s)`. -/
abbrev TwistedIndV (s : G) : Type _ :=
  IndV (inter H L s).subtype (twisted H L ρ s)

/-- The generator `[l, v]` of `Ind_{L_s}^L (V^s)`, for `l : L`, `v : V`. -/
noncomputable abbrev twistedMk (s : G) (l : L) : V →ₗ[k] TwistedIndV H L ρ s :=
  IndV.mk (inter H L s).subtype (twisted H L ρ s) l

/-- The `L`-representation `Ind_{L_s}^L (ρ^s)` on `TwistedIndV H L ρ s`. -/
noncomputable abbrev indTwisted (s : G) : Representation k L (TwistedIndV H L ρ s) :=
  ind (inter H L s).subtype (twisted H L ρ s)

/-- The summand of the Mackey direct sum at `D ∈ H\G/L`: `Ind_{L_{s_D}}^L (V^{s_D})` for
the canonical representative `s_D = D.out`. -/
abbrev Summand (D : Cosets H L) : Type _ := TwistedIndV H L ρ D.out

/- Registering the module structure on the summands once, so that the direct sum
elaborates without the `letI` blocks of the original file. -/
noncomputable instance (s : G) : AddCommGroup (TwistedIndV H L ρ s) :=
  inferInstanceAs (AddCommGroup (IndV (inter H L s).subtype (twisted H L ρ s)))

noncomputable instance (s : G) : Module k (TwistedIndV H L ρ s) :=
  inferInstanceAs (Module k (IndV (inter H L s).subtype (twisted H L ρ s)))

/-- The Mackey direct sum `W = ⨁_{D ∈ H\G/L} Ind_{L_{s_D}}^L (V^{s_D})` as an
`L`-representation acting componentwise. (Was `mackeyDirectSum`.) -/
noncomputable def mackeySum : Representation k L (⨁ D, Summand H L ρ D) :=
  directSum fun D => indTwisted H L ρ D.out

/-- The restriction to `L` of the induced representation: `Res_L (Ind_H^G ρ)`. -/
noncomputable def resInd : Representation k L (IndV H.subtype ρ) :=
  (ind H.subtype ρ).comp L.subtype

/-! ## Universal property of the induced representation (arbitrary `φ`) -/

section UniversalProperty

variable {Γ Δ : Type*} [Group Γ] [Group Δ] (φ : Γ →* Δ) (τ : Representation k Γ V)
    {W : Type*} [AddCommGroup W] [Module k W]

/-- Defining relation of `Ind_φ V` on generators: `[φ h * g, τ h v] = [g, v]`.
(Was the second half of `universal_property`, there stated as
`(F ∘ mk (φ h * g)) ∘ τ h = F ∘ mk g` for every linear `F`; this is the `F = id` case,
which implies the general one.) -/
theorem indV_mk_eq (h : Γ) (g : Δ) (v : V) :
    IndV.mk φ τ (φ h * g) (τ h v) = IndV.mk φ τ g v := by
  have key := Coinvariants.mk_self_apply
    (ρ := Representation.tprod ((leftRegular k Δ).comp φ) τ) h
    (Finsupp.single g (1 : k) ⊗ₜ[k] v)
  simpa [Representation.tprod_apply, leftRegular, ofMulAction_single] using key

/-- Universal property of `Ind_φ V` (was the first half of `universal_property`): a family
of maps `f g : V →ₗ[k] W` (`g : Δ`) satisfying `f (φ h * g) ∘ τ h = f g` factors uniquely
through `Ind_φ V`, via `F [g, v] = f g v`. -/
theorem existsUnique_indLift (f : Δ → V →ₗ[k] W)
    (hf : ∀ (h : Γ) (g : Δ), f (φ h * g) ∘ₗ (τ h : V →ₗ[k] V) = f g) :
    ∃! F : IndV φ τ →ₗ[k] W, ∀ (g : Δ) (v : V), F (IndV.mk φ τ g v) = f g v := by
  refine ⟨Coinvariants.lift _ (TensorProduct.lift (Finsupp.lift (V →ₗ[k] W) k Δ f)) ?_,
    fun g v => ?_, fun F' hF' => ?_⟩
  · intro x
    ext g v
    simpa [Representation.tprod_apply, leftRegular, ofMulAction_single] using
      LinearMap.congr_fun (hf x g) v
  · simp [IndV.mk]
  · refine IndV.hom_ext _ _ fun g => LinearMap.ext fun v => ?_
    simpa [IndV.mk] using hF' g v

/-- Uniqueness of the `Δ`-action on `Ind_φ V` (was `G_action`): a representation `π` on the
module `Ind_φ V` satisfying `π x [g, v] = [g * x⁻¹, v]` is `Representation.ind φ τ`. -/
theorem ind_ext (π : Representation k Δ (IndV φ τ))
    (hπ : ∀ (x g : Δ) (v : V), π x (IndV.mk φ τ g v) = IndV.mk φ τ (g * x⁻¹) v) :
    π = ind φ τ := by
  refine MonoidHom.ext fun x => IndV.hom_ext _ _ fun g => LinearMap.ext fun v => ?_
  change π x (IndV.mk φ τ g v) = ind φ τ x (IndV.mk φ τ g v)
  rw [hπ x g v, ind_mk]

end UniversalProperty

/-! ## Double-coset lemmas -/

/-- (Was half of `double_coset_closure`.) The double coset `HsL` is stable under left
multiplication by elements of `H`. -/
theorem mul_mem_doubleCoset {s g : G}
    (hg : g ∈ DoubleCoset.doubleCoset s (H : Set G) (L : Set G)) (b : H) :
    (b : G) * g ∈ DoubleCoset.doubleCoset s (H : Set G) (L : Set G) := by
  obtain ⟨x, hx, y, hy, rfl⟩ := DoubleCoset.mem_doubleCoset.1 hg
  exact DoubleCoset.mem_doubleCoset.2 ⟨(b : G) * x, H.mul_mem b.2 hx, y, hy, by group⟩

/-- (Was half of `double_coset_closure`.) The double coset `HsL` is stable under right
multiplication by inverses of elements of `L`. -/
theorem mul_inv_mem_doubleCoset {s g : G}
    (hg : g ∈ DoubleCoset.doubleCoset s (H : Set G) (L : Set G)) (l : L) :
    g * (l : G)⁻¹ ∈ DoubleCoset.doubleCoset s (H : Set G) (L : Set G) := by
  obtain ⟨x, hx, y, hy, rfl⟩ := DoubleCoset.mem_doubleCoset.1 hg
  exact DoubleCoset.mem_doubleCoset.2
    ⟨x, hx, y * (l : G)⁻¹, L.mul_mem hy (L.inv_mem l.2), by group⟩

/-- (Was `L_action_cosets`.) `ℓ • Hg := H(gℓ⁻¹)` is a well-defined left action of `L` on
the right-coset space `H\G`, here packaged as a homomorphism into the permutation group
(which encodes the two action axioms). -/
theorem exists_rightCosetAction :
    ∃ act : L →* Equiv.Perm (Quotient (QuotientGroup.rightRel H)),
      ∀ (l : L) (g : G), act l (Quotient.mk _ g) = Quotient.mk _ (g * (l : G)⁻¹) := by
  have hrel : ∀ (a x y : G), QuotientGroup.rightRel H x y →
      QuotientGroup.rightRel H (x * a) (y * a) := by
    intro a x y hxy
    rw [QuotientGroup.rightRel_apply] at hxy ⊢
    simpa [mul_assoc] using hxy
  refine ⟨MonoidHom.mk' (fun l =>
      ⟨Quotient.map' (· * (l : G)⁻¹) (hrel _),
       Quotient.map' (· * (l : G)) (hrel _),
       fun q => Quotient.inductionOn' q fun g => by simp [Quotient.map'_mk''],
       fun q => Quotient.inductionOn' q fun g => by simp [Quotient.map'_mk'']⟩)
    ?_, fun l g => rfl⟩
  intro l₁ l₂
  ext q
  induction q using Quotient.inductionOn' with
  | _ g => simp [Quotient.map'_mk'', mul_assoc]

/-- (Was half of `index_two_singleton`.) If `K` has index `2` and `J ≰ K` then `KJ = G`:
every `g : G` factors as `g = x * y` with `x ∈ K`, `y ∈ J`. -/
theorem exists_mul_eq_of_index_two {K J : Subgroup G} (hK : K.index = 2) (hJ : ¬ J ≤ K)
    (g : G) : ∃ x ∈ K, ∃ y ∈ J, g = x * y := by
  obtain ⟨j, hjJ, hjK⟩ := SetLike.not_le_iff_exists.1 hJ
  by_cases hg : g ∈ K
  · exact ⟨g, hg, 1, J.one_mem, (mul_one g).symm⟩
  · obtain ⟨a, ha⟩ := Subgroup.index_eq_two_iff.1 hK
    have key : ∀ x : G, x ∉ K → x * a ∈ K := by
      intro x hx
      rcases ha x with ⟨h1, -⟩ | ⟨h1, -⟩
      exacts [h1, absurd h1 hx]
    refine ⟨g * j⁻¹, ?_, j, hjJ, by simp⟩
    simpa [mul_assoc] using K.mul_mem (key g hg) (K.inv_mem (key j hjK))

/-- (Was half of `index_two_singleton`.) If `K` has index `2` and `J ≰ K`, there is exactly
one double coset in `K\G/J`. -/
theorem subsingleton_cosets_of_index_two {K J : Subgroup G} (hK : K.index = 2)
    (hJ : ¬ J ≤ K) : Subsingleton (Cosets K J) := by
  have key : ∀ g : G, DoubleCoset.mk K J g = DoubleCoset.mk K J 1 := by
    intro g
    obtain ⟨x, hx, y, hy, rfl⟩ := exists_mul_eq_of_index_two hK hJ g
    exact ((DoubleCoset.eq K J 1 (x * y)).2 ⟨x, hx, y, hy, by simp⟩).symm
  exact ⟨fun D₁ D₂ => Quotient.ind₂' (fun g₁ g₂ => (key g₁).trans (key g₂).symm) D₁ D₂⟩

/-! ## The comparison maps `Θ` and `Π` -/

section Comparison

/-- (Was `theta_def`.) For each `s : G` there is a unique `k`-linear map
`Θ_s : Ind_{L_s}^L (V^s) →ₗ[k] Ind_H^G V` with `Θ_s [l, v] = [s * l, v]`. -/
theorem existsUnique_theta (s : G) :
    ∃! Θ : TwistedIndV H L ρ s →ₗ[k] IndV H.subtype ρ,
      ∀ (l : L) (v : V),
        Θ (twistedMk H L ρ s l v) = IndV.mk H.subtype ρ (s * (l : G)) v := by
  refine existsUnique_indLift (inter H L s).subtype (twisted H L ρ s)
    (fun l => IndV.mk H.subtype ρ (s * (l : G))) fun a l => ?_
  refine LinearMap.ext fun v => ?_
  change IndV.mk H.subtype ρ (s * (((inter H L s).subtype a * l : L) : G))
      (twisted H L ρ s a v) = IndV.mk H.subtype ρ (s * (l : G)) v
  rw [twisted_apply]
  have h1 : (s * (((inter H L s).subtype a * l : L) : G) : G)
      = H.subtype ⟨s * ((a : L) : G) * s⁻¹, a.2⟩ * (s * (l : G)) := by
    push_cast [Subgroup.coe_subtype]
    group
  rw [h1]
  exact indV_mk_eq H.subtype ρ ⟨s * ((a : L) : G) * s⁻¹, a.2⟩ (s * (l : G)) v

/-- (Was `theta_equivariant`.) Any `Θ` with the values of `existsUnique_theta` intertwines
the `L`-action of `Ind_{L_s}^L (ρ^s)` with the restricted `L`-action on `Ind_H^G V`. -/
theorem theta_component_equivariant (s : G)
    (Θ : TwistedIndV H L ρ s →ₗ[k] IndV H.subtype ρ)
    (hΘ : ∀ (l : L) (v : V),
      Θ (twistedMk H L ρ s l v) = IndV.mk H.subtype ρ (s * (l : G)) v)
    (l : L) :
    Θ ∘ₗ indTwisted H L ρ s l = resInd H L ρ l ∘ₗ Θ := by
  refine IndV.hom_ext _ _ fun l' => LinearMap.ext fun v => ?_
  change Θ (indTwisted H L ρ s l (twistedMk H L ρ s l' v))
      = resInd H L ρ l (Θ (twistedMk H L ρ s l' v))
  rw [show indTwisted H L ρ s l (twistedMk H L ρ s l' v)
      = twistedMk H L ρ s (l' * l⁻¹) v from ind_mk _ _ l l' v]
  rw [hΘ, hΘ]
  change _ = ind H.subtype ρ (L.subtype l) _
  rw [ind_mk]
  have h1 : (s * ((l' * l⁻¹ : L) : G) : G) = s * (l' : G) * (L.subtype l)⁻¹ := by
    push_cast [Subgroup.coe_subtype]
    group
  rw [h1]

/-- (Was `independence`.) If `h * s * l = h' * s * l'` with `h, h' ∈ H` and `l, l' ∈ L`,
then `[l, ρ(h)⁻¹ v] = [l', ρ(h')⁻¹ v]` in `Ind_{L_s}^L (V^s)`. -/
theorem independence (s : G) (h h' : H) (l l' : L)
    (heq : (h : G) * s * (l : G) = (h' : G) * s * (l' : G)) (v : V) :
    twistedMk H L ρ s l (ρ h⁻¹ v) = twistedMk H L ρ s l' (ρ h'⁻¹ v) := by
  have e1 : s * ((l : G) * (l' : G)⁻¹) * s⁻¹ = (h : G)⁻¹ * (h' : G) := by
    have h2 : (h : G) * (s * ((l : G) * (l' : G)⁻¹) * s⁻¹) = (h' : G) := by
      calc (h : G) * (s * ((l : G) * (l' : G)⁻¹) * s⁻¹)
          = ((h : G) * s * (l : G)) * ((l' : G)⁻¹ * s⁻¹) := by group
        _ = ((h' : G) * s * (l' : G)) * ((l' : G)⁻¹ * s⁻¹) := by rw [heq]
        _ = (h' : G) := by group
    calc s * ((l : G) * (l' : G)⁻¹) * s⁻¹
        = (h : G)⁻¹ * ((h : G) * (s * ((l : G) * (l' : G)⁻¹) * s⁻¹)) := by group
      _ = (h : G)⁻¹ * (h' : G) := by rw [h2]
  have hmem : l * l'⁻¹ ∈ inter H L s := by
    rw [mem_inter]
    have e2 : (s * ((l * l'⁻¹ : L) : G) * s⁻¹ : G) = (h : G)⁻¹ * (h' : G) := by
      push_cast
      exact e1
    rw [e2]
    exact H.mul_mem (H.inv_mem h.2) h'.2
  have hsub : (inter H L s).subtype ⟨l * l'⁻¹, hmem⟩ * l' = l := inv_mul_cancel_right l l'
  have hvec : twisted H L ρ s ⟨l * l'⁻¹, hmem⟩ (ρ h'⁻¹ v) = ρ h⁻¹ v := by
    rw [twisted_apply]
    have hc : ∀ (c : H), (c : G) = (h : G)⁻¹ * (h' : G) → ρ c (ρ h'⁻¹ v) = ρ h⁻¹ v := by
      intro c hcc
      have hc2 : c = h⁻¹ * h' := Subtype.ext (by push_cast; exact hcc)
      rw [hc2, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel_right]
    refine hc _ ?_
    push_cast
    exact e1
  calc twistedMk H L ρ s l (ρ h⁻¹ v)
      = twistedMk H L ρ s ((inter H L s).subtype ⟨l * l'⁻¹, hmem⟩ * l')
          (twisted H L ρ s ⟨l * l'⁻¹, hmem⟩ (ρ h'⁻¹ v)) := by rw [hsub, hvec]
    _ = twistedMk H L ρ s l' (ρ h'⁻¹ v) :=
        indV_mk_eq (inter H L s).subtype (twisted H L ρ s) ⟨l * l'⁻¹, hmem⟩ l' (ρ h'⁻¹ v)

/-! ### σ-generic machinery (private)

The comparison maps are constructed for an arbitrary system `σ` of double-coset
representatives; the audited statements below are the `σ = Quotient.out` instances, and
`mackey_equiv` is the fully general consequence. Nothing in this subsection needs to be
audited: all content flows through the statements above and below. -/

section RepresentativeSystem

variable (σ : Cosets H L → G) (hσ : ∀ D, DoubleCoset.mk H L (σ D) = D)

include hσ in
private theorem exists_factor (g : G) :
    ∃ (h : H) (l : L), g = (h : G) * σ (DoubleCoset.mk H L g) * (l : G) := by
  obtain ⟨x, hx, y, hy, hxy⟩ :=
    (DoubleCoset.eq H L (σ (DoubleCoset.mk H L g)) g).1 (hσ (DoubleCoset.mk H L g))
  exact ⟨⟨x, hx⟩, ⟨y, hy⟩, hxy⟩

private theorem mk_mul_left (h : H) (g : G) :
    DoubleCoset.mk H L (H.subtype h * g) = DoubleCoset.mk H L g :=
  (DoubleCoset.eq H L (H.subtype h * g) g).2
    ⟨(H.subtype h)⁻¹, H.inv_mem h.2, 1, L.one_mem, by group⟩

include hσ in
private theorem mk_sigma_mul (D : Cosets H L) (l : L) :
    DoubleCoset.mk H L (σ D * (l : G)) = D := by
  have h1 : DoubleCoset.mk H L (σ D * (l : G)) = DoubleCoset.mk H L (σ D) :=
    (DoubleCoset.eq H L (σ D * (l : G)) (σ D)).2
      ⟨1, H.one_mem, (l : G)⁻¹, L.inv_mem l.2, by group⟩
  rw [h1, hσ D]

variable [DecidableEq (Cosets H L)]

include hσ in
private theorem existsUnique_piGen :
    ∃! P : IndV H.subtype ρ →ₗ[k] (⨁ D, TwistedIndV H L ρ (σ D)),
      ∀ (g : G) (h : H) (l : L),
        g = (h : G) * σ (DoubleCoset.mk H L g) * (l : G) →
        ∀ v : V,
          P (IndV.mk H.subtype ρ g v)
            = DirectSum.of (fun D => TwistedIndV H L ρ (σ D)) (DoubleCoset.mk H L g)
                (twistedMk H L ρ (σ (DoubleCoset.mk H L g)) l (ρ h⁻¹ v)) := by
  choose h₀ l₀ hfac using exists_factor H L σ hσ
  have hcompat : ∀ (h : H) (g : G),
      (DirectSum.lof k (Cosets H L) (fun D => TwistedIndV H L ρ (σ D))
          (DoubleCoset.mk H L (H.subtype h * g)) ∘ₗ
        twistedMk H L ρ (σ (DoubleCoset.mk H L (H.subtype h * g))) (l₀ (H.subtype h * g)) ∘ₗ
          (ρ (h₀ (H.subtype h * g))⁻¹ : V →ₗ[k] V)) ∘ₗ (ρ h : V →ₗ[k] V)
      = DirectSum.lof k (Cosets H L) (fun D => TwistedIndV H L ρ (σ D))
          (DoubleCoset.mk H L g) ∘ₗ
        twistedMk H L ρ (σ (DoubleCoset.mk H L g)) (l₀ g) ∘ₗ (ρ (h₀ g)⁻¹ : V →ₗ[k] V) := by
    intro h g
    refine LinearMap.ext fun v => ?_
    have hmkeq := mk_mul_left H L h g
    have hfg := hfac (H.subtype h * g)
    rw [hmkeq] at hfg
    have heq' : ((h₀ (H.subtype h * g) : H) : G) * σ (DoubleCoset.mk H L g)
          * ((l₀ (H.subtype h * g) : L) : G)
        = ((h * h₀ g : H) : G) * σ (DoubleCoset.mk H L g) * ((l₀ g : L) : G) := by
      rw [← hfg]
      have h4 : ((h * h₀ g : H) : G) * σ (DoubleCoset.mk H L g) * ((l₀ g : L) : G)
          = (h : G) * ((h₀ g : G) * σ (DoubleCoset.mk H L g) * (l₀ g : G)) := by
        push_cast
        group
      rw [h4, ← hfac g]
      rfl
    have hind := independence H L ρ (σ (DoubleCoset.mk H L g)) (h₀ (H.subtype h * g))
      (h * h₀ g) (l₀ (H.subtype h * g)) (l₀ g) heq' (ρ h v)
    change DirectSum.of (fun D => TwistedIndV H L ρ (σ D))
        (DoubleCoset.mk H L (H.subtype h * g))
        (twistedMk H L ρ (σ (DoubleCoset.mk H L (H.subtype h * g))) (l₀ (H.subtype h * g))
          (ρ (h₀ (H.subtype h * g))⁻¹ (ρ h v)))
      = DirectSum.of (fun D => TwistedIndV H L ρ (σ D)) (DoubleCoset.mk H L g)
          (twistedMk H L ρ (σ (DoubleCoset.mk H L g)) (l₀ g) (ρ (h₀ g)⁻¹ v))
    rw [hmkeq, hind]
    congr 1
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_rev, inv_mul_cancel_right]
  obtain ⟨P, hP, hPuniq⟩ := existsUnique_indLift H.subtype ρ
    (fun g => DirectSum.lof k (Cosets H L) (fun D => TwistedIndV H L ρ (σ D))
        (DoubleCoset.mk H L g) ∘ₗ
      twistedMk H L ρ (σ (DoubleCoset.mk H L g)) (l₀ g) ∘ₗ (ρ (h₀ g)⁻¹ : V →ₗ[k] V))
    hcompat
  refine ⟨P, fun g h l hgl v => ?_, fun P' hP' => ?_⟩
  · exact (hP g v).trans (congrArg
      (fun x => DirectSum.of (fun D => TwistedIndV H L ρ (σ D)) (DoubleCoset.mk H L g) x)
      (independence H L ρ (σ (DoubleCoset.mk H L g)) (h₀ g) h (l₀ g) l
        ((hfac g).symm.trans hgl) v))
  · exact hPuniq P' fun g v => hP' g (h₀ g) (l₀ g) (hfac g) v

private noncomputable def thetaGen :
    (⨁ D, TwistedIndV H L ρ (σ D)) →ₗ[k] IndV H.subtype ρ :=
  DirectSum.toModule k (Cosets H L) (IndV H.subtype ρ) fun D =>
    (existsUnique_theta H L ρ (σ D)).choose

private theorem thetaGen_of (D : Cosets H L) (l : L) (v : V) :
    thetaGen H L ρ σ (DirectSum.of (fun D => TwistedIndV H L ρ (σ D)) D
        (twistedMk H L ρ (σ D) l v))
      = IndV.mk H.subtype ρ (σ D * (l : G)) v := by
  have h := (existsUnique_theta H L ρ (σ D)).choose_spec.1 l v
  unfold thetaGen
  rw [← DirectSum.lof_eq_of k, DirectSum.toModule_lof]
  exact h

private noncomputable def piGen :
    IndV H.subtype ρ →ₗ[k] (⨁ D, TwistedIndV H L ρ (σ D)) :=
  (existsUnique_piGen H L ρ σ hσ).choose

private theorem piGen_mk (g : G) (h : H) (l : L)
    (hg : g = (h : G) * σ (DoubleCoset.mk H L g) * (l : G)) (v : V) :
    piGen H L ρ σ hσ (IndV.mk H.subtype ρ g v)
      = DirectSum.of (fun D => TwistedIndV H L ρ (σ D)) (DoubleCoset.mk H L g)
          (twistedMk H L ρ (σ (DoubleCoset.mk H L g)) l (ρ h⁻¹ v)) :=
  (existsUnique_piGen H L ρ σ hσ).choose_spec.1 g h l hg v

private theorem piGen_comp_thetaGen :
    piGen H L ρ σ hσ ∘ₗ thetaGen H L ρ σ = LinearMap.id := by
  refine DirectSum.linearMap_ext _ fun D => IndV.hom_ext _ _ fun l => LinearMap.ext fun v => ?_
  change piGen H L ρ σ hσ (thetaGen H L ρ σ
      (DirectSum.of (fun D => TwistedIndV H L ρ (σ D)) D (twistedMk H L ρ (σ D) l v)))
    = DirectSum.of (fun D => TwistedIndV H L ρ (σ D)) D (twistedMk H L ρ (σ D) l v)
  rw [thetaGen_of]
  have hmk2 : DoubleCoset.mk H L (σ D * (l : G)) = D := mk_sigma_mul H L σ hσ D l
  have hfacc : σ D * (l : G)
      = ((1 : H) : G) * σ (DoubleCoset.mk H L (σ D * (l : G))) * (l : G) := by
    rw [hmk2]
    simp
  rw [piGen_mk H L ρ σ hσ (σ D * (l : G)) 1 l hfacc v, hmk2]
  simp

private theorem thetaGen_comp_piGen :
    thetaGen H L ρ σ ∘ₗ piGen H L ρ σ hσ = LinearMap.id := by
  refine IndV.hom_ext _ _ fun g => LinearMap.ext fun v => ?_
  change thetaGen H L ρ σ (piGen H L ρ σ hσ (IndV.mk H.subtype ρ g v))
      = IndV.mk H.subtype ρ g v
  obtain ⟨h, l, hfacg⟩ := exists_factor H L σ hσ g
  rw [piGen_mk H L ρ σ hσ g h l hfacg v, thetaGen_of]
  have h2 : σ (DoubleCoset.mk H L g) * (l : G) = H.subtype h⁻¹ * g := by
    conv_rhs => rw [hfacg]
    push_cast [Subgroup.coe_subtype]
    group
  rw [h2]
  exact indV_mk_eq H.subtype ρ h⁻¹ g v

private theorem thetaGen_intertwines (l : L) :
    thetaGen H L ρ σ ∘ₗ (directSum fun D => indTwisted H L ρ (σ D)) l
      = resInd H L ρ l ∘ₗ thetaGen H L ρ σ := by
  refine DirectSum.linearMap_ext _ fun D => IndV.hom_ext _ _ fun l' =>
    LinearMap.ext fun v => ?_
  change thetaGen H L ρ σ ((directSum fun D => indTwisted H L ρ (σ D)) l
      (DirectSum.lof k (Cosets H L) (fun D => TwistedIndV H L ρ (σ D)) D
        (twistedMk H L ρ (σ D) l' v)))
    = resInd H L ρ l (thetaGen H L ρ σ
        (DirectSum.of (fun D => TwistedIndV H L ρ (σ D)) D (twistedMk H L ρ (σ D) l' v)))
  rw [directSum_apply, DirectSum.lmap_lof, DirectSum.lof_eq_of k]
  rw [show indTwisted H L ρ (σ D) l (twistedMk H L ρ (σ D) l' v)
      = twistedMk H L ρ (σ D) (l' * l⁻¹) v from ind_mk _ _ l l' v]
  rw [thetaGen_of, thetaGen_of]
  change _ = ind H.subtype ρ (L.subtype l) _
  rw [ind_mk]
  have h1 : (σ D * ((l' * l⁻¹ : L) : G) : G) = σ D * (l' : G) * (L.subtype l)⁻¹ := by
    push_cast [Subgroup.coe_subtype]
    group
  rw [h1]

end RepresentativeSystem

variable [DecidableEq (Cosets H L)]

/-- (Was `pi_def`.) There is a unique `k`-linear map `Π` from `Ind_H^G V` to the Mackey
direct sum such that for every `g : G`, every factorisation `g = h * s_D * l` through the
canonical representative `s_D` of the double coset `D = ⟦g⟧` of `g`, and every `v : V`,
`Π [g, v] = ι_D [l, ρ(h)⁻¹ v]`. -/
theorem existsUnique_pi :
    ∃! P : IndV H.subtype ρ →ₗ[k] (⨁ D, Summand H L ρ D),
      ∀ (g : G) (h : H) (l : L),
        g = (h : G) * (DoubleCoset.mk H L g).out * (l : G) →
        ∀ v : V,
          P (IndV.mk H.subtype ρ g v)
            = DirectSum.of (Summand H L ρ) (DoubleCoset.mk H L g)
                (twistedMk H L ρ (DoubleCoset.mk H L g).out l (ρ h⁻¹ v)) :=
  existsUnique_piGen H L ρ Quotient.out (DoubleCoset.out_eq' H L)

/-- (Was `thetaSum`.) The comparison map `Θ : W →ₗ[k] Ind_H^G V`, with `D`-th component
the unique `Θ_{s_D}` provided by `existsUnique_theta`. -/
noncomputable def theta : (⨁ D, Summand H L ρ D) →ₗ[k] IndV H.subtype ρ :=
  DirectSum.toModule k (Cosets H L) (IndV H.subtype ρ) fun D =>
    (existsUnique_theta H L ρ D.out).choose

/-- Values of `Θ`: `Θ (ι_D [l, v]) = [s_D * l, v]`. Proved from `existsUnique_theta`, so
there is nothing extra to audit here beyond the definition of `theta`. -/
@[simp]
lemma theta_of (D : Cosets H L) (l : L) (v : V) :
    theta H L ρ (DirectSum.of (Summand H L ρ) D (twistedMk H L ρ D.out l v))
      = IndV.mk H.subtype ρ (D.out * (l : G)) v :=
  thetaGen_of H L ρ Quotient.out D l v

/-- (Was `piMap`.) The inverse comparison map `Π`, from `existsUnique_pi`. -/
noncomputable def pi : IndV H.subtype ρ →ₗ[k] (⨁ D, Summand H L ρ D) :=
  (existsUnique_pi H L ρ).choose

/-- Values of `Π`. Proved from `existsUnique_pi`. -/
lemma pi_mk (g : G) (h : H) (l : L)
    (hg : g = (h : G) * (DoubleCoset.mk H L g).out * (l : G)) (v : V) :
    pi H L ρ (IndV.mk H.subtype ρ g v)
      = DirectSum.of (Summand H L ρ) (DoubleCoset.mk H L g)
          (twistedMk H L ρ (DoubleCoset.mk H L g).out l (ρ h⁻¹ v)) :=
  (existsUnique_pi H L ρ).choose_spec.1 g h l hg v

/-- (Was `pi_theta`.) `Π ∘ Θ = id` on the Mackey direct sum. -/
theorem pi_comp_theta : pi H L ρ ∘ₗ theta H L ρ = LinearMap.id :=
  piGen_comp_thetaGen H L ρ Quotient.out (DoubleCoset.out_eq' H L)

/-- (Was `theta_pi`.) `Θ ∘ Π = id` on `Ind_H^G V`. -/
theorem theta_comp_pi : theta H L ρ ∘ₗ pi H L ρ = LinearMap.id :=
  thetaGen_comp_piGen H L ρ Quotient.out (DoubleCoset.out_eq' H L)

/-- (Was conjunct (i) of `mackey`.) `Θ` is `L`-equivariant from `mackeySum` to `resInd`. -/
theorem theta_intertwines (l : L) :
    theta H L ρ ∘ₗ mackeySum H L ρ l = resInd H L ρ l ∘ₗ theta H L ρ :=
  thetaGen_intertwines H L ρ Quotient.out l

/-- **Mackey's restriction–induction formula** (was `mackey`): there is an equivalence of
`L`-representations `e : ⨁_{D ∈ H\G/L} Ind_{L_{s_D}}^L (V^{s_D}) ≃ Res_L Ind_H^G V`
determined on generators by `e (ι_D [l, v]) = [s_D * l, v]`. -/
theorem mackey :
    ∃ e : Representation.Equiv (mackeySum H L ρ) (resInd H L ρ),
      ∀ (D : Cosets H L) (l : L) (v : V),
        e (DirectSum.of (Summand H L ρ) D (twistedMk H L ρ D.out l v))
          = IndV.mk H.subtype ρ (D.out * (l : G)) v :=
  ⟨Representation.Equiv.mk
    (LinearEquiv.ofLinear (theta H L ρ) (pi H L ρ) (theta_comp_pi H L ρ)
      (pi_comp_theta H L ρ))
    (theta_intertwines H L ρ), theta_of H L ρ⟩

end Comparison

/-! ## The pen-and-paper formulation -/

/-- **Mackey's formula, pen-and-paper form**: for *any* choice of double-coset
representatives `σ : H\G/L → G` there is an equivalence of `L`-representations
`⨁_{D ∈ H\G/L} Ind_{L_{σ D}}^L (V^{σ D}) ≃ Res_L Ind_H^G V`, with no particular map
named. The `σ := Quotient.out` case is `mackey`; the component lemmas
(`existsUnique_theta`, …, `theta_comp_pi`) are stated for an arbitrary representative
`s`, so the same machinery proves this general form. -/
theorem mackey_equiv (σ : Cosets H L → G) (hσ : ∀ D, DoubleCoset.mk H L (σ D) = D) :
    Nonempty (Representation.Equiv
      (directSum fun D => indTwisted H L ρ (σ D)) (resInd H L ρ)) := by
  classical
  exact ⟨Representation.Equiv.mk
    (LinearEquiv.ofLinear (thetaGen H L ρ σ) (piGen H L ρ σ hσ)
      (thetaGen_comp_piGen H L ρ σ hσ) (piGen_comp_thetaGen H L ρ σ hσ))
    (thetaGen_intertwines H L ρ σ)⟩

/-- Formal glue (no informal counterpart): over a `Unique` index type, the direct sum of
a constant family of representations is equivalent to its single summand. -/
theorem directSum_unique_equiv {ι : Type*} [Unique ι] {Γ : Type*} [Group Γ]
    {X : Type*} [AddCommGroup X] [Module k X] (f : Representation k Γ X) :
    Nonempty (Representation.Equiv (directSum fun _ : ι => f) f) := by
  classical
  refine ⟨Representation.Equiv.mk (LinearEquiv.ofLinear
    (DirectSum.toModule k ι X fun _ => LinearMap.id)
    (DirectSum.lof k ι (fun _ => X) default) ?_ ?_) fun g => ?_⟩
  · ext x
    simp [DirectSum.toModule_lof]
  · refine DirectSum.linearMap_ext _ fun i => ?_
    obtain rfl := Unique.eq_default i
    ext x
    simp [DirectSum.toModule_lof]
  · refine DirectSum.linearMap_ext _ fun i => ?_
    obtain rfl := Unique.eq_default i
    ext x
    simp [DirectSum.toModule_lof]

/-- Twisting by the representative `s = 1` is restriction: `J_1 = {a ∈ J | a ∈ K}` and
`τ^1 a = τ a`, so the Mackey summand `Ind_{J_1}^J (τ^1)` is equivalent to
`Ind_{K ⊓ J}^J (Res τ)` as it appears in `index_two`. -/
theorem indTwisted_one (K J : Subgroup G) (τ : Representation k K V) :
    Nonempty (Representation.Equiv
      (ind (Subgroup.inclusion (inf_le_right : K ⊓ J ≤ J))
        (τ.comp (Subgroup.inclusion (inf_le_left : K ⊓ J ≤ K))))
      (indTwisted K J τ 1)) := by
  have hmem : ∀ c : ↥(K ⊓ J),
      Subgroup.inclusion (inf_le_right : K ⊓ J ≤ J) c ∈ inter K J 1 := by
    intro c
    rw [mem_inter]
    simpa [Subgroup.coe_inclusion] using c.2.1
  have hmem' : ∀ a : ↥(inter K J 1), ((a : J) : G) ∈ K ⊓ J := by
    intro a
    have h1 := a.2
    rw [mem_inter] at h1
    exact ⟨by simpa using h1, (a : J).2⟩
  -- the two twisted actions agree
  have hτ : ∀ c : ↥(K ⊓ J),
      (τ.comp (Subgroup.inclusion (inf_le_left : K ⊓ J ≤ K))) c
        = twisted K J τ 1 ⟨Subgroup.inclusion inf_le_right c, hmem c⟩ := by
    intro c
    rw [twisted_apply]
    change τ (Subgroup.inclusion (inf_le_left : K ⊓ J ≤ K) c) = _
    congr 1
    ext
    simp [Subgroup.coe_inclusion]
  have hτ' : ∀ a : ↥(inter K J 1),
      twisted K J τ 1 a
        = (τ.comp (Subgroup.inclusion (inf_le_left : K ⊓ J ≤ K))) ⟨((a : J) : G), hmem' a⟩ := by
    intro a
    rw [twisted_apply]
    change _ = τ (Subgroup.inclusion (inf_le_left : K ⊓ J ≤ K) ⟨((a : J) : G), hmem' a⟩)
    congr 1
    ext
    simp [Subgroup.coe_inclusion]
  -- compatibility of the generator families
  have hA : ∀ (c : ↥(K ⊓ J)) (x : ↥J),
      (fun x : ↥J => IndV.mk (inter K J 1).subtype (twisted K J τ 1) x)
          (Subgroup.inclusion (inf_le_right : K ⊓ J ≤ J) c * x) ∘ₗ
        ((τ.comp (Subgroup.inclusion (inf_le_left : K ⊓ J ≤ K))) c : V →ₗ[k] V)
      = (fun x : ↥J => IndV.mk (inter K J 1).subtype (twisted K J τ 1) x) x := by
    intro c x
    refine LinearMap.ext fun v => ?_
    change IndV.mk (inter K J 1).subtype (twisted K J τ 1)
        (Subgroup.inclusion inf_le_right c * x)
        ((τ.comp (Subgroup.inclusion inf_le_left)) c v)
      = IndV.mk (inter K J 1).subtype (twisted K J τ 1) x v
    rw [hτ c]
    exact indV_mk_eq (inter K J 1).subtype (twisted K J τ 1)
      ⟨Subgroup.inclusion inf_le_right c, hmem c⟩ x v
  have hB : ∀ (a : ↥(inter K J 1)) (x : ↥J),
      (fun x : ↥J => IndV.mk (Subgroup.inclusion (inf_le_right : K ⊓ J ≤ J))
          (τ.comp (Subgroup.inclusion (inf_le_left : K ⊓ J ≤ K))) x)
          ((inter K J 1).subtype a * x) ∘ₗ (twisted K J τ 1 a : V →ₗ[k] V)
      = (fun x : ↥J => IndV.mk (Subgroup.inclusion inf_le_right)
          (τ.comp (Subgroup.inclusion inf_le_left)) x) x := by
    intro a x
    refine LinearMap.ext fun v => ?_
    change IndV.mk (Subgroup.inclusion inf_le_right) (τ.comp (Subgroup.inclusion inf_le_left))
        ((inter K J 1).subtype a * x) (twisted K J τ 1 a v)
      = IndV.mk (Subgroup.inclusion inf_le_right) (τ.comp (Subgroup.inclusion inf_le_left)) x v
    rw [hτ' a]
    have hsub : (inter K J 1).subtype a
        = Subgroup.inclusion (inf_le_right : K ⊓ J ≤ J) ⟨((a : J) : G), hmem' a⟩ := by
      ext
      simp [Subgroup.coe_inclusion]
    rw [hsub]
    exact indV_mk_eq (Subgroup.inclusion inf_le_right)
      (τ.comp (Subgroup.inclusion inf_le_left)) ⟨((a : J) : G), hmem' a⟩ x v
  obtain ⟨F, hF, -⟩ := existsUnique_indLift (Subgroup.inclusion (inf_le_right : K ⊓ J ≤ J))
    (τ.comp (Subgroup.inclusion (inf_le_left : K ⊓ J ≤ K)))
    (fun x : ↥J => IndV.mk (inter K J 1).subtype (twisted K J τ 1) x) hA
  obtain ⟨F', hF', -⟩ := existsUnique_indLift (inter K J 1).subtype (twisted K J τ 1)
    (fun x : ↥J => IndV.mk (Subgroup.inclusion (inf_le_right : K ⊓ J ≤ J))
      (τ.comp (Subgroup.inclusion (inf_le_left : K ⊓ J ≤ K))) x) hB
  have hFF' : F ∘ₗ F' = LinearMap.id := by
    refine IndV.hom_ext _ _ fun x => LinearMap.ext fun v => ?_
    change F (F' (IndV.mk (inter K J 1).subtype (twisted K J τ 1) x v))
      = IndV.mk (inter K J 1).subtype (twisted K J τ 1) x v
    rw [hF' x v, hF x v]
  have hF'F : F' ∘ₗ F = LinearMap.id := by
    refine IndV.hom_ext _ _ fun x => LinearMap.ext fun v => ?_
    change F' (F (IndV.mk (Subgroup.inclusion inf_le_right)
        (τ.comp (Subgroup.inclusion inf_le_left)) x v))
      = IndV.mk (Subgroup.inclusion inf_le_right) (τ.comp (Subgroup.inclusion inf_le_left)) x v
    rw [hF x v, hF' x v]
  refine ⟨Representation.Equiv.mk (LinearEquiv.ofLinear F F' hFF' hF'F) fun j => ?_⟩
  refine IndV.hom_ext _ _ fun x => LinearMap.ext fun v => ?_
  change F (ind (Subgroup.inclusion inf_le_right) (τ.comp (Subgroup.inclusion inf_le_left)) j
      (IndV.mk (Subgroup.inclusion inf_le_right) (τ.comp (Subgroup.inclusion inf_le_left)) x v))
    = indTwisted K J τ 1 j
        (F (IndV.mk (Subgroup.inclusion inf_le_right)
          (τ.comp (Subgroup.inclusion inf_le_left)) x v))
  rw [ind_mk, hF, hF x v]
  exact (ind_mk (inter K J 1).subtype (twisted K J τ 1) j x v).symm

/-! ## Index-two corollaries -/

/-- (Was `index_two`.) If `K` has index `2` and `J ≰ K`, then restriction of the induced
representation decomposes with a single summand:
`Res_J Ind_K^G V ≅ Ind_{K ⊓ J}^J (Res_{K ⊓ J} τ)` as `J`-representations.
(`resInd K J τ` is `Res_J Ind_K^G τ`, i.e. `(ind K.subtype τ).comp J.subtype`.)

**Proved** from `mackey_equiv`: by `subsingleton_cosets_of_index_two` there is exactly
one double coset, so we may choose the representative system `σ D = 1`; the direct sum
collapses to its single summand (`directSum_unique_equiv`), and twisting by `1` is
restriction to `K ⊓ J` (`indTwisted_one`). -/
theorem index_two {K J : Subgroup G} (hK : K.index = 2) (hJ : ¬ J ≤ K)
    (τ : Representation k K V) :
    Nonempty (Representation.Equiv (resInd K J τ)
      (ind (Subgroup.inclusion (inf_le_right : K ⊓ J ≤ J))
        (τ.comp (Subgroup.inclusion (inf_le_left : K ⊓ J ≤ K))))) := by
  haveI : Subsingleton (Cosets K J) := subsingleton_cosets_of_index_two hK hJ
  haveI : Unique (Cosets K J) := ⟨⟨DoubleCoset.mk K J 1⟩, fun D => Subsingleton.elim D _⟩
  obtain ⟨e₁⟩ := mackey_equiv K J τ (fun _ => (1 : G)) fun D => Subsingleton.elim _ D
  obtain ⟨e₂⟩ := directSum_unique_equiv (ι := Cosets K J) (indTwisted K J τ 1)
  obtain ⟨e₃⟩ := indTwisted_one K J τ
  exact ⟨(e₃.trans (e₂.symm.trans e₁)).symm⟩

/-- (Was `index_two_character`.) The rank-one case of `index_two`: for a character `ψ`
of `K`, `Res_J Ind_K^G ψ ≅ Ind_{K ⊓ J}^J (ψ|_{K ⊓ J})` as `J`-representations.

Here "character" is encoded as `ψ : Representation k K k`, a `k`-linear action of `K` on
the module `k` itself. This is *exactly* the data of a homomorphism `K →* kˣ`: since `K`
is a group, every `ψ a : End k k ≅ k` is automatically invertible (with inverse
`ψ a⁻¹`), so unit-valuedness need not be assumed. This is literally `index_two` with
`V := k`. -/
theorem index_two_character {K J : Subgroup G} (hK : K.index = 2) (hJ : ¬ J ≤ K)
    (ψ : Representation k K k) :
    Nonempty (Representation.Equiv (resInd K J ψ)
      (ind (Subgroup.inclusion (inf_le_right : K ⊓ J ≤ J))
        (ψ.comp (Subgroup.inclusion (inf_le_left : K ⊓ J ≤ K))))) :=
  index_two hK hJ ψ

end Mackey
