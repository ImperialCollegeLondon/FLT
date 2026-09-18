import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.IndexNormal
import Mathlib.GroupTheory.GroupAction.ConjAct
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Projection
import Mathlib.RepresentationTheory.Induced
import Mathlib.RepresentationTheory.Irreducible

/-!
# Two-dimensional restrictions to a normal subgroup

This file contains a self-contained Lean development for two related statements about a
two-dimensional representation `ρ : Representation k G V`.

The first statement, `main_theorem_1_3`, says that if `H` is normal, `G ⧸ H` is cyclic, and the
restriction of `ρ` to `H` acts by scalar operators through a character `χ : H →* kˣ`, then `ρ`
is not irreducible.  The proof chooses an eigenline for a lift of a generator of `G ⧸ H`; scalar
action of `H` and cyclicity of the quotient make that line stable under all of `G`.

The second statement, `main_theorem_1_8`, is a Clifford-type dichotomy.  If `ρ` is irreducible
and `V` has dimension two, then the restriction to `H` is either irreducible, or it splits as a
direct sum of two distinct `G`-conjugate characters of `H`.

The file works with Mathlib's unbundled `Representation k G V`, i.e. a monoid homomorphism
`G →* V →ₗ[k] V`.  Direct sums of characters are encoded by complementary one-dimensional
submodules rather than by a bundled representation isomorphism.
-/

open scoped Pointwise

namespace Representation

variable {k G V : Type*} [Field k] [Group G] [AddCommGroup V] [Module k V]

variable (ρ : Representation k G V)

private lemma not_irreducible_of_nonzero_proper_subrepresentation
    (L : Subrepresentation ρ) (hL_bot : L.toSubmodule ≠ ⊥) (hL_top : L.toSubmodule ≠ ⊤) :
    ¬ IsIrreducible ρ := by
  intro hρ
  have hL_bot' : L ≠ ⊥ := by
    intro hL
    exact hL_bot (by rw [hL]; rfl)
  have hL_top' : L ≠ ⊤ := by
    intro hL
    exact hL_top (by rw [hL]; rfl)
  exact (IsSimpleOrder.eq_bot_or_eq_top (self := hρ) L).elim hL_bot' hL_top'

private lemma exists_nonzero_proper_subrepresentation_of_not_irreducible [Nontrivial V]
    {ρ : Representation k G V} (hρ : ¬ IsIrreducible ρ) :
    ∃ L : Subrepresentation ρ, L.toSubmodule ≠ ⊥ ∧ L.toSubmodule ≠ ⊤ := by
  haveI : Nontrivial (Subrepresentation ρ) := by
    refine ⟨⟨⊥, ⊤, ?_⟩⟩
    intro h
    have h' := congrArg Subrepresentation.toSubmodule h
    change (⊥ : Submodule k V) = ⊤ at h'
    exact (bot_ne_top : (⊥ : Submodule k V) ≠ ⊤) h'
  by_contra hred
  apply hρ
  refine { eq_bot_or_eq_top := ?_ }
  intro L
  by_cases hL_bot : L.toSubmodule = ⊥
  · left
    exact Subrepresentation.toSubmodule_injective hL_bot
  · right
    apply Subrepresentation.toSubmodule_injective
    by_contra hL_top
    exact hred ⟨L, hL_bot, hL_top⟩

/- If a linear map sends a vector into its span, then it preserves the whole line spanned by that
vector. -/
private lemma span_singleton_stable {f : V →ₗ[k] V} {v : V}
    (hf : f v ∈ k ∙ v) :
    ∀ ⦃w : V⦄, w ∈ k ∙ v → f w ∈ k ∙ v := by
  exact (Submodule.span_singleton_le_iff_mem v ((k ∙ v).comap f)).2 hf

/- An eigenline for `ρ g` is stable under every integer power of `g`.  Negative powers use the
inverse linear automorphism supplied by the representation. -/
private lemma stable_zpow_generator_line {g : G} {μ : k} {v : V}
    (hv : Module.End.HasEigenvector (ρ g) μ v) :
    ∀ n : ℤ, ∀ ⦃w : V⦄, w ∈ k ∙ v → ρ (g ^ n) w ∈ k ∙ v := by
  have hμ_ne_zero : μ ≠ 0 := by
    intro hμ
    have hgv : ρ g v = 0 := by
      simpa [hμ] using Module.End.HasEigenvector.apply_eq_smul hv
    exact hv.2 ((ρ.apply_bijective g).1 (by simpa using hgv))
  have hg_inv_v : ρ g⁻¹ v = μ⁻¹ • v := by
    apply (ρ.apply_bijective g).1
    simp [Module.End.HasEigenvector.apply_eq_smul hv, smul_smul, hμ_ne_zero]
  have hv_inv : Module.End.HasEigenvector (ρ g⁻¹) μ⁻¹ v :=
    ⟨Module.End.mem_eigenspace_iff.2 hg_inv_v, hv.2⟩
  have hpow :
      ∀ (a : G) (μa : k), Module.End.HasEigenvector (ρ a) μa v →
        ∀ m : ℕ, ∀ ⦃w : V⦄, w ∈ k ∙ v → ρ (a ^ m) w ∈ k ∙ v := by
    intro a μa hva m
    refine span_singleton_stable ?_
    exact Submodule.mem_span_singleton.2
      ⟨μa ^ m, by
        simpa [map_pow] using (Module.End.HasEigenvector.pow_apply hva m).symm⟩
  intro n
  cases n with
  | ofNat m =>
      simpa [zpow_natCast] using hpow g μ hv m
  | negSucc m =>
      simpa [zpow_negSucc, inv_pow] using hpow g⁻¹ μ⁻¹ hv_inv (m + 1)

/- If `G ⧸ H` is cyclic, choose a lift `g : G` of a generator.  Every element of `G` can then be
written as an element of `H` times an integer power of `g`. -/
private lemma quotient_cyclic_normal_form (H : Subgroup G) [H.Normal] [IsCyclic (G ⧸ H)] :
    ∃ g : G, ∀ x : G, ∃ n : ℤ, ∃ h : H, x = h * g ^ n := by
  obtain ⟨gbar, hgbar⟩ := IsCyclic.exists_generator (α := G ⧸ H)
  obtain ⟨g, hg⟩ := QuotientGroup.mk'_surjective H gbar
  refine ⟨g, fun x => ?_⟩
  obtain ⟨n, hn⟩ := (Subgroup.mem_zpowers_iff.mp (hgbar (QuotientGroup.mk' H x)))
  have hquot : (x : G ⧸ H) = (g ^ n : G ⧸ H) := by
    calc
      (x : G ⧸ H) = gbar ^ n := hn.symm
      _ = (g ^ n : G ⧸ H) := by
        simp [← hg]
  have hxH : x / g ^ n ∈ H := (QuotientGroup.eq_iff_div_mem (N := H)).1 hquot
  refine ⟨n, ⟨x / g ^ n, hxH⟩, ?_⟩
  change x = (x / g ^ n) * g ^ n
  simp [div_eq_mul_inv, mul_assoc]

/- Scalar action on `H`, together with cyclicity of `G ⧸ H`, produces a proper `G`-stable line:
an eigenline for a lift of a quotient generator. -/
theorem scalar_restriction_not_irreducible [IsAlgClosed k]
    (H : Subgroup G) [H.Normal] [IsCyclic (G ⧸ H)] (hV : Module.finrank k V = 2) (χ : H →* kˣ)
    (hχ : ∀ h : H, ρ h = ((χ h : k) • LinearMap.id : V →ₗ[k] V)) :
    ¬ IsIrreducible ρ := by
  haveI : FiniteDimensional k V := Module.finite_of_finrank_eq_succ hV
  haveI : Nontrivial V := Module.nontrivial_of_finrank_eq_succ hV
  obtain ⟨g, hg⟩ := quotient_cyclic_normal_form (G := G) H
  obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue (ρ g)
  obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
  let L : Submodule k V := k ∙ v
  have hL_ne_bot : L ≠ ⊥ := by
    simpa [L, Submodule.span_singleton_eq_bot] using hv.2
  have hL_ne_top : L ≠ ⊤ := by
    intro htop
    have hbad : (1 : ℕ) = 2 := by
      calc
        1 = Module.finrank k L := (finrank_span_singleton hv.2).symm
        _ = Module.finrank k (⊤ : Submodule k V) := by rw [htop]
        _ = Module.finrank k V := by simp
        _ = 2 := hV
    norm_num at hbad
  have hH : ∀ h : H, ∀ ⦃w : V⦄, w ∈ L → ρ h w ∈ L := by
    intro h w hw
    rw [hχ h]
    exact L.smul_mem (χ h : k) hw
  have hgpow : ∀ n : ℤ, ∀ ⦃w : V⦄, w ∈ L → ρ (g ^ n) w ∈ L := by
    simpa [L] using stable_zpow_generator_line (ρ := ρ) hv
  let W : Subrepresentation ρ := {
    toSubmodule := L
    apply_mem_toSubmodule := by
      intro x w hw
      obtain ⟨n, h, rfl⟩ := hg x
      rw [map_mul, Module.End.mul_apply]
      exact hH h (hgpow n hw) }
  exact not_irreducible_of_nonzero_proper_subrepresentation (ρ := ρ) W hL_ne_bot hL_ne_top

/-!
## A Clifford-type restriction dichotomy

The theorem below separates the restriction of a two-dimensional irreducible representation to a
finite-index normal subgroup `H` into two alternatives.

The first alternative says that the restricted representation has no nonzero proper `H`-stable
subspace over the base field `k`.

The second alternative is represented by `SplitsAsDistinctConjugateCharacters`: the restriction
has two complementary one-dimensional `H`-stable summands, `H` acts on one summand by a character
`χ`, and on the other by a distinct conjugate character `gχ`.
-/

/--
The subgroup `H` acts on the subspace `L` through the character `χ`.

That is, for every `h : H`, every vector of `L` is an eigenvector for the operator `ρ h`, with
eigenvalue `χ h`.
-/
def ActsByCharacterOn (H : Subgroup G) (ρ : Representation k G V) (L : Submodule k V)
    (χ : H →* kˣ) : Prop :=
  ∀ h : H, ∀ ⦃v : V⦄, v ∈ L → ρ h v = (χ h : k) • v

/--
The restriction of `ρ` to `H` is a direct sum of two characters.

The witnesses are two one-dimensional submodules `L` and `M` of `V`.  The condition
`IsCompl L M` means `L ∩ M = 0` and `L + M = V`, so every vector of `V` has a unique decomposition
as a vector in `L` plus a vector in `M`.  The last two fields say that `H` acts on these two lines
through the characters `χ` and `ψ`.
-/
def SplitsAsCharacters (H : Subgroup G) (ρ : Representation k G V) (χ ψ : H →* kˣ) :
    Prop :=
  ∃ L M : Submodule k V,
    Module.finrank k L = 1 ∧
      Module.finrank k M = 1 ∧
        IsCompl L M ∧ ActsByCharacterOn H ρ L χ ∧ ActsByCharacterOn H ρ M ψ

/--
The conjugate character `(gχ)(h) = χ(g⁻¹hg)`.

Normality of `H` is used by `MulAut.conjNormal` to regard `g⁻¹ * h * g` as an element of `H`,
so that `χ` can be applied to it.
-/
def conjCharacter (H : Subgroup G) [H.Normal] (χ : H →* kˣ) (g : G) : H →* kˣ :=
  χ.comp (MulAut.conjNormal g).symm.toMonoidHom

/--
The restriction of `ρ` to `H` splits as a character plus one of its `G`-conjugates.

This allows the conjugate character to equal the original character; the distinct version below
records the sharper non-scalar alternative.
-/
def SplitsAsConjugateCharacters (H : Subgroup G) [H.Normal]
    (ρ : Representation k G V) : Prop :=
  ∃ χ : H →* kˣ, ∃ g : G, SplitsAsCharacters H ρ χ (conjCharacter H χ g)

/--
The non-scalar splitting alternative: the restriction to `H` is a direct sum
`χ ⊕ gχ`, and the conjugate character `gχ` is not equal to `χ`.
-/
def SplitsAsDistinctConjugateCharacters (H : Subgroup G) [H.Normal]
    (ρ : Representation k G V) : Prop :=
  ∃ χ : H →* kˣ, ∃ g : G,
    conjCharacter H χ g ≠ χ ∧ SplitsAsCharacters H ρ χ (conjCharacter H χ g)

@[simp]
lemma conjCharacter_one (H : Subgroup G) [H.Normal] (χ : H →* kˣ) :
    conjCharacter H χ 1 = χ := by
  change χ.comp (MulAut.conjNormal (1 : G)).symm.toMonoidHom = χ
  rw [show MulAut.conjNormal (1 : G) = 1 by simp]
  rfl

lemma conjCharacter_mul (H : Subgroup G) [H.Normal] (χ : H →* kˣ) (x y : G) :
    conjCharacter H (conjCharacter H χ y) x = conjCharacter H χ (x * y) := by
  ext h
  change
    (χ ((MulAut.conjNormal y).symm ((MulAut.conjNormal x).symm h)) : k) =
      (χ ((MulAut.conjNormal (x * y)).symm h) : k)
  rw [show MulAut.conjNormal (x * y) = MulAut.conjNormal x * MulAut.conjNormal y by
    exact map_mul (MulAut.conjNormal (H := H)) x y]
  rfl

lemma conjCharacter_subgroup_element (H : Subgroup G) [H.Normal] (χ : H →* kˣ) (h₀ : H) :
    conjCharacter H χ h₀ = χ := by
  ext h
  change (χ ((MulAut.conjNormal (h₀ : G)).symm h) : k) = (χ h : k)
  have hunit : χ ((MulAut.conjNormal (h₀ : G)).symm h) = χ h := by
    calc
    χ ((MulAut.conjNormal (h₀ : G)).symm h)
        = χ (h₀⁻¹ * h * h₀) := by
          congr 1
          ext
          simp [MulAut.conjNormal_symm_apply, mul_assoc]
    _ = χ h₀⁻¹ * χ h * χ h₀ := by simp [map_mul, mul_assoc]
    _ = χ h := by
      rw [map_inv]
      simp [mul_comm]
  exact congrArg Units.val hunit

def characterStabilizer (H : Subgroup G) [H.Normal] (χ : H →* kˣ) : Subgroup G where
  carrier := { g | conjCharacter H χ g = χ }
  one_mem' := by simp
  mul_mem' := by
    intro x y hx hy
    change conjCharacter H χ (x * y) = χ
    rw [← conjCharacter_mul]
    rw [hy, hx]
  inv_mem' := by
    intro x hx
    change conjCharacter H χ x⁻¹ = χ
    have hmul :
        conjCharacter H (conjCharacter H χ x) x⁻¹ = conjCharacter H χ (x⁻¹ * x) :=
      conjCharacter_mul H χ x⁻¹ x
    rw [hx] at hmul
    simpa using hmul

@[simp]
lemma mem_characterStabilizer_iff (H : Subgroup G) [H.Normal] (χ : H →* kˣ) (g : G) :
    g ∈ characterStabilizer H χ ↔ conjCharacter H χ g = χ :=
  Iff.rfl

/- In a two-dimensional space, any nonzero proper submodule has dimension one. -/
private lemma finrank_eq_one_of_ne_bot_ne_top [FiniteDimensional k V]
    (hV : Module.finrank k V = 2) {L : Submodule k V} (hL_bot : L ≠ ⊥)
    (hL_top : L ≠ ⊤) :
    Module.finrank k L = 1 := by
  have hlt : Module.finrank k L < 2 := by
    simpa [hV] using Submodule.finrank_lt (K := k) (V := V) hL_top
  have hpos : 1 ≤ Module.finrank k L := Submodule.one_le_finrank_iff.2 hL_bot
  omega

/- A one-dimensional stable subspace carries a character: each restricted endomorphism of the
line is scalar, and uniqueness of that scalar gives the character laws. -/
private lemma exists_character_of_stable_line (H : Subgroup G) (ρ : Representation k G V)
    (L : Submodule k V) (hLdim : Module.finrank k L = 1)
    (hstable : ∀ h : H, ∀ ⦃v : V⦄, v ∈ L → ρ h v ∈ L) :
    ∃ χ : H →* kˣ, ActsByCharacterOn H ρ L χ := by
  classical
  have hL_ne_bot : L ≠ ⊥ := by
    intro hbot
    have hzero : Module.finrank k L = 0 := by rw [hbot, finrank_bot]
    omega
  obtain ⟨v₀, hv₀L, hv₀_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hL_ne_bot
  let lineEnd (h : H) : L →ₗ[k] L := {
    toFun v := ⟨ρ h v.1, hstable h v.2⟩
    map_add' v w := by
      ext
      simp
    map_smul' a v := by
      ext
      simp }
  let scalar : H → k := fun h =>
    Classical.choose (LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one hLdim (lineEnd h))
  have scalar_spec : ∀ h : H, lineEnd h = scalar h • LinearMap.id := fun h =>
    (Classical.choose_spec
      (LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one hLdim (lineEnd h))).1
  have scalar_unique : ∀ (h : H) (c : k), lineEnd h = c • LinearMap.id → scalar h = c := by
    intro h c hc
    exact ((Classical.choose_spec
      (LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one hLdim (lineEnd h))).2 c hc).symm
  have scalar_ne_zero : ∀ h : H, scalar h ≠ 0 := by
    intro h hzero
    let vL : L := ⟨v₀, hv₀L⟩
    have hmap_zero : lineEnd h vL = 0 := by
      rw [scalar_spec h, hzero]
      simp
    have hmap_zero' : ρ h v₀ = 0 := by
      simpa [lineEnd, vL] using congrArg Subtype.val hmap_zero
    exact hv₀_ne ((ρ.apply_bijective h.1).1 (by simpa using hmap_zero'))
  let χ : H →* kˣ := {
    toFun h := Units.mk0 (scalar h) (scalar_ne_zero h)
    map_one' := by
      ext
      change scalar 1 = 1
      exact scalar_unique 1 1 (by
        ext v
        simp [lineEnd])
    map_mul' h₁ h₂ := by
      ext
      change scalar (h₁ * h₂) = scalar h₁ * scalar h₂
      exact scalar_unique (h₁ * h₂) (scalar h₁ * scalar h₂) (by
        ext v
        change ρ (h₁ * h₂) v = (scalar h₁ * scalar h₂) • v
        have h₂_spec : ρ h₂ (v : V) = scalar h₂ • (v : V) := by
          have h := LinearMap.congr_fun (scalar_spec h₂) v
          simpa [lineEnd] using congrArg Subtype.val h
        have h₁_spec : ρ h₁ (ρ h₂ (v : V)) = scalar h₁ • ρ h₂ (v : V) := by
          have h := LinearMap.congr_fun (scalar_spec h₁) (lineEnd h₂ v)
          simpa [lineEnd] using congrArg Subtype.val h
        calc
          ρ (h₁ * h₂) (v : V) = ρ h₁ (ρ h₂ (v : V)) := by
            rw [map_mul, Module.End.mul_apply]
          _ = scalar h₁ • ρ h₂ (v : V) := h₁_spec
          _ = scalar h₁ • (scalar h₂ • (v : V)) := by rw [h₂_spec]
          _ = (scalar h₁ * scalar h₂) • (v : V) := by rw [smul_smul]) }
  refine ⟨χ, ?_⟩
  intro h v hv
  change ρ h v = scalar h • v
  have hspec := LinearMap.congr_fun (scalar_spec h) ⟨v, hv⟩
  simpa [lineEnd] using congrArg Subtype.val hspec

lemma finrank_map_apply_eq (ρ : Representation k G V) (g : G) (L : Submodule k V) :
    Module.finrank k (Submodule.map (ρ g) L) = Module.finrank k L := by
  let e : V ≃ₗ[k] V := LinearEquiv.ofBijective (ρ g) (ρ.apply_bijective g)
  change Module.finrank k (Submodule.map (e : V →ₗ[k] V) L) = Module.finrank k L
  exact LinearEquiv.finrank_map_eq e L

lemma actsByCharacterOn_map_apply (H : Subgroup G) [H.Normal]
    (ρ : Representation k G V) {L : Submodule k V} {χ : H →* kˣ} (g : G)
    (hχL : ActsByCharacterOn H ρ L χ) :
    ActsByCharacterOn H ρ (Submodule.map (ρ g) L) (conjCharacter H χ g) := by
  intro h m hm
  rcases Submodule.mem_map.1 hm with ⟨v, hvL, rfl⟩
  let hgh : H := (MulAut.conjNormal g).symm h
  change ρ h (ρ g v) = (χ hgh : k) • ρ g v
  calc
    ρ h (ρ g v) = ρ ((h : G) * g) v := by
      rw [map_mul, Module.End.mul_apply]
    _ = ρ (g * hgh) v := by
      rw [show (h : G) * g = g * (hgh : G) by
        rw [show (hgh : G) = g⁻¹ * h * g by
          simp [hgh, MulAut.conjNormal_symm_apply]]
        group]
    _ = ρ g (ρ hgh v) := by
      rw [map_mul, Module.End.mul_apply]
    _ = ρ g ((χ hgh : k) • v) := by rw [hχL hgh hvL]
    _ = (χ hgh : k) • ρ g v := by simp

private lemma character_eq_of_common_nonzero_vector (H : Subgroup G)
    (ρ : Representation k G V) {L N : Submodule k V} {χ θ : H →* kˣ}
    (hχL : ActsByCharacterOn H ρ L χ) (hθN : ActsByCharacterOn H ρ N θ)
    {v : V} (hvL : v ∈ L) (hvN : v ∈ N) (hv_ne : v ≠ 0) :
    χ = θ := by
  ext h
  have hχ := hχL h hvL
  have hθ := hθN h hvN
  have hscalar : (χ h : k) • v = (θ h : k) • v := hχ.symm.trans hθ
  have hzero : ((χ h : k) - (θ h : k)) • v = 0 := by
    rw [sub_smul, hscalar, sub_self]
  exact sub_eq_zero.mp ((smul_eq_zero.mp hzero).resolve_right hv_ne)

lemma character_line_eq_left_or_right (H : Subgroup G) (ρ : Representation k G V)
    {χ η θ : H →* kˣ} {L M N : Submodule k V}
    (hχη : χ ≠ η) (hLdim : Module.finrank k L = 1)
    (hMdim : Module.finrank k M = 1) (hNdim : Module.finrank k N = 1)
    (hLM : IsCompl L M) (hχL : ActsByCharacterOn H ρ L χ)
    (hηM : ActsByCharacterOn H ρ M η) (hθN : ActsByCharacterOn H ρ N θ) :
    (N = L ∧ θ = χ) ∨ (N = M ∧ θ = η) := by
  classical
  have hN_ne_bot : N ≠ ⊥ := by
    intro hbot
    have hzero : Module.finrank k N = 0 := by rw [hbot, finrank_bot]
    omega
  obtain ⟨n, hnN, hn_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hN_ne_bot
  obtain ⟨x, y, hxy, -⟩ := Submodule.existsUnique_add_of_isCompl hLM n
  have hNatom : IsAtom N := (Submodule.isAtom_iff_finrank_eq_one).2 hNdim
  have hLatom : IsAtom L := (Submodule.isAtom_iff_finrank_eq_one).2 hLdim
  have hMatom : IsAtom M := (Submodule.isAtom_iff_finrank_eq_one).2 hMdim
  by_cases hy : (y : V) = 0
  · have hx_eq_n : (x : V) = n := by
      simpa [hy] using hxy
    have hxN : (x : V) ∈ N := by
      rw [hx_eq_n]
      exact hnN
    have hx_ne : (x : V) ≠ 0 := by
      rw [hx_eq_n]
      exact hn_ne
    have hNL : N = L := by
      by_contra hne
      have hd := hNatom.disjoint_of_ne hLatom hne
      exact hx_ne (Submodule.disjoint_def.mp hd (x : V) hxN x.2)
    have hθχ : θ = χ :=
      (character_eq_of_common_nonzero_vector H ρ hχL hθN x.2 hxN hx_ne).symm
    exact Or.inl ⟨hNL, hθχ⟩
  · by_cases hx : (x : V) = 0
    · have hy_eq_n : (y : V) = n := by
        simpa [hx] using hxy
      have hyN : (y : V) ∈ N := by
        rw [hy_eq_n]
        exact hnN
      have hy_ne : (y : V) ≠ 0 := by
        rw [hy_eq_n]
        exact hn_ne
      have hNM : N = M := by
        by_contra hne
        have hd := hNatom.disjoint_of_ne hMatom hne
        exact hy_ne (Submodule.disjoint_def.mp hd (y : V) hyN y.2)
      have hθη : θ = η :=
        (character_eq_of_common_nonzero_vector H ρ hηM hθN y.2 hyN hy_ne).symm
      exact Or.inr ⟨hNM, hθη⟩
    · exfalso
      have hdiff : ∃ h : H, χ h ≠ η h := by
        by_contra h
        apply hχη
        ext h₀
        exact not_not.mp (by
          intro hne
          exact h ⟨h₀, fun hunit => hne (congrArg Units.val hunit)⟩)
      obtain ⟨h₀, hχη_ne⟩ := hdiff
      have hcomponents :
          (χ h₀ : k) • (x : V) + (η h₀ : k) • (y : V) =
            (θ h₀ : k) • (x : V) + (θ h₀ : k) • (y : V) := by
        calc
          (χ h₀ : k) • (x : V) + (η h₀ : k) • (y : V)
              = ρ h₀ ((x : V) + (y : V)) := by
                rw [map_add, hχL h₀ x.2, hηM h₀ y.2]
          _ = ρ h₀ n := by rw [hxy]
          _ = (θ h₀ : k) • n := hθN h₀ hnN
          _ = (θ h₀ : k) • ((x : V) + (y : V)) := by rw [hxy]
          _ = (θ h₀ : k) • (x : V) + (θ h₀ : k) • (y : V) := by rw [smul_add]
      have hxscalar : (χ h₀ : k) • (x : V) = (θ h₀ : k) • (x : V) := by
        have hp := congrArg (fun z => L.projection M hLM z) hcomponents
        simpa [map_add, map_smul] using hp
      have hχθ : χ h₀ = θ h₀ := by
        apply Units.ext
        have hzero : ((χ h₀ : k) - (θ h₀ : k)) • (x : V) = 0 := by
          rw [sub_smul, hxscalar, sub_self]
        exact sub_eq_zero.mp ((smul_eq_zero.mp hzero).resolve_right hx)
      have hyscalar : (η h₀ : k) • (y : V) = (θ h₀ : k) • (y : V) := by
        have hp := congrArg (fun z => M.projection L hLM.symm z) hcomponents
        simpa [map_add, map_smul] using hp
      have hηθ : η h₀ = θ h₀ := by
        apply Units.ext
        have hzero : ((η h₀ : k) - (θ h₀ : k)) • (y : V) = 0 := by
          rw [sub_smul, hyscalar, sub_self]
        exact sub_eq_zero.mp ((smul_eq_zero.mp hzero).resolve_right hy)
      exact hχη_ne (hχθ.trans hηθ.symm)

lemma conjugate_character_eq_left_or_right_of_splitting (H : Subgroup G) [H.Normal]
    (ρ : Representation k G V) {χ η : H →* kˣ} {L M : Submodule k V}
    (hχη : χ ≠ η) (hLdim : Module.finrank k L = 1)
    (hMdim : Module.finrank k M = 1) (hLM : IsCompl L M)
    (hχL : ActsByCharacterOn H ρ L χ) (hηM : ActsByCharacterOn H ρ M η) (g : G) :
    conjCharacter H χ g = χ ∨ conjCharacter H χ g = η := by
  have hNdim : Module.finrank k (Submodule.map (ρ g) L) = 1 := by
    rw [finrank_map_apply_eq, hLdim]
  have hNact : ActsByCharacterOn H ρ (Submodule.map (ρ g) L) (conjCharacter H χ g) :=
    actsByCharacterOn_map_apply H ρ g hχL
  rcases character_line_eq_left_or_right H ρ hχη hLdim hMdim hNdim hLM hχL hηM hNact with
    ⟨-, hθχ⟩ | ⟨-, hθη⟩
  · exact Or.inl hθχ
  · exact Or.inr hθη

lemma subgroup_le_characterStabilizer (H : Subgroup G) [H.Normal] (χ : H →* kˣ) :
    H ≤ characterStabilizer H χ := by
  intro h hh
  change conjCharacter H χ h = χ
  simpa using conjCharacter_subgroup_element H χ ⟨h, hh⟩

lemma characterStabilizer_index_eq_two_of_splitting (H : Subgroup G) [H.Normal]
    (ρ : Representation k G V) {χ η : H →* kˣ} {L M : Submodule k V} {a : G}
    (hη : η = conjCharacter H χ a) (hχη : χ ≠ η)
    (hLdim : Module.finrank k L = 1) (hMdim : Module.finrank k M = 1)
    (hLM : IsCompl L M) (hχL : ActsByCharacterOn H ρ L χ)
    (hηM : ActsByCharacterOn H ρ M η) :
    (characterStabilizer H χ).index = 2 := by
  classical
  let S := characterStabilizer H χ
  rw [Subgroup.index_eq_two_iff_exists_notMem_and']
  refine ⟨a⁻¹, ?_, ?_⟩
  · intro ha_inv
    have ha : a ∈ S := by
      simpa [S] using S.inv_mem ha_inv
    exact hχη (ha.symm.trans hη.symm)
  · intro b
    rcases conjugate_character_eq_left_or_right_of_splitting H ρ hχη hLdim hMdim hLM hχL hηM b with
      hb | hb
    · exact Or.inr hb
    · left
      change conjCharacter H χ (a⁻¹ * b) = χ
      rw [← conjCharacter_mul H χ a⁻¹ b, hb, hη]
      simpa using conjCharacter_mul H χ a⁻¹ a

lemma characterStabilizer_eq_of_unique_index_two (H K : Subgroup G) [H.Normal]
    (ρ : Representation k G V) {χ η : H →* kˣ} {L M : Submodule k V} {a : G}
    (hK_unique : ∀ S : Subgroup G, H ≤ S → S.index = 2 → S = K)
    (hη : η = conjCharacter H χ a) (hχη : χ ≠ η)
    (hLdim : Module.finrank k L = 1) (hMdim : Module.finrank k M = 1)
    (hLM : IsCompl L M) (hχL : ActsByCharacterOn H ρ L χ)
    (hηM : ActsByCharacterOn H ρ M η) :
    characterStabilizer H χ = K := by
  exact hK_unique (characterStabilizer H χ) (subgroup_le_characterStabilizer H χ)
    (characterStabilizer_index_eq_two_of_splitting H ρ hη hχη hLdim hMdim hLM hχL hηM)

/--
Core representation-theoretic content of Theorem 1.6, up to the final induced-module comparison.

If `K` is the unique index-two subgroup of `G` containing `H`, and the restriction to `H`
splits as two distinct conjugate character lines `L` and `M`, then `K` stabilizes `L`.  The
restricted action on `L` is therefore given by a character `ψ : K →* kˣ`, and `ψ` extends the
original character `χ` on `H`.
-/
theorem theorem_1_6_core_line_stable_and_extending_character
    (H K : Subgroup G) [H.Normal] (ρ : Representation k G V)
    {χ η : H →* kˣ} {L M : Submodule k V} {a : G}
    (hHK : H ≤ K) (hK_unique : ∀ S : Subgroup G, H ≤ S → S.index = 2 → S = K)
    (hη : η = conjCharacter H χ a) (hχη : χ ≠ η)
    (hLdim : Module.finrank k L = 1) (hMdim : Module.finrank k M = 1)
    (hLM : IsCompl L M) (hχL : ActsByCharacterOn H ρ L χ)
    (hηM : ActsByCharacterOn H ρ M η) :
    ∃ _ : ∀ k : K, ∀ ⦃v : V⦄, v ∈ L → ρ (k : G) v ∈ L,
      ∃ ψ : K →* kˣ,
        ActsByCharacterOn K ρ L ψ ∧
          ∀ h : H, ψ ⟨h, hHK h.2⟩ = χ h := by
  classical
  have hStab_eq :
      characterStabilizer H χ = K :=
    characterStabilizer_eq_of_unique_index_two H K ρ hK_unique hη hχη
      hLdim hMdim hLM hχL hηM
  have hKstable : ∀ k : K, ∀ ⦃v : V⦄, v ∈ L → ρ (k : G) v ∈ L := by
    intro k₀ v hv
    have hkχ : conjCharacter H χ (k₀ : G) = χ := by
      have hkS : (k₀ : G) ∈ characterStabilizer H χ := by
        rw [hStab_eq]
        exact k₀.2
      exact hkS
    have hNdim : Module.finrank k (Submodule.map (ρ (k₀ : G)) L) = 1 := by
      rw [finrank_map_apply_eq, hLdim]
    have hNact :
        ActsByCharacterOn H ρ (Submodule.map (ρ (k₀ : G)) L)
          (conjCharacter H χ (k₀ : G)) :=
      actsByCharacterOn_map_apply H ρ (k₀ : G) hχL
    rcases character_line_eq_left_or_right H ρ hχη hLdim hMdim hNdim hLM hχL hηM hNact with
      ⟨hmap, -⟩ | ⟨-, hkη⟩
    · rw [← hmap]
      exact Submodule.mem_map.2 ⟨v, hv, rfl⟩
    · exfalso
      exact hχη (hkχ.symm.trans hkη)
  obtain ⟨ψ, hψL⟩ := exists_character_of_stable_line (H := K) (ρ := ρ) L hLdim hKstable
  refine ⟨hKstable, ψ, hψL, ?_⟩
  have hL_ne_bot : L ≠ ⊥ := by
    intro hbot
    have hzero : Module.finrank k L = 0 := by rw [hbot, finrank_bot]
    omega
  obtain ⟨v₀, hv₀L, hv₀_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hL_ne_bot
  intro h
  apply Units.ext
  have hψv := hψL ⟨h, hHK h.2⟩ hv₀L
  have hχv := hχL h hv₀L
  have hscalar : (ψ ⟨h, hHK h.2⟩ : k) • v₀ = (χ h : k) • v₀ :=
    hψv.symm.trans hχv
  have hzero : ((ψ ⟨h, hHK h.2⟩ : k) - (χ h : k)) • v₀ = 0 := by
    rw [sub_smul, hscalar, sub_self]
  exact sub_eq_zero.mp ((smul_eq_zero.mp hzero).resolve_right hv₀_ne)

noncomputable def stableLineRepresentation
    (K : Subgroup G) (ρ : Representation k G V) (L : Submodule k V)
    (hKstable : ∀ k : K, ∀ ⦃v : V⦄, v ∈ L → ρ (k : G) v ∈ L) :
    Representation k K L :=
  Representation.subrepresentation (ρ.comp K.subtype) L (by
    intro k v hv
    exact hKstable k hv)

noncomputable def inducedStableLineToAmbientLinear
    (K : Subgroup G) (ρ : Representation k G V) (L : Submodule k V)
    (hKstable : ∀ k : K, ∀ ⦃v : V⦄, v ∈ L → ρ (k : G) v ∈ L) :
    IndV K.subtype (stableLineRepresentation K ρ L hKstable) →ₗ[k] V := by
  let ρL := stableLineRepresentation K ρ L hKstable
  refine Coinvariants.lift _
    (TensorProduct.lift <| Finsupp.linearCombination k fun g : G =>
      (ρ g⁻¹).comp L.subtype) ?_
  intro s
  ext g v
  simp [stableLineRepresentation, map_mul]

@[simp]
lemma inducedStableLineToAmbientLinear_apply_mk
    (K : Subgroup G) (ρ : Representation k G V) (L : Submodule k V)
    (hKstable : ∀ k : K, ∀ ⦃v : V⦄, v ∈ L → ρ (k : G) v ∈ L)
    (g : G) (v : L) :
    inducedStableLineToAmbientLinear K ρ L hKstable
      (IndV.mk K.subtype (stableLineRepresentation K ρ L hKstable) g v) =
        ρ g⁻¹ v := by
  simp [IndV.mk, inducedStableLineToAmbientLinear]

noncomputable def inducedStableLineToAmbient
    (K : Subgroup G) (ρ : Representation k G V) (L : Submodule k V)
    (hKstable : ∀ k : K, ∀ ⦃v : V⦄, v ∈ L → ρ (k : G) v ∈ L) :
    (Representation.ind K.subtype (stableLineRepresentation K ρ L hKstable)).IntertwiningMap ρ where
  toLinearMap := inducedStableLineToAmbientLinear K ρ L hKstable
  isIntertwining' := by
    intro g
    ext h v
    change inducedStableLineToAmbientLinear K ρ L hKstable
        ((Representation.ind K.subtype (stableLineRepresentation K ρ L hKstable)) g
          (IndV.mk K.subtype (stableLineRepresentation K ρ L hKstable) h v)) =
      ρ g (inducedStableLineToAmbientLinear K ρ L hKstable
        (IndV.mk K.subtype (stableLineRepresentation K ρ L hKstable) h v))
    rw [Representation.ind_mk, inducedStableLineToAmbientLinear_apply_mk,
      inducedStableLineToAmbientLinear_apply_mk]
    simp [map_mul]

@[simp]
lemma inducedStableLineToAmbient_apply_mk
    (K : Subgroup G) (ρ : Representation k G V) (L : Submodule k V)
    (hKstable : ∀ k : K, ∀ ⦃v : V⦄, v ∈ L → ρ (k : G) v ∈ L)
    (g : G) (v : L) :
    inducedStableLineToAmbient K ρ L hKstable
      (IndV.mk K.subtype (stableLineRepresentation K ρ L hKstable) g v) =
        ρ g⁻¹ v := by
  exact inducedStableLineToAmbientLinear_apply_mk K ρ L hKstable g v

set_option linter.unnecessarySimpa false in
lemma IndV_mk_subgroup_mul
    (K : Subgroup G) (σ : Representation k K V) (s : K) (g : G) (v : V) :
    IndV.mk K.subtype σ ((s : G) * g) v =
      IndV.mk K.subtype σ g (σ s⁻¹ v) := by
  simpa [IndV.mk] using
    (Coinvariants.mk_tmul_inv
      (ρ := (leftRegular k G).comp K.subtype) (τ := σ)
      (x := Finsupp.single g 1) (y := v) (g := s)).symm

private lemma IndV_mk_finsupp_single
    (K : Subgroup G) (σ : Representation k K V) (g : G) (r : k) (v : V) :
    Coinvariants.mk (Representation.tprod ((leftRegular k G).comp K.subtype) σ)
        (Finsupp.single g r ⊗ₜ[k] v) =
      IndV.mk K.subtype σ g (r • v) := by
  rw [← Finsupp.smul_single_one g r, TensorProduct.smul_tmul]
  simp [IndV.mk]

set_option linter.unnecessarySimpa false in
lemma IndV_exists_mk_one_add_mk_inv_of_index_two
    (K : Subgroup G) (σ : Representation k K V) {t : G}
    (hKindex : K.index = 2) (ht : t ∉ K) (z : IndV K.subtype σ) :
    ∃ x y : V, z = IndV.mk K.subtype σ 1 x + IndV.mk K.subtype σ t⁻¹ y := by
  classical
  refine Coinvariants.induction_on z ?_
  intro q
  induction q using TensorProduct.induction_on with
  | zero =>
      exact ⟨0, 0, by simp⟩
  | tmul f v =>
      induction f using Finsupp.induction_linear with
      | zero =>
          exact ⟨0, 0, by simp⟩
      | add f₁ f₂ hf₁ hf₂ =>
          rcases hf₁ with ⟨x₁, y₁, h₁⟩
          rcases hf₂ with ⟨x₂, y₂, h₂⟩
          refine ⟨x₁ + x₂, y₁ + y₂, ?_⟩
          simp [IndV.mk, TensorProduct.add_tmul, TensorProduct.tmul_add, h₁, h₂]
          abel
      | single g r =>
          have hsingle :
              Coinvariants.mk (Representation.tprod ((leftRegular k G).comp K.subtype) σ)
                  (Finsupp.single g r ⊗ₜ[k] v) =
                IndV.mk K.subtype σ g (r • v) :=
            IndV_mk_finsupp_single K σ g r v
          by_cases hg : g ∈ K
          · let s : K := ⟨g, hg⟩
            refine ⟨σ s⁻¹ (r • v), 0, ?_⟩
            calc
              Coinvariants.mk (Representation.tprod ((leftRegular k G).comp K.subtype) σ)
                    (Finsupp.single g r ⊗ₜ[k] v)
                  = IndV.mk K.subtype σ g (r • v) := hsingle
              _ = IndV.mk K.subtype σ 1 (σ s⁻¹ (r • v)) +
                    IndV.mk K.subtype σ t⁻¹ 0 := by
                    simpa [s] using IndV_mk_subgroup_mul K σ s 1 (r • v)
          · have hgt : g * t ∈ K := by
              rw [Subgroup.mul_mem_iff_of_index_two hKindex]
              exact iff_of_false hg ht
            let s : K := ⟨g * t, hgt⟩
            refine ⟨0, σ s⁻¹ (r • v), ?_⟩
            calc
              Coinvariants.mk (Representation.tprod ((leftRegular k G).comp K.subtype) σ)
                    (Finsupp.single g r ⊗ₜ[k] v)
                  = IndV.mk K.subtype σ g (r • v) := hsingle
              _ = IndV.mk K.subtype σ 1 0 +
                    IndV.mk K.subtype σ t⁻¹ (σ s⁻¹ (r • v)) := by
                    simpa [s, mul_assoc] using
                      IndV_mk_subgroup_mul K σ s t⁻¹ (r • v)
  | add q₁ q₂ hq₁ hq₂ =>
      rcases hq₁ with ⟨x₁, y₁, h₁⟩
      rcases hq₂ with ⟨x₂, y₂, h₂⟩
      refine ⟨x₁ + x₂, y₁ + y₂, ?_⟩
      simp [IndV.mk, TensorProduct.tmul_add, h₁, h₂]
      abel

lemma map_line_eq_right_of_not_mem_characterStabilizer (H : Subgroup G) [H.Normal]
    (ρ : Representation k G V) {χ η : H →* kˣ} {L M : Submodule k V} {t : G}
    (hnot : t ∉ characterStabilizer H χ) (hχη : χ ≠ η)
    (hLdim : Module.finrank k L = 1) (hMdim : Module.finrank k M = 1)
    (hLM : IsCompl L M) (hχL : ActsByCharacterOn H ρ L χ)
    (hηM : ActsByCharacterOn H ρ M η) :
    Submodule.map (ρ t) L = M := by
  have hNdim : Module.finrank k (Submodule.map (ρ t) L) = 1 := by
    rw [finrank_map_apply_eq, hLdim]
  have hNact : ActsByCharacterOn H ρ (Submodule.map (ρ t) L) (conjCharacter H χ t) :=
    actsByCharacterOn_map_apply H ρ t hχL
  rcases character_line_eq_left_or_right H ρ hχη hLdim hMdim hNdim hLM hχL hηM hNact with
    ⟨-, htχ⟩ | ⟨hmap, -⟩
  · exact (hnot htχ).elim
  · exact hmap

set_option linter.unnecessarySimpa false in
lemma inducedStableLineToAmbient_bijective
    (H K : Subgroup G) [H.Normal] (ρ : Representation k G V)
    {χ η : H →* kˣ} {L M : Submodule k V}
    (hStab_eq : characterStabilizer H χ = K) (hKindex : K.index = 2)
    (hχη : χ ≠ η) (hLdim : Module.finrank k L = 1)
    (hMdim : Module.finrank k M = 1) (hLM : IsCompl L M)
    (hχL : ActsByCharacterOn H ρ L χ) (hηM : ActsByCharacterOn H ρ M η)
    (hKstable : ∀ k : K, ∀ ⦃v : V⦄, v ∈ L → ρ (k : G) v ∈ L) :
    Function.Bijective (inducedStableLineToAmbient K ρ L hKstable) := by
  classical
  let σ := stableLineRepresentation K ρ L hKstable
  let Φ := inducedStableLineToAmbient K ρ L hKstable
  obtain ⟨t, htK, -⟩ := (Subgroup.index_eq_two_iff_exists_notMem_and'.mp hKindex)
  have htmap : Submodule.map (ρ t) L = M := by
    apply map_line_eq_right_of_not_mem_characterStabilizer H ρ ?_ hχη hLdim hMdim hLM hχL hηM
    intro htS
    exact htK (by rwa [← hStab_eq])
  have hsurj : Function.Surjective Φ := by
    intro v
    obtain ⟨x, y, hxL, hyM, hxy⟩ :=
      Submodule.codisjoint_iff_exists_add_eq.mp hLM.codisjoint v
    have hy_map : y ∈ Submodule.map (ρ t) L := by
      rwa [htmap]
    rcases Submodule.mem_map.1 hy_map with ⟨y₀, hy₀L, hy₀⟩
    refine ⟨IndV.mk K.subtype σ 1 ⟨x, hxL⟩ +
      IndV.mk K.subtype σ t⁻¹ ⟨y₀, hy₀L⟩, ?_⟩
    calc
      Φ (IndV.mk K.subtype σ 1 ⟨x, hxL⟩ +
          IndV.mk K.subtype σ t⁻¹ ⟨y₀, hy₀L⟩)
          = x + ρ t y₀ := by
            rw [map_add]
            rw [inducedStableLineToAmbient_apply_mk,
              inducedStableLineToAmbient_apply_mk]
            simp
      _ = x + y := by rw [hy₀]
      _ = v := hxy
  have hker : ∀ z : IndV K.subtype σ, Φ z = 0 → z = 0 := by
    intro z hzΦ
    obtain ⟨x, y, hz⟩ := IndV_exists_mk_one_add_mk_inv_of_index_two K σ hKindex htK z
    have hxyzero : (x : V) + ρ t (y : V) = 0 := by
      calc
        (x : V) + ρ t (y : V)
            = Φ (IndV.mk K.subtype σ 1 x + IndV.mk K.subtype σ t⁻¹ y) := by
              rw [map_add]
              rw [inducedStableLineToAmbient_apply_mk,
                inducedStableLineToAmbient_apply_mk]
              simp
        _ = Φ z := by rw [hz]
        _ = 0 := hzΦ
    have hρtyM : ρ t (y : V) ∈ M := by
      rw [← htmap]
      exact Submodule.mem_map.2 ⟨(y : V), y.2, rfl⟩
    have hxM : (x : V) ∈ M := by
      have hx_eq : (x : V) = -ρ t (y : V) := eq_neg_of_add_eq_zero_left hxyzero
      rw [hx_eq]
      exact M.neg_mem hρtyM
    have hx0 : (x : V) = 0 :=
      Submodule.disjoint_def.mp hLM.disjoint (x : V) x.2 hxM
    have hρty0 : ρ t (y : V) = 0 := by
      simpa [hx0] using hxyzero
    have hy0 : (y : V) = 0 :=
      (ρ.apply_bijective t).1 (by simpa using hρty0)
    have hx0' : x = 0 := Subtype.ext hx0
    have hy0' : y = 0 := Subtype.ext hy0
    rw [hz, hx0', hy0']
    simp
  refine ⟨?_, hsurj⟩
  intro z₁ z₂ hz
  have hdiff : Φ (z₁ - z₂) = 0 := by
    rw [map_sub, hz, sub_self]
  exact sub_eq_zero.mp (hker (z₁ - z₂) hdiff)

/--
Theorem 1.6, in the explicit-witness form used throughout this file.

If the restriction to `H` splits as two distinct conjugate character lines `L` and `M`, and `K`
is the unique index-two subgroup of `G` containing `H`, then `L` is `K`-stable, the action of `K`
on `L` is given by a character `ψ` extending `χ`, and the canonical induced map is an isomorphism
of representations.  Mathlib's induced representation convention sends the generator
`IndV.mk g v` to `ρ g⁻¹ v`.
-/
theorem theorem_1_6_induced_form
    (H K : Subgroup G) [H.Normal] (ρ : Representation k G V)
    {χ η : H →* kˣ} {L M : Submodule k V} {a : G}
    (hHK : H ≤ K) (hK_unique : ∀ S : Subgroup G, H ≤ S → S.index = 2 → S = K)
    (hη : η = conjCharacter H χ a) (hχη : χ ≠ η)
    (hLdim : Module.finrank k L = 1) (hMdim : Module.finrank k M = 1)
    (hLM : IsCompl L M) (hχL : ActsByCharacterOn H ρ L χ)
    (hηM : ActsByCharacterOn H ρ M η) :
    ∃ hKstable : ∀ k : K, ∀ ⦃v : V⦄, v ∈ L → ρ (k : G) v ∈ L,
      ∃ ψ : K →* kˣ,
        ActsByCharacterOn K ρ L ψ ∧
          (∀ h : H, ψ ⟨h, hHK h.2⟩ = χ h) ∧
            ∃ e :
              (Representation.ind K.subtype
                (stableLineRepresentation K ρ L hKstable)).Equiv ρ,
              ∀ g : G, ∀ v : L,
                e (IndV.mk K.subtype (stableLineRepresentation K ρ L hKstable) g v) =
                  ρ g⁻¹ v := by
  classical
  have hStab_eq :
      characterStabilizer H χ = K :=
    characterStabilizer_eq_of_unique_index_two H K ρ hK_unique hη hχη
      hLdim hMdim hLM hχL hηM
  have hKindex : K.index = 2 := by
    rw [← hStab_eq]
    exact characterStabilizer_index_eq_two_of_splitting H ρ hη hχη
      hLdim hMdim hLM hχL hηM
  rcases theorem_1_6_core_line_stable_and_extending_character
      H K ρ hHK hK_unique hη hχη hLdim hMdim hLM hχL hηM with
    ⟨hKstable, ψ, hψL, hψ_ext⟩
  have hbij :
      Function.Bijective (inducedStableLineToAmbient K ρ L hKstable) :=
    inducedStableLineToAmbient_bijective H K ρ hStab_eq hKindex hχη
      hLdim hMdim hLM hχL hηM hKstable
  let e :
      (Representation.ind K.subtype (stableLineRepresentation K ρ L hKstable)).Equiv ρ :=
    (inducedStableLineToAmbient K ρ L hKstable).ofBijective hbij
  refine ⟨hKstable, ψ, hψL, hψ_ext, e, ?_⟩
  intro g v
  change inducedStableLineToAmbient K ρ L hKstable
      (IndV.mk K.subtype (stableLineRepresentation K ρ L hKstable) g v) =
    ρ g⁻¹ v
  exact inducedStableLineToAmbient_apply_mk K ρ L hKstable g v

/- The Clifford splitting step for dimension two.

If the restriction to `H` is not irreducible, choose a nonzero proper `H`-stable line `L`.
Since `ρ` is irreducible over `G`, some translate `ρ g L` is not contained in `L`; in dimension
two the distinct lines `L` and `ρ g L` are complementary.  The character on `ρ g L` is the
conjugate of the character on `L`. -/
theorem clifford_splitting_of_not_irreducible_restriction
    (H : Subgroup G) [H.Normal] (ρ : Representation k G V)
    (hV : Module.finrank k V = 2) (hρ : IsIrreducible ρ)
    (hres : ¬ IsIrreducible (ρ.comp H.subtype)) :
    SplitsAsConjugateCharacters H ρ := by
  classical
  haveI : FiniteDimensional k V := Module.finite_of_finrank_eq_succ hV
  haveI : Nontrivial V := Module.nontrivial_of_finrank_eq_succ hV
  rcases exists_nonzero_proper_subrepresentation_of_not_irreducible
      (ρ := ρ.comp H.subtype) hres with
    ⟨L', hL'_bot, hL'_top⟩
  let L : Submodule k V := L'.toSubmodule
  have hL_bot : L ≠ ⊥ := hL'_bot
  have hL_top : L ≠ ⊤ := hL'_top
  have hLdim : Module.finrank k L = 1 :=
    finrank_eq_one_of_ne_bot_ne_top (k := k) (V := V) hV hL_bot hL_top
  have hLstable : ∀ h : H, ∀ ⦃v : V⦄, v ∈ L → ρ h v ∈ L := by
    intro h v hv
    exact L'.apply_mem_toSubmodule h hv
  have hnot_Gstable :
      ¬ ∀ g : G, ∀ ⦃v : V⦄, v ∈ L → ρ g v ∈ L := by
    intro hGstable
    let W : Subrepresentation ρ := {
      toSubmodule := L
      apply_mem_toSubmodule := hGstable }
    exact not_irreducible_of_nonzero_proper_subrepresentation
      (ρ := ρ) W hL_bot hL_top hρ
  obtain ⟨g, hg_not_stable⟩ := not_forall.1 hnot_Gstable
  have hg_witness : ∃ v : V, v ∈ L ∧ ρ g v ∉ L := by
    by_contra hnone
    apply hg_not_stable
    intro v hv
    by_contra hv_image
    exact hnone ⟨v, hv, hv_image⟩
  obtain ⟨v, hvL, hgv_notL⟩ := hg_witness
  let M : Submodule k V := Submodule.map (ρ g) L
  have hM_not_le_L : ¬ M ≤ L := by
    intro hle
    exact hgv_notL (hle (Submodule.mem_map.2 ⟨v, hvL, rfl⟩))
  have hMdim : Module.finrank k M = 1 := by
    let e : V ≃ₗ[k] V := LinearEquiv.ofBijective (ρ g) (ρ.apply_bijective g)
    change Module.finrank k (Submodule.map (e : V →ₗ[k] V) L) = 1
    simpa [hLdim] using (LinearEquiv.finrank_map_eq e L)
  obtain ⟨χ, hχL⟩ := exists_character_of_stable_line (H := H) (ρ := ρ) L hLdim hLstable
  have hdisjoint : Disjoint L M := by
    have hLatom : IsAtom L := (Submodule.isAtom_iff_finrank_eq_one).2 hLdim
    have hMatom : IsAtom M := (Submodule.isAtom_iff_finrank_eq_one).2 hMdim
    exact hLatom.disjoint_of_ne hMatom (by
      intro hLM
      apply hM_not_le_L
      rw [← hLM])
  have hcompl : IsCompl L M := by
    apply (Submodule.isCompl_iff_disjoint L M ?_).2 hdisjoint
    rw [hV, hLdim, hMdim]
  have hχM : ActsByCharacterOn H ρ M (conjCharacter H χ g) := by
    intro h m hm
    rcases Submodule.mem_map.1 hm with ⟨v, hvL, rfl⟩
    let hgh : H := (MulAut.conjNormal g).symm h
    change ρ h (ρ g v) = (χ hgh : k) • ρ g v
    calc
      ρ h (ρ g v) = ρ ((h : G) * g) v := by
        rw [map_mul, Module.End.mul_apply]
      _ = ρ (g * hgh) v := by
        rw [show (h : G) * g = g * (hgh : G) by
          rw [show (hgh : G) = g⁻¹ * h * g by
            simp [hgh]]
          group]
      _ = ρ g (ρ hgh v) := by
        rw [map_mul, Module.End.mul_apply]
      _ = ρ g ((χ hgh : k) • v) := by rw [hχL hgh hvL]
      _ = (χ hgh : k) • ρ g v := by simp
  exact ⟨χ, g, L, M, hLdim, hMdim, hcompl, hχL, hχM⟩

/- If `ρ|H` splits as `χ ⊕ χ`, then every element of `H` acts on all of `V` by the same scalar
`χ h`.  The complementary-line decomposition lets us check this on each summand. -/
private theorem scalar_of_splitsAsSameCharacter (H : Subgroup G) (ρ : Representation k G V)
    (χ : H →* kˣ) (hχ : SplitsAsCharacters H ρ χ χ) :
    ∀ h : H, ρ h = ((χ h : k) • LinearMap.id : V →ₗ[k] V) := by
  rintro h
  rcases hχ with ⟨L, M, -, -, hLM, hL, hM⟩
  ext v
  obtain ⟨x, y, hx, hy, hxy⟩ := Submodule.codisjoint_iff_exists_add_eq.mp hLM.codisjoint v
  calc
    ρ h v = ρ h (x + y) := by rw [hxy]
    _ = ρ h x + ρ h y := map_add (ρ h) x y
    _ = (χ h : k) • x + (χ h : k) • y := by rw [hL h hx, hM h hy]
    _ = (χ h : k) • (x + y) := by rw [smul_add]
    _ = (χ h : k) • v := by rw [hxy]

/- The scalar action case is incompatible with irreducibility of the ambient representation when
`G ⧸ H` is cyclic: `scalar_restriction_not_irreducible` produces a proper `G`-stable line. -/
private theorem scalar_restriction_impossible_of_irreducible [IsAlgClosed k]
    (H : Subgroup G) [H.Normal] [IsCyclic (G ⧸ H)] (ρ : Representation k G V)
    (hV : Module.finrank k V = 2) (hρ : IsIrreducible ρ) :
    ¬ ∃ χ : H →* kˣ,
      ∀ h : H, ρ h = ((χ h : k) • LinearMap.id : V →ₗ[k] V) := by
  rintro ⟨χ, hχ⟩
  haveI : Nontrivial V := Module.nontrivial_of_finrank_eq_succ hV
  exact scalar_restriction_not_irreducible (ρ := ρ) H hV χ hχ hρ

/--
The equal-character splitting alternative cannot occur under the hypotheses of the cyclic quotient
dichotomy.

If `ρ|H` splits as `χ ⊕ χ`, then `scalar_of_splitsAsSameCharacter` turns that splitting into
scalar action of `H` on all of `V`.  The cyclic-quotient theorem `main_theorem_1_3` then makes
`ρ` not irreducible, contradicting `hρ`.
-/
theorem main_theorem_1_8_no_equal_character [IsAlgClosed k]
    (H : Subgroup G) [H.Normal] [IsCyclic (G ⧸ H)]
    (ρ : Representation k G V) (hV : Module.finrank k V = 2) (hρ : IsIrreducible ρ) :
    ¬ ∃ χ : H →* kˣ, SplitsAsCharacters H ρ χ χ := by
  rintro ⟨χ, hχ⟩
  exact scalar_restriction_impossible_of_irreducible (ρ := ρ) H hV hρ
    ⟨χ, scalar_of_splitsAsSameCharacter H ρ χ hχ⟩



end Representation
