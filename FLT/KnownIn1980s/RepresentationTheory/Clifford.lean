import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.GroupAction.ConjAct
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
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
private theorem scalar_restriction_not_irreducible [IsAlgClosed k]
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

/--
Scalar-restriction non-irreducibility for cyclic quotients.

The hypothesis `hχ` means that every element of `H` acts on all of `V` as the scalar
`χ h`.  In informal representation-theoretic language, this is the equal-character case
`ρ|H = χ ⊕ χ`.  Under the cyclic quotient hypothesis, such a representation has a nonzero proper
`G`-stable line, hence is not irreducible.
-/
theorem main_theorem_1_3 [IsAlgClosed k] (H : Subgroup G) [H.Normal]
    [IsCyclic (G ⧸ H)] (ρ : Representation k G V) (hV : Module.finrank k V = 2)
    (χ : H →* kˣ)
    (hχ : ∀ h : H, ρ h = ((χ h : k) • LinearMap.id : V →ₗ[k] V)) :
    ¬ IsIrreducible ρ :=
  scalar_restriction_not_irreducible (ρ := ρ) H hV χ hχ

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

/- The Clifford splitting step for dimension two.

If the restriction to `H` is not irreducible, choose a nonzero proper `H`-stable line `L`.
Since `ρ` is irreducible over `G`, some translate `ρ g L` is not contained in `L`; in dimension
two the distinct lines `L` and `ρ g L` are complementary.  The character on `ρ g L` is the
conjugate of the character on `L`. -/
private theorem clifford_splitting_of_not_irreducible_restriction
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

/--
The main Clifford-type restriction dichotomy for this file.

Let `ρ` be an irreducible two-dimensional representation of `G`, and let `H` be a finite-index
normal subgroup with cyclic quotient.  Then either the restricted representation `ρ|H` is
irreducible, or `ρ|H` splits as the direct sum of a character `χ` and a distinct conjugate
character `gχ`.
-/
theorem main_theorem_1_8 [IsAlgClosed k]
    (H : Subgroup G) [H.Normal] [IsCyclic (G ⧸ H)]
    (ρ : Representation k G V) (hV : Module.finrank k V = 2) (hρ : IsIrreducible ρ) :
    IsIrreducible (ρ.comp H.subtype) ∨ SplitsAsDistinctConjugateCharacters H ρ := by
  by_cases hres : IsIrreducible (ρ.comp H.subtype)
  · exact Or.inl hres
  · right
    rcases clifford_splitting_of_not_irreducible_restriction (ρ := ρ) H hV hρ hres with
      ⟨χ, g, hsplit⟩
    refine ⟨χ, g, ?_, hsplit⟩
    intro hsame
    apply main_theorem_1_8_no_equal_character (ρ := ρ) H hV hρ
    refine ⟨χ, ?_⟩
    rcases hsplit with ⟨L, M, hLdim, hMdim, hLM, hL, hM⟩
    refine ⟨L, M, hLdim, hMdim, hLM, hL, ?_⟩
    intro h v hv
    simpa [hsame] using hM h hv

end Representation
