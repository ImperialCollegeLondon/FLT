/-
Copyright (c) 2024 Mitchell Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mitchell Lee
-/
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.AlgebraicGeometry.PrimeSpectrum.Basic
import Mathlib.RingTheory.Flat.Basic

/-! # Locally free modules
Let $R$ be a commutative ring and let $M$ be an $R$-module. We say that $M$ is *locally free* if
there exist $f_1, \ldots, f_n \in R$, which generate the unit ideal, such that the localization
$M_{f_i}$ is a free $R_{f_i}$-module for all $i$.

We say that $M$ is *locally free of finite rank* if there exist $f_1, \ldots, f_n \in R$, which
generate the unit ideal, such that $M_{f_i}$ is a free $R_{f_i}$-module of finite rank for all $i$.

The main result of this file is [Lemma 10.78.2](https://stacks.math.columbia.edu/tag/00NV) of the
Stacks project, which states that the following are equivalent:

1. $M$ is finitely presented and flat.
2. $M$ is finitely generated and projective.
3. $M$ is a direct summand of a free $R$-module of finite rank.
4. $M$ is finitely presented and stalkwise free (i.e. $M_{\mathfrak{p}}$ is a free
$R_{\mathfrak{p}}$-module for all prime ideals $\mathfrak{p} \subset R$).
5. $M$ is finitely presented and $M_{\mathfrak{m}}$ is a free $R_{\mathfrak{m}}$-module for all
maximal ideals $\mathfrak{m} \subset R$.
6. $M$ is finitely generated and locally free.
7. $M$ is locally free of finite rank.
8. $M$ is finitely generated and stalkwise free, and the rank of $M_{\mathfrak{p}}$ over
$R_{\mathfrak{p}}$ is Zariski-locally constant.

## TODO
- Notation for $R_f$ and $R_{\mathfrak{p}}$
- "Finitely presented" as a predicate
- Localization is exact
- Projectiveness is a local property
- Flatness is a local property
- Direct sum of two modules / split short exact sequences
- Actually prove the lemma

-/

section LocallyFree

variable (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M]

open Module
open scoped Topology

/-- The proposition that $M$ is locally free; that is, there exist $f_1, \ldots, f_n \in R$, which
generate the unit ideal, such that the localization $M_{f_i}$ is a free $R_{f_i}$-module for all
$i$. -/
class LocallyFree : Prop where
  locally_free_at (p : PrimeSpectrum R) : ∃ f : R, p ∈ PrimeSpectrum.basicOpen f ∧
    Free (Localization.Away f) (LocalizedModule (Submonoid.powers f) M)

/-- The proposition that $M$ is locally free of finite rank; that is, there exist
$f_1, \ldots, f_n \in R$, which generate the unit ideal, such that the localization $M_{f_i}$ is a
free $R_{f_i}$-module of finite rank for all $i$. -/
class LocallyFreeOfFiniteRank : Prop where
  locally_free_of_finite_rank_at (p : PrimeSpectrum R) : ∃ f : R, p ∈ PrimeSpectrum.basicOpen f ∧
    Free (Localization.Away f) (LocalizedModule (Submonoid.powers f) M) ∧
    Finite (Localization.Away f) (LocalizedModule (Submonoid.powers f) M)

theorem locallyFreeOfFiniteRank_iff : List.TFAE [
      -- $M$ is finitely presented and flat.
      Nonempty (FinitePresentation R M) ∧ Flat R M,
      -- $M$ is finitely generated and projective.
      Finite R M ∧ Projective R M,
      /- $M$ is a direct summand of a free module of finite rank.
        The `sorry` is here because $M \oplus M'$ doesn't yet have the structure of an $R$-module.
        This should certainly be fixed. -/
      ∃ (M' : Type _) (_ : AddCommGroup M') (_ : Module R M'),
        @Free R (M ⊕ M') inferInstance sorry sorry ∧ @Finite R (M ⊕ M') inferInstance sorry sorry,
      /- $M$ is finitely presented and stalkwise free (i.e. $M_{\mathfrak{p}}$ is a free
        $R_{\mathfrak{p}}$-module for all prime ideals $\mathfrak{p} \subset R$). -/
      Nonempty (FinitePresentation R M) ∧ ∀ p : PrimeSpectrum R,
        Free (Localization.AtPrime p.asIdeal) (LocalizedModule p.asIdeal.primeCompl M),
      /- $M$ is finitely presented and $M_{\mathfrak{m}}$ is a free $R_{\mathfrak{m}}$-module for
        all maximal ideals $\mathfrak{m} \subset R$. -/
      Nonempty (FinitePresentation R M) ∧ ∀ m : PrimeSpectrum R, m.asIdeal.IsMaximal →
        Free (Localization.AtPrime m.asIdeal) (LocalizedModule m.asIdeal.primeCompl M),
      -- $M$ is finitely generated and locally free.
      Finite R M ∧ LocallyFree R M,
      -- $M$ is locally free of finite rank.
      LocallyFreeOfFiniteRank R M,
      /- $M$ is finitely generated and stalkwise free, and the rank of $M_{\mathfrak{p}}$ over
        $R_{\mathfrak{p}}$ is Zariski-locally constant.-/
      ∀ p : PrimeSpectrum R, ∃ n : ℕ, ∀ᶠ q in 𝓝 p, Nonempty (Basis (Fin n) R M)] := by
  sorry

end LocallyFree
