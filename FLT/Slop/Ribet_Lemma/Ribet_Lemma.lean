/-
Copyright (c) 2026 Bryan Hu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Hu
-/
module

public import FLT.Slop.Ribet_Lemma.Brauer_Nesbitt

/-!
# Ribet's lemma (Ribet, Invent. Math. 34 (1976), Prop. 2.1)

Sections 8–10, and the goal, of this development (see the overview in the
header of `stable_lattices.lean`).  The reference is

  K. A. Ribet, *A modular construction of unramified p-extensions of
  `Q(μₚ)`*, Invent. Math. 34 (1976), 151–162; Proposition 2.1, p. 154.

In the notation of §1–7:

  Let `O` be a *complete* DVR with fraction field `K` and residue field `F`,
  and `ρ` an irreducible 2-dimensional representation of a group `G` over
  `K` with a stable lattice `Λ₀` whose reduction has semisimplification
  `φ₁ ⊕ φ₂`.  Then some stable lattice has reduction a **non-split**
  extension with sub `φ₁` and quotient `φ₂` — in the matrix form of the
  paper, "of the form `(φ₁ *; 0 φ₂)` but not semi-simple".  Applying the
  theorem with `φ₁, φ₂` swapped (via `HasSemisimplification.symm`) realizes
  the other ordering, and by §7 the hypothesis may be checked on any single
  stable lattice.

Compared to the paper, the statement is proved for an arbitrary complete DVR
(Ribet works over the ring of integers of a finite extension of `ℚ_p`; the
proof only uses completeness), and Ribet's standing hypothesis that `G`
leaves some lattice stable is an explicit argument `Λ₀` here — §4 produces
one when `G` is compact and the stabilizer of a lattice is open, matching
the parenthetical remark on p. 154 of the paper.

Contents:

* §8 — the completeness input: a finite free module over a precomplete ring
  is precomplete (`isPrecomplete_of_free`, missing from Mathlib as of July
  2026), and the chain lemma `exists_stable_line_of_chain`: an infinite
  straight chain of neighbors would produce a `ρ`-stable line.  This is the
  lattice form of the convergence of the matrices `Mᵢ = (1 tᵢ; 0 1)` on
  p. 155 of the paper.
* §9 — Ribet's lemma, `ribet_lemma_slop` (the slop proof of
  `StableLattice.ribet_lemma` in `FLT.KnownIn1980s.Ribet_Lemma.Defs`).
* §10 — remarks.

Conventions: irreducibility is Mathlib's `Representation.IsIrreducible`,
that is, `IsSimpleOrder (Subrepresentation ρ)`.  Completeness of `O` is
`IsAdicComplete (maximalIdeal O) O`; §8 is the only place in the development
where it is used.  The whole development is `sorry`-free.
-/

@[expose] public section

open Pointwise IsLocalRing

namespace StableLattice

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
variable {K : Type*} [Field K] [Algebra O K] [IsFractionRing O K]
variable {V : Type*} [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V]
variable [FiniteDimensional K V]
variable {G : Type*} [Group G]

/-! ## 8. Completeness: from an infinite walk to a stable line

The lattice-modification engine lives in §6 (`Brauer_Nesbitt.lean`).  Here
completeness of `O` enters, and only here.  An infinite *straight* chain of
neighbors `f (n+1) = preimageLattice (f n) Lₙ` — straight meaning
`f (n+2) ≠ 𝔪 f n`, i.e. no step undoes the previous one — satisfies
`f n = f (n+1) ⊔ 𝔪ⁿ f 0`, so approximations `xₙ ∈ f n` can be chosen that
form an `𝔪`-adic Cauchy sequence inside `f 0`; the limit is a nonzero
element of `⋂ₙ f n`, whose `K`-span is a `ρ`-stable line.  In
`ribet_lemma_slop` this is ruled out by irreducibility, which is what forces
the walk of §9 to terminate. -/

section Completeness

variable {ρ : Representation K G V}

omit [IsDomain O] [IsDiscreteValuationRing O] [IsFractionRing O K]
  [FiniteDimensional K V] in
/-- Missing Mathlib API (stated here in the generality we need): a finite free
module over a ring that is precomplete for an ideal `I` is itself precomplete
for `I`.  Limits are taken coordinatewise in a basis. -/
theorem isPrecomplete_of_free {M : Type*} [AddCommGroup M] [Module O M]
    [Module.Finite O M] [Module.Free O M] (I : Ideal O) [IsPrecomplete I O] :
    IsPrecomplete I M := by
  constructor
  intro y hy
  classical
  let ι := Module.Free.ChooseBasisIndex O M
  let b : Module.Basis ι O M := Module.Free.chooseBasis O M
  have hIT : ∀ J : Ideal O, (J • ⊤ : Submodule O O) = J := fun J =>
    le_antisymm (Submodule.smul_le.mpr fun r hr m _ => by
        simpa [smul_eq_mul] using J.mul_mem_right m hr)
      (fun r hr => by
        simpa using Submodule.smul_mem_smul hr
          (Submodule.mem_top : (1 : O) ∈ (⊤ : Submodule O O)))
  -- the coordinate sequences are Cauchy
  have hcoord : ∀ i, ∃ Li : O,
      ∀ n, b.repr (y n) i ≡ Li [SMOD (I ^ n • ⊤ : Submodule O O)] := by
    intro i
    refine IsPrecomplete.prec inferInstance ?_
    intro m n hmn
    have hsub := hy hmn
    rw [SModEq.sub_mem] at hsub ⊢
    have hmap : b.repr (y m) i - b.repr (y n) i = b.repr (y m - y n) i := by
      rw [map_sub, Finsupp.sub_apply]
    rw [hmap]
    have hc : (I ^ m • ⊤ : Submodule O M).map
        ((Finsupp.lapply i).comp (b.repr : M →ₗ[O] (ι →₀ O)))
        ≤ (I ^ m • ⊤ : Submodule O O) := by
      rw [Submodule.map_smul'']
      exact smul_mono_right _ le_top
    exact hc (Submodule.mem_map_of_mem hsub)
  choose Li hLi using hcoord
  refine ⟨∑ i, Li i • b i, fun n => ?_⟩
  rw [SModEq.sub_mem]
  have hsum : y n - ∑ i, Li i • b i = ∑ i, (b.repr (y n) i - Li i) • b i := by
    conv_lhs => rw [← b.sum_repr (y n)]
    rw [← Finset.sum_sub_distrib]
    simp only [← sub_smul]
  rw [hsum]
  refine Submodule.sum_mem _ fun i _ => ?_
  have h1 := hLi i n
  rw [SModEq.sub_mem, hIT] at h1
  exact Submodule.smul_mem_smul h1 Submodule.mem_top

omit [FiniteDimensional K V] in
/-- **Where completeness enters.**  A "straight" infinite chain of neighboring
stable lattices (no backtracking: `f (n + 2) ≠ 𝔪 • f n`) yields a `ρ`-stable
`K`-line — which `ribet_lemma_slop` rules out by irreducibility.  A compatible
sequence of approximations is chosen along the chain, and its `𝔪`-adic limit
is a nonzero element of the intersection of the chain, whose `K`-span is the
line.  Mathlib provides the Hausdorff half of completeness for finite modules
(`Mathlib.RingTheory.AdicCompletion.Noetherian`); the precompleteness half is
`isPrecomplete_of_free` above. -/
theorem exists_stable_line_of_chain
    [IsAdicComplete (maximalIdeal O) O]
    (hdim : Module.finrank K V = 2)
    (f : ℕ → Submodule O V) (hf : ∀ n, IsStableLattice ρ (f n))
    (hstep : ∀ n, ∃ L : Submodule (ResidueField O) (Reduction O V (f n)),
      Module.finrank (ResidueField O) L = 1 ∧ f (n + 1) = preimageLattice (f n) L)
    (hstraight : ∀ n, f (n + 2) ≠ maximalIdeal O • f n) :
    ∃ W : Submodule K V, Module.finrank K W = 1 ∧ ∀ g : G, W.map (ρ g) ≤ W := by
  classical
  haveI : FiniteDimensional K V := Module.finite_of_finrank_pos (by omega)
  choose Lst hLst1 hLstep using hstep
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hπK : algebraMap O K π ≠ 0 := fun h0 =>
    hπ.ne_zero (IsFractionRing.injective O K (by rw [h0, map_zero]))
  have h𝔪pow : ∀ (j : ℕ) (N : Submodule O V),
      maximalIdeal O ^ j • N = (π ^ j) • N := by
    intro j N
    rw [hπ.maximalIdeal_eq, Ideal.span_singleton_pow,
      Submodule.ideal_span_singleton_smul]
  have hunit : ∀ (u₀ : Oˣ) (N : Submodule O V), (u₀ : O) • N = N := by
    intro u₀ N
    refine le_antisymm ?_ fun x hx => ?_
    · rintro _ ⟨z, hz, rfl⟩
      exact N.smul_mem _ hz
    · refine ⟨(u₀⁻¹ : Oˣ) • x, N.smul_mem _ hx, ?_⟩
      change (u₀ : O) • ((u₀⁻¹ : Oˣ) • x) = x
      rw [Units.smul_def, smul_smul]
      simp
  -- basic chain facts
  have hle : ∀ n, f (n + 1) ≤ f n := fun n => by
    rw [hLstep n]; exact preimageLattice_le _ _
  have hsm : ∀ n, maximalIdeal O • f n ≤ f (n + 1) := fun n => by
    rw [hLstep n]; exact smul_le_preimageLattice _ _
  have hle0 : ∀ n, f n ≤ f 0 := by
    intro n
    induction n with
    | zero => exact le_rfl
    | succ m ihm => exact (hle m).trans ihm
  have hpow0 : ∀ n, maximalIdeal O ^ n • f 0 ≤ f n := by
    intro n
    induction n with
    | zero => rw [pow_zero, Ideal.one_eq_top, Submodule.top_smul]
    | succ m ihm =>
      rw [pow_succ, mul_comm, Submodule.mul_smul]
      exact (smul_mono_right _ ihm).trans (hsm m)
  have hproper : ∀ n, f (n + 1) ≠ f n := by
    intro n hEq
    haveI := (hf n).isLattice
    have hpre : preimageLattice (f n) (Lst n) = f n := (hLstep n).symm.trans hEq
    have hLtop : Lst n = ⊤ := by
      rw [eq_top_iff]
      rintro ξ -
      obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ ξ
      refine (mem_preimageLattice z).mp ?_
      rw [hpre]
      exact z.2
    have hd := hLst1 n
    rw [hLtop, finrank_top, finrank_reduction (K := K) (f n), hdim] at hd
    omega
  -- straightness as an identity: `f (n+1) = f (n+2) ⊔ 𝔪 f n`
  have hstr : ∀ n, f (n + 1) = f (n + 2) ⊔ maximalIdeal O • f n := by
    intro n
    haveI := (hf (n + 1)).isLattice
    have hdim1 : Module.finrank (ResidueField O) (Reduction O V (f (n + 1))) = 2 := by
      rw [finrank_reduction (K := K), hdim]
    haveI : FiniteDimensional (ResidueField O) (Reduction O V (f (n + 1))) :=
      Module.finite_of_finrank_pos (by omega)
    -- the images of `f (n+2)` and of `𝔪 f n` in the reduction of `f (n+1)`
    have hA_eq : reductionImage O (hle (n + 1)) = Lst (n + 1) := by
      have h1 : reductionImage O (hle (n + 1))
          = reductionImage O (preimageLattice_le (f (n + 1)) (Lst (n + 1))) := by
        congr 1
        exact hLstep (n + 1)
      rw [h1, reductionImage_preimageLattice]
    have hA1 : Module.finrank (ResidueField O) ↥(reductionImage O (hle (n + 1))) = 1 := by
      rw [hA_eq]; exact hLst1 (n + 1)
    have hB_ne_bot : reductionImage O (hsm n) ≠ ⊥ := by
      intro hb
      have h1 : maximalIdeal O • f n ≤ maximalIdeal O • f (n + 1) :=
        (reductionImage_eq_bot _).mp hb
      have h2 : f n ≤ f (n + 1) := by
        intro x hx
        have hπx : π • x ∈ maximalIdeal O • f n := by
          rw [hπ.maximalIdeal_eq, Submodule.ideal_span_singleton_smul]
          exact Submodule.smul_mem_pointwise_smul x π _ hx
        have h3 := h1 hπx
        rw [hπ.maximalIdeal_eq, Submodule.ideal_span_singleton_smul] at h3
        obtain ⟨z, hz, hxz⟩ := h3
        have hzx : z = x := by
          apply smul_right_injective V hπK
          change algebraMap O K π • z = algebraMap O K π • x
          rw [algebraMap_smul, algebraMap_smul]
          exact hxz
        rwa [← hzx]
      exact hproper n (le_antisymm (hle n) h2)
    have hAB : reductionImage O (hle (n + 1)) ≠ reductionImage O (hsm n) := by
      intro hab
      apply hstraight n
      have hpb : preimageLattice (f (n + 1)) (reductionImage O (hsm n))
          = maximalIdeal O • f n := by
        rw [preimageLattice_reductionImage]
        exact sup_eq_left.mpr (smul_mono_right _ (hle n))
      have hpa : preimageLattice (f (n + 1)) (reductionImage O (hle (n + 1)))
          = f (n + 2) := by
        rw [preimageLattice_reductionImage]
        exact sup_eq_left.mpr (hsm (n + 1))
      rw [← hpa, hab, hpb]
    have hsupAB : reductionImage O (hle (n + 1)) ⊔ reductionImage O (hsm n) = ⊤ := by
      have hBA : ¬ reductionImage O (hsm n) ≤ reductionImage O (hle (n + 1)) := by
        intro hba
        have hBpos : 0 < Module.finrank (ResidueField O) ↥(reductionImage O (hsm n)) :=
          Module.finrank_pos_iff.mpr (Submodule.nontrivial_iff_ne_bot.mpr hB_ne_bot)
        exact hAB (Submodule.eq_of_le_of_finrank_le hba (by rw [hA1]; omega)).symm
      have hlt : reductionImage O (hle (n + 1))
          < reductionImage O (hle (n + 1)) ⊔ reductionImage O (hsm n) := by
        rcases lt_or_eq_of_le
          (le_sup_left : reductionImage O (hle (n + 1)) ≤ _ ⊔ reductionImage O (hsm n))
          with hcase | hcase
        · exact hcase
        · exfalso
          apply hBA
          rw [hcase]
          exact le_sup_right
      have h2 := Submodule.finrank_lt_finrank_of_lt hlt
      rw [hA1] at h2
      have hle2 := Submodule.finrank_le
        (reductionImage O (hle (n + 1)) ⊔ reductionImage O (hsm n))
      rw [hdim1] at hle2
      exact Submodule.eq_top_of_finrank_eq (by rw [hdim1]; omega)
    refine le_antisymm ?_ (sup_le (hle (n + 1)) (hsm n))
    intro w hw
    have hwT : (Submodule.Quotient.mk (⟨w, hw⟩ : f (n + 1)) :
        Reduction O V (f (n + 1))) ∈ reductionImage O (hle (n + 1)) ⊔
          reductionImage O (hsm n) := by
      rw [hsupAB]; trivial
    obtain ⟨α, hα, β, hβ, hab⟩ := Submodule.mem_sup.mp hwT
    obtain ⟨ξa, rfl⟩ := hα
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ ξa
    obtain ⟨ξb, rfl⟩ := hβ
    obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ ξb
    rw [reductionMap_mk, reductionMap_mk, ← Submodule.Quotient.mk_add] at hab
    have hd := (Submodule.Quotient.eq _).mp hab
    rw [mem_smul_top_iff] at hd
    have hd' : ((a : V) + (c : V)) - w ∈ maximalIdeal O • f n := by
      refine (smul_mono_right _ (hle n)) ?_
      simpa using hd
    have hw_eq : w = (a : V) + ((c : V) - (((a : V) + (c : V)) - w)) := by abel
    rw [hw_eq]
    exact Submodule.add_mem_sup a.2 (Submodule.sub_mem _ c.2 hd')
  -- the iterated identity `f n = f (n+1) ⊔ 𝔪^n f 0`, and its consequence
  have hiter : ∀ n, f n = f (n + 1) ⊔ maximalIdeal O ^ n • f 0 := by
    intro n
    induction n with
    | zero =>
      rw [pow_zero, Ideal.one_eq_top, Submodule.top_smul]
      exact (sup_eq_right.mpr (hle 0)).symm
    | succ m ihm =>
      have hthis := hstr m
      rw [ihm, Submodule.smul_sup, ← Submodule.mul_smul, ← pow_succ'] at hthis
      rw [← sup_assoc, sup_eq_left.mpr (hsm (m + 1))] at hthis
      exact hthis
  have hnot : ∀ n, ¬ maximalIdeal O ^ n • f 0 ≤ f (n + 1) := by
    intro n hcon
    exact hproper n ((hiter n).trans (sup_eq_left.mpr hcon)).symm
  -- choose approximations along the chain
  have hchoice : ∀ n (xcur : V), xcur ∈ f n →
      ∃ xnext ∈ f (n + 1), xcur - xnext ∈ maximalIdeal O ^ n • f 0 := by
    intro n xcur hx
    rw [hiter n] at hx
    obtain ⟨z, hz, m, hm, hzm⟩ := Submodule.mem_sup.mp hx
    refine ⟨z, hz, ?_⟩
    rw [← hzm]
    simpa using hm
  have hstart : ∃ v, v ∈ f 1 ∧ v ∉ maximalIdeal O • f 0 := by
    have hL0 : Lst 0 ≠ ⊥ := by
      intro hb
      have h1 := hLst1 0
      rw [hb, finrank_bot] at h1
      omega
    obtain ⟨ξ, hξ, hξ0⟩ := (Submodule.ne_bot_iff _).mp hL0
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ ξ
    refine ⟨(z : V), ?_, ?_⟩
    · rw [hLstep 0]
      exact (mem_preimageLattice z).mpr hξ
    · intro hmem
      exact hξ0 ((Submodule.Quotient.mk_eq_zero _).mpr
        ((mem_smul_top_iff _ _ _).mpr hmem))
  -- the recursive sequence of approximations, `T n ∈ f (n+1)`
  let T : (n : ℕ) → {v : V // v ∈ f (n + 1)} := fun n => Nat.rec
    ⟨Classical.choose hstart, (Classical.choose_spec hstart).1⟩
    (fun m prev => ⟨Classical.choose (hchoice (m + 1) prev.1 prev.2),
      (Classical.choose_spec (hchoice (m + 1) prev.1 prev.2)).1⟩) n
  have hTdiff : ∀ n, (T n).1 - (T (n + 1)).1 ∈ maximalIdeal O ^ (n + 1) • f 0 :=
    fun n => (Classical.choose_spec (hchoice (n + 1) (T n).1 (T n).2)).2
  -- pass to the fixed lattice `f 0` and take the `𝔪`-adic limit
  haveI := (hf 0).isLattice
  haveI : IsPrecomplete (maximalIdeal O) ↥(f 0) :=
    isPrecomplete_of_free (maximalIdeal O)
  let Y : ℕ → ↥(f 0) := fun n => ⟨(T n).1, hle0 (n + 1) (T n).2⟩
  have hYstep : ∀ n, Y n - Y (n + 1)
      ∈ (maximalIdeal O ^ (n + 1) • ⊤ : Submodule O ↥(f 0)) := by
    intro n
    rw [mem_smul_top_iff]
    simpa using hTdiff n
  have hYc : ∀ {m n}, m ≤ n →
      Y m ≡ Y n [SMOD (maximalIdeal O ^ m • ⊤ : Submodule O ↥(f 0))] := by
    intro m n hmn
    induction n, hmn using Nat.le_induction with
    | base => rfl
    | succ n hmn ihn =>
      refine ihn.trans ?_
      rw [SModEq.sub_mem]
      exact Submodule.smul_mono_left (Ideal.pow_le_pow_right (by omega)) (hYstep n)
  obtain ⟨Lm, hLm⟩ := IsPrecomplete.prec inferInstance hYc
  have hxf : ∀ n, (Lm : V) ∈ f n := by
    intro n
    have h1 := hLm n
    rw [SModEq.sub_mem, mem_smul_top_iff] at h1
    have h2 : (Lm : V) = (T n).1 - (((T n).1 : V) - Lm) := by abel
    rw [h2]
    exact Submodule.sub_mem _ ((hle n) (T n).2) (hpow0 n (by simpa using h1))
  have hx1 : (Lm : V) ∉ maximalIdeal O • f 0 := by
    intro hmem
    have h1 := hLm 1
    rw [SModEq.sub_mem, mem_smul_top_iff] at h1
    have h2 : (T 0).1 ∈ maximalIdeal O • f 0 := by
      have hd0 := hTdiff 0
      have heq : (T 0).1 = ((T 0).1 - (T 1).1) + (((T 1).1 : V) - Lm) + Lm := by
        abel
      rw [heq]
      refine Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) hmem
      · simpa [pow_one] using hd0
      · simpa [pow_one] using h1
    exact (Classical.choose_spec hstart).2 h2
  have hx0 : (Lm : V) ≠ 0 := by
    intro h0
    apply hx1
    rw [h0]
    exact Submodule.zero_mem _
  -- the `K`-span of the intersection of the chain is the desired stable line
  have hxN : (Lm : V) ∈ (⨅ n, f n : Submodule O V) :=
    (Submodule.mem_iInf _).mpr hxf
  refine ⟨Submodule.span K ((⨅ n, f n : Submodule O V) : Set V), ?_, ?_⟩
  · have hWne : Submodule.span K ((⨅ n, f n : Submodule O V) : Set V) ≠ ⊥ := by
      intro hb
      have hmem : (Lm : V) ∈ Submodule.span K ((⨅ n, f n : Submodule O V) : Set V) :=
        Submodule.subset_span hxN
      rw [hb] at hmem
      exact hx0 ((Submodule.mem_bot K).mp hmem)
    have hWnetop : Submodule.span K ((⨅ n, f n : Submodule O V) : Set V) ≠ ⊤ := by
      intro ht
      haveI : IsNoetherian O ↥(f 0) :=
        isNoetherian_of_isNoetherianRing_of_finite O ↥(f 0)
      haveI : IsNoetherian O ↥(⨅ n, f n : Submodule O V) :=
        isNoetherian_of_le (iInf_le f 0)
      haveI hNlat : Submodule.IsLattice K (⨅ n, f n : Submodule O V) :=
        ⟨by rw [← Module.Finite.iff_fg]; infer_instance, ht⟩
      obtain ⟨b, hb0, hble⟩ :=
        Submodule.IsLattice.exists_smul_le (K := K) (⨅ n, f n : Submodule O V) (f 0)
      obtain ⟨s, u, hbu⟩ := IsDiscreteValuationRing.associated_pow_irreducible hb0 hπ
      have hps : maximalIdeal O ^ s • f 0 ≤ (⨅ n, f n : Submodule O V) := by
        rw [h𝔪pow, ← hbu, mul_smul, hunit u]
        exact hble
      exact hnot s (hps.trans (iInf_le f (s + 1)))
    have hfr := Submodule.finrank_le
      (Submodule.span K ((⨅ n, f n : Submodule O V) : Set V))
    rw [hdim] at hfr
    have hpos : 0 < Module.finrank K
        ↥(Submodule.span K ((⨅ n, f n : Submodule O V) : Set V)) :=
      Module.finrank_pos_iff.mpr (Submodule.nontrivial_iff_ne_bot.mpr hWne)
    have hne2 : Module.finrank K
        ↥(Submodule.span K ((⨅ n, f n : Submodule O V) : Set V)) ≠ 2 := by
      intro h2
      exact hWnetop (Submodule.eq_top_of_finrank_eq (by rw [h2, hdim]))
    omega
  · intro g
    rw [Submodule.map_span]
    refine Submodule.span_mono ?_
    rintro _ ⟨v, hv, rfl⟩
    have hvN : ∀ n, v ∈ f n := (Submodule.mem_iInf _).mp hv
    refine (Submodule.mem_iInf _).mpr fun n => ?_
    have hstable := (hf n).stable g
    rw [← hstable]
    exact Submodule.mem_map_of_mem (hvN n)

omit [IsFractionRing O K] [FiniteDimensional K V] in
variable (ρ) in
/-- The data carried along the walk in the proof of `ribet_lemma_slop`: a
stable lattice whose reduction realizes the ordering sub-`φ₁`/quotient-`φ₂`,
with a marked line witnessing it. -/
private def WalkPack (φ₁ φ₂ : G →* (ResidueField O)ˣ) : Type _ :=
  Σ' (Λ : Submodule O V) (h : IsStableLattice ρ Λ)
      (L : Submodule (ResidueField O) (Reduction O V Λ)),
    Module.finrank (ResidueField O) L = 1 ∧
    (∀ g : G, ∀ x ∈ L, reducedRep ρ Λ h.stable g x = (φ₁ g : ResidueField O) • x) ∧
    (∀ g : G, ∀ x, reducedRep ρ Λ h.stable g x - (φ₂ g : ResidueField O) • x ∈ L)

end Completeness

/-! ## 9. Ribet's lemma -/

omit [FiniteDimensional K V] in
/-- **Ribet's lemma** (Ribet 1976, Proposition 2.1).

`O` a complete DVR, `ρ` a 2-dimensional irreducible representation of `G` over
`K = Frac O`, and `Λ₀` a stable lattice whose reduction has semisimplification
`φ₁ ⊕ φ₂`.  Then there is a stable lattice whose reduction is a **non-split**
extension with sub `φ₁` and quotient `φ₂`.

Proof: by contradiction, walking through neighbors.  If `hss` provides the
wrong ordering, one preliminary neighbor step swaps it (key computation,
§6).  If every reduction realizing the ordering were split, one could step
forever along splitting lines avoiding the marked sub-line (`WalkPack`),
producing a straight infinite chain; §8 would turn it into a `ρ`-stable
line, contradicting irreducibility.  So the walk terminates, at a stable
lattice whose reduction is the desired non-split extension.

Slop proof of `StableLattice.ribet_lemma` in
`FLT.KnownIn1980s.Ribet_Lemma.Defs`. -/
theorem ribet_lemma_slop [IsAdicComplete (maximalIdeal O) O]
    (ρ : Representation K G V) [ρ.IsIrreducible]
    (hdim : Module.finrank K V = 2)
    (Λ₀ : Submodule O V) (h₀ : IsStableLattice ρ Λ₀)
    (φ₁ φ₂ : G →* (ResidueField O)ˣ)
    (hss : HasSemisimplification (reducedRep ρ Λ₀ h₀.stable) φ₁ φ₂) :
    ∃ (Λ : Submodule O V) (h : IsStableLattice ρ Λ),
      IsExtensionOf (reducedRep ρ Λ h.stable) φ₁ φ₂ ∧
      ¬ IsSplitExtensionOf (reducedRep ρ Λ h.stable) φ₁ φ₂ := by
  classical
  by_contra hcon
  push Not at hcon
  -- `hcon`: the reduction of every stable lattice realizing the ordering splits.
  -- The walk step: replace the lattice by the neighbor along a splitting line
  -- avoiding the marked one
  have step : ∀ p : WalkPack ρ φ₁ φ₂, ∃ q : WalkPack ρ φ₁ φ₂,
      (∃ C : Submodule (ResidueField O) (Reduction O V p.1),
        Module.finrank (ResidueField O) C = 1 ∧
        q.1 = preimageLattice p.1 C) ∧
      q.1 ≠ preimageLattice p.1 p.2.2.1 ∧
      preimageLattice q.1 q.2.2.1 = maximalIdeal O • p.1 := by
    rintro ⟨Λp, hp, Lp, hLp1, hLpchar, hLpquot⟩
    haveI := hp.isLattice
    have hdimp : Module.finrank (ResidueField O) (Reduction O V Λp) = 2 := by
      rw [finrank_reduction (K := K), hdim]
    haveI : FiniteDimensional (ResidueField O) (Reduction O V Λp) :=
      Module.finite_of_finrank_pos (by omega)
    have hsplit : IsSplitExtensionOf (reducedRep ρ Λp hp.stable) φ₁ φ₂ :=
      hcon Λp hp ⟨Lp, hLp1, hLpchar, hLpquot⟩
    -- select a stepping line `C ≠ Lp` realizing the opposite ordering
    have hCex : ∃ C : Submodule (ResidueField O) (Reduction O V Λp),
        Module.finrank (ResidueField O) C = 1 ∧
        (∀ g : G, ∀ x ∈ C, reducedRep ρ Λp hp.stable g x
          = (φ₂ g : ResidueField O) • x) ∧
        (∀ g : G, ∀ x, reducedRep ρ Λp hp.stable g x
          - (φ₁ g : ResidueField O) • x ∈ C) ∧
        C ≠ Lp := by
      by_cases hφ : φ₁ = φ₂
      · -- equal characters: the split action is scalar, any line ≠ `Lp` works
        subst hφ
        obtain ⟨L₁, L₂, h₁, hact₁, hact₂, hcompl⟩ := hsplit
        have hscalar : ∀ (g : G) x, reducedRep ρ Λp hp.stable g x
            = (φ₁ g : ResidueField O) • x := by
          intro g x
          have hx : x ∈ L₁ ⊔ L₂ := by rw [hcompl.codisjoint.eq_top]; trivial
          obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hx
          rw [map_add, hact₁ g a ha, hact₂ g b hb, smul_add]
        have hLne_top : Lp ≠ ⊤ := by
          intro ht
          rw [ht, finrank_top, hdimp] at hLp1
          omega
        obtain ⟨w, -, hw⟩ := SetLike.exists_of_lt (lt_top_iff_ne_top.mpr hLne_top)
        have hw0 : w ≠ 0 := fun h0 => hw (h0 ▸ Submodule.zero_mem _)
        refine ⟨Submodule.span (ResidueField O) {w}, finrank_span_singleton hw0,
          fun g x _ => hscalar g x, fun g x => by rw [hscalar g x]; simp, ?_⟩
        intro hCeq
        exact hw (hCeq ▸ Submodule.mem_span_singleton_self w)
      · -- distinct characters: take the `φ₂`-line of the splitting
        obtain ⟨C, L₁, hC1, hCact, hL₁act, hcompl⟩ := hsplit.symm hdimp
        have hCquot : ∀ (g : G) x, reducedRep ρ Λp hp.stable g x
            - (φ₁ g : ResidueField O) • x ∈ C := by
          intro g x
          have hx : x ∈ C ⊔ L₁ := by rw [hcompl.codisjoint.eq_top]; trivial
          obtain ⟨c, hc, l, hl, rfl⟩ := Submodule.mem_sup.mp hx
          have hcalc : reducedRep ρ Λp hp.stable g (c + l)
              - (φ₁ g : ResidueField O) • (c + l)
              = ((φ₂ g : ResidueField O) - (φ₁ g : ResidueField O)) • c := by
            rw [map_add, hCact g c hc, hL₁act g l hl, smul_add, sub_smul]
            abel
          rw [hcalc]
          exact C.smul_mem _ hc
        refine ⟨C, hC1, hCact, hCquot, ?_⟩
        intro hCeq
        apply hφ
        have hC0 : C ≠ ⊥ := by
          intro hb
          rw [hb, finrank_bot] at hC1
          omega
        obtain ⟨ξ, hξC, hξ0⟩ := (Submodule.ne_bot_iff _).mp hC0
        refine MonoidHom.ext fun g => Units.ext ?_
        have h2 := hCact g ξ hξC
        have h3 := hLpchar g ξ (hCeq ▸ hξC)
        exact smul_left_injective _ hξ0 (h3.symm.trans h2)
    obtain ⟨C, hC1, hCchar, hCquot, hCne⟩ := hCex
    have hstabC : ∀ g : G, C.map (reducedRep ρ Λp hp.stable g) ≤ C := by
      rintro g x ⟨ξ, hξ, rfl⟩
      rw [hCchar g ξ hξ]
      exact C.smul_mem _ hξ
    have hstab' := stabilizes_preimageLattice hp.stable hstabC
    have spec := preimageLattice_extension_spec hdim hp hC1 hCchar hCquot hstab'
    refine ⟨⟨preimageLattice Λp C, ⟨isLattice_preimageLattice (K := K) Λp C, hstab'⟩,
      reductionImage O (smul_le_preimageLattice Λp C), spec.1, spec.2.1, spec.2.2⟩,
      ⟨C, hC1, rfl⟩, ?_, ?_⟩
    · intro hEq
      exact hCne (preimageLattice_injective hEq)
    · rw [preimageLattice_reductionImage]
      exact sup_eq_left.mpr (smul_mono_right _ (preimageLattice_le _ _))
  -- an initial pack, from the semisimplification hypothesis
  have hinit : ∃ _ : WalkPack ρ φ₁ φ₂, True := by
    haveI := h₀.isLattice
    cases hss with
    | inl hext =>
      obtain ⟨L, h1, hchar, hquot⟩ := hext
      exact ⟨⟨Λ₀, h₀, L, h1, hchar, hquot⟩, trivial⟩
    | inr hext =>
      -- wrong ordering: one preliminary neighbor step swaps it
      obtain ⟨L, h1, hchar, hquot⟩ := hext
      have hstabL : ∀ g : G, L.map (reducedRep ρ Λ₀ h₀.stable g) ≤ L := by
        rintro g x ⟨ξ, hξ, rfl⟩
        rw [hchar g ξ hξ]
        exact L.smul_mem _ hξ
      have hstab' := stabilizes_preimageLattice h₀.stable hstabL
      have spec := preimageLattice_extension_spec hdim h₀ h1 hchar hquot hstab'
      exact ⟨⟨preimageLattice Λ₀ L,
        ⟨isLattice_preimageLattice (K := K) Λ₀ L, hstab'⟩,
        reductionImage O (smul_le_preimageLattice Λ₀ L),
        spec.1, spec.2.1, spec.2.2⟩, trivial⟩
  obtain ⟨p₀, -⟩ := hinit
  -- iterate the step and extract the chain of lattices
  choose stepf hstepEx hstepNe hstepBack using step
  let pseq : ℕ → WalkPack ρ φ₁ φ₂ := fun n => Nat.rec p₀ (fun _ prev => stepf prev) n
  have hfstab : ∀ n, IsStableLattice ρ (pseq n).1 := fun n => (pseq n).2.1
  have hchainstep : ∀ n, ∃ L : Submodule (ResidueField O)
      (Reduction O V (pseq n).1),
      Module.finrank (ResidueField O) L = 1 ∧
      (pseq (n + 1)).1 = preimageLattice (pseq n).1 L :=
    fun n => hstepEx (pseq n)
  have hchainstraight : ∀ n,
      (pseq (n + 2)).1 ≠ maximalIdeal O • (pseq n).1 := by
    intro n hEq
    exact hstepNe (pseq (n + 1)) (hEq.trans (hstepBack (pseq n)).symm)
  -- the chain yields a stable line, contradicting irreducibility
  obtain ⟨W, hW1, hWstab⟩ := exists_stable_line_of_chain hdim
    (fun n => (pseq n).1) hfstab hchainstep hchainstraight
  have hbot_le : (⊥ : Subrepresentation ρ) ≤ ⟨⊥, by simp⟩ := bot_le
  have hle_top : (⟨⊤, by simp⟩ : Subrepresentation ρ) ≤ ⊤ := le_top
  rcases eq_bot_or_eq_top
    (⟨W, fun g v hv => hWstab g (Submodule.mem_map_of_mem hv)⟩ :
      Subrepresentation ρ) with hb | ht
  · have hle : W ≤ ⊥ := by
      intro x hx
      have h1 : x ∈ (⊥ : Subrepresentation ρ) := hb ▸ hx
      exact hbot_le h1
    rw [le_bot_iff] at hle
    rw [hle, finrank_bot] at hW1
    omega
  · have hge : (⊤ : Submodule K V) ≤ W := by
      intro x hx
      have h0 : x ∈ (⟨⊤, by simp⟩ : Subrepresentation ρ) := hx
      have h1 : x ∈ (⊤ : Subrepresentation ρ) := hle_top h0
      rw [← ht] at h1
      exact h1
    have hWtop : W = ⊤ := eq_top_iff.mpr hge
    rw [hWtop, finrank_top, hdim] at hW1
    omega

/-! ## 10. Remarks

* Neither §4 (existence of stable lattices) nor §7 (independence of the
  lattice) is used in the proof of `ribet_lemma_slop` itself: the hypothesis
  is anchored to the given `Λ₀`, and the walk tracks the two characters
  constructively.  Both are needed to *apply* the lemma as in Ribet's paper:
  §4 produces `Λ₀` for a continuous representation of a compact group
  (Ribet's parenthetical remark on p. 154), and §7 — which the paper quotes
  from Curtis–Reiner (30.16) — lets one verify `hss` on any convenient
  lattice.
* The proof formalized here is Ribet's own (p. 155), transposed from
  matrices to lattices: his conjugation by `P = (1 0; 0 π)` is
  `preimageLattice`, his diagonalization step `U = (1 u; 0 1)` is the choice
  of a splitting line avoiding the marked one, and the limit of his matrices
  `Mᵢ` is the `𝔪`-adic limit of §8.  Staying inside `Submodule` language
  avoids choosing bases altogether.  An alternative route is Bellaïche's
  proof ("À propos d'un lemme de Ribet", Rend. Sem. Mat. Univ. Padova 109
  (2003)).
* Natural Mathlib upstreaming candidates proved here: the complements to
  `Submodule.IsLattice` in §1, and `isPrecomplete_of_free` in §8.
-/

end StableLattice
