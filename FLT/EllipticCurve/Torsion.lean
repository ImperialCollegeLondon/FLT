/-
Copyright (c) 2024 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.Topology.Instances.ZMod
public import FLT.Deformations.RepresentationTheory.GaloisRep
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.GroupTheory.FiniteAbelian.Basic

/-!

See
https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there-code-for-X.3F/topic/n-torsion.20or.20multiplication.20by.20n.20as.20an.20additive.20group.20hom/near/429096078

The main theorems in this file are part of the PhD thesis work of David Angdinata, one of KB's
PhD students. It would be great if anyone who is interested in working on these results
could talk to David first. Note that he has already made substantial progress.

-/

@[expose] public section

universe u

variable {k : Type u} [Field k] (E : WeierstrassCurve k) [E.IsElliptic] [DecidableEq k]

open WeierstrassCurve WeierstrassCurve.Affine

/-- The `n`-torsion subgroup of an elliptic curve `E` over `k`: the kernel of multiplication
by `n` on the group of `k`-points of `E`. -/
abbrev WeierstrassCurve.nTorsion (n : ℕ) : Type u := Submodule.torsionBy ℤ (E⁄k).Point n

--variable (n : ℕ) in
--#synth AddCommGroup (E.nTorsion n)

-- not sure if this instance will cause more trouble than it's worth
noncomputable instance (n : ℕ) : Module (ZMod n) (E.nTorsion n) :=
  AddCommGroup.zmodModule <| by
  intro ⟨P, hP⟩
  simpa using hP

-- This theorem needs e.g. a theory of division polynomials. It's ongoing work of David Angdinata.
-- Please do not work on it without talking to KB and David first.
theorem WeierstrassCurve.n_torsion_finite {n : ℕ} (hn : 0 < n) : Finite (E.nTorsion n) := sorry

-- This theorem needs e.g. a theory of division polynomials. It's ongoing work of David Angdinata.
-- Please do not work on it without talking to KB and David first.
-- This theorem was well-known in the early part of the 20th century.
theorem WeierstrassCurve.n_torsion_card [IsSepClosed k] {n : ℕ} (hn : (n : k) ≠ 0) :
    Nat.card (E.nTorsion n) = n^2 := sorry

private lemma card_torsionBy_zmod {m : ℕ} (hm : 0 < m) (d : ℕ) :
    Nat.card (Submodule.torsionBy ℤ (ZMod m) d) = m.gcd d := by
  have : NeZero m := ⟨hm.ne'⟩
  let g := m.gcd d
  have hg : 0 < g := Nat.gcd_pos_of_pos_left d hm
  have hgm : g ∣ m := Nat.gcd_dvd_left m d
  have hgd : g ∣ d := Nat.gcd_dvd_right m d
  let m' := m / g
  have hmg : m' * g = m := Nat.div_mul_cancel hgm
  have hm' : 0 < m' := Nat.div_pos (Nat.le_of_dvd hm hgm) hg
  have hm'_dvd : ∀ x : Submodule.torsionBy ℤ (ZMod m) d, m' ∣ x.1.val := by
    intro x
    have h0 : ((d * x.1.val : ℕ) : ZMod m) = 0 := by
      have hx : (d : ℤ) • x.1 = 0 := Submodule.smul_coe_torsionBy (d : ℤ) x
      rw [natCast_zsmul, nsmul_eq_mul, ← ZMod.natCast_zmod_val x.1, ← Nat.cast_mul] at hx
      exact hx
    have hdiv : m ∣ d * x.1.val := (ZMod.natCast_eq_zero_iff _ _).mp h0
    have hdiv' : m' ∣ (d / g) * x.1.val := by
      apply Nat.dvd_of_mul_dvd_mul_left hg
      rw [mul_comm g m', hmg, ← mul_assoc, Nat.mul_div_cancel' hgd]
      exact hdiv
    exact (Nat.coprime_div_gcd_div_gcd hg).dvd_of_dvd_mul_left hdiv'
  let e : Fin g ≃ Submodule.torsionBy ℤ (ZMod m) d :=
    { toFun k := ⟨((m' * k.1 : ℕ) : ZMod m), by
        rw [Submodule.mem_torsionBy_iff, natCast_zsmul, nsmul_eq_mul, ← Nat.cast_mul,
          ZMod.natCast_eq_zero_iff]
        refine ⟨(d / g) * k.1, ?_⟩
        calc
          d * (m' * k.1) = (d / g * g) * (m' * k.1) := by rw [Nat.div_mul_cancel hgd]
          _ = (m' * g) * (d / g * k.1) := by ring
          _ = m * (d / g * k.1) := by rw [hmg]⟩
      invFun x := ⟨x.1.val / m', Nat.div_lt_of_lt_mul (by rw [hmg]; exact x.1.val_lt)⟩
      left_inv k := by
        ext
        have hlt : m' * k.1 < m := by
          calc
            m' * k.1 < m' * g := Nat.mul_lt_mul_of_pos_left k.2 hm'
            _ = m := hmg
        simp only [ZMod.val_natCast_of_lt hlt, Nat.mul_div_right _ hm']
      right_inv x := by
        ext
        simp only [Nat.mul_div_cancel' (hm'_dvd x), ZMod.natCast_zmod_val] }
  rw [← Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_fin]

private def torsionByTorsionByEquiv {A : Type*} [AddCommGroup A] {d n : ℕ} (hdn : d ∣ n) :
    Submodule.torsionBy ℤ A d ≃+ Submodule.torsionBy ℤ (Submodule.torsionBy ℤ A n) d where
  toFun x := ⟨⟨x.1, by
    rcases hdn with ⟨k, rfl⟩
    rw [Submodule.mem_torsionBy_iff, Nat.cast_mul, mul_comm, mul_smul,
      Submodule.smul_coe_torsionBy (d : ℤ) x, smul_zero]⟩,
    Subtype.ext (Submodule.smul_coe_torsionBy (d : ℤ) x)⟩
  invFun y := ⟨y.1.1, by
    rw [Submodule.mem_torsionBy_iff]
    exact congrArg Subtype.val (Submodule.smul_coe_torsionBy (d : ℤ) y)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

private def torsionByAddEquiv {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    (e : M ≃+ N) (d : ℕ) :
    Submodule.torsionBy ℤ M d ≃+ Submodule.torsionBy ℤ N d where
  toFun x := ⟨e x.1, by
    rw [Submodule.mem_torsionBy_iff, ← map_zsmul, Submodule.smul_coe_torsionBy (d : ℤ) x, map_zero]⟩
  invFun y := ⟨e.symm y.1, by
    rw [Submodule.mem_torsionBy_iff, ← map_zsmul, Submodule.smul_coe_torsionBy (d : ℤ) y, map_zero]⟩
  left_inv x := Subtype.ext (e.symm_apply_apply x.1)
  right_inv y := Subtype.ext (e.apply_symm_apply y.1)
  map_add' _ _ := Subtype.ext (map_add e _ _)

private def torsionByPiEquiv {ι : Type*} {M : ι → Type*} [∀ i, AddCommGroup (M i)] (d : ℕ) :
    Submodule.torsionBy ℤ (∀ i, M i) d ≃+ (∀ i, Submodule.torsionBy ℤ (M i) d) where
  toFun x i := ⟨x.1 i, congrFun (Submodule.smul_coe_torsionBy (d : ℤ) x) i⟩
  invFun f := ⟨fun i ↦ (f i).1, funext fun i ↦ Submodule.smul_coe_torsionBy (d : ℤ) (f i)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

theorem torsionBy_equiv_pi_zmod_of_prime_le {A : Type*} [AddCommGroup A] {n : ℕ} (hn : 0 < n)
    (r : ℕ → ℕ)
    (hn_card : Nat.card (Submodule.torsionBy ℤ A n) =
      ∏ p ∈ n.primeFactors, p ^ (r p * n.factorization p))
    (hp_card : ∀ p : ℕ, p.Prime → p ∣ n → Nat.card (Submodule.torsionBy ℤ A p) ≤ p ^ r p) :
    Nonempty ((Submodule.torsionBy ℤ A n) ≃+
      ((p : n.primeFactors) → Fin (r p.1) → ZMod (p.1 ^ n.factorization p.1))) := by
  classical
  have hfin : Finite (Submodule.torsionBy ℤ A n) :=
    Nat.finite_of_card_ne_zero <| by
      rw [hn_card]
      exact (Finset.prod_pos fun p hp ↦ pow_pos (Nat.prime_of_mem_primeFactors hp).pos _).ne'
  obtain ⟨ι₀, _, q₀, hq₀, e₀, ⟨φ₀⟩⟩ :=
    AddCommGroup.equiv_directSum_zmod_of_finite (Submodule.torsionBy ℤ A n)
  let ι := {i : ι₀ // e₀ i ≠ 0}
  let q : ι → ℕ := fun i ↦ q₀ i.1
  let e : ι → ℕ := fun i ↦ e₀ i.1
  have hq : ∀ i : ι, (q i).Prime := fun i ↦ hq₀ i.1
  have he_pos : ∀ i : ι, 0 < e i := fun i ↦ Nat.pos_of_ne_zero i.2
  let dropZero : ((i : ι₀) → ZMod (q₀ i ^ e₀ i)) ≃+ ((i : ι) → ZMod (q i ^ e i)) :=
    { toFun f i := f i.1
      invFun g i := if hi : e₀ i = 0 then 0 else g ⟨i, hi⟩
      left_inv f := by
        funext i
        dsimp only
        by_cases hi : e₀ i = 0
        · rw [dite_eq_left hi]
          have : Subsingleton (ZMod (q₀ i ^ e₀ i)) :=
            ZMod.subsingleton_iff.mpr (by rw [hi, pow_zero])
          exact Subsingleton.elim _ _
        · rw [dite_eq_right hi]
      right_inv g := by
        funext ⟨i, hi⟩
        dsimp only
        exact dite_eq_right hi
      map_add' _ _ := rfl }
  let φ : Submodule.torsionBy ℤ A n ≃+ ((i : ι) → ZMod (q i ^ e i)) :=
    (φ₀.trans (DirectSum.addEquivProd _)).trans dropZero
  have hdvd : ∀ i : ι, q i ^ e i ∣ n := by
    intro i
    let f : (j : ι) → ZMod (q j ^ e j) := Pi.single i 1
    have h0 : (n : ℤ) • φ.symm f = 0 := Submodule.smul_torsionBy (n : ℤ) (φ.symm f)
    have h1 : (n : ℤ) • f = 0 := by
      have := congrArg φ h0
      rwa [map_zsmul, φ.apply_symm_apply, map_zero] at this
    have h2 : (n : ZMod (q i ^ e i)) = 0 := by
      have := congrFun h1 i
      simpa [f, natCast_zsmul] using this
    exact (ZMod.natCast_eq_zero_iff n (q i ^ e i)).mp h2
  have hmem : ∀ i : ι, q i ∈ n.primeFactors := fun i ↦
    Nat.mem_primeFactors.mpr ⟨hq i, (dvd_pow_self (q i) (he_pos i).ne').trans (hdvd i), hn.ne'⟩
  have hle : ∀ i : ι, e i ≤ n.factorization (q i) := fun i ↦
    ((hq i).pow_dvd_iff_le_factorization hn.ne').mp (hdvd i)
  let S : n.primeFactors → Finset ι := fun p ↦ Finset.univ.filter (fun i : ι ↦ q i = p.1)
  have hS_le : ∀ p : n.primeFactors, (S p).card ≤ r p.1 := by
    intro p
    have hp : p.1.Prime := Nat.prime_of_mem_primeFactors p.2
    have hdp : p.1 ∣ n := Nat.dvd_of_mem_primeFactors p.2
    have hequiv :
        Submodule.torsionBy ℤ A p.1 ≃+ (∀ i : ι, Submodule.torsionBy ℤ (ZMod (q i ^ e i)) p.1) :=
      ((torsionByTorsionByEquiv hdp).trans (torsionByAddEquiv φ p.1)).trans (torsionByPiEquiv p.1)
    have hcard_p : Nat.card (Submodule.torsionBy ℤ A p.1) = p.1 ^ (S p).card := by
      rw [Nat.card_congr hequiv.toEquiv, Nat.card_pi,
        ← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun i ↦ q i = p.1)]
      have h1 : ∏ i ∈ S p, Nat.card (Submodule.torsionBy ℤ (ZMod (q i ^ e i)) p.1) =
          p.1 ^ (S p).card := by
        rw [← Finset.prod_const]
        refine Finset.prod_congr rfl fun i hi ↦ ?_
        rw [card_torsionBy_zmod (pow_pos (hq i).pos _) p.1, (Finset.mem_filter.mp hi).2]
        exact Nat.gcd_eq_right (dvd_pow_self p.1 (he_pos i).ne')
      have h2 : ∏ i ∈ Finset.univ.filter (fun i : ι ↦ ¬ q i = p.1),
          Nat.card (Submodule.torsionBy ℤ (ZMod (q i ^ e i)) p.1) = 1 := by
        refine Finset.prod_eq_one fun i hi ↦ ?_
        rw [card_torsionBy_zmod (pow_pos (hq i).pos _) p.1]
        exact ((Nat.coprime_primes (hq i) hp).mpr (Finset.mem_filter.mp hi).2).pow_left (e i)
      rw [h1, h2, mul_one]
    exact (Nat.pow_le_pow_iff_right hp.one_lt).mp (hcard_p ▸ hp_card p.1 hp hdp)
  have hprod_card : ∏ i : ι, q i ^ e i = ∏ p ∈ n.primeFactors, p ^ (r p * n.factorization p) := by
    have : ∀ i : ι, NeZero (q i ^ e i) := fun i ↦ ⟨(pow_pos (hq i).pos _).ne'⟩
    simpa [Nat.card_pi, Nat.card_zmod] using (Nat.card_congr φ.toEquiv).symm.trans hn_card
  have hsum_eq : ∀ p : n.primeFactors, ∑ i ∈ S p, e i = r p.1 * n.factorization p.1 := by
    intro p
    have hfact := congrArg (fun m : ℕ ↦ m.factorization p.1) hprod_card
    rw [Nat.factorization_prod (fun i _ ↦ (pow_pos (hq i).pos _).ne'),
      Nat.factorization_prod (fun p' hp' ↦
        pow_ne_zero _ (Nat.prime_of_mem_primeFactors hp').ne_zero),
      Finsupp.finsetSum_apply, Finsupp.finsetSum_apply] at hfact
    have hlhs : ∑ i : ι, (q i ^ e i).factorization p.1 = ∑ i ∈ S p, e i := by
      simp_rw [(hq _).factorization_pow, Finsupp.single_apply]
      rw [← Finset.sum_filter]
    have hrhs : ∑ p' ∈ n.primeFactors, (p' ^ (r p' * n.factorization p')).factorization p.1 =
        r p.1 * n.factorization p.1 := by
      have hcongr : ∑ p' ∈ n.primeFactors, (p' ^ (r p' * n.factorization p')).factorization p.1 =
          ∑ p' ∈ n.primeFactors, if p' = p.1 then r p' * n.factorization p' else 0 := by
        refine Finset.sum_congr rfl fun p' hp' ↦ ?_
        rw [(Nat.prime_of_mem_primeFactors hp').factorization_pow, Finsupp.single_apply]
      rw [hcongr, Finset.sum_ite_eq', ite_eq_left p.2]
    exact hlhs.symm.trans (hfact.trans hrhs)
  have hS_card : ∀ p : n.primeFactors, (S p).card = r p.1 := by
    intro p
    have hk_pos : 0 < n.factorization p.1 :=
      Nat.Prime.factorization_pos_of_dvd (Nat.prime_of_mem_primeFactors p.2) hn.ne'
        (Nat.dvd_of_mem_primeFactors p.2)
    have hle_sum : ∑ i ∈ S p, e i ≤ (S p).card * n.factorization p.1 := by
      rw [← smul_eq_mul, ← Finset.sum_const]
      refine Finset.sum_le_sum fun i hi ↦ ?_
      simpa [← (Finset.mem_filter.mp hi).2] using hle i
    have hmul_le : r p.1 * n.factorization p.1 ≤ (S p).card * n.factorization p.1 :=
      (hsum_eq p).symm.trans_le hle_sum
    exact le_antisymm (hS_le p) (Nat.le_of_mul_le_mul_right hmul_le hk_pos)
  have heq : ∀ i : ι, e i = n.factorization (q i) := by
    suffices ∀ p : n.primeFactors, ∀ i ∈ S p, e i = n.factorization p.1 by
      intro i
      exact this ⟨q i, hmem i⟩ i (Finset.mem_filter.mpr ⟨Finset.mem_univ i, rfl⟩)
    intro p
    have hle_S : ∀ i ∈ S p, e i ≤ n.factorization p.1 := fun i hi ↦ by
      simpa [← (Finset.mem_filter.mp hi).2] using hle i
    refine (Finset.sum_eq_sum_iff_of_le hle_S).mp ?_
    rw [hsum_eq p, Finset.sum_const, smul_eq_mul, hS_card p]
  have hfiber : ∀ p : n.primeFactors, Nonempty ({i : ι // q i = p.1} ≃ Fin (r p.1)) := by
    intro p
    refine Fintype.card_eq.mp ?_
    rw [Fintype.card_subtype, Fintype.card_fin]
    exact hS_card p
  let σ : (p : n.primeFactors) → {i : ι // q i = p.1} ≃ Fin (r p.1) := fun p ↦ (hfiber p).some
  let castEquiv : ∀ {a b : ℕ}, a = b → ZMod a ≃+ ZMod b :=
    fun h ↦ (ZMod.ringEquivCongr h).toAddEquiv
  have hcongr : ∀ {a b c : ℕ} (h1 : a = b) (h2 : b = c) (x : ZMod a),
      castEquiv h2 (castEquiv h1 x) = castEquiv (h1.trans h2) x := by
    rintro a _ _ rfl rfl x
    simp [castEquiv]
  let reindex : ((i : ι) → ZMod (q i ^ e i)) ≃+
      ((p : n.primeFactors) → Fin (r p.1) → ZMod (p.1 ^ n.factorization p.1)) :=
    { toFun f p j :=
        castEquiv (by rw [heq, ((σ p).symm j).2]) (f ((σ p).symm j).1)
      invFun g i :=
        castEquiv (by rw [heq i]) (g ⟨q i, hmem i⟩ (σ ⟨q i, hmem i⟩ ⟨i, rfl⟩))
      left_inv f := by
        funext i
        dsimp only
        rw [hcongr]
        have happly : ∀ {i₁ i₂ : ι} (h12 : i₁ = i₂) (h1 : q i₁ ^ e i₁ = q i₂ ^ e i₂),
            castEquiv h1 (f i₁) = f i₂ := by
          rintro i₁ _ rfl _
          simp [castEquiv]
        exact happly (congrArg Subtype.val ((σ ⟨q i, hmem i⟩).symm_apply_apply ⟨i, rfl⟩)) _
      right_inv g := by
        funext p j
        dsimp only
        rw [hcongr]
        have hright : ∀ {p₁ p₂ : n.primeFactors} (hp : p₁ = p₂) {j₁ : Fin (r p₁.1)}
            {j₂ : Fin (r p₂.1)} (hj : HEq j₁ j₂)
            (h1 : p₁.1 ^ n.factorization p₁.1 = p₂.1 ^ n.factorization p₂.1),
            castEquiv h1 (g p₁ j₁) = g p₂ j₂ := by
          rintro p₁ _ rfl j₁ _ ⟨⟩ _
          simp [castEquiv]
        have hp : (⟨q ((σ p).symm j).1, hmem ((σ p).symm j).1⟩ : n.primeFactors) = p :=
          Subtype.ext ((σ p).symm j).2
        have hj :
            HEq (σ ⟨q ((σ p).symm j).1, hmem ((σ p).symm j).1⟩ ⟨((σ p).symm j).1, rfl⟩) j := by
          have hsub : ∀ {p₁ p₂ : n.primeFactors} (h12 : p₁ = p₂) (x : {i : ι // q i = p₁.1})
              (y : {i : ι // q i = p₂.1}), x.1 = y.1 → HEq (σ p₁ x) (σ p₂ y) := by
            rintro p₁ _ rfl ⟨x, hx⟩ ⟨y, hy⟩ rfl
            rfl
          exact (hsub hp _ ((σ p).symm j) rfl).trans (heq_of_eq ((σ p).apply_symm_apply j))
        exact hright hp hj _
      map_add' f₁ f₂ := by
        funext p j
        exact map_add _ _ _ }
  exact ⟨φ.trans reindex⟩

theorem group_theory_lemma_of_prime_le {A : Type*} [AddCommGroup A] {n : ℕ} (hn : 0 < n) (r : ℕ)
    (hn_card : Nat.card (Submodule.torsionBy ℤ A n) = n ^ r)
    (hp_card : ∀ p : ℕ, p.Prime → p ∣ n → Nat.card (Submodule.torsionBy ℤ A p) ≤ p ^ r) :
    Nonempty ((Submodule.torsionBy ℤ A n) ≃+ (Fin r → (ZMod n))) := by
  have hprod : ∏ p ∈ n.primeFactors, p ^ (r * n.factorization p) = n ^ r := by
    calc ∏ p ∈ n.primeFactors, p ^ (r * n.factorization p)
        = (∏ p ∈ n.primeFactors, p ^ n.factorization p) ^ r := by
          rw [← Finset.prod_pow]
          exact Finset.prod_congr rfl fun p _ ↦ by rw [mul_comm, pow_mul]
      _ = (n.factorization.prod (· ^ ·)) ^ r := by
          rw [Finsupp.prod, Nat.support_factorization]
      _ = n ^ r := by rw [Nat.prod_factorization_pow_eq_self hn.ne']
  obtain ⟨ψ⟩ := torsionBy_equiv_pi_zmod_of_prime_le hn (fun _ ↦ r) (hn_card.trans hprod.symm)
    hp_card
  let swap : ((p : n.primeFactors) → Fin r → ZMod (p.1 ^ n.factorization p.1)) ≃+
      (Fin r → (p : n.primeFactors) → ZMod (p.1 ^ n.factorization p.1)) :=
    { toFun f j p := f p j
      invFun g p j := g j p
      left_inv _ := rfl
      right_inv _ := rfl
      map_add' _ _ := rfl }
  exact ⟨(ψ.trans swap).trans
    (AddEquiv.piCongrRight fun _ ↦ (ZMod.equivPi n hn.ne').symm.toAddEquiv)⟩

-- This theorem was well-known in the early part of the 20th century.
theorem group_theory_lemma {A : Type*} [AddCommGroup A] {n : ℕ} (hn : 0 < n) (r : ℕ)
    (h : ∀ d : ℕ, d ∣ n → Nat.card (Submodule.torsionBy ℤ A d) = d ^ r) :
    Nonempty ((Submodule.torsionBy ℤ A n) ≃+ (Fin r → (ZMod n))) :=
  group_theory_lemma_of_prime_le hn r (h n dvd_rfl) fun p _ hp ↦ (h p hp).le

-- I only need this if n is prime but there's no harm thinking about it in general I guess.
-- It follows from the previous theorem using pure group theory (possibly including the
-- structure theorem for finite abelian groups)
theorem WeierstrassCurve.n_torsion_dimension [IsSepClosed k] {n : ℕ} (hn : (n : k) ≠ 0) :
    Nonempty (E.nTorsion n ≃+ (ZMod n) × (ZMod n)) := by
  obtain ⟨φ⟩ : Nonempty (E.nTorsion n ≃+ (Fin 2 → (ZMod n))) := by
    apply group_theory_lemma (Nat.pos_of_ne_zero fun h ↦ by simp [h] at hn)
    intro d hd
    apply E.n_torsion_card
    contrapose! hn
    rcases hd with ⟨c, rfl⟩
    simp [hn]
  exact ⟨φ.trans (RingEquiv.piFinTwo _).toAddEquiv⟩

-- follows easily from the above
noncomputable instance (n : ℕ) : Module.Finite (ZMod n) (E.nTorsion n) := by
  sorry

-- This should be a straightforward but perhaps long unravelling of the definition
/-- The map on points for an elliptic curve over `k` induced by a morphism of `k`-algebras
is a group homomorphism. -/
noncomputable def WeierstrassCurve.Points.map {K L : Type u} [Field K] [Field L] [Algebra k K]
    [Algebra k L] [DecidableEq K] [DecidableEq L]
    (f : K →ₐ[k] L) : (E⁄K).Point →+ (E⁄L).Point := WeierstrassCurve.Affine.Point.map f

omit [E.IsElliptic] [DecidableEq k] in
lemma WeierstrassCurve.Points.map_id (K : Type u) [Field K] [DecidableEq K] [Algebra k K] :
    WeierstrassCurve.Points.map E (AlgHom.id k K) = AddMonoidHom.id _ := by
      ext
      exact WeierstrassCurve.Affine.Point.map_id _

omit [E.IsElliptic] [DecidableEq k] in
lemma WeierstrassCurve.Points.map_comp (K L M : Type u) [Field K] [Field L] [Field M]
    [DecidableEq K] [DecidableEq L] [DecidableEq M] [Algebra k K] [Algebra k L] [Algebra k M]
    (f : K →ₐ[k] L) (g : L →ₐ[k] M) :
    (WeierstrassCurve.Affine.Point.map g).comp (WeierstrassCurve.Affine.Point.map f) =
    WeierstrassCurve.Affine.Point.map (W' := E) (g.comp f) := by
  ext P
  exact WeierstrassCurve.Affine.Point.map_map _ _ _

/-- The Galois action on the points of an elliptic curve. -/
noncomputable instance WeierstrassCurve.galoisRepresentationSmul
    (K : Type u) [Field K] [DecidableEq K] [Algebra k K] :
    SMul (K ≃ₐ[k] K) (E⁄K).Point := ⟨
  fun g P ↦ WeierstrassCurve.Affine.Point.map (g : K →ₐ[k] K) P⟩

/-- The Galois action on the points of an elliptic curve. -/
noncomputable instance WeierstrassCurve.galoisRepresentation
    (K : Type u) [Field K] [DecidableEq K] [Algebra k K] :
    DistribMulAction (K ≃ₐ[k] K) (E⁄K).Point where
      one_smul := sorry -- these should all be easy
      mul_smul := sorry
      smul_zero := sorry
      smul_add := sorry

-- the next `sorry` is data but the only thing which should be missing is
-- the continuity argument, which follows from the finiteness asserted above.

/-- A classical decidable instance on `AlgebraicClosure ℚ`, given that there is
no hope of a constructive one with the current definition of algebraic closure. -/
noncomputable instance : DecidableEq (AlgebraicClosure ℚ) := Classical.typeDecidableEq _

/-- The continuous Galois representation associated to an elliptic curve over a field. -/
def WeierstrassCurve.galoisRep {K : Type u} [Field K] (E : WeierstrassCurve K) [E.IsElliptic]
    [DecidableEq K] [DecidableEq (AlgebraicClosure K)] (n : ℕ) (hn : 0 < n) :
  GaloisRep K (ZMod n) ((E.map (algebraMap K (AlgebraicClosure K))).nTorsion n) := sorry
