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

-- This theorem was well-known in the early part of the 20th century.
theorem group_theory_lemma {A : Type*} [AddCommGroup A] {n : ℕ} (hn : 0 < n) (r : ℕ)
    (h : ∀ d : ℕ, d ∣ n → Nat.card (Submodule.torsionBy ℤ A d) = d ^ r) :
    Nonempty ((Submodule.torsionBy ℤ A n) ≃+ (Fin r → (ZMod n))) := by
  classical
  have hfin : Finite (Submodule.torsionBy ℤ A n) :=
    Nat.finite_of_card_ne_zero (by rw [h n dvd_rfl]; positivity)
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
  have hcard_eq : ∀ d : ℕ, d ∣ n → d ^ r = ∏ i : ι, (q i ^ e i).gcd d := by
    intro d hd
    have hequiv :
        Submodule.torsionBy ℤ A d ≃+ (∀ i : ι, Submodule.torsionBy ℤ (ZMod (q i ^ e i)) d) :=
      ((torsionByTorsionByEquiv hd).trans (torsionByAddEquiv φ d)).trans (torsionByPiEquiv d)
    rw [← h d hd, Nat.card_congr hequiv.toEquiv, Nat.card_pi]
    refine Finset.prod_congr rfl fun i _ ↦ ?_
    exact card_torsionBy_zmod (pow_pos (hq i).pos _) d
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
  have hS_card : ∀ p : n.primeFactors, (S p).card = r := by
    intro p
    have hp : p.1.Prime := Nat.prime_of_mem_primeFactors p.2
    have hdp : p.1 ∣ n := Nat.dvd_of_mem_primeFactors p.2
    have hprod : p.1 ^ r = p.1 ^ (S p).card := by
      rw [hcard_eq p.1 hdp,
        ← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun i ↦ q i = p.1)]
      have h1 : ∏ i ∈ S p, (q i ^ e i).gcd p.1 = p.1 ^ (S p).card := by
        rw [← Finset.prod_const]
        refine Finset.prod_congr rfl fun i hi ↦ ?_
        have hqi : q i = p.1 := (Finset.mem_filter.mp hi).2
        rw [hqi]
        exact Nat.gcd_eq_right (dvd_pow_self p.1 (he_pos i).ne')
      have h2 : ∏ i ∈ Finset.univ.filter (fun i : ι ↦ ¬ q i = p.1), (q i ^ e i).gcd p.1 = 1 := by
        refine Finset.prod_eq_one fun i hi ↦ ?_
        have hne : q i ≠ p.1 := (Finset.mem_filter.mp hi).2
        exact ((Nat.coprime_primes (hq i) hp).mpr hne).pow_left (e i)
      rw [h1, h2, mul_one]
    exact (Nat.pow_right_injective hp.two_le hprod).symm
  have heq : ∀ i : ι, e i = n.factorization (q i) := by
    suffices ∀ p : n.primeFactors, ∀ i ∈ S p, e i = n.factorization p.1 by
      intro i
      exact this ⟨q i, hmem i⟩ i (Finset.mem_filter.mpr ⟨Finset.mem_univ i, rfl⟩)
    intro p
    have hp : p.1.Prime := Nat.prime_of_mem_primeFactors p.2
    let k := n.factorization p.1
    have hle_S : ∀ i ∈ S p, e i ≤ k := by
      intro i hi
      have hqi : q i = p.1 := (Finset.mem_filter.mp hi).2
      simpa only [k, ← hqi] using hle i
    have hsum : ∑ i ∈ S p, e i = ∑ _i ∈ S p, k := by
      have hprod : p.1 ^ (k * r) = p.1 ^ (∑ i ∈ S p, e i) := by
        rw [pow_mul, hcard_eq (p.1 ^ k) (Nat.ordProj_dvd n p.1),
          ← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun i ↦ q i = p.1)]
        have h1 : ∏ i ∈ S p, (q i ^ e i).gcd (p.1 ^ k) = p.1 ^ (∑ i ∈ S p, e i) := by
          rw [← Finset.prod_pow_eq_pow_sum]
          refine Finset.prod_congr rfl fun i hi ↦ ?_
          have hqi : q i = p.1 := (Finset.mem_filter.mp hi).2
          rw [hqi]
          exact Nat.gcd_eq_left (Nat.pow_dvd_pow p.1 (hle_S i hi))
        have h2 : ∏ i ∈ Finset.univ.filter (fun i : ι ↦ ¬ q i = p.1),
            (q i ^ e i).gcd (p.1 ^ k) = 1 := by
          refine Finset.prod_eq_one fun i hi ↦ ?_
          have hne : q i ≠ p.1 := (Finset.mem_filter.mp hi).2
          exact (((Nat.coprime_primes (hq i) hp).mpr hne).pow_left (e i)).pow_right k
        rw [h1, h2, mul_one]
      have hkr : ∑ i ∈ S p, e i = k * r := (Nat.pow_right_injective hp.two_le hprod).symm
      rw [hkr, Finset.sum_const, smul_eq_mul, hS_card p, mul_comm]
    exact (Finset.sum_eq_sum_iff_of_le hle_S).mp hsum
  have hfiber : ∀ p : n.primeFactors, Nonempty ({i : ι // q i = p.1} ≃ Fin r) := by
    intro p
    refine Fintype.card_eq.mp ?_
    rw [Fintype.card_subtype, Fintype.card_fin]
    exact hS_card p
  let σ : (p : n.primeFactors) → {i : ι // q i = p.1} ≃ Fin r := fun p ↦ (hfiber p).some
  let castEquiv : ∀ {a b : ℕ}, a = b → ZMod a ≃+ ZMod b :=
    fun h ↦ (ZMod.ringEquivCongr h).toAddEquiv
  have hcongr : ∀ {a b c : ℕ} (h1 : a = b) (h2 : b = c) (x : ZMod a),
      castEquiv h2 (castEquiv h1 x) = castEquiv (h1.trans h2) x := by
    rintro a _ _ rfl rfl x
    simp [castEquiv]
  let reindex : ((i : ι) → ZMod (q i ^ e i)) ≃+
      (Fin r → (p : n.primeFactors) → ZMod (p.1 ^ n.factorization p.1)) :=
    { toFun f j p :=
        castEquiv (by rw [heq, ((σ p).symm j).2]) (f ((σ p).symm j).1)
      invFun g i :=
        castEquiv (by rw [heq i]) (g (σ ⟨q i, hmem i⟩ ⟨i, rfl⟩) ⟨q i, hmem i⟩)
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
        funext j p
        dsimp only
        rw [hcongr]
        have hright : ∀ {p₁ p₂ : n.primeFactors} (hp : p₁ = p₂) {j₁ j₂ : Fin r} (hj : j₁ = j₂)
            (h1 : p₁.1 ^ n.factorization p₁.1 = p₂.1 ^ n.factorization p₂.1),
            castEquiv h1 (g j₁ p₁) = g j₂ p₂ := by
          rintro p₁ _ rfl j₁ _ rfl _
          simp [castEquiv]
        have hp : (⟨q ((σ p).symm j).1, hmem ((σ p).symm j).1⟩ : n.primeFactors) = p :=
          Subtype.ext ((σ p).symm j).2
        have hj : σ ⟨q ((σ p).symm j).1, hmem ((σ p).symm j).1⟩ ⟨((σ p).symm j).1, rfl⟩ = j := by
          have hsub : ∀ {p₁ p₂ : n.primeFactors} (h12 : p₁ = p₂) (x : {i : ι // q i = p₁.1})
              (y : {i : ι // q i = p₂.1}), x.1 = y.1 → σ p₁ x = σ p₂ y := by
            rintro p₁ _ rfl ⟨x, hx⟩ ⟨y, hy⟩ rfl
            rfl
          exact (hsub hp _ ((σ p).symm j) rfl).trans ((σ p).apply_symm_apply j)
        exact hright hp hj _
      map_add' f₁ f₂ := by
        funext j p
        exact map_add _ _ _ }
  exact ⟨(φ.trans reindex).trans
    (AddEquiv.piCongrRight fun _ ↦ (ZMod.equivPi n hn.ne').symm.toAddEquiv)⟩

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
