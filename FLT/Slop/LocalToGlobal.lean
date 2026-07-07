/-
Copyright (c) 2025 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McCarthy
-/
module

public import FLT.Slop.PRegularSum

@[expose] public section

universe u

/-!
# Bernstein's local-to-global step

This file turns the local prime-by-prime conclusions into the global integral
statement needed for Brauer induction.

The file has two parts.

* First, denominator clearing shows that membership in the localized span
  `Jloc p` gives an integral multiple lying in `J p`, with denominator
  coprime to `p`.

* Second, a gcd argument shows that if a submodule contains a multiple of
  `1` by an integer coprime to every prime `p`, then it contains `1` itself.
  This is used to prove `one_mem_J_global`.

-/

namespace BrauerInduction

variable {k : Type u} [Field k]
variable {G : Type u} [Group G]

section DenominatorClearing

/-!
## Clearing denominators

The localized span `Jloc p` is defined over the `p`-local integers.  This
section proves that an element of `Jloc p` can be cleared of denominators: after
multiplying by an integer coprime to `p`, it lies in the integral span `J p`.

Applying this to `1 ∈ Jloc p` gives an integer `n`, not divisible by `p`, such
that `n • 1 ∈ J p`.
-/

/--
Clear denominators from an element of the localized span `Jloc p`.

If `f ∈ Jloc p`, then some integer `m` coprime to `p` satisfies `m • f ∈ J p`.
-/
lemma exists_intCoprime_smul_mem_J
    [Fintype G] [CharZero k]
    (p : ℕ) [Fact p.Prime] (f : ClassFun k G) (hf : f ∈ Jloc (k := k) (G := G) p) :
    ∃ (m : Zlocal.intCoprimeSubmonoid p), (m : ℤ) • f ∈ J (k := k) (G := G) p := by
  refine Submodule.span_induction
    (p := fun f _ => ∃ (m : Zlocal.intCoprimeSubmonoid p), (m : ℤ) • f ∈ J (k := k) p)
      ?_ ?_ ?_ ?_ hf
  · intro x hx
    use 1
    simp only [Submonoid.coe_one, one_smul]
    exact Submodule.subset_span hx
  · use 1
    simpa only [Submonoid.coe_one, Int.cast_one, one_smul]
      using Submodule.zero_mem _
  · rintro x y _ _ ⟨mx, hmx⟩ ⟨my, hmy⟩
    use mx * my
    have h_add : ((mx * my : Zlocal.intCoprimeSubmonoid p) : ℤ) • (x + y) =
        (my : ℤ) • ((mx : ℤ) • x) + (mx : ℤ) • ((my : ℤ) • y) := by
      simp only [Submonoid.coe_mul, smul_add]
      congr 1
      · rw [mul_comm, mul_smul]
      · rw [mul_smul]
    rw [h_add]
    apply Submodule.add_mem
    · exact Submodule.smul_mem _ (my : ℤ) hmx
    · exact Submodule.smul_mem _ (mx : ℤ) hmy
  · rintro c x _ ⟨mx, hmx⟩
    obtain ⟨⟨a, mc⟩, hc⟩ := IsLocalization.mk'_surjective (Zlocal.intCoprimeSubmonoid p) c
    use mc * mx
    have h_clear := ClassFun.Zlocal.clear_denom (G := G) (k := k) p a mc x
    have h_goal_simpl : ((mc * mx : Zlocal.intCoprimeSubmonoid p) : ℤ) • (c • x)
                      = (a : ℤ) • ((mx : ℤ) • x) := by
      simp only [Submonoid.coe_mul]
      rw [mul_comm (mc : ℤ), mul_smul]
      rw [← hc]
      change (mx : ℤ) •
        ((mc : ℤ) • ((Zlocal.toK (k := k) (p := p))
          (IsLocalization.mk' (Zlocal p) a mc) • x)) = _
      rw [h_clear]
      simp only [← mul_smul, ← mul_smul]
      rw [mul_comm (a : ℤ), mul_smul]
    rw [h_goal_simpl]
    exact Submodule.smul_mem _ (a : ℤ) hmx

/--
Bernstein Step 9: from `1 ∈ Jloc p` obtain an integral multiple of `1` lying in
`J p`.

The multiplier is represented by an element of the localization submonoid, so it
is not divisible by `p`.
-/
theorem exists_n_not_dvd_smul_one_mem_J
    [CharZero k] [IsAlgClosed k] [Fintype G]
    (p : ℕ) [Fact p.Prime] :
    ∃ n : ℤ, ¬ (p : ℤ) ∣ n ∧
      (n • (1 : ClassFun k G)) ∈ J (k := k) (G := G) p := by
  obtain ⟨m, hm⟩ :=
    exists_intCoprime_smul_mem_J p (1 : ClassFun k G) (one_mem_Jloc p)
  exact ⟨(m : ℤ), Zlocal.intCoprimeSubmonoid.not_dvd m, hm⟩

end DenominatorClearing

section J_global

/-!
## The global Bernstein span

This section combines the prime-local ideals `J p` into the global integral
Bernstein span `J_global`.

The key algebraic bridge is a gcd argument: if an integral submodule contains
a multiple `n_p • 1` with `p ∤ n_p` for every prime `p`, then the ideal of
integers multiplying `1` into the submodule is the whole of `ℤ`.
-/

/--
A gcd bridge for integral submodules.

Let `M` be a `ℤ`-submodule of a `ℤ`-module and let `x` be an element. If for
every prime `p`, the submodule contains some multiple `n • x` with `p ∤ n`,
then `M` contains `x`.
-/
lemma mem_of_forall_prime_exists_not_dvd_smul
    {A : Type*} [AddCommGroup A] [Module ℤ A]
    (M : Submodule ℤ A) (x : A)
    (h_exists : ∀ (p : ℕ) [Fact p.Prime],
      ∃ n : ℤ, ¬ (p : ℤ) ∣ n ∧ n • x ∈ M) :
    x ∈ M := by
  let I : Ideal ℤ :=
    { carrier := { m | m • x ∈ M }
      zero_mem' := by
        change (0 : ℤ) • x ∈ M
        simp
      add_mem' := by
        intro m n hm hn
        change (m + n) • x ∈ M
        simpa [add_zsmul] using Submodule.add_mem M hm hn
      smul_mem' := by
        intro c m hm
        change (c * m) • x ∈ M
        rw [mul_smul]
        exact Submodule.smul_of_tower_mem M c hm }
  obtain ⟨d, hd⟩ := (inferInstance : I.IsPrincipal).principal
  have h_d_abs_eq_one : d.natAbs = 1 := by
    by_contra hneq
    obtain ⟨p, hp_prime, hp_dvd_abs⟩ := Nat.exists_prime_and_dvd hneq
    haveI : Fact p.Prime := ⟨hp_prime⟩
    obtain ⟨n, hn_ndvd, hn_mem⟩ := h_exists p
    have hn_in_I : n ∈ I := hn_mem
    have hd_dvd_n : d ∣ n := by
      rw [hd, Ideal.mem_span_singleton] at hn_in_I
      exact hn_in_I
    have hp_dvd_d : (p : ℤ) ∣ d := by
      have hp_dvd_abs_int : (p : ℤ) ∣ (d.natAbs : ℤ) := by
        exact_mod_cast hp_dvd_abs
      simpa [Int.dvd_natAbs] using hp_dvd_abs_int
    exact hn_ndvd (dvd_trans hp_dvd_d hd_dvd_n)
  have h_one_in_I : (1 : ℤ) ∈ I := by
    have hd_abs_dvd_one : (d.natAbs : ℤ) ∣ (1 : ℤ) := by
      rw [h_d_abs_eq_one]
      exact one_dvd 1
    have hd_dvd_one : d ∣ (1 : ℤ) := by
      simpa [Int.dvd_natAbs] using hd_abs_dvd_one
    rw [hd]
    exact Ideal.mem_span_singleton.mpr hd_dvd_one
  have hx : (1 : ℤ) • x ∈ M := h_one_in_I
  simpa using hx


/--
The global integral Bernstein span.

This is the supremum, over all primes `p`, of the prime-local integral spans
`J p`.
-/
def J_global
    (k : Type u) [Field k]
    (G : Type u) [Group G] [Fintype G] :
    Submodule ℤ (ClassFun k G) :=
  ⨆ (p : ℕ) (_ : Fact p.Prime), J (k := k) (G := G) p

/--
The constant class function `1` belongs to the global integral Bernstein span.

This is the local-to-global conclusion obtained by applying the denominator
clearing result prime by prime and then using the gcd bridge.
-/
theorem one_mem_J_global [Fintype G] [IsAlgClosed k] [CharZero k] :
    (1 : ClassFun k G) ∈ J_global k G:= by
  refine mem_of_forall_prime_exists_not_dvd_smul
    (J_global k G) (1 : ClassFun k G) (fun p hp => ?_)
  haveI : Fact p.Prime := hp
  obtain ⟨n, hn_ndvd, hn_mem_Jp⟩ :=
    BrauerInduction.exists_n_not_dvd_smul_one_mem_J (k:=k) p (G:=G)
  use n
  constructor
  · exact hn_ndvd
  · apply Submodule.mem_iSup_of_mem p
    apply Submodule.mem_iSup_of_mem hp
    exact hn_mem_Jp

end J_global

end BrauerInduction
