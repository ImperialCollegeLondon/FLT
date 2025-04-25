import FLT.Mathlib.Topology.Algebra.Valued.ValuationTopology
import FLT.Mathlib.Algebra.Order.GroupWithZero
import Mathlib.RingTheory.DedekindDomain.AdicValuation

/-!

# Adic Completions

If `A` is a valued ring with field of fractions `K` there are two different
complete rings containing `A` one might define, the first is
`𝒪_v = {x ∈ K_v | v x ≤ 1}` and the second is the `v-adic` completion of `A`.
In the case when `A` is a Dedekind domain these definitions give isomorphic
topological `A`-algebras. This file makes some progress towards this.

## Main theorems

* `FiniteAdeleRing.closureAlgebraMapIntegers_eq_integers` : The closure of `A` in `K_v` is `𝒪_v`.

* `FiniteAdeleRing.closureAlgebraMapIntegers_eq_prodIntegers` : If `s` is a set of primes of `A`,
    then the closure of `A` in `∏_{v ∈ s} K_v` is `∏_{v ∈ s} 𝒪_v`.
-/

namespace IsDedekindDomain.HeightOneSpectrum

section Multiplicative

open scoped Multiplicative
lemma exists_ofAdd_natCast_of_le_one {x : ℤₘ₀} (hx : x ≠ 0) (hx' : x ≤ 1):
    ∃ (k : ℕ), (Multiplicative.ofAdd (-(k : ℤ))) = x := by
  let y := WithZero.unzero hx
  have hy : y = x := WithZero.coe_unzero hx
  have hy' : y ≤ 1 := by
    rw [← hy] at hx'
    exact WithBot.coe_le_one.mp hx'
  obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le (Int.neg_nonneg_of_nonpos hy')
  use k
  simp only [← hk, Int.neg_neg, ← hy, WithZero.coe_inj]
  rfl

lemma exists_ofAdd_natCast_lt {x : ℤₘ₀} (hx : x ≠ 0) :
    ∃ (k : ℕ), (Multiplicative.ofAdd (-(k : ℤ))) < x := by
  obtain ⟨y, hnz, hyx⟩ := WithZero.exists_ne_zero_and_lt hx
  let k': ℤ := WithZero.unzero hnz
  use k'.natAbs
  apply lt_of_le_of_lt _ hyx
  rw [← WithZero.coe_unzero hnz]
  norm_cast
  let _ := |k'|
  apply neg_abs_le k'

end Multiplicative

variable { A : Type* } ( K : Type* ) [CommRing A] [Field K] [Algebra A K] [IsFractionRing A K]
    [IsDedekindDomain A] (v : HeightOneSpectrum A)

lemma ne_zero_of_some_le_intValuation {a : A} {m : Multiplicative ℤ} (h : m ≤ v.intValuation a)
    : a ≠ 0 := by
  rintro rfl
  simp at h

lemma intValuation_eq_coe_neg_multiplicity {a : A} (hnz : a ≠ 0) :
    v.intValuation a =
    (Multiplicative.ofAdd (-(multiplicity v.asIdeal (Ideal.span {a}): ℤ))) := by
  classical
  have hnb : Ideal.span {a} ≠ ⊥ := by
    rwa [ne_eq, Ideal.span_singleton_eq_bot]
  rw [intValuation_apply, intValuationDef_if_neg _ hnz,
    count_associates_factors_eq hnb v.isPrime v.ne_bot]
  nth_rw 1 [← normalize_eq v.asIdeal]
  congr
  symm
  apply multiplicity_eq_of_emultiplicity_eq_some
  rw [← UniqueFactorizationMonoid.emultiplicity_eq_count_normalizedFactors v.irreducible hnb]

lemma emultiplicity_eq_of_valuation_eq_ofAdd {a : A} {k : ℕ}
    (hv : v.intValuation a = (Multiplicative.ofAdd (-(k : ℤ)))) :
    emultiplicity v.asIdeal (Ideal.span {a}) = k := by
  classical
  have hnz : a ≠ 0 := ne_zero_of_some_le_intValuation _ (le_of_eq hv.symm)
  have hnb : Ideal.span {a} ≠ ⊥ := by
    rwa [ne_eq, Ideal.span_singleton_eq_bot]
  simp only [intValuation_apply,  intValuationDef_if_neg _ hnz,
    ofAdd_neg, WithZero.coe_inv, inv_inj, WithZero.coe_inj, EmbeddingLike.apply_eq_iff_eq,
    Nat.cast_inj] at hv
  rw [← hv, UniqueFactorizationMonoid.emultiplicity_eq_count_normalizedFactors v.irreducible hnb,
    count_associates_factors_eq hnb v.isPrime v.ne_bot, normalize_eq]

/-- Given `a, b ∈ A` and `v b ≤ v a` we can find `y in A` such that `y` is close to `a / b` by
    the valuation v. -/
lemma exists_adicValued_mul_sub_le {a b : A} {γ : WithZero (Multiplicative ℤ)} (hγ : γ ≠ 0)
    (hle : γ ≤ v.intValuation a)
    (hle' : v.intValuation b ≤ v.intValuation a) :
    ∃ y, v.intValuation (y * a - b) ≤ γ := by
  -- Find `n` such that `γ = Multiplicative.ofAdd (-(n : ℤ))`
  have hγ' : γ ≤ 1 := by
    apply hle.trans
    rw [intValuation_apply]
    apply intValuation_le_one
  obtain ⟨n, hn⟩ := exists_ofAdd_natCast_of_le_one hγ hγ'
  rw [← hn] at hle ⊢
  have hnz : a ≠ 0 := ne_zero_of_some_le_intValuation _ hle
  have hnb : Ideal.span {a} ≠ ⊥ := by
    rwa [ne_eq, Ideal.span_singleton_eq_bot]
  -- Rewrite the statements to involve multiplicity rather than valuations
  rw [intValuation_eq_coe_neg_multiplicity _ hnz, WithZero.coe_le_coe, Multiplicative.ofAdd_le,
    neg_le_neg_iff, Int.ofNat_le] at hle
  have hm : emultiplicity v.asIdeal (Ideal.span {a}) ≤ n :=
    le_of_eq_of_le
      (emultiplicity_eq_of_valuation_eq_ofAdd v <| intValuation_eq_coe_neg_multiplicity v hnz)
      (ENat.coe_le_coe.mpr hle)
  have hb : b ∈ v.asIdeal ^ multiplicity v.asIdeal (Ideal.span {a}) := by
    rwa [← Ideal.dvd_span_singleton, ← intValuation_le_pow_iff_dvd,
        ← intValuation_eq_coe_neg_multiplicity _ hnz]
  -- Now make use of
  -- `v.asIdeal ^ multiplicity v.asIdeal (Ideal.span {a}) = v.asIdeal ^ n ⊔ Ideal.span {a}`
  -- (this is where we need `IsDedekindDomain A`)
  rw [← irreducible_pow_sup_of_ge hnb (irreducible v) n hm] at hb
  -- Extract y by writing b as a general term of the sum of the two ideals.
  obtain ⟨x, hx, z, hz, hxz⟩ := Submodule.mem_sup.mp hb
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.mp hz
  use y
  -- And again prove the result about valuations by turning into one about ideals.
  rwa [hy, ← hxz, sub_add_cancel_right, intValuation_apply,
      intValuation_le_pow_iff_dvd, Ideal.dvd_span_singleton, neg_mem_iff]

lemma exists_adicValued_sub_lt_of_adicValued_le_one {x : (WithVal (v.valuation K))}
    (γ : (WithZero (Multiplicative ℤ))ˣ) (hx : Valued.v x ≤ 1) :
    ∃a, Valued.v ((algebraMap A K a) - (x : v.adicCompletion K)) < γ.val := by
  -- Write `x = n / d`
  obtain ⟨⟨n, d, hd⟩, hnd⟩ := IsLocalization.surj (nonZeroDivisors A) x
  dsimp only at hnd
  -- Show `v n ≤ v d`
  have hnd' := congr_arg Valued.v hnd
  simp only [adicValued_apply', map_mul] at hnd'
  have hge : Valued.v ((algebraMap A (WithVal (v.valuation K))) d) ≥
      Valued.v ((algebraMap A (WithVal (v.valuation K))) n) :=
    calc Valued.v ((algebraMap A (WithVal (v.valuation K))) d)
          ≥ (valuation K v) x *
            (valuation K v) ((algebraMap A (WithVal (v.valuation K))) d) :=
                mul_le_of_le_one_left' hx
        _ = Valued.v ((algebraMap A (WithVal (v.valuation K))) n) := hnd'
  simp only [adicValued_apply', ge_iff_le,
    WithVal, adicValued_apply,
    valuation_of_algebraMap] at hge
  have hdz : (algebraMap A (WithVal (v.valuation K)) d) ≠ 0 :=
    IsLocalization.to_map_ne_zero_of_mem_nonZeroDivisors _ (fun _ ↦ id) hd
  -- Find a suitable `γ` for the bound in `exists_adicValued_mul_sub_le`
  have hv : Valued.v ((algebraMap A (WithVal (v.valuation K)) d)) ≠ 0 := by
    rw [Valuation.ne_zero_iff]
    exact hdz
  let hu : Valued.v ((algebraMap A (WithVal (v.valuation K)) d)) * γ.val ≠ 0 := by
    rw [mul_ne_zero_iff]
    exact ⟨hv, γ.ne_zero⟩
  obtain ⟨γ', hγ, hγu, hγv⟩ := WithZero.exists_ne_zero_and_lt_and_lt hu hv
  simp only [WithVal, adicValued_apply,
    valuation_of_algebraMap, intValuation_apply] at hγv
  -- Now can apply `exists_adicValued_mul_sub_le` to get the approximation of `x`.
  obtain ⟨a, hval⟩ := exists_adicValued_mul_sub_le v hγ hγv.le hge
  use a
  rw [← eq_div_iff_mul_eq hdz] at hnd
  rw [← UniformSpace.Completion.coe_sub,
      valuedAdicCompletion_eq_valuation',
      hnd, sub_div' hdz, map_div₀]
  unfold WithVal at hdz ⊢
  rw [← Valuation.pos_iff (valuation K v)] at hdz
  rw [← map_mul, ← map_sub, div_lt_iff₀' hdz, valuation_of_algebraMap,
      intValuation_apply]
  exact lt_of_le_of_lt hval hγu

/-- The closure of `A` in `K_v` is `𝒪_v`. -/
theorem closureAlgebraMapIntegers_eq_integers :
    closure (algebraMap A (v.adicCompletion K)).range =
    SetLike.coe (v.adicCompletionIntegers K) := by
  apply subset_antisymm
  -- We know `closure A ⊆ 𝒪_v` because `𝒪_v` is closed and `A ⊆ 𝒪_v`
  . apply closure_minimal _ Valued.valuationSubring_isClosed
    rintro b ⟨a, rfl⟩
    exact coe_mem_adicCompletionIntegers v a
  -- Show `𝒪_v ⊆ closure A` from `𝒪_v ⊆ closure O_[K]` and `closure O_[K] ⊆ closure A`
  . let f := fun (k : WithVal (v.valuation K)) => (k : v.adicCompletion K)
    suffices h : closure (f '' (f ⁻¹' (adicCompletionIntegers K v))) ⊆
        closure (algebraMap A (adicCompletion K v)).range by
      apply Set.Subset.trans _ h
      exact DenseRange.subset_closure_image_preimage_of_isOpen
        UniformSpace.Completion.denseRange_coe (Valued.valuationSubring_isOpen _)
    -- Unfold the topological definitions until we get the result from the previous lemma
    apply closure_minimal _ isClosed_closure
    rintro k ⟨x, hx, rfl⟩
    unfold f at hx
    rw [Set.mem_preimage, SetLike.mem_coe, mem_adicCompletionIntegers,
        Valued.valuedCompletion_apply, adicValued_apply'] at hx
    rw [mem_closure_iff_nhds_zero]
    intro U hU
    rw [Valued.mem_nhds] at hU
    obtain ⟨γ, hγ⟩ := hU
    obtain ⟨a, ha⟩ := exists_adicValued_sub_lt_of_adicValued_le_one K v γ hx
    use algebraMap A K a
    constructor
    . use a
      rfl
    . apply hγ
      simpa

/-- `A` is dense in `𝒪_v`. -/
theorem denseRange_of_integerAlgebraMap :
    DenseRange (algebraMap A (v.adicCompletionIntegers K)) := by
  rw [denseRange_iff_closure_range, Set.eq_univ_iff_forall]
  intro x
  rw [closure_subtype]
  suffices h : Subtype.val ''
      Set.range ((algebraMap A ↥(adicCompletionIntegers K v))) =
      (algebraMap A (v.adicCompletion K)).range by
    rw [h, closureAlgebraMapIntegers_eq_integers K v]
    exact Subtype.coe_prop x
  simp only [RingHom.coe_range, ← Set.range_comp']
  rfl

/-- An element of `𝒪_v` can be approximated by an element of `A`. -/
theorem exists_adicValued_sub_lt_of_adicCompletionInteger ( x : v.adicCompletionIntegers K )
    ( γ : (WithZero (Multiplicative ℤ))ˣ ) :
    ∃a, Valued.v ((algebraMap A K a) - (x : v.adicCompletion K)) < γ.val := by
  have h := closureAlgebraMapIntegers_eq_integers K v
  rw [Set.ext_iff] at h
  specialize h x
  simp_rw [RingHom.coe_range, Subtype.coe_prop, iff_true, mem_closure_iff_nhds] at h
  specialize h { y | Valued.v (y  - (x : v.adicCompletion K)) < γ.val }
  have hn : {y | Valued.v (y - (x : v.adicCompletion K)) < γ.val} ∈ nhds x.val := by
    rw [Valued.mem_nhds]
    use γ
  obtain ⟨z, ⟨hz, a, ha⟩⟩ := h hn
  use a
  rw [algebraMap_adicCompletion, Function.comp_apply] at ha
  rwa [ha]

/-- An element of `∏_{v ∈ s} 𝒪_v`, with `s` finite, can be approximated by an element of `A`.
-/
theorem exists_forall_adicValued_sub_lt {ι : Type*} (s : Finset ι)
    (e : ι → (WithZero (Multiplicative ℤ))ˣ ) (valuation : ι → HeightOneSpectrum A)
    (injective : Function.Injective valuation)
    (x : (i : ι) → (valuation i).adicCompletionIntegers K) :
    ∃ a, ∀ i ∈ s, Valued.v ((algebraMap A K a) - (x i).val) < (e i).val := by
  -- Approximate elements of `𝒪_v` with elements of `A` using the previous theorem.
  choose f hf using fun (i : s) =>
    exists_adicValued_sub_lt_of_adicCompletionInteger K (valuation i) (x i) (e i)

  -- Convert the hypotheses from being about valuations to being about ideals, so
  -- that we can apply (a suitable corollary of) the Chinese remainder theorem.
  have hexists_e' : ∀ (i : ι), ∃ (e' : ℕ), (Multiplicative.ofAdd (-(e' : ℤ))) < (e i).val := by
    intro i
    apply exists_ofAdd_natCast_lt (e i).ne_zero
  choose e' he' using hexists_e'
  have hinj : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      (fun i ↦ (valuation i).asIdeal) i ≠ (fun i ↦ (valuation i).asIdeal) j := by
    intro _ _ _ _
    exact mt <| fun hij ↦ injective (HeightOneSpectrum.ext hij)

  -- Use Chinese remainder theorem to get a single approximation for `f i` for all `i ∈ s`.
  obtain ⟨a, ha⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := s)
    (fun i => (valuation i).asIdeal) e' (fun i hi => (valuation i).prime) hinj f
  use a
  intro i hi
  specialize ha i hi
  specialize hf ⟨i, hi⟩
  rw [← Ideal.dvd_span_singleton, ← intValuation_le_pow_iff_dvd,
      ← intValuation_apply, ← valuation_of_algebraMap (K := K),
      ← valuedAdicCompletion_eq_valuation, algebraMap.coe_sub] at ha
  refine lt_of_le_of_lt ?_ (Valuation.map_add_lt _ (ha.trans_lt (he' i)) hf)
  apply le_of_eq
  congr
  rw [add_sub, sub_eq_sub_iff_add_eq_add, add_right_cancel_iff,
    add_comm_sub, add_sub, eq_sub_iff_add_eq]
  rfl

/-- The closure of `A` in `∏_{v ∈ s} K_v` is `∏_{v ∈ s} 𝒪_v`. `s` may be infinite. -/
theorem closureAlgebraMapIntegers_eq_prodIntegers {ι : Type*}
    (valuation : ι → HeightOneSpectrum A) (injective : Function.Injective valuation) :
    closure (SetLike.coe (algebraMap A ((i : ι) → (valuation i).adicCompletion K)).range) =
    (Set.pi Set.univ (fun (i : ι) ↦ ((valuation i).adicCompletionIntegers K).carrier)) := by
  apply Set.Subset.antisymm
  . apply closure_minimal
    . rintro c ⟨a, ha⟩ i -
      rw [← ha]
      simp only [Pi.algebraMap_apply, SetLike.mem_coe]
      exact coe_mem_adicCompletionIntegers (valuation i) a
    . apply isClosed_set_pi
      rintro w -
      exact Valued.valuationSubring_isClosed
  . intro f hf
    rw [mem_closure_iff_nhds_zero]
    intro U hU
    rw [Pi.zero_def, nhds_pi, Filter.mem_pi'] at hU
    obtain ⟨I, t, htn, hts⟩ := hU
    choose g hg using fun w => (Valued.is_topological_valuation (t w)).mp (htn w)
    obtain ⟨a, ha⟩ :=
      exists_forall_adicValued_sub_lt K I g valuation injective (fun w => ⟨f w, hf w ⟨⟩⟩)
    use algebraMap A _ a
    constructor
    . rw [RingHom.coe_range]
      exact Set.mem_range_self a
    . exact hts fun w hw ↦ hg w <| ha w hw

end IsDedekindDomain.HeightOneSpectrum
