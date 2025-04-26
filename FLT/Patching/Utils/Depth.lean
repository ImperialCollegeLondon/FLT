import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.Regular.RegularSequence
import Mathlib.RingTheory.TensorProduct.Free
import FLT.Patching.Utils.Lemmas

variable (R S M : Type*) [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
variable [AddCommGroup M] [Module R M] [Module S M] [Algebra R S] [IsScalarTower R S M]
variable [IsLocalHom (algebraMap R S)]

open IsLocalRing RingTheory

noncomputable section

/--
Not sure if we should use `IsRegular` or `IsWeaklyRegular`.
They agree for nontrivial finite modules over local rings.
Using `IsWeaklyRegular` gives `depth R 0 = ∞`, which is the right one according to stacks.
-/
def Module.depth : ℕ∞ :=
  sSup { List.length s | (s : List R)
    (_ : Sequence.IsWeaklyRegular M s)
    (_ : ∀ r ∈ s, r ∈ maximalIdeal R) }

instance [Subsingleton M] (N : Submodule R M) : Subsingleton (M ⧸ N) :=
  Function.Surjective.subsingleton N.mkQ_surjective

lemma Module.length_le_depth (s : List R)
    (hs : Sequence.IsWeaklyRegular M s) (hs' : ∀ r ∈ s, r ∈ maximalIdeal R) :
    s.length ≤ Module.depth R M :=
  le_sSup ⟨s, hs, hs', rfl⟩


lemma Module.depth_of_subsingleton [Subsingleton M] :
    Module.depth R M = ⊤ := by
  rw [Module.depth, sSup_eq_top]
  rintro (_ | b) hb
  · cases hb.ne rfl
  · refine ⟨_, ⟨List.replicate b.succ 0,
      (Sequence.isWeaklyRegular_iff_Fin ..).mpr fun i ↦ ?_, by simp, by simp⟩,
      WithTop.coe_lt_coe.mpr (b.lt_succ_self)⟩
    exact fun _ _ _ ↦ Subsingleton.elim _ _

lemma Module.depth_of_isScalarTower :
    Module.depth R M ≤ Module.depth S M := by
  refine sSup_le_sSup ?_
  rintro _ ⟨s, hs₁, hs₂, rfl⟩
  rw [← Sequence.isWeaklyRegular_map_algebraMap_iff S M s] at hs₁
  exact ⟨_, hs₁, by simpa, by simp⟩

@[stacks 00LK]
lemma Module.depth_le_krullDim_support [Nontrivial M] [Module.Finite R M] :
    .some (Module.depth R M) ≤ Order.krullDim (Module.support R M) := by
  have : Nonempty (Module.support R M) := by
    rwa [Set.nonempty_coe_sort, Set.nonempty_iff_ne_empty,
      ne_eq, support_eq_empty_iff, not_subsingleton_iff_nontrivial]
  cases h : Order.krullDim (Module.support R M) with
  | bot => simpa using Order.krullDim_nonneg.trans_eq h
  | coe n =>
  cases n with
  | top => simp
  | coe n =>
  clear this
  simp only [WithBot.coe_le_coe, ge_iff_le]
  induction n using Nat.strong_induction_on generalizing M with
  | h n IH =>
    rw [depth, sSup_le_iff]
    rintro _ ⟨l, hl, hl', rfl⟩
    apply WithTop.coe_le_coe.mpr ?_
    cases l with
    | nil => simp
    | cons x l =>
    simp only [Sequence.isWeaklyRegular_cons_iff] at hl
    have : Nontrivial (QuotSMulTop x M) := by
      apply Submodule.Quotient.nontrivial_of_lt_top
      rw [← Submodule.ideal_span_singleton_smul, lt_top_iff_ne_top, ne_comm]
      apply Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator
      refine le_trans ?_ (maximalIdeal_le_jacobson _)
      rw [Ideal.span_le, Set.singleton_subset_iff]
      exact hl' _ (by simp)
    rw [Module.support_eq_zeroLocus, ← ringKrullDim_quotient] at h
    let f : (R ⧸ annihilator R M) ⧸ Ideal.span {(Ideal.Quotient.mk (annihilator R M)) x} →+*
        R ⧸ annihilator R (QuotSMulTop x M) :=
      Ideal.Quotient.lift _ (Ideal.quotientMap _ (.id R)
        (LinearMap.annihilator_le_of_surjective _ (Submodule.mkQ_surjective _)))
        (show Ideal.span _ ≤ RingHom.ker _ by
          rw [Ideal.span_le, Set.singleton_subset_iff]
          simp only [SetLike.mem_coe, RingHom.mem_ker, Ideal.quotientMap_mk, RingHom.id_apply,
            Ideal.Quotient.eq_zero_iff_mem, Module.mem_annihilator]
          intro m
          obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ m
          rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
          exact ⟨m, trivial, rfl⟩)
    have hf : Function.Surjective f := by
      apply Ideal.Quotient.lift_surjective_of_surjective
      apply Ideal.Quotient.lift_surjective_of_surjective
      exact Ideal.Quotient.mk_surjective
    have := ringKrullDim_quotient_succ_le_of_nonZeroDivisor (R := R ⧸ annihilator R M) x (by
      intro z hz
      obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective z
      simp only [← map_mul, Ideal.Quotient.eq_zero_iff_mem,
        Module.mem_annihilator] at hz ⊢
      intro m
      apply hl.1
      simpa [smul_comm x, mul_smul] using hz m)
    rw [h] at this
    replace this := (add_le_add (ringKrullDim_le_of_surjective f hf) le_rfl).trans this
    cases h : ringKrullDim (R ⧸ annihilator R (QuotSMulTop x M)) with
    | bot =>
      have : Nontrivial (R ⧸ annihilator R (QuotSMulTop x M)) := by
        apply Ideal.Quotient.nontrivial
        rw [← Submodule.annihilator_top, ne_eq, Submodule.annihilator_eq_top_iff]
        exact top_ne_bot
      have := ringKrullDim_nonneg_of_nontrivial.trans_eq h
      simp at this
    | coe m =>
    cases m with
    | top =>
      have : (⊤ : ℕ∞) ≤ (n : ℕ) := by apply WithBot.coe_le_coe.mp; simpa only [h] using this
      cases (ENat.coe_lt_top n).not_le this
    | coe m =>
    rw [h] at this
    replace this : m + 1 ≤ n := WithTop.coe_le_coe.mp (WithBot.coe_le_coe.mp this)
    replace IH := IH m (Nat.succ_le.mp this) (QuotSMulTop x M)
      (by rwa [Module.support_eq_zeroLocus, ← ringKrullDim_quotient])
    replace IH := WithTop.coe_le_coe.mp
      ((Module.length_le_depth _ _ l hl.2 (by simp_all)).trans IH)
    · simp only [List.length_cons, Nat.cast_add, Nat.cast_one, ge_iff_le]
      linarith

lemma Module.depth_le_dim_annihilator
    [Nontrivial M] [Module.Finite R M] :
    .some (Module.depth R M) ≤ ringKrullDim (R ⧸ Module.annihilator R M) := by
  rw [ringKrullDim_quotient, ← Module.support_eq_zeroLocus]
  exact Module.depth_le_krullDim_support _ _

lemma Module.depth_le_dim [Nontrivial M] [Module.Finite R M] :
    .some (Module.depth R M) ≤ ringKrullDim R :=
  (depth_le_dim_annihilator R M).trans (ringKrullDim_quotient_le _)

lemma isSMulRegular_iff_of_free {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [Module.Free R M] [Nontrivial M] {r : R} :
    IsSMulRegular M r ↔ IsSMulRegular R r := by
  let I := Module.Free.ChooseBasisIndex R M
  let b : Basis I R M := Module.Free.chooseBasis R M
  constructor
  · intro H m n h
    have i := Nonempty.some (inferInstanceAs (Nonempty I))
    have := @H (m • b i) (n • b i) (by simp_all [← mul_smul])
    simpa using congr(b.repr $this i)
  · intro H m n h
    apply b.repr.injective
    ext i
    replace h := congr(b.repr $h i)
    simp only [map_smul] at h
    exact H h

lemma RingTheory.Sequence.isWeaklyRegular_of_subsingleton
    {R : Type*} (M : Type*) [CommRing R] [AddCommGroup M] [Module R M]
    [Subsingleton R] (s : List R) : Sequence.IsWeaklyRegular M s :=
  have : Subsingleton M := Module.subsingleton R M
  (isWeaklyRegular_iff_Fin ..).mpr fun _ _ _ _ ↦ Subsingleton.elim _ _

universe u v in
open scoped Pointwise TensorProduct in
lemma RingTheory.Sequence.isWeaklyRegular_of_free_aux
    {R : Type u} {M : Type max u v} [CommRing R] [AddCommGroup M] [Module R M]
    [Module.Free R M] [Nontrivial M] {s : List R} :
      Sequence.IsWeaklyRegular M s ↔ Sequence.IsWeaklyRegular R s := by
  generalize hn : s.length = n
  induction n generalizing R M with
  | zero => simp_all
  | succ n IH =>
    cases s with
    | nil => simp at hn
    | cons x xs =>
    let e : QuotSMulTop x R ≃ₗ[R] R ⧸ Ideal.span {x} := Submodule.quotEquivOfEq _ _
      (by rw [← Submodule.ideal_span_singleton_smul]; simp)
    let e' := QuotSMulTop.equivQuotTensor x M
    rw [Sequence.isWeaklyRegular_cons_iff, Sequence.isWeaklyRegular_cons_iff,
      e.isWeaklyRegular_congr, e'.isWeaklyRegular_congr,
      ← isWeaklyRegular_map_algebraMap_iff (R ⧸ Ideal.span {x}),
      ← isWeaklyRegular_map_algebraMap_iff (R := R) (R ⧸ Ideal.span {x})]
    refine and_congr isSMulRegular_iff_of_free ?_
    cases subsingleton_or_nontrivial (R ⧸ Ideal.span {x})
    · simp [RingTheory.Sequence.isWeaklyRegular_of_subsingleton]
    exact IH (by simp_all)

lemma RingTheory.Sequence.isWeaklyRegular_of_free
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [Module.Free R M] [Nontrivial M] {s : List R} :
      Sequence.IsWeaklyRegular M s ↔ Sequence.IsWeaklyRegular R s := by
  let b := Module.Free.chooseBasis R M
  have : Nontrivial R := Module.nontrivial R M
  rw [b.repr.isWeaklyRegular_congr, isWeaklyRegular_of_free_aux]

lemma Module.depth_le_of_free [Module.Free R M] : Module.depth R R ≤ Module.depth R M := by
  cases subsingleton_or_nontrivial M
  · simp [Module.depth_of_subsingleton]
  apply sSup_le_sSup
  rintro _ ⟨s, hs, hs', rfl⟩
  refine ⟨s, Sequence.isWeaklyRegular_of_free.mpr hs, hs', rfl⟩

lemma Module.faithfulSMul_of_depth_eq_ringKrullDim [IsDomain R] [Nontrivial M] [Module.Finite R M]
    (H : ringKrullDim R < ⊤) (H' : .some (Module.depth R M) = ringKrullDim R) :
    FaithfulSMul R M := by
  have : Nontrivial (R ⧸ annihilator R M) := Ideal.Quotient.nontrivial
    (by rw [ne_eq, ← Submodule.annihilator_top, Submodule.annihilator_eq_top_iff]
        exact top_ne_bot)
  rw [← Module.annihilator_eq_bot]
  by_contra H''
  apply (le_refl ((.some (Module.depth R M)) : WithBot ℕ∞)).not_lt
  calc
    _ ≤ ringKrullDim (R ⧸ annihilator R M) := Module.depth_le_dim_annihilator _ _
    _ < ringKrullDim R := by
      simp only [ringKrullDim, Order.krullDim_eq_iSup_length,
        WithBot.coe_lt_coe]
      rw [← ENat.add_one_le_iff, ENat.iSup_add, iSup_le_iff]
      · intro l
        let l' : LTSeries (PrimeSpectrum R) := (l.map
          (PrimeSpectrum.comap (Ideal.Quotient.mk _)) ?_).cons ⊥ ?_
        · refine le_trans ?_ (le_iSup _ l')
          show _ ≤ ((0 + l.length + 1 : ℕ) : ℕ∞)
          simp
        · intros I J
          show I < J → I.asIdeal.comap _ < J.asIdeal.comap _
          simp [lt_iff_le_not_le, ← Ideal.map_le_iff_le_comap,
            Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective]
        · refine (bot_lt_iff_ne_bot.mpr H'').trans_le ?_
          conv_lhs => rw [← Ideal.mk_ker (I := annihilator R M), RingHom.ker]
          exact Ideal.comap_mono bot_le
      · rw [← lt_top_iff_ne_top]
        apply WithBot.coe_lt_coe.mp
        rw [← Order.krullDim_eq_iSup_length, ← ringKrullDim]
        refine (ringKrullDim_quotient_le _).trans_lt H
    _ = .some (Module.depth R M) := H'.symm
