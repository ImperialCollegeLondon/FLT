import Mathlib -- **TODO** fix when finished or if `exact?` is too slow
--import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
--import Mathlib.NumberTheory.NumberField.Basic
--import Mathlib.NumberTheory.RamificationInertia
/-!

# Base change of adele rings.

If `A` is a Dedekind domain with field of fractions `K`, if `L/K` is a finite separable
extension and if `B` is the integral closure of `A` in `L`, then `B` is also a Dedekind
domain. Hence the rings of finite adeles `𝔸_K^∞` and `𝔸_L^∞` (defined using `A` and `B`)
are defined. In this file we define the natural `K`-algebra map `𝔸_K^∞ → 𝔸_L^∞` and
the natural `L`-algebra map `𝔸_K^∞ ⊗[K] L → 𝔸_L^∞`, and show that the latter map
is an isomorphism.

-/

-- The general set-up.

variable (A K L B : Type*) [CommRing A] [CommRing B] [Algebra A B] [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K] [Algebra B L] [IsDedekindDomain A]
    [Algebra K L] [Algebra A L] [IsScalarTower A B L] [IsScalarTower A K L]
    [IsIntegralClosure B A L] [FiniteDimensional K L]

variable [Algebra.IsSeparable K L]

-- example : IsDedekindDomain B := IsIntegralClosure.isDedekindDomain A K L B
variable [IsDedekindDomain B]

-- example : IsFractionRing B L := IsIntegralClosure.isFractionRing_of_finite_extension A K L B
variable [IsFractionRing B L]

-- example : IsDomain B := IsDomain.mk
variable [IsDomain B]

-- example : Algebra.IsIntegral A B := IsIntegralClosure.isIntegral_algebra A L
variable [Algebra.IsIntegral A B]

-- I can't find in mathlib the assertion that B is a finite A-module.
-- But it is!
example : Module.Finite A B := by
  have := IsIntegralClosure.isNoetherian A K L B
  exact Module.IsNoetherian.finite A B

/-
In this generality there's a natural isomorphism `L ⊗[K] 𝔸_K^∞ → 𝔸_L^∞` .

Update: Javier suggests p21 of
https://math.berkeley.edu/~ltomczak/notes/Mich2022/LF_Notes.pdf
-/

-- We start by filling in some holes in the API for finite extensions of Dedekind domains.
namespace IsDedekindDomain

namespace HeightOneSpectrum

-- first need a way to pull back valuations on B to A
variable {B L} in
def comap (w : HeightOneSpectrum B) : HeightOneSpectrum A where
  asIdeal := w.asIdeal.comap (algebraMap A B)
  isPrime := Ideal.comap_isPrime (algebraMap A B) w.asIdeal
  ne_bot := mt Ideal.eq_bot_of_comap_eq_bot w.ne_bot

open scoped algebraMap

lemma mk_count_factors_map
    (hAB : Function.Injective (algebraMap A B))
    (w : HeightOneSpectrum B) (I : Ideal A) [DecidableEq (Associates (Ideal A))]
  [DecidableEq (Associates (Ideal B))] [∀ p : Associates (Ideal A), Decidable (Irreducible p)]
  [∀ p : Associates (Ideal B), Decidable (Irreducible p)] :
    (Associates.mk w.asIdeal).count (Associates.mk (Ideal.map (algebraMap A B) I)).factors =
    Ideal.ramificationIdx (algebraMap A B) (comap A w).asIdeal w.asIdeal *
      (Associates.mk (comap A w).asIdeal).count (Associates.mk I).factors := by
  classical
  induction I using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ =>
    rw [Associates.mk_zero, Ideal.zero_eq_bot, Ideal.map_bot, ← Ideal.zero_eq_bot,
      Associates.mk_zero]
    simp [Associates.count, Associates.factors_zero, w.associates_irreducible,
      associates_irreducible (comap A w), Associates.bcount]
  | h₂ I hI =>
    obtain rfl : I = ⊤ := by simpa using hI
    simp only [Submodule.zero_eq_bot, ne_eq, top_ne_bot, not_false_eq_true, Ideal.map_top]
    simp only [← Ideal.one_eq_top, Associates.mk_one, Associates.factors_one]
    rw [Associates.count_zero (associates_irreducible _),
      Associates.count_zero (associates_irreducible _), mul_zero]
  | h₃ I p hI hp IH =>
    simp only [Ideal.map_mul, ← Associates.mk_mul_mk]
    have hp_bot : p ≠ ⊥ := hp.ne_zero
    have hp_bot' := (Ideal.map_eq_bot_iff_of_injective hAB).not.mpr hp_bot
    have hI_bot := (Ideal.map_eq_bot_iff_of_injective hAB).not.mpr hI
    rw [Associates.count_mul (Associates.mk_ne_zero.mpr hp_bot) (Associates.mk_ne_zero.mpr hI)
      (associates_irreducible _), Associates.count_mul (Associates.mk_ne_zero.mpr hp_bot')
      (Associates.mk_ne_zero.mpr hI_bot) (associates_irreducible _)]
    simp only [IH, mul_add]
    congr 1
    by_cases hw : (w.comap A).asIdeal = p
    · have : Irreducible (Associates.mk p) := Associates.irreducible_mk.mpr hp.irreducible
      rw [hw, Associates.factors_self this, Associates.count_some this]
      simp only [UniqueFactorizationMonoid.factors_eq_normalizedFactors, Multiset.nodup_singleton,
        Multiset.mem_singleton, Multiset.count_eq_one_of_mem, mul_one]
      rw [count_associates_factors_eq hp_bot' w.2 w.3,
        Ideal.IsDedekindDomain.ramificationIdx_eq_normalizedFactors_count hp_bot' w.2 w.3]
    · have : (Associates.mk (comap A w).asIdeal).count (Associates.mk p).factors = 0 :=
        Associates.count_eq_zero_of_ne (associates_irreducible _)
          (Associates.irreducible_mk.mpr hp.irreducible)
          (by rwa [ne_eq, Associates.mk_eq_mk_iff_associated, associated_iff_eq])
      rw [this, mul_zero, eq_comm]
      by_contra H
      rw [eq_comm, ← ne_eq, Associates.count_ne_zero_iff_dvd hp_bot' (irreducible w),
        Ideal.dvd_iff_le, Ideal.map_le_iff_le_comap] at H
      apply hw (((Ideal.isPrime_of_prime hp).isMaximal hp_bot).eq_of_le (comap A w).2.ne_top H).symm

lemma intValuation_comap (hAB : Function.Injective (algebraMap A B))
    (w : HeightOneSpectrum B) (x : A) :
    (comap A w).intValuation x ^
    (Ideal.ramificationIdx (algebraMap A B) (comap A w).asIdeal w.asIdeal) =
    w.intValuation (algebraMap A B x) := by
  classical
  have h_ne_zero : Ideal.ramificationIdx (algebraMap A B) (comap A w).asIdeal w.asIdeal ≠ 0 :=
    Ideal.IsDedekindDomain.ramificationIdx_ne_zero
      ((Ideal.map_eq_bot_iff_of_injective hAB).not.mpr (comap A w).3) w.2 Ideal.map_comap_le
  by_cases hx : x = 0
  · simpa [hx]
  simp only [intValuation, Valuation.coe_mk, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk]
  show (ite _ _ _) ^ _ = ite _ _ _
  by_cases hx : x = 0
  · subst hx; simp [h_ne_zero]
  rw [map_eq_zero_iff _ hAB, if_neg hx, if_neg hx, ← Set.image_singleton, ← Ideal.map_span,
    mk_count_factors_map _ _ hAB, mul_comm]
  simp

-- Need to know how the valuation `w` and its pullback are related on elements of `K`.
omit [IsIntegralClosure B A L] [FiniteDimensional K L] [Algebra.IsSeparable K L] in
lemma valuation_comap (w : HeightOneSpectrum B) (x : K) :
    (comap A w).valuation x ^
    (Ideal.ramificationIdx (algebraMap A B) (comap A w).asIdeal w.asIdeal) =
    w.valuation (algebraMap K L x) := by
  obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective (A := A) x
  simp [valuation, ← IsScalarTower.algebraMap_apply A K L, IsScalarTower.algebraMap_apply A B L,
    ← intValuation_comap A B (algebraMap_injective_of_field_isFractionRing A B K L), div_pow]

-- Say w is a finite place of L lying above v a finite places
-- of K. Then there's a ring hom K_v -> L_w.
variable {B L} in
noncomputable def adicCompletion_comap_ringHom (w : HeightOneSpectrum B) :
    (adicCompletion K (comap A w)) →+* (adicCompletion L w) :=
  letI : UniformSpace K := (comap A w).adicValued.toUniformSpace;
  letI : UniformSpace L := w.adicValued.toUniformSpace;
  UniformSpace.Completion.mapRingHom (algebraMap K L) <| by
  -- question is the following:
  -- if L/K is a finite extension of sensible fields (e.g. number fields)
  -- and if w is a finite place of L lying above v a finite place of K,
  -- and if we give L the w-adic topology and K the v-adic topology,
  -- then the map K → L is continuous
  refine continuous_of_continuousAt_zero (algebraMap K L) ?hf
  delta ContinuousAt
  simp only [map_zero]
  rw [(@Valued.hasBasis_nhds_zero K _ _ _ (comap A w).adicValued).tendsto_iff
    (@Valued.hasBasis_nhds_zero L _ _ _ w.adicValued)]
  simp only [HeightOneSpectrum.adicValued_apply, Set.mem_setOf_eq, true_and, true_implies]
  -- Modulo the fact that the division doesn't make sense, the next line is
  -- "refine fun i ↦ ⟨i ^ (1 / Ideal.ramificationIdx (algebraMap A B) (comap A w).asIdeal w.asIdeal), fun _ h ↦ ?_⟩"
  -- now use `valuation_comap` to finish
  sorry


noncomputable local instance (w : HeightOneSpectrum B) :
    Algebra K (adicCompletion L w) := RingHom.toAlgebra <|
  (algebraMap L (adicCompletion L w)).comp (algebraMap K L)


variable {B L} in
noncomputable def adicCompletion_comap_algHom (w : HeightOneSpectrum B) :
    (HeightOneSpectrum.adicCompletion K (comap A w)) →ₐ[K] (HeightOneSpectrum.adicCompletion L w) := by
    use adicCompletion_comap_ringHom A K w
    intro r
    simp only [RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe,
      MonoidHom.coe_coe]
    have : (adicCompletion_comap_ringHom A K w) (r : adicCompletion K (comap A w))  =
    (algebraMap L (adicCompletion L w)) (algebraMap K L r) := by
      letI : UniformSpace L := w.adicValued.toUniformSpace;
      letI : UniformSpace K := (comap A w).adicValued.toUniformSpace;
      rw [adicCompletion_comap_ringHom]
      rw [UniformSpace.Completion.mapRingHom]
      have h : @UniformSpace.Completion.coe' K this r  = (r : adicCompletion K (comap A w)) := by
        rfl
      rw [← h]
      rw [UniformSpace.Completion.extensionHom_coe
      (UniformSpace.Completion.coeRingHom.comp (algebraMap K L))
      (UniformSpace.Completion.mapRingHom.proof_2 (algebraMap K L)
      (adicCompletion_comap_ringHom.proof_4 A K w) :
      Continuous ⇑(UniformSpace.Completion.coeRingHom.comp Algebra.toRingHom)) r]
      rfl
    rw [this]
    rfl

end IsDedekindDomain.HeightOneSpectrum

namespace DedekindDomain

open IsDedekindDomain HeightOneSpectrum

open scoped TensorProduct -- ⊗ notation for tensor product

-- make `∏_w L_w` into an algebra over `K` (it's already
-- an algebra over `L` which is a `K`-algebra).
noncomputable local instance : Algebra K (ProdAdicCompletions B L) := RingHom.toAlgebra <|
  (algebraMap L (ProdAdicCompletions B L)).comp (algebraMap K L)

-- These should be easy but I've just noticed that it should be an alghom
noncomputable def ProdAdicCompletions.baseChange :
    L ⊗[K] ProdAdicCompletions A K →ₗ[K] ProdAdicCompletions B L := TensorProduct.lift <| {
  toFun := fun l ↦ {
    toFun := fun kv w ↦ l • (adicCompletion_comap_algHom A K w (kv (comap A w)))
    map_add' := sorry
    map_smul' := sorry
  }
  map_add' := sorry
  map_smul' := sorry
}

-- This is harder
theorem ProdAdicCompletions.baseChange_surjective :
  Function.Surjective (ProdAdicCompletions.baseChange A K L B) := sorry

-- hard but hopefully enough (this proof will be a lot of work)
theorem ProdAdicCompletions.baseChange_iso (x : ProdAdicCompletions A K) :
  ProdAdicCompletions.IsFiniteAdele x ↔
  ProdAdicCompletions.IsFiniteAdele (ProdAdicCompletions.baseChange A K L B (1 ⊗ₜ x)) := sorry

noncomputable local instance : Algebra K (FiniteAdeleRing B L) := RingHom.toAlgebra <|
  (algebraMap L (FiniteAdeleRing B L)).comp (algebraMap K L)

def FiniteAdeleRing.baseChange : L ⊗[K] FiniteAdeleRing A K ≃ₗ[K] FiniteAdeleRing B L := by
  -- modulo the sorries above this should be easy
  sorry

end DedekindDomain
