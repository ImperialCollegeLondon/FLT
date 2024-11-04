import Mathlib -- **TODO** fix when finished or if `exact?` is too slow
/-!

# Base change of adele rings.

If `A` is a Dedekind domain with field of fractions `K`, if `L/K` is a finite separable
extension and if `B` is the integral closure of `A` in `L`, then `B` is also a Dedekind
domain. Hence the rings of finite adeles `𝔸_K^∞` and `𝔸_L^∞` (defined using `A` and `B`)
are defined, and there's a canonical map `L ⊗[K] 𝔸_K^∞ → 𝔸_L^∞`. The main theorem
of this file is that it's an isomorphism. This result should be in mathlib.

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

-- I can't find in mathlib the assertion that B is a finite A-moduie.
-- It should follow from L/K finite.

/-
Conjecture: in this generality there's a natural isomorphism `L ⊗[K] 𝔸_K^∞ → 𝔸_L^∞`
I've not found a reference for this but we can try following the usual
references (which work for global fields). This is what we do below.

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

-- lemma: pushforward of pullback is P^(ram index)
lemma map_comap (w : HeightOneSpectrum B) :
    (w.comap A).asIdeal.map (algebraMap A B) =
    w.asIdeal ^ ((Ideal.ramificationIdx (algebraMap A B) (comap A w).asIdeal w.asIdeal)) := by
  -- This must be standard? Maybe a hole in the library for Dedekind domains
  -- or maybe I just missed it?
  -- simp


open scoped algebraMap



-- Need to know how the valuation `w` and its pullback are related on elements of `K`.
def intValuation_comap (w : HeightOneSpectrum B) (x : A) :
    (comap A w).intValuation x =
    w.intValuation (algebraMap A B x) ^
    (Ideal.ramificationIdx (algebraMap A B) (comap A w).asIdeal w.asIdeal) := by
  classical
  simp only [intValuation, Valuation.coe_mk, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk]
  show ite _ _ _ = (ite _ _ _) ^ _
  have h_inj : Function.Injective (algebraMap A B) := sorry
  have H₁ : Ideal.map (algebraMap A B) (comap A w).asIdeal ≠ ⊥ := by
    rw [ne_eq, Ideal.map_eq_bot_iff_of_injective h_inj]; exact (comap A w).ne_bot

  have h_ne_zero : Ideal.ramificationIdx (algebraMap A B) (comap A w).asIdeal w.asIdeal ≠ 0 := by
    apply Ideal.IsDedekindDomain.ramificationIdx_ne_zero H₁
    · exact w.2
    · rw [Ideal.map_le_iff_le_comap]
      rfl
  by_cases hx : x = 0
  · subst hx; simp [h_ne_zero]
  · rw [map_eq_zero_iff _ h_inj, if_neg hx, if_neg hx]
    rw [← WithZero.coe_pow]
    congr 1
    apply Multiplicative.toAdd.injective
    simp only [ofAdd_neg, toAdd_inv, toAdd_ofAdd, inv_pow, toAdd_pow, nsmul_eq_mul, neg_inj]
    rw [← Nat.cast_mul]
    congr 1
    apply le_antisymm
    rw [Ideal.IsDedekindDomain.ramificationIdx_eq_factors_count]


    simp only [ofAdd_neg, WithZero.coe_inv, inv_pow, inv_inj]



  -- This should follow from map_comap?
  sorry


-- Need to know how the valuation `w` and its pullback are related on elements of `K`.
def valuation_comap (w : HeightOneSpectrum B) (x : K) :
    (comap A w).valuation x =
    w.valuation (algebraMap K L x) ^
    (Ideal.ramificationIdx (algebraMap A B) (comap A w).asIdeal w.asIdeal) := by
  simp [valuation]
  -- This should follow from map_comap?
  sorry

-- Say w is a finite place of L lying above v a finite places
-- of K. Then there's a ring hom K_v -> L_w.
variable {B L} in
noncomputable def adicCompletion_comap (w : HeightOneSpectrum B) :
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
noncomputable def adicCompletion_alg_comap (w : HeightOneSpectrum B) :
    letI : Algebra K (adicCompletion L w) := RingHom.toAlgebra <|
  (algebraMap L (adicCompletion L w)).comp (algebraMap K L);
    letI : Module K (adicCompletion L w) := Algebra.toModule
    (HeightOneSpectrum.adicCompletion K (comap A w)) →ₗ[K] (HeightOneSpectrum.adicCompletion L w) :=
  sorry -- use `adicCompletion_comap` and prove it's a K-algebra homomorphism

end IsDedekindDomain.HeightOneSpectrum

namespace DedekindDomain

open IsDedekindDomain HeightOneSpectrum

open scoped TensorProduct -- ⊗ notation for tensor product

-- make `∏_w L_w` into an algebra over `K` (it's already
-- an algebra over `L` which is a `K`-algebra).
noncomputable local instance : Algebra K (ProdAdicCompletions B L) := RingHom.toAlgebra <|
  (algebraMap L (ProdAdicCompletions B L)).comp (algebraMap K L)

-- These should be easy
noncomputable def ProdAdicCompletions.baseChange :
    L ⊗[K] ProdAdicCompletions A K →ₗ[K] ProdAdicCompletions B L := TensorProduct.lift <| {
  toFun := fun l ↦ {
    toFun := fun kv w ↦ l • (adicCompletion_comap A K w (kv (comap A w)))
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
