/-
Copyright (c) 2026 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll, Claude
-/
module

public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.DiscreteValuationRing.TFAE
public import Mathlib.FieldTheory.PrimitiveElement
public import Mathlib.RingTheory.LocalRing.Quotient
public import FLT.Mathlib.FieldTheory.SeparableDegree
public import FLT.Mathlib.RingTheory.AdjoinRoot

import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.DedekindDomain.Basic

/-!
# `R[X]/(P)` as an unramified discrete valuation ring

Proposed new Mathlib file `Mathlib.RingTheory.DiscreteValuationRing.AdjoinRoot`: for a monic
`P` over a discrete valuation ring `R` with irreducible reduction, `S = R[X]/(P)` is a discrete
valuation ring, unramified over `R`, with fraction field `K[X]/(P)` and residue field
`k[X]/(P̄)`; separability of simple extensions; auxiliary local-ring lemmas.
-/

@[expose] public section

open IsLocalRing Polynomial

universe u

/-- A ring homomorphism from a discrete valuation ring to a domain is injective as soon as its
kernel does not contain the maximal ideal: the kernel is a prime ideal, so it is either `⊥` or
the maximal ideal. -/
theorem IsDiscreteValuationRing.injective_of_not_maximalIdeal_le_ker {S L : Type*} [CommRing S]
    [IsDomain S] [IsDiscreteValuationRing S] [CommRing L] [IsDomain L] (φ : S →+* L)
    (h : ¬maximalIdeal S ≤ RingHom.ker φ) : Function.Injective φ := by
  rw [RingHom.injective_iff_ker_eq_bot]
  by_contra hne
  exact h (IsLocalRing.eq_maximalIdeal ((RingHom.ker_isPrime φ).isMaximal hne)).ge

/-- A finite separable field extension `k'/k` is `k[X]/(p)` for a monic separable irreducible
polynomial `p` of degree `[k' : k]` (the primitive element theorem, packaged via `AdjoinRoot`). -/
theorem Field.exists_monic_irreducible_adjoinRoot_algEquiv (k k' : Type*) [Field k] [Field k']
    [Algebra k k'] [FiniteDimensional k k'] [Algebra.IsSeparable k k'] :
    ∃ p : k[X], p.Monic ∧ p.Separable ∧ Irreducible p ∧ p.natDegree = Module.finrank k k' ∧
      Nonempty (AdjoinRoot p ≃ₐ[k] k') := by
  set pb := powerBasisOfFiniteOfSeparable k k' with hpb
  have hint : IsIntegral k pb.gen := Algebra.IsIntegral.isIntegral pb.gen
  exact ⟨minpoly k pb.gen, minpoly.monic hint, Algebra.IsSeparable.isSeparable k pb.gen,
    minpoly.irreducible hint, by rw [pb.natDegree_minpoly, pb.finrank],
    ⟨AdjoinRoot.equiv' _ pb (by rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]) (minpoly.aeval _ _)⟩⟩

/-- A monic polynomial over the residue field of a local ring lifts to a monic polynomial of the
same degree over the ring. -/
theorem IsLocalRing.exists_monic_map_residue_eq {A : Type u} [CommRing A] [IsLocalRing A]
    {pbar : (ResidueField A)[X]} (h : pbar.Monic) :
    ∃ P : A[X], P.Monic ∧ P.map (residue A) = pbar ∧ P.natDegree = pbar.natDegree := by
  obtain ⟨P0, hP0⟩ := Polynomial.map_surjective (residue A) Ideal.Quotient.mk_surjective pbar
  obtain ⟨P, hP_map, hP_deg, hP_monic⟩ :=
    Polynomial.lifts_and_natDegree_eq_and_monic ⟨P0, hP0⟩ h
  exact ⟨P, hP_monic, hP_map, hP_deg⟩

/-- An integral algebra `S` over a local ring `R` such that `𝔪_R · S` is a maximal ideal is
itself local, with maximal ideal `𝔪_R · S`: any maximal ideal of `S` contracts to `𝔪_R` by
integrality, hence contains `𝔪_R · S`, hence equals it. -/
theorem IsLocalRing.of_isMaximal_map_maximalIdeal {R S : Type*} [CommRing R] [IsLocalRing R]
    [CommRing S] [Algebra R S] [Algebra.IsIntegral R S]
    (hmax : ((maximalIdeal R).map (algebraMap R S)).IsMaximal) : IsLocalRing S :=
  of_unique_max_ideal ⟨(maximalIdeal R).map (algebraMap R S), hmax, fun M hM ↦ by
    have hc : (M.comap (algebraMap R S)).IsMaximal :=
      Ideal.isMaximal_comap_of_isIntegral_of_isMaximal M
    have hle : (maximalIdeal R).map (algebraMap R S) ≤ M := by
      rw [← eq_maximalIdeal hc]; exact Ideal.map_comap_le
    exact (hmax.eq_of_le hM.ne_top hle).symm⟩

/-- If `S = A[X]/(P)` is local with maximal ideal `𝔪_A · S`, then its residue field is
`(A/𝔪_A)[X]/(P mod 𝔪_A)`. -/
noncomputable def AdjoinRoot.residueFieldEquiv {A : Type*} [CommRing A] [IsLocalRing A]
    {P : A[X]} [IsLocalRing (AdjoinRoot P)]
    (hmax : maximalIdeal (AdjoinRoot P) = (maximalIdeal A).map (algebraMap A (AdjoinRoot P))) :
    ResidueField (AdjoinRoot P) ≃ₐ[A] AdjoinRoot (P.map (residue A)) :=
  (Ideal.quotientEquivAlgOfEq A hmax).trans (quotEquivQuotMap P (maximalIdeal A))

/-- The root of an irreducible separable polynomial `q` is a separable element of `F[X]/(q)`:
its minimal polynomial is `q` up to a unit. -/
theorem AdjoinRoot.isSeparable_root {F : Type*} [Field F] {q : F[X]} [Fact (Irreducible q)]
    (hq : q.Separable) : IsSeparable F (root q) := by
  have hq0 : q ≠ 0 := (Fact.out (p := Irreducible q)).ne_zero
  simp only [IsSeparable, minpoly_root hq0]
  exact hq.mul_unit (isUnit_C.mpr (isUnit_iff_ne_zero.mpr
    (inv_ne_zero (leadingCoeff_ne_zero.mpr hq0))))

/-- The simple extension `F[X]/(q)` by a root of an irreducible separable polynomial is
separable. -/
theorem AdjoinRoot.isSeparable_of_separable {F : Type*} [Field F] {q : F[X]} [Fact (Irreducible q)]
    (hq : q.Separable) : Algebra.IsSeparable F (AdjoinRoot q) :=
  .of_isSeparable_of_adjoin_eq_top (isSeparable_root hq)
    (IntermediateField.adjoin_eq_top_of_algebra (hS := adjoinRoot_eq_top))

/-- If the reduction of `P` modulo the maximal ideal of a local ring `A` is irreducible, then
`𝔪_A · A[X]/(P)` is a maximal ideal: the quotient by it is the field `(A/𝔪_A)[X]/(P̄)`. -/
theorem AdjoinRoot.isMaximal_map_maximalIdeal {A : Type*} [CommRing A] [IsLocalRing A] {P : A[X]}
    (hirr : Irreducible (P.map (residue A))) :
    ((maximalIdeal A).map (algebraMap A (AdjoinRoot P))).IsMaximal := by
  have : Fact (Irreducible (P.map (residue A))) := ⟨hirr⟩
  rw [algebraMap_eq]
  exact Ideal.Quotient.maximal_of_isField _
    ((quotAdjoinRootEquivQuotPolynomialQuot (maximalIdeal A) P).toMulEquiv.isField
      (Field.toIsField (AdjoinRoot (P.map (residue A)))))

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable {K : Type u} [Field K] [Algebra R K] [IsFractionRing R K]

/-- For a monic `P` over a discrete valuation ring `R` whose reduction is irreducible over the
residue field, `S = R[X]/(P)` is again a discrete valuation ring, *unramified* over `R`: its maximal
ideal is `𝔪_R · S` (residue field `(ResidueField R)[X]/(P̄)`), so `R → S` is a local
homomorphism. -/
theorem AdjoinRoot.isDiscreteValuationRing_of_irreducible_map_residue
    {P : R[X]} [IsDomain (AdjoinRoot P)] (hPm : P.Monic) (hP0 : P.degree ≠ 0)
    (hirr : Irreducible (P.map (residue R))) :
    ((maximalIdeal R).map (algebraMap R (AdjoinRoot P))).IsMaximal ∧
      IsDiscreteValuationRing (AdjoinRoot P) ∧ IsLocalHom (algebraMap R (AdjoinRoot P)) := by
  have : Module.Finite R (AdjoinRoot P) := hPm.finite_adjoinRoot
  have : Algebra.IsIntegral R (AdjoinRoot P) := Algebra.IsIntegral.of_finite R _
  have hmS_max := isMaximal_map_maximalIdeal hirr
  have : IsLocalRing (AdjoinRoot P) := IsLocalRing.of_isMaximal_map_maximalIdeal hmS_max
  have hmaxS : maximalIdeal (AdjoinRoot P) = (maximalIdeal R).map (algebraMap R (AdjoinRoot P)) :=
    (IsLocalRing.eq_maximalIdeal hmS_max).symm
  have hinj : Function.Injective (algebraMap R (AdjoinRoot P)) := by
    rw [algebraMap_eq]; exact of.injective_of_degree_ne_zero hP0
  have hSnotfield : ¬ IsField (AdjoinRoot P) := fun hf ↦ IsDiscreteValuationRing.not_a_field R
    ((Ideal.map_eq_bot_iff_of_injective hinj).mp
      (hmaxS ▸ IsLocalRing.isField_iff_maximalIdeal_eq.mp hf))
  have : IsDiscreteValuationRing (AdjoinRoot P) :=
    ((IsDiscreteValuationRing.TFAE (AdjoinRoot P) hSnotfield).out 4 0).mp
      (hmaxS ▸ Submodule.IsPrincipal.map_ringHom _
        (IsPrincipalIdealRing.principal (maximalIdeal R)))
  exact ⟨hmS_max, inferInstance,
    ((local_hom_TFAE (algebraMap R (AdjoinRoot P))).out 2 0).mp (le_of_eq hmaxS.symm)⟩

/-- Clearing denominators in `L = K[X]/(P·K)` over `S = R[X]/(P)`: any element of `L`, multiplied
by (the image of) a suitable nonzero element of `R`, lies in the image of `S`
(`IsLocalization.integerNormalization` for the polynomial `g` representing the element). The
hypothesis `hmap` records that `algebraMap S L` reduces `mk P` to `mk (P·K) ∘ map`. -/
theorem AdjoinRoot.exists_nonZeroDivisor_mul_eq_algebraMap {R : Type*} [CommRing R] {K : Type*}
    [Field K] [Algebra R K] [IsFractionRing R K] {P : R[X]}
    [Algebra (AdjoinRoot P) (AdjoinRoot (P.map (algebraMap R K)))]
    [IsScalarTower R (AdjoinRoot P) (AdjoinRoot (P.map (algebraMap R K)))]
    (hmap : (algebraMap (AdjoinRoot P) (AdjoinRoot (P.map (algebraMap R K)))).comp (mk P)
      = (mk (P.map (algebraMap R K))).comp (Polynomial.mapRingHom (algebraMap R K)))
    (z : AdjoinRoot (P.map (algebraMap R K))) :
    ∃ b ∈ nonZeroDivisors R, ∃ x : AdjoinRoot P,
      z * algebraMap R (AdjoinRoot (P.map (algebraMap R K))) b
        = algebraMap (AdjoinRoot P) (AdjoinRoot (P.map (algebraMap R K))) x := by
  obtain ⟨g, rfl⟩ := mk_surjective (g := P.map (algebraMap R K)) z
  obtain ⟨b, hbmem, hb⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors R) g
  refine ⟨b, hbmem,
    mk P (IsLocalization.integerNormalization (nonZeroDivisors R) g), ?_⟩
  have hR := RingHom.congr_fun hmap (IsLocalization.integerNormalization (nonZeroDivisors R) g)
  rw [RingHom.comp_apply, RingHom.comp_apply, Polynomial.coe_mapRingHom, hb] at hR
  have hkey : algebraMap R (AdjoinRoot (P.map (algebraMap R K))) b
      = mk (P.map (algebraMap R K)) (Polynomial.C (algebraMap R K b)) := by
    rw [IsScalarTower.algebraMap_apply R K (AdjoinRoot (P.map (algebraMap R K))),
      algebraMap_eq, ← mk_C]
  have hsmul : b • g = Polynomial.C (algebraMap R K b) * g := by
    rw [Algebra.smul_def, IsScalarTower.algebraMap_apply R K (Polynomial K),
      Polynomial.algebraMap_eq]
  rw [hR, hkey, hsmul, ← map_mul, mul_comm]

/-- `L = K[X]/(P·K) = Frac(S)` for `S = R[X]/(P)` a discrete valuation ring: `algebraMap S L` is
injective (its kernel is a prime of the DVR `S`, and it does not kill a uniformizer), and every
element of `L` clears its `K`-denominators (`exists_nonZeroDivisor_mul_eq_algebraMap`) to a
multiple in the image of `S`. The hypothesis `hmap` records that `algebraMap S L` reduces `mk P`
to `mk (P·K) ∘ map`. -/
theorem AdjoinRoot.isFractionRing_map {P : R[X]} (hP0 : P.degree ≠ 0)
    [IsDomain (AdjoinRoot P)] [IsDiscreteValuationRing (AdjoinRoot P)]
    [Fact (Irreducible (P.map (algebraMap R K)))]
    [Algebra (AdjoinRoot P) (AdjoinRoot (P.map (algebraMap R K)))]
    [IsScalarTower R (AdjoinRoot P) (AdjoinRoot (P.map (algebraMap R K)))]
    (hmaxS : maximalIdeal (AdjoinRoot P) = (maximalIdeal R).map (algebraMap R (AdjoinRoot P)))
    (hmap : (algebraMap (AdjoinRoot P) (AdjoinRoot (P.map (algebraMap R K)))).comp (mk P)
      = (mk (P.map (algebraMap R K))).comp (Polynomial.mapRingHom (algebraMap R K))) :
    IsFractionRing (AdjoinRoot P) (AdjoinRoot (P.map (algebraMap R K))) := by
  set S := AdjoinRoot P
  set pK := P.map (algebraMap R K)
  set L := AdjoinRoot pK
  have hinj : Function.Injective (algebraMap R S) := by
    rw [algebraMap_eq]; exact of.injective_of_degree_ne_zero hP0
  have hRL_inj : Function.Injective (algebraMap R L) := by
    rw [IsScalarTower.algebraMap_eq R K L]
    exact (algebraMap K L).injective.comp (IsFractionRing.injective R K)
  have hSL_inj : Function.Injective (algebraMap S L) :=
    IsDiscreteValuationRing.injective_of_not_maximalIdeal_le_ker _ fun hle ↦ by
      obtain ⟨ϖ, hϖmem, hϖ0⟩ :=
        Submodule.exists_mem_ne_zero_of_ne_bot (IsDiscreteValuationRing.not_a_field R)
      have hmem := hle (hmaxS.symm ▸ Ideal.mem_map_of_mem (algebraMap R S) hϖmem)
      rw [RingHom.mem_ker, ← IsScalarTower.algebraMap_apply R S L] at hmem
      exact hϖ0 (hRL_inj (by rw [hmem, map_zero]))
  refine (_root_.isLocalization_iff (nonZeroDivisors S) L).mpr ⟨fun y ↦ ?_, fun z ↦ ?_,
    fun {x y} h ↦ ⟨1, by rw [hSL_inj h]⟩⟩
  · exact isUnit_iff_ne_zero.mpr fun h ↦
      nonZeroDivisors.ne_zero y.2 (hSL_inj (by rw [h, map_zero]))
  · obtain ⟨b, hbmem, x, hx⟩ := exists_nonZeroDivisor_mul_eq_algebraMap hmap z
    refine ⟨⟨x, ⟨algebraMap R S b, mem_nonZeroDivisors_of_ne_zero fun h ↦
      nonZeroDivisors.ne_zero hbmem (hinj (by rw [h, map_zero]))⟩⟩, ?_⟩
    rwa [← IsScalarTower.algebraMap_apply R S L]

end
