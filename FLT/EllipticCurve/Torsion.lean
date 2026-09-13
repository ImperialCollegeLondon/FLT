/-
Copyright (c) 2024 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.Topology.Instances.ZMod
public import FLT.Deformations.RepresentationTheory.GaloisRep

import Mathlib.Topology.LocallyConstant.Basic

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

-- This theorem was well-known in the early part of the 20th century.
theorem group_theory_lemma {A : Type*} [AddCommGroup A] {n : ℕ} (hn : 0 < n) (r : ℕ)
    (h : ∀ d : ℕ, d ∣ n → Nat.card (Submodule.torsionBy ℤ A d) = d ^ r) :
    Nonempty ((Submodule.torsionBy ℤ A n) ≃+ (Fin r → (ZMod n))) := sorry

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
      one_smul := by
        intro P
        change WeierstrassCurve.Affine.Point.map (AlgHom.id k K) P = P
        exact WeierstrassCurve.Affine.Point.map_id P
      mul_smul := by
        intro g h P
        change WeierstrassCurve.Affine.Point.map ((g * h : K ≃ₐ[k] K) : K →ₐ[k] K) P =
        WeierstrassCurve.Affine.Point.map (g : K →ₐ[k] K)
            (WeierstrassCurve.Affine.Point.map (h : K →ₐ[k] K) P)
        exact (WeierstrassCurve.Affine.Point.map_map (h : K →ₐ[k] K) (g : K →ₐ[k] K) P).symm
      smul_zero := by
        intro g
        exact (WeierstrassCurve.Affine.Point.map (g : K →ₐ[k] K)).map_zero
      smul_add := by
        intro g P Q
        exact (WeierstrassCurve.Affine.Point.map (g : K →ₐ[k] K)).map_add P Q

omit [E.IsElliptic] [DecidableEq k] in
/-- The Galois action on points is continuous when the points have the discrete topology. -/
instance WeierstrassCurve.continuousSMulDiscrete_points
    (K : Type u) [Field K] [DecidableEq K] [Algebra k K] [Algebra.IsAlgebraic k K] :
    ContinuousSMulDiscrete (K ≃ₐ[k] K) (E⁄K).Point where
  isOpen_smul_eq := by
    intro P Q
    cases P with
    | zero =>
      by_cases h : Q = 0
      · subst Q
        change IsOpen {g : K ≃ₐ[k] K | (0 : (E⁄K).Point) = 0}
        simpa only [Set.ofPred_true] using
          (isOpen_univ : IsOpen (Set.univ : Set (K ≃ₐ[k] K)))
      · change IsOpen {g : K ≃ₐ[k] K | (0 : (E⁄K).Point) = Q}
        simpa only [Ne.symm h, Set.ofPred_false] using
          (isOpen_empty : IsOpen (∅ : Set (K ≃ₐ[k] K)))
    | some x y hP =>
      cases Q with
      | zero =>
        change IsOpen {g : K ≃ₐ[k] K | Point.map (g : K →ₐ[k] K) (.some x y hP) = 0}
        simpa only [Point.map_some, reduceCtorEq, Set.ofPred_false] using isOpen_empty
      | some x' y' hQ =>
        change IsOpen {g : K ≃ₐ[k] K |
          Point.map (g : K →ₐ[k] K) (.some x y hP) = .some x' y' hQ}
        simpa only [Point.map_some, Point.some.injEq, Set.ofPred_and, AlgEquiv.smul_def,
          AlgEquiv.coe_toAlgHom] using
          (ContinuousSMulDiscrete.isOpen_smul_eq (K ≃ₐ[k] K) x x').inter
            (ContinuousSMulDiscrete.isOpen_smul_eq (K ≃ₐ[k] K) y y')

/-- A classical decidable instance on `AlgebraicClosure ℚ`, given that there is
no hope of a constructive one with the current definition of algebraic closure. -/
noncomputable instance : DecidableEq (AlgebraicClosure ℚ) := Classical.typeDecidableEq _

/-- The algebraic Galois representation on the `n`-torsion of an elliptic curve. -/
noncomputable def WeierstrassCurve.torsionGaloisRepresentation
    {K : Type u} [Field K] (E : WeierstrassCurve K)
    [DecidableEq (AlgebraicClosure K)] (n : ℕ) :
    Field.absoluteGaloisGroup K →*
      Module.End (ZMod n) ((E.map (algebraMap K (AlgebraicClosure K))).nTorsion n) := by
  -- Identify the two presentations of the base-changed curve when synthesizing the action.
  letI : DistribMulAction (Field.absoluteGaloisGroup K)
      ((E.map (algebraMap K (AlgebraicClosure K)))⁄(AlgebraicClosure K)).Point :=
    inferInstanceAs (DistribMulAction (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
      (E⁄(AlgebraicClosure K)).Point)
  exact
    { toFun := fun g ↦ AddMonoidHom.toZModLinearMap n
        { toFun := fun P ↦ ⟨g • P.val, by
            change (n : ℤ) • (g • P.val) = 0
            have hP : (n : ℤ) • P.val = 0 := P.property
            rw [smul_comm, hP, smul_zero]⟩
          map_zero' := Subtype.ext (smul_zero g)
          map_add' := fun P Q ↦ Subtype.ext (smul_add g P.val Q.val) }
      map_one' := by
        ext P
        exact one_smul _ P.val
      map_mul' := fun g h ↦ by
        ext P
        exact mul_smul g h P.val }

/-- The torsion representation acts by applying the field automorphism to the point. -/
@[simp] theorem WeierstrassCurve.torsionGaloisRepresentation_apply
    {K : Type u} [Field K] (E : WeierstrassCurve K)
    [DecidableEq (AlgebraicClosure K)] (n : ℕ)
    (g : Field.absoluteGaloisGroup K)
    (P : (E.map (algebraMap K (AlgebraicClosure K))).nTorsion n) :
    (E.torsionGaloisRepresentation n g P).val =
      Point.map (W' := E) (g : AlgebraicClosure K →ₐ[K] AlgebraicClosure K) P.val := rfl

/-- Finitely many torsion points make the entire Galois representation locally constant. -/
theorem WeierstrassCurve.isLocallyConstant_torsionGaloisRepresentation
    {K : Type u} [Field K] (E : WeierstrassCurve K) [E.IsElliptic]
    [DecidableEq (AlgebraicClosure K)] (n : ℕ) (hn : 0 < n) :
    IsLocallyConstant (E.torsionGaloisRepresentation n) := by
  let := (E.map (algebraMap K (AlgebraicClosure K))).n_torsion_finite hn
  apply IsLocallyConstant.iff_isOpen_fiber.mpr
  intro f
  -- A fiber of the representation is a finite intersection of open point-action fibers.
  have hf : (E.torsionGaloisRepresentation n) ⁻¹' {f} =
      ⋂ P, {g | (E.torsionGaloisRepresentation n g P).val = (f P).val} := by
    ext g
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iInter, Set.mem_ofPred_eq]
    exact ⟨fun h P ↦ congrArg (fun f ↦ (f P).val) h,
      fun h ↦ LinearMap.ext fun P ↦ Subtype.ext (h P)⟩
  rw [hf]
  apply isOpen_iInter_of_finite
  intro P
  change IsOpen {g : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K |
    g • (show (E⁄(AlgebraicClosure K)).Point from P.val) =
      (show (E⁄(AlgebraicClosure K)).Point from (f P).val)}
  exact ContinuousSMulDiscrete.isOpen_smul_eq _ _ _

/-- The continuous Galois representation associated to an elliptic curve over a field. -/
noncomputable def WeierstrassCurve.galoisRep
    {K : Type u} [Field K] (E : WeierstrassCurve K) [E.IsElliptic]
    [DecidableEq (AlgebraicClosure K)] (n : ℕ) (hn : 0 < n) :
  GaloisRep K (ZMod n) ((E.map (algebraMap K (AlgebraicClosure K))).nTorsion n) :=
  letI := moduleTopology (ZMod n)
    (Module.End (ZMod n) ((E.map (algebraMap K (AlgebraicClosure K))).nTorsion n))
  { E.torsionGaloisRepresentation n with
    continuous_toFun := (E.isLocallyConstant_torsionGaloisRepresentation n hn).continuous }

/-- The continuous representation retains the coordinate action on torsion points. -/
@[simp] theorem WeierstrassCurve.galoisRep_apply
    {K : Type u} [Field K] (E : WeierstrassCurve K) [E.IsElliptic]
    [DecidableEq (AlgebraicClosure K)] (n : ℕ) (hn : 0 < n)
    (g : Field.absoluteGaloisGroup K)
    (P : (E.map (algebraMap K (AlgebraicClosure K))).nTorsion n) :
    (E.galoisRep n hn g P).val =
      Point.map (W' := E) (g : AlgebraicClosure K →ₐ[K] AlgebraicClosure K) P.val := rfl
