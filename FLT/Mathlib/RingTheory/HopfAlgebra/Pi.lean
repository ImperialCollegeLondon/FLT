/-
Copyright (c) 2025 Bryan Wang Peng Jun. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Wang Peng Jun
-/
module

public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.TensorProduct.Pi
public import Mathlib.LinearAlgebra.StdBasis

/-!
# The Hopf algebra of functions on a finite group

Given a finite group `G` and a commutative ring `S`, the ring `G → S` of `S`-valued functions
on `G` (with pointwise operations) is an `S`-Hopf algebra. This is the affine algebra of the
constant group scheme `G` over `S`, and is the dual of the group algebra `S[G]`
(`MonoidAlgebra.instHopfAlgebra`).

## Main definitions

* `Pi.instHopfAlgebra`: the `S`-Hopf algebra structure on `G → S` for a finite group `G`.

## Implementation notes

The comultiplication is dual to multiplication on `G`: it is the composite of precomposition with
multiplication `G × G → G` (in curried form `(G → S) →ₐ[S] (G → G → S)`) with the inverse of the
canonical algebra isomorphism `(G → S) ⊗[S] (G → S) ≃ₐ[S] (G → G → S)`
(`Algebra.TensorProduct.piScalarRight`, which is bijective precisely because `G` is finite). The
counit is evaluation at `1`, and the antipode is precomposition with inversion.
-/

@[expose] public section

open scoped TensorProduct

namespace Pi.HopfAlgebra

variable (S : Type*) [CommRing S]
variable (G : Type*) [Group G] [Fintype G] [DecidableEq G]

/-- Precomposition with multiplication `G × G → G`, in curried form: `f ↦ fun a b ↦ f (a * b)`,
as an `S`-algebra homomorphism `(G → S) →ₐ[S] (G → G → S)`. -/
noncomputable def comulAux : (G → S) →ₐ[S] (G → G → S) :=
  AlgHom.pi (fun a => AlgHom.pi (fun b => Pi.evalAlgHom S (fun _ : G => S) (a * b)))

omit [Fintype G] [DecidableEq G] in
@[simp]
lemma comulAux_apply (f : G → S) (a b : G) : comulAux S G f a b = f (a * b) := rfl

omit [Fintype G] in
lemma comulAux_single (g : G) :
    comulAux S G (Pi.single g 1) = fun a => Pi.single (a⁻¹ * g) (1 : S) := by
  ext a b
  simp only [comulAux_apply]
  rw [Pi.single_apply, Pi.single_apply]
  simp only [eq_inv_mul_iff_mul_eq]

/-- The comultiplication of the Hopf algebra `G → S`: precomposition with multiplication,
transported through the canonical iso `(G → S) ⊗[S] (G → S) ≃ₐ[S] (G → G → S)`. -/
noncomputable def comul : (G → S) →ₐ[S] (G → S) ⊗[S] (G → S) :=
  (Algebra.TensorProduct.piScalarRight S S (G → S) G).symm.toAlgHom.comp (comulAux S G)

/-- The counit of the Hopf algebra `G → S`: evaluation at the identity. -/
noncomputable def counit : (G → S) →ₐ[S] S := Pi.evalAlgHom S (fun _ : G => S) 1

/-- The antipode of the Hopf algebra `G → S`: precomposition with inversion. -/
noncomputable def antipode : (G → S) →ₐ[S] (G → S) :=
  AlgHom.pi (fun g => Pi.evalAlgHom S (fun _ : G => S) g⁻¹)

variable {S G}

omit [Fintype G] [DecidableEq G] in
@[simp]
lemma counit_apply (f : G → S) : counit S G f = f 1 := rfl

omit [Fintype G] [DecidableEq G] in
@[simp]
lemma antipode_apply (f : G → S) (g : G) : antipode S G f g = f g⁻¹ := rfl

omit [Fintype G] in
lemma counit_single (g : G) : counit S G (Pi.single g 1) = if (1 : G) = g then (1 : S) else 0 := by
  simp only [counit_apply, Pi.single_apply]

/-- The key formula for the comultiplication on the indicator basis. -/
lemma comul_single (g : G) :
    comul S G (Pi.single g 1) = ∑ c : G, Pi.single (c⁻¹ * g) (1 : S) ⊗ₜ[S] Pi.single c 1 := by
  have he : comul S G (Pi.single g 1)
      = (Algebra.TensorProduct.piScalarRight S S (G → S) G).symm
          (comulAux S G (Pi.single g 1)) := rfl
  rw [he, comulAux_single]
  apply (Algebra.TensorProduct.piScalarRight S S (G → S) G).injective
  rw [AlgEquiv.apply_symm_apply, map_sum]
  funext a
  rw [Finset.sum_apply]
  simp only [Algebra.TensorProduct.piScalarRight_tmul_apply]
  rw [Finset.sum_eq_single a]
  · rw [Pi.single_eq_same, one_smul]
  · intro c _ hc
    rw [Pi.single_eq_of_ne (Ne.symm hc), zero_smul]
  · intro h; exact absurd (Finset.mem_univ a) h

variable (S G)

lemma comul_counit_rTensor :
    (Algebra.TensorProduct.map (counit S G) (.id S (G → S))).comp (comul S G)
      = (Algebra.TensorProduct.lid S (G → S)).symm := by
  apply AlgHom.toLinearMap_injective
  refine Module.Basis.ext (Pi.basisFun S G) (fun i => ?_)
  simp only [AlgHom.toLinearMap_apply, Pi.basisFun_apply, AlgHom.comp_apply, comul_single,
    map_sum, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, counit_single]
  rw [Finset.sum_eq_single i]
  · rw [if_pos (inv_mul_cancel i).symm]; rfl
  · intro x _ hx
    rw [if_neg (fun h => hx (inv_mul_eq_one.1 h.symm)), TensorProduct.zero_tmul]
  · intro h; exact absurd (Finset.mem_univ i) h

lemma comul_counit_lTensor :
    (Algebra.TensorProduct.map (.id S (G → S)) (counit S G)).comp (comul S G)
      = (Algebra.TensorProduct.rid S S (G → S)).symm := by
  apply AlgHom.toLinearMap_injective
  refine Module.Basis.ext (Pi.basisFun S G) (fun i => ?_)
  simp only [AlgHom.toLinearMap_apply, Pi.basisFun_apply, AlgHom.comp_apply, comul_single,
    map_sum, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, counit_single]
  rw [Finset.sum_eq_single 1]
  · rw [if_pos rfl, inv_one, one_mul]; rfl
  · intro x _ hx
    rw [if_neg (fun h => hx h.symm), TensorProduct.tmul_zero]
  · intro h; exact absurd (Finset.mem_univ 1) h

lemma comul_coassoc :
    (Algebra.TensorProduct.assoc S S S (G → S) (G → S) (G → S)).toAlgHom.comp
      ((Algebra.TensorProduct.map (comul S G) (.id S (G → S))).comp (comul S G))
      = (Algebra.TensorProduct.map (.id S (G → S)) (comul S G)).comp (comul S G) := by
  apply AlgHom.toLinearMap_injective
  refine Module.Basis.ext (Pi.basisFun S G) (fun i => ?_)
  simp only [AlgHom.toLinearMap_apply, Pi.basisFun_apply, AlgHom.comp_apply, comul_single,
    map_sum, Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
    TensorProduct.sum_tmul, TensorProduct.tmul_sum]
  sorry

/-- The bialgebra structure on `G → S`. -/
noncomputable instance instBialgebra : Bialgebra S (G → S) :=
  Bialgebra.ofAlgHom (comul S G) (counit S G) (comul_coassoc S G)
    (comul_counit_rTensor S G) (comul_counit_lTensor S G)

lemma antipode_mul_id :
    ((Algebra.TensorProduct.lift (antipode S G) (.id S (G → S)) fun _ _ => Commute.all _ _).comp
      (Bialgebra.comulAlgHom S (G → S))) = (Algebra.ofId S (G → S)).comp
        (Bialgebra.counitAlgHom S (G → S)) := by
  sorry

lemma id_mul_antipode :
    ((Algebra.TensorProduct.lift (.id S (G → S)) (antipode S G) fun _ _ => Commute.all _ _).comp
      (Bialgebra.comulAlgHom S (G → S))) = (Algebra.ofId S (G → S)).comp
        (Bialgebra.counitAlgHom S (G → S)) := by
  sorry

/-- The Hopf algebra structure on `G → S` for a finite group `G`. -/
noncomputable instance instHopfAlgebra : HopfAlgebra S (G → S) :=
  HopfAlgebra.ofAlgHom (antipode S G) (antipode_mul_id S G) (id_mul_antipode S G)

end Pi.HopfAlgebra
