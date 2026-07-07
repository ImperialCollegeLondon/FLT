/-
Copyright (c) 2025 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McCarthy
-/
module

public import FLT.Slop.BrauerInduction.Background.FDRep.Simple

@[expose] public section

/-!
# Central characters and central kernels

This file defines the central character of a simple finite-dimensional
representation. By Schur's lemma, every central element acts by a scalar; these
scalars form a multiplicative character of the center.

-/

universe u v

open CategoryTheory

namespace FDRep

section endoOfCentral

variable {k : Type u} [Field k]
variable {G : Type v} [Group G]

/--
The endomorphism of a representation induced by the action of a central
element.
-/
noncomputable def endoOfCentral
    (ρ : FDRep k G) (z : Subgroup.center G) : ρ ⟶ ρ :=
  FDRep.forget₂HomLinearEquiv ρ ρ
    (Rep.ofHom
      { toLinearMap := ρ.ρ (z : G)
        isIntertwining' := by
          intro g
          ext v
          have hz : g * (z : G) = (z : G) * g :=
            Subgroup.mem_center_iff.mp z.2 g
          change
            ρ.ρ (z : G) (ρ.ρ g v) =
              ρ.ρ g (ρ.ρ (z : G) v)
          calc
            ρ.ρ (z : G) (ρ.ρ g v)
                = (ρ.ρ (z : G) * ρ.ρ g) v := rfl
            _ = ρ.ρ ((z : G) * g) v := by
                rw [map_mul]
            _ = ρ.ρ (g * (z : G)) v := by
                rw [hz]
            _ = (ρ.ρ g * ρ.ρ (z : G)) v := by
                rw [map_mul]
            _ = ρ.ρ g (ρ.ρ (z : G) v) := rfl })

/--
Evaluation of the endomorphism induced by a central element.
-/
@[simp]
lemma endoOfCentral_homToLinearMap_apply
    (ρ : FDRep k G) (z : Subgroup.center G) (v : ρ) :
    FDRep.homToLinearMap (FDRep.endoOfCentral ρ z) v =
      ρ.ρ (z : G) v := by
  rfl

end endoOfCentral

section Center

variable {k : Type u} [Field k] [IsAlgClosed k]
variable {G : Type v} [Group G]


/--
Schur's lemma applied to the center: every central element acts as a scalar on
a simple representation.
-/
lemma center_action_is_scalar
    (ρ : FDRep k G) [Simple ρ] (z : Subgroup.center G) :
    ∃ c : k, ρ.ρ z = c • LinearMap.id := by
  let f : ρ ⟶ ρ := endoOfCentral ρ z
  obtain ⟨c, hc⟩ := end_eq_smul_id_of_simple ρ f
  refine ⟨c, ?_⟩
  ext v
  have h_apply :
      f.hom v = (c • 𝟙 ρ : ρ ⟶ ρ).hom v := by
    exact congrArg (fun m : ρ ⟶ ρ => m.hom v) hc
  have hL : f.hom v = ρ.ρ (z : G) v := by
    change (endoOfCentral ρ z).hom v = ρ.ρ (z : G) v
    rfl
  have hR : (c • 𝟙 ρ : ρ ⟶ ρ).hom v = c • v := by
    change (c • (𝟙 ρ : ρ ⟶ ρ).hom) v = c • v
    rfl
  rw [hL, hR] at h_apply
  simpa using h_apply

/--
The scalar by which a central element acts on a simple representation.
-/
noncomputable def centralScalar
    (ρ : FDRep k G) [Simple ρ]
    (z : Subgroup.center G) : k :=
  Classical.choose (center_action_is_scalar ρ z)

/--
The defining property of `centralScalar`.
-/
lemma centralScalar_spec
    (ρ : FDRep k G) [Simple ρ]
    (z : Subgroup.center G) :
    ρ.ρ (z : G) =
      centralScalar ρ z • LinearMap.id :=
  Classical.choose_spec (center_action_is_scalar ρ z)

/--
The identity central element acts by the scalar `1`.
-/
lemma centralScalar_one
    (ρ : FDRep k G) [Simple ρ] :
    centralScalar ρ (1 : Subgroup.center G) = 1 := by
  apply FDRep.smul_id_injective (ρ := ρ)
  change
    centralScalar ρ (1 : Subgroup.center G) •
        (LinearMap.id : ρ →ₗ[k] ρ)
      =
    (1 : k) • (LinearMap.id : ρ →ₗ[k] ρ)
  rw [← centralScalar_spec (ρ := ρ) (z := 1)]
  simp only [OneMemClass.coe_one, map_one, Module.End.one_eq_id, one_smul]

/--
The scalar action of central elements is multiplicative.
-/
lemma centralScalar_mul
    (ρ : FDRep k G) [Simple ρ]
    (z₁ z₂ : Subgroup.center G) :
    centralScalar ρ (z₁ * z₂) =
      centralScalar ρ z₁ * centralScalar ρ z₂ := by
  let I : ρ →ₗ[k] ρ := LinearMap.id
  have hinj : Function.Injective fun a : k => a • I := by
    simpa [I] using FDRep.smul_id_injective (ρ := ρ)
  apply hinj
  change
    centralScalar ρ (z₁ * z₂) • I =
      (centralScalar ρ z₁ * centralScalar ρ z₂) • I
  rw [← centralScalar_spec ρ (z₁ * z₂)]
  rw [Subgroup.coe_mul, map_mul]
  rw [centralScalar_spec ρ z₁, centralScalar_spec ρ z₂]
  simp only [I]
  ext v
  simp only [Algebra.mul_smul_comm, Algebra.smul_mul_assoc, LinearMap.smul_apply,
    Module.End.mul_apply, LinearMap.id_coe, id_eq]
  rw [smul_smul, mul_comm]

/--
The scalar by which a central element acts is nonzero.
-/
lemma centralScalar_ne_zero
    (ρ : FDRep k G) [Simple ρ]
    (z : Subgroup.center G) :
    centralScalar ρ z ≠ 0 := by
  intro hzero
  have hρz_zero : ρ.ρ (z : G) = 0 := by
    rw [centralScalar_spec ρ z, hzero]
    simp
  have hprod :
      ρ.ρ (z : G) * ρ.ρ ((z⁻¹ : Subgroup.center G) : G) = 1 := by
    rw [← map_mul]
    simp
  rw [hρz_zero, zero_mul] at hprod
  have hid_ne :
      (LinearMap.id : ρ →ₗ[k] ρ) ≠ 0 :=
    linearMap_id_ne_zero_of_simple ρ
  apply hid_ne
  change (1 : ρ →ₗ[k] ρ) = 0
  simpa using hprod.symm

/--
The central character of a simple representation.

It sends a central element to the unit given by its scalar action.
-/
noncomputable def centralCharacter
    (ρ : FDRep k G) [Simple ρ] :
    Subgroup.center G →* kˣ :=
{ toFun := fun z => Units.mk0 (centralScalar ρ z) (centralScalar_ne_zero ρ z)
  map_one' := by
    apply Units.ext
    simp [centralScalar_one]
  map_mul' := by
    intro z₁ z₂
    apply Units.ext
    simp [centralScalar_mul] }

end Center

section centralKernel

variable {k : Type u} [Field k] [IsAlgClosed k]
variable {G : Type v} [Group G]

/--
The central kernel of a simple representation.

This is the subgroup of central elements acting trivially on the representation.
-/
noncomputable def centralKernel
    (ρ : FDRep k G) [Simple ρ] :
    Subgroup G :=
  Subgroup.map
    (Subgroup.center G).subtype
    (MonoidHom.ker (centralCharacter ρ))

/--
The central kernel is contained in the center.
-/
lemma centralKernel_le_center
    (ρ : FDRep k G) [Simple ρ] :
    centralKernel ρ ≤ Subgroup.center G := by
  intro g hg
  rcases (Subgroup.mem_map).1 hg with ⟨z, hz, rfl⟩
  exact z.2

/--
The central kernel is a normal subgroup.
-/
instance centralKernel_normal
    (ρ : FDRep k G) [Simple ρ] :
    (centralKernel ρ).Normal where
  conj_mem := by
    intro x hx g
    rcases (Subgroup.mem_map).1 hx with ⟨z, hz, rfl⟩
    have hcomm : g * (z : G) = (z : G) * g :=
      Subgroup.mem_center_iff.mp z.2 g
    have hconj : g * (z : G) * g⁻¹ = z := by
      calc
        g * (z : G) * g⁻¹ = (z : G) * g * g⁻¹ := by
          rw [hcomm]
        _ = z := by
          simp [mul_assoc]
    simpa only [Subgroup.subtype_apply, hconj]

/--
Every element of the central kernel acts trivially.
-/
lemma centralKernel_acts_trivially
    (ρ : FDRep k G) [Simple ρ]
    (g : centralKernel ρ) :
    ρ.ρ (g : G) = 1 := by
  rcases (Subgroup.mem_map).1 g.2 with ⟨z, hz, hz_eq⟩
  rw [← hz_eq]
  have hz_char :
      centralCharacter ρ z = 1 := hz
  have hz_scalar :
      centralScalar ρ z = 1 := by
    simpa [centralCharacter] using congrArg Units.val hz_char
  change ρ.ρ (z : G) = 1
  rw [centralScalar_spec ρ z, hz_scalar]
  simp only [Module.End.one_eq_id, one_smul]

/--
A central element lies in the central kernel iff it acts trivially.
-/
lemma center_coe_mem_centralKernel_iff
    (ρ : FDRep k G) [Simple ρ]
    (z : Subgroup.center G) :
    (z : G) ∈ centralKernel ρ ↔
      ρ.ρ (z : G) = 1 := by
  constructor
  · intro hz
    exact centralKernel_acts_trivially ρ ⟨(z : G), hz⟩
  · intro hz
    refine (Subgroup.mem_map).2 ?_
    refine ⟨z, ?_, rfl⟩
    apply Units.ext
    change centralScalar ρ z = 1
    apply FDRep.smul_id_injective ρ
    change
      centralScalar ρ z •
          (LinearMap.id : ρ →ₗ[k] ρ)
        =
      (1 : k) •
          (LinearMap.id : ρ →ₗ[k] ρ)
    rw [← centralScalar_spec ρ z, hz]
    simp only [Module.End.one_eq_id, one_smul]

/--
The representation is trivial on its central kernel.
-/
lemma rho_eq_one_of_mem_centralKernel
    (ρ : FDRep k G) [Simple ρ] :
    ∀ x ∈ centralKernel ρ, ρ.ρ x = 1 := by
  intro x hx
  exact centralKernel_acts_trivially ρ ⟨x, hx⟩

end centralKernel

end FDRep
