/-
Copyright (c) 2025 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McCarthy
-/
module

public import FLT.Slop.BrauerInduction.Background.LinearChar.Basic
public import FLT.Slop.BrauerInduction.Background.ClassFun.Character.Basic

@[expose] public section

universe u v

variable {G : Type v} [Group G]
variable {k : Type u} [Field k]

namespace FDRep

/--
Construct a linear character from a one-dimensional representation of a group.

If `σ` is one-dimensional, choose a linear equivalence `σ ≃ₗ[k] k` and a
nonzero vector `v₀` mapping to `1`.  Each group element acts on the line spanned
by `v₀` by a nonzero scalar; these scalars form the desired linear character.
-/
noncomputable def linearCharOfOneDim
    (σ : FDRep k G)
    (h_dim : Module.finrank k σ = 1) :
    G →* kˣ := by
  let e : σ ≃ₗ[k] k :=
    LinearEquiv.ofFinrankEq σ k (by rw [h_dim, Module.finrank_self])
  let v0 : σ := e.symm 1
  have hv0 : v0 ≠ 0 := by
    intro h
    have : e v0 = 0 := by rw [h, map_zero]
    simp [v0] at this
  let χ : G → k := fun g => e (σ.ρ g v0)
  have h_scale : ∀ g : G, σ.ρ g v0 = (χ g) • v0 := by
    intro g
    apply e.injective
    simp only [v0, map_smul, LinearEquiv.apply_symm_apply, smul_eq_mul, mul_one, χ]
  have hχ_ne0 : ∀ g : G, χ g ≠ 0 := by
    intro g hg
    have h_im := h_scale g
    rw [hg, zero_smul] at h_im
    have h_inj : Function.Injective (σ.ρ g) :=
      LinearMap.ker_eq_bot.mp (LinearMap.ker_eq_bot_of_inverse
        (g := σ.ρ g⁻¹)
        (by ext; simp)
      )
    apply hv0
    apply h_inj
    rw [map_zero, h_im]
  refine {
    toFun := fun g => Units.mk0 (χ g) (hχ_ne0 g),
    map_one' := by
      ext
      simp only [Units.val_mk0, χ]
      simp only [Units.val_one]
      simp only [map_one, Module.End.one_apply, LinearEquiv.apply_symm_apply e 1, v0]
    map_mul' := by
      intro x y
      ext
      simp only [Units.val_mk0, Units.val_mul]
      dsimp [χ]
      simp only [map_mul, Module.End.mul_apply]
      rw [h_scale y, map_smul, h_scale x]
      rw [smul_smul, map_smul, mul_comm]
      have he : e v0 = 1 := by simp [v0]
      simp only [smul_eq_mul, mul_one, map_smul, he]
  }

/--
The one-dimensional representation is isomorphic to the representation attached
to its associated linear character.
-/
noncomputable def isoLinearCharOfOneDim
    (σ : FDRep k G)
    (h_dim : Module.finrank k σ = 1) :
    ofLinearChar (linearCharOfOneDim σ h_dim) ≅ σ := by
  let e : σ ≃ₗ[k] k :=
    LinearEquiv.ofFinrankEq σ k (by rw [h_dim, Module.finrank_self])
  let v0 : σ := e.symm 1
  let χ : G → k := fun g => e (σ.ρ g v0)
  have hv0_span : ∀ t : k, e.symm t = t • v0 := by
    intro t
    simpa [v0, map_smul] using (e.symm.map_smul t (1 : k))
  have h_scale : ∀ g : G, σ.ρ g v0 = (χ g) • v0 := by
    intro g
    apply e.injective
    simp only [map_smul, LinearEquiv.apply_symm_apply, smul_eq_mul, mul_one, v0, χ]
  refine FDRep.isoOfLinearEquiv (Y := σ) e.symm ?_
  intro g
  apply LinearMap.ext
  intro v
  symm
  change
    e.symm ((ofLinearChar (linearCharOfOneDim σ h_dim)).ρ g v) =
      σ.ρ g (e.symm v)
  rw [ofLinearChar_rho_apply]
  apply e.injective
  have hψ : (linearCharOfOneDim σ h_dim g : k) = χ g := rfl
  rw [ hψ, LinearEquiv.apply_symm_apply, hv0_span v,
    map_smul, h_scale g, smul_smul, map_smul ]
  simp only [ mul_comm, LinearEquiv.apply_symm_apply, smul_eq_mul,
    one_mul, χ, v0 ]


/--
The value of the constructed linear character equals the character of the
original one-dimensional representation.
-/
lemma linearCharOfOneDim_spec
    (σ : FDRep k G)
    (h_dim : Module.finrank k σ = 1) (g : G) :
    (linearCharOfOneDim σ h_dim g : k) = σ.character g := by
  let i : ofLinearChar (linearCharOfOneDim σ h_dim) ≅ σ :=
    isoLinearCharOfOneDim (k := k) σ h_dim
  have hchar_g :
      (ofLinearChar (linearCharOfOneDim σ h_dim)).character g =
        σ.character g := by
    exact congrArg
      (fun χ : ClassFun k G => χ g)
      (ClassFun.char_eq_of_iso i)
  simpa only [char_ofLinearChar] using hchar_g

/--
A one-dimensional representation is isomorphic to a linear-character
representation.
-/
lemma exists_iso_ofLinearChar_of_finrank_one
    (σ : FDRep k G)
    (h_dim : Module.finrank k σ = 1) :
    ∃ ψ : G →* kˣ, Nonempty (σ ≅ ofLinearChar ψ) := by
  refine ⟨linearCharOfOneDim σ h_dim, ?_⟩
  exact ⟨(isoLinearCharOfOneDim σ h_dim).symm⟩

end FDRep
