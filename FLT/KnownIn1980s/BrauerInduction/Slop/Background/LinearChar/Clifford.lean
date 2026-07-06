/-
Copyright (c) 2025 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McCarthy
-/
module

public import FLT.KnownIn1980s.BrauerInduction.Slop.Background.FDRep.AbelianGroup
public import FLT.KnownIn1980s.BrauerInduction.Slop.Background.FDRep.CentralKernel
public import FLT.KnownIn1980s.BrauerInduction.Slop.Background.LinearChar.Mackey
public import FLT.KnownIn1980s.BrauerInduction.Slop.Background.LinearChar.OneDimensional
public import FLT.KnownIn1980s.BrauerInduction.Slop.Background.LinearChar.QuotientDescent
public import FLT.KnownIn1980s.BrauerInduction.Slop.Background.Group.Nilpotent
public import FLT.KnownIn1980s.BrauerInduction.Slop.Background.Fintype.Basic

@[expose] public section

/-!
# Clifford theory for nilpotent groups

This file proves the Clifford-theoretic step used in Serre's theorem for
finite nilpotent groups.

The main ingredients are:

* a simple representation restricts nontrivially to a linear character on a
  normal abelian subgroup;
* the associated inertia subgroup induces back to the original representation;
* if the central kernel is trivial, this inertia subgroup is proper;
* if the central kernel is nontrivial, the representation descends to a smaller
  quotient.

Combining these cases proves the nilpotent-group monomiality theorem used in
Brauer induction: every simple representation of a finite nilpotent group over
an algebraically closed field of characteristic zero is induced from a linear
character of a subgroup.
-/

universe u v

variable {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]
variable {G : Type u} [Group G] [Finite G]

open CategoryTheory

namespace FDRep

/--
A simple representation restricts nontrivially to some linear character of an
abelian subgroup.
-/
theorem exists_linearChar_of_restrict
    (ρ : FDRep k G) [Simple ρ]
    (A : Subgroup G) [IsMulCommutative A] :
    ∃ ψ : A →* kˣ,
      ∃ f : FDRep.ofLinearChar ψ ⟶ ρ.res A,
        f ≠ 0 := by
  have hres_nz : Nontrivial (ρ.res A) := by
    change Nontrivial ρ
    exact FDRep.nontrivial_of_simple ρ
  have h_notIsZero: ¬ Limits.IsZero (ρ.res A) :=
     (nontrivial_iff_not_IsZero (ρ.res A)).mp hres_nz
  haveI : NeZero (Nat.card A : k) :=
    ⟨One.natCast_natCard_ne_zero_of_finite A k⟩
  obtain ⟨σ, i, hσsimp, hi_mono⟩ :=
    FDRep.exists_simple_subobject (ρ.res A) h_notIsZero
  haveI : Simple σ := hσsimp
  haveI : Mono i := hi_mono
  have hi_ne : i ≠ 0 := by
    intro hi
    have hinj : Function.Injective i.hom :=
      FDRep.hom_injective_of_mono i
    have hσnz : Nontrivial σ :=
      FDRep.nontrivial_of_simple σ
    obtain ⟨x, y, hxy⟩ := exists_pair_ne σ
    apply hxy
    apply hinj
    simp only [hi]
    exact LinearMap.sub_mem_ker_iff.mp rfl
  have hdim : Module.finrank k σ = 1 :=
    FDRep.abelian_simple_is_linear σ
  let ψ : A →* kˣ := σ.linearCharOfOneDim hdim
  let e : FDRep.ofLinearChar ψ ≅ σ :=
    σ.isoLinearCharOfOneDim hdim
  let f : FDRep.ofLinearChar ψ ⟶ ρ.res A :=
    e.hom ≫ i
  refine ⟨ψ, f, ?_⟩
  intro hf
  apply hi_ne
  calc
    i = 𝟙 σ ≫ i := by simp
    _ = (e.inv ≫ e.hom) ≫ i := by
      rw [e.inv_hom_id]
    _ = e.inv ≫ (e.hom ≫ i) := by
      simp only [Category.assoc]
    _ = e.inv ≫ f := rfl
    _ = e.inv ≫ 0 := by rw [hf]
    _ = 0 := by simp


/--
If `σ` is a simple representation of the inertia subgroup and embeds into the
`ψ`-eigenspace of `ρ`, then `Ind_I^G σ` is simple.
-/
lemma simple_ind_of_inertia_submodule
    (ρ : FDRep k G) [Simple ρ]
    (A : Subgroup G) [A.Normal] [IsMulCommutative A]
    (ψ : A →* kˣ)
    (σ : FDRep k (LinearChar.inertia ψ))
    (ι : σ ⟶ LinearChar.psiEigenspaceFDRep
      (ρ := ρ) (A := A) (ψ := ψ))
    [Mono ι] [Simple σ] :
    Simple (FDRep.ind (LinearChar.inertia ψ) σ) := by
  haveI : NeZero (Nat.card G : k) := ⟨One.natCast_natCard_ne_zero_of_finite G k⟩
  rw [FDRep.simple_iff_end_is_rank_one]
  exact finrank_end_ind_from_inertia_eq_one ρ A ψ σ ι


/--
If an element acts trivially on a representation, then every element of its
normal closure acts trivially.
-/
private lemma rho_trivial_of_mem_normalClosure_singleton
    {k : Type u} [CommRing k]
    {G : Type v} [Group G]
    (ρ : FDRep k G)
    {c z : G}
    (hc : ρ.ρ c = LinearMap.id)
    (hz : z ∈ Subgroup.normalClosure ({c} : Set G)) :
    ρ.ρ z = LinearMap.id := by
  let K : Subgroup G := MonoidHom.ker ρ.ρ
  have hK_normal : K.Normal := by
    infer_instance
  have hcK : c ∈ K := by
    change ρ.ρ c = 1
    exact MonoidHom.mem_ker.mp hc
  have hle : Subgroup.normalClosure ({c} : Set G) ≤ K := by
    intro x hx
    exact Subgroup.normalClosure_le_normal
      (by
        intro y hy
        simp only [Set.mem_singleton_iff] at hy
        subst y
        exact hcK)
      hx
  have hzK : z ∈ K := hle hz
  change ρ.ρ z = 1 at hzK
  change ρ.ρ z = (1 : ρ →ₗ[k] ρ)
  exact hzK

/--
Inducing a linear character from the top subgroup gives the corresponding
representation of `G`.
-/
noncomputable def indLin_top_iso_self
    {k : Type u} [Field k] [CharZero k]
    (ψ : (⊤ : Subgroup G) →* kˣ) :
    FDRep.indLin (k := k) (⊤ : Subgroup G) ψ ≅
      FDRep.ofTop (G := G) (k := k)
        (FDRep.ofLinearChar
          (G := (⊤ : Subgroup G)) (k := k) ψ) := by
  unfold FDRep.indLin
  exact
    FDRep.indTopIsoOfTop
      (G := G) (k := k)
      (FDRep.ofLinearChar
        (G := (⊤ : Subgroup G)) (k := k) ψ)

/--
For a commutative group, every simple representation is a linear character,
viewed as induction from the top subgroup.
-/
theorem simple_of_commGroup_iso_indLin_top
     [IsMulCommutative G]
    (ρ : FDRep k G) [Simple ρ] :
    ∃ ψ : (⊤ : Subgroup G) →* kˣ,
      Nonempty (ρ ≅ FDRep.indLin (⊤ : Subgroup G) ψ) := by
  let T : Subgroup G := ⊤
  -- Work with the restriction to `⊤`.
  have hdim : Module.finrank k (ρ.res T) = 1 := by
    -- underlying vector space is unchanged
    change Module.finrank k ρ = 1
    exact FDRep.abelian_simple_is_linear ρ
  let ψ : T →* kˣ :=
     (ρ.res T).linearCharOfOneDim hdim
  refine ⟨ψ, ?_⟩
  let eχ : FDRep.ofLinearChar ψ ≅ ρ.res T :=
    (ρ.res T).isoLinearCharOfOneDim hdim
  let eind :
      FDRep.indLin T ψ ≅ FDRep.ofTop (FDRep.ofLinearChar ψ) :=
        indLin_top_iso_self ψ
  let eres : FDRep.ofTop (ρ.res T) ≅ ρ := FDRep.ofTop_res_top_iso ρ
  let eχ_top :
    FDRep.ofTop (FDRep.ofLinearChar ψ) ≅
      FDRep.ofTop (ρ.res T) :=
  (FDRep.ofTopFunctor (k := k) (G := G)).mapIso eχ
  exact ⟨eres.symm ≪≫ eχ_top.symm ≪≫ eind.symm⟩

/--
Central-kernel quotient branch.

If the central kernel of `ρ` is nontrivial, then `ρ` descends to
`G ⧸ centralKernel ρ`.  Applying the induction hypothesis to the descended
simple representation and pulling the result back along the quotient map gives
an induced linear-character description of `ρ`.
-/
theorem exists_indLin_of_centralKernel_ne_bot
    [Group.IsNilpotent G]
    (ρ : FDRep k G) [CategoryTheory.Simple ρ]
    (hKne : FDRep.centralKernel ρ ≠ ⊥)
    (IH :
      ∀ (Q : Type u) [Group Q] [Finite Q] [Group.IsNilpotent Q],
        Nat.card Q < Nat.card G →
        ∀ (σ : FDRep k Q), [Simple σ] →
          ∃ (H : Subgroup Q) (ψ : H →* kˣ),
            Nonempty (σ ≅ FDRep.indLin H ψ)) :
    ∃ (H : Subgroup G) (ψ : H →* kˣ),
      Nonempty (ρ ≅ FDRep.indLin H ψ) := by
  let K : Subgroup G := FDRep.centralKernel ρ
  haveI : K.Normal := by
    dsimp [K]
    infer_instance
  have hKne' : K ≠ ⊥ := by
    simpa [K] using hKne
  have htriv : ∀ x ∈ K, ρ.ρ x = 1 := by
    intro x hx
    dsimp [K] at hx
    exact rho_eq_one_of_mem_centralKernel ρ x hx
  let ρbar : FDRep k (G ⧸ K) :=
    FDRep.lift ρ K htriv
  haveI : Finite (G ⧸ K) := by
    infer_instance
  haveI : Group.IsNilpotent (G ⧸ K) := by
    infer_instance
  have hcard : Nat.card (G ⧸ K) < Nat.card G := by
    exact QuotientGroup.natCard_quotient_lt_natCard_of_ne_bot K hKne'
  haveI : Simple ρbar := by
    dsimp [ρbar]
    exact FDRep.lift_simple_of_simple ρ K htriv
  obtain ⟨Q, ψQ, hQ⟩ :=
    IH (G ⧸ K) hcard ρbar
  exact
    FDRep.exists_indLin_of_lift_exists_indLin
      (ρ := ρ) (K := K) htriv
      ⟨Q, ψQ, hQ⟩

end FDRep

namespace LinearChar

open Classical in
/--
If the `ψ`-eigenspace is nonzero, then `ρ` is induced from a simple
representation of the inertia subgroup of `ψ`.
-/
theorem exists_induced_from_inertia
    (ρ : FDRep k G) [Simple ρ]
    (A : Subgroup G) [A.Normal] [IsMulCommutative A]
    (ψ : A →* kˣ)
    (hW : psiEigenspace ρ A ψ ≠ ⊥) :
    ∃ σ : FDRep k (LinearChar.inertia ψ),
        Simple σ ∧ Nonempty (ρ ≅ FDRep.ind (LinearChar.inertia ψ) σ) := by
  let Iψ : Subgroup G := LinearChar.inertia ψ
  let W : FDRep k Iψ :=
    psiEigenspaceFDRep (ρ := ρ) (A := A) (ψ := ψ)
  have hW_nontrivial : Nontrivial W := by
    change Nontrivial (psiEigenspace ρ A ψ)
    exact Submodule.nontrivial_iff_ne_bot.mpr hW
  have hW_notIsZero:  ¬ Limits.IsZero W := by
    exact (FDRep.nontrivial_iff_not_IsZero W).mp hW_nontrivial
  haveI : NeZero ↑(Nat.card ↥Iψ) :=
    neZero_iff.mpr (One.natCard_ne_zero_of_finite ↥Iψ)
  obtain ⟨σ, ι, hσsimp, hιmono⟩ :=
    FDRep.exists_simple_subobject W hW_notIsZero
  haveI : Simple σ := hσsimp
  haveI : Mono ι := hιmono
  let incl : W ⟶ FDRep.res ρ Iψ :=
    psiEigenspaceIncl (ρ := ρ) (A := A) (ψ := ψ)
  haveI : Mono incl := psiEigenspaceIncl_mono ρ A ψ
  let j : σ ⟶ FDRep.res ρ Iψ := ι ≫ incl
  have hι_ne : ι ≠ 0 := by
    intro hι_zero
    have hinj : Function.Injective ι.hom :=
      FDRep.hom_injective_of_mono ι
    have hσnz : Nontrivial σ :=
      FDRep.nontrivial_of_simple σ
    obtain ⟨x, y, hxy⟩ := exists_pair_ne σ
    apply hxy
    apply hinj
    simp only [hι_zero]
    exact LinearMap.sub_mem_ker_iff.mp rfl
  have hj_ne : j ≠ 0 := by
    intro hj_zero
    apply hι_ne
    have hj_zero' : ι ≫ incl = 0 ≫ incl := by
      simpa [j] using hj_zero
    exact (cancel_mono incl).1 hj_zero'
  let e : (FDRep.ind Iψ σ ⟶ ρ) ≃ₗ[k] (σ ⟶ FDRep.res ρ Iψ)
    := FDRep.indHomComapEquiv Iψ.subtype σ ρ
  let f : FDRep.ind Iψ σ ⟶ ρ := e.symm j
  have hf_ne : f ≠ 0 := by
    intro hf_zero
    apply hj_ne
    have hj_eq : j = e f := by
      simpa only [f] using (e.apply_symm_apply j).symm
    calc
      j = e f := hj_eq
      _ = e 0 := by rw [hf_zero]
      _ = 0 := by simp
  haveI : Simple (FDRep.ind Iψ σ) :=
    FDRep.simple_ind_of_inertia_submodule ρ A ψ σ ι
  haveI : IsIso f :=
    CategoryTheory.isIso_of_hom_simple hf_ne
  refine ⟨σ, hσsimp, ?_⟩
  exact ⟨(asIso f).symm⟩

/--
Clifford step packaged with the existence of a linear character in the
restriction to a normal abelian subgroup.

Given a simple representation `ρ` and an abelian normal subgroup `A`, there is
a linear character `ψ : A →* kˣ` and a simple representation of the inertia
subgroup of `ψ` from which `ρ` is induced.
-/
theorem exists_induced_from_normal_abelian
    (ρ : FDRep k G) [Simple ρ]
    (A : Subgroup G) [A.Normal] [IsMulCommutative A] :
    ∃ (ψ : A →* kˣ),
      LinearChar.psiEigenspace ρ A ψ ≠ ⊥ ∧
      ∃ (τ : FDRep k (LinearChar.inertia ψ)),
        Simple τ ∧
          Nonempty (ρ ≅ FDRep.ind (LinearChar.inertia ψ) τ) := by
  obtain ⟨ψ, f, hf⟩ :=
    FDRep.exists_linearChar_of_restrict
      (ρ := ρ) A
  have hW : LinearChar.psiEigenspace ρ A ψ ≠ ⊥ :=
      LinearChar.psiEigenspace_ne_bot_of_hom
        (ρ := ρ) (A := A) (ψ := ψ) f hf
  obtain ⟨σ, hσsimp, hiso⟩ :=
    LinearChar.exists_induced_from_inertia
      (ρ := ρ) (A := A) (ψ := ψ) hW
  exact ⟨ψ, hW, σ, hσsimp, hiso⟩

/--
If `g` and `a` do not commute, then the commutator `g * a * g⁻¹ * a⁻¹` is
nontrivial.
-/
private lemma commutator_ne_one_of_mul_ne {G : Type v} [Group G]
    {g a : G} (hga : g * a ≠ a * g) :
    g * a * g⁻¹ * a⁻¹ ≠ 1 := by
  intro hc
  apply hga
  have hconj : g * a * g⁻¹ = a := by
    apply mul_inv_eq_one.mp
    simpa [mul_assoc] using hc
  calc
    g * a = (g * a * g⁻¹) * g := by
      simp [mul_assoc]
    _ = a * g := by
      rw [hconj]

/--
If the central kernel of a simple representation is trivial, and `A` is a
normal abelian subgroup strictly larger than the center, then any linear
character of `A` occurring in `ρ|_A` has proper inertia.
-/
theorem inertia_ne_top_of_centralKernel_eq_bot
    {k : Type u} [Field k] [IsAlgClosed k]
    {G : Type v} [Group G]
    [Group.IsNilpotent G]
    (ρ : FDRep k G) [Simple ρ]
    (hck : FDRep.centralKernel ρ = ⊥)
    (A : Subgroup G) [A.Normal] [IsMulCommutative A]
    (hA : Subgroup.center G < A)
    (ψ : A →* kˣ)
    (hW : LinearChar.psiEigenspace ρ A ψ ≠ ⊥) :
    LinearChar.inertia ψ ≠ ⊤ := by
  intro hI
  have hA_scalar :
      ∀ a : A, ρ.ρ (a : G) = (ψ a : k) • LinearMap.id :=
    rho_eq_smul_of_inertia_eq_top ρ A ψ hI hW
  -- Since `A` is strictly larger than the center, choose a noncentral element of `A`.
  obtain ⟨a, haA, ha_not_center⟩ : ∃ a : G, a ∈ A ∧ a ∉ Subgroup.center G := by
    by_contra h'; push Not at h'; exact (not_le_of_gt hA) h'
  -- Since `a` is not central, choose `g` with `g * a ≠ a * g`.
  obtain ⟨g, hga_ne⟩ : ∃ g : G, g * a ≠ a * g := by
    by_contra h; push Not at h; exact ha_not_center ((Subgroup.mem_center_iff).2 h)
  -- The commutator is nontrivial.
  let c : G := g * a * g⁻¹ * a⁻¹
  have hc_ne_one : c ≠ 1 := by
    dsimp [c]; exact commutator_ne_one_of_mul_ne hga_ne
  -- But because `a` acts by scalar on `ρ`, its conjugate also acts by the same scalar,
  -- so the commutator acts trivially.
  have hc_trivial :
      ρ.ρ c = LinearMap.id := by
    let aA : A := ⟨a, haA⟩
    have ha_scalar :
        ρ.ρ a = (ψ aA : k) • LinearMap.id := by
      simpa [aA] using hA_scalar aA
    have hainv_scalar :
        ρ.ρ a⁻¹ = (ψ aA⁻¹ : k) • LinearMap.id := by
      simpa [aA] using hA_scalar aA⁻¹
    dsimp [c]
    rw [map_mul, map_mul, map_mul]
    rw [ha_scalar, hainv_scalar]
    ext v
    simp only [Module.End.mul_apply, LinearMap.smul_apply, LinearMap.id_coe, id_eq,
      map_smul, smul_smul]
    simp only [map_inv, Units.val_inv_eq_inv_val, ne_eq, Units.ne_zero, not_false_eq_true,
      inv_mul_cancel₀, Representation.self_inv_apply, one_smul]
  -- From the nontrivial normal closure of `c`, nilpotence gives a nontrivial central
  -- element in that normal closure.
  obtain ⟨z, hz_center, hz_nc, hz_ne⟩ :
      ∃ z : G,
        z ∈ Subgroup.center G ∧
        z ∈ Subgroup.normalClosure ({c} : Set G) ∧
        z ≠ 1 := by
    -- nilpotent group lemma: nontrivial normal subgroup meets center nontrivially
    exact Group.exists_center_mem_normalClosure_singleton_of_ne_one hc_ne_one
  -- Since `c` acts trivially, everything in its normal closure acts trivially.
  have hz_trivial :
      ρ.ρ z = LinearMap.id := by
      exact FDRep.rho_trivial_of_mem_normalClosure_singleton ρ hc_trivial hz_nc
  -- A nontrivial central element acting trivially lies in the central kernel,
  -- contradicting `centralKernel ρ = ⊥`.
  have hz_ck : z ∈ FDRep.centralKernel ρ := by
    exact
      (FDRep.center_coe_mem_centralKernel_iff ρ ⟨z, hz_center⟩).2 hz_trivial
  have hz_one : z = 1 := by
    have : z ∈ (⊥ : Subgroup G) := by
      simpa [hck] using hz_ck
    simpa using this
  exact hz_ne hz_one

end LinearChar

namespace FDRep

/--
Finite nilpotent groups are monomial.

Every simple finite-dimensional representation of a finite nilpotent group over
an algebraically closed field of characteristic zero is induced from a linear
character of a subgroup. This is the nilpotent-group input used in the proof of
Brauer induction.
-/
theorem exists_indLin_of_nilpotent_simple
    [Group.IsNilpotent G]
    (ρ : FDRep k G) [Simple ρ] :
    ∃ (H : Subgroup G) (ψ : H →* kˣ),
      Nonempty (ρ ≅ FDRep.indLin H ψ) := by
  let P : ℕ → Prop :=
    fun n =>
      ∀ (Q : Type u) [Group Q] [Finite Q] [Group.IsNilpotent Q],
        Nat.card Q = n →
        ∀ (σ : FDRep k Q), [Simple σ] →
          ∃ (H : Subgroup Q) (ψ : H →* kˣ),
            Nonempty (σ ≅ FDRep.indLin H ψ)
  have hP : ∀ n, P n := by
    intro n
    refine Nat.strong_induction_on n ?_
    intro n IHn Q _ _ _ hcard σ _
    have IH :
        ∀ (Q' : Type u) [Group Q'] [Finite Q'] [Group.IsNilpotent Q'],
          Nat.card Q' < Nat.card Q →
          ∀ (σ' : FDRep k Q'), [Simple σ'] →
            ∃ (H : Subgroup Q') (ψ : H →* kˣ),
              Nonempty (σ' ≅ FDRep.indLin H ψ) := by
      intro Q' _ _ _ hlt σ' _
      have hlt_n : Nat.card Q' < n := by
        simpa [hcard] using hlt
      exact (IHn (Nat.card Q') hlt_n) Q' rfl σ'
    -- Abelian case.
    by_cases hcomm : IsMulCommutative Q
    · obtain ⟨ψ, hρ⟩ :=
        FDRep.simple_of_commGroup_iso_indLin_top
          (G := Q) (k := k) σ
      exact ⟨⊤, ψ, hρ⟩
    by_cases hKne : FDRep.centralKernel σ ≠ ⊥
    · exact
        exists_indLin_of_centralKernel_ne_bot
          (ρ := σ) hKne IH
    have hKbot : FDRep.centralKernel σ = ⊥ := by
      by_contra h
      exact hKne h
    obtain ⟨A, hA_normal, hA_comm, hA_gt⟩ :=
      Group.exists_normal_abelian_gt_center
        (G := Q) hcomm
    haveI : A.Normal := hA_normal
    haveI : IsMulCommutative A := hA_comm
    obtain ⟨ψ, hW, τ, hτ_simple, hσ_ind⟩ :=
      LinearChar.exists_induced_from_normal_abelian
        (ρ := σ) A
    haveI : Simple τ := hτ_simple
    have hI_ne_top :
        LinearChar.inertia ψ ≠ ⊤ := by
      exact
        LinearChar.inertia_ne_top_of_centralKernel_eq_bot
          (ρ := σ) (hck := hKbot) (A := A)
          hA_gt ψ hW
    have hcardI :
        Nat.card (LinearChar.inertia ψ) < Nat.card Q :=
      Subgroup.natCard_lt_natCard_of_ne_top
        (LinearChar.inertia ψ) hI_ne_top
    obtain ⟨H, θ, hτ_lin⟩ :=
      IH (LinearChar.inertia ψ) hcardI τ
    rcases hσ_ind with ⟨eσ⟩
    rcases hτ_lin with ⟨eτ⟩
    let I : Subgroup Q := LinearChar.inertia ψ
    let eτ_ind :
        FDRep.ind I τ ≅ FDRep.ind I (FDRep.indLin H θ) :=
      (FDRep.indHomFunctor
        (k := k)
        (G := I)
        (H := Q)
        I.subtype).mapIso eτ
    let HG : Subgroup Q := H.map I.subtype
    let eH : H ≃* HG :=
      H.equivMapOfInjective I.subtype Subtype.coe_injective
    let θG : HG →* kˣ :=
      θ.comp eH.symm.toMonoidHom
    let estage :
        FDRep.ind I (FDRep.indLin H θ) ≅
          FDRep.indLin HG θG :=
      FDRep.indLin_trans
        (I := I) (H := H) θ
    refine ⟨HG, θG, ?_⟩
    exact ⟨eσ ≪≫ eτ_ind ≪≫ estage⟩
  exact (hP (Nat.card G)) G rfl ρ

end FDRep
