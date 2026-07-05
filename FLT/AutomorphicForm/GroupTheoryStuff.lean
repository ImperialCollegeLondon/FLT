/-
Copyright (c) 2026 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.Algebra.Group.Submonoid.Units
public import Mathlib.GroupTheory.Torsion
public import Mathlib.RingTheory.UniqueFactorizationDomain.Nat

/-! # Random assortments of results on group theory. -/

@[expose] public section

attribute [simp] Subgroup.mem_subgroupOf

/-- The maximal `p`-quotient of a group.

Note that the torsion free parts of `G` will not get quotiented out.
So `G / MaximalPQuotient` is a `p`-group only when `G` is torsion free. -/
abbrev MaximalPQuotient (G : Type*) [Group G] (p : ℕ) :=
    G ⧸ ⨅ (N : Subgroup G) (_ : N.Normal) (_ : IsPGroup p (G ⧸ N)), N

instance (G : Type*) [Group G] (p : ℕ) :
    (⨅ (N : Subgroup G) (_ : N.Normal) (_ : IsPGroup p (G ⧸ N)), N).Normal :=
  Subgroup.normal_iInf_normal fun N ↦ Subgroup.normal_iInf_normal fun _ ↦
    Subgroup.normal_iInf_normal fun _ ↦ ‹_›

/-- Quotient map into the maximal `p`-quotient of a group. -/
abbrev MaximalPQuotient.mk (G : Type*) [Group G] (p : ℕ) : G →* MaximalPQuotient G p :=
  QuotientGroup.mk' _

lemma MaximalPQuotient.mk_surjective {G : Type*} [Group G] {p : ℕ} :
    Function.Surjective (mk G p) := QuotientGroup.mk'_surjective _

lemma MaximalPQuotient.mk_eq_zero_of_pow_eq_zero {G : Type*} [Group G]
    {p q : ℕ} {g : G} (H : g ^ q = 1) (hpq : p.Coprime q) : mk G p g = 1 := by
  simp only [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_iInf]
  intro K _ hK
  simpa using (hK.orderOf_coprime hpq g:).of_dvd_right
    (orderOf_dvd_of_pow_eq_one (G := G ⧸ K) (x := g) (by simp [← QuotientGroup.mk_pow, H]))

-- Also see `IsPrincipalIdealRing.exists_isCoprime_and_dvd_pow`
lemma Nat.exists_coprime_and_dvd_pow (a b : ℕ) (ha : a ≠ 0) :
    ∃ x y N, a = x * y ∧ x.Coprime b ∧ y ∣ b ^ N := by
  induction a using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => cases ha rfl
  | h₂ a ha' => refine ⟨1, a, 0, by simp [ha'.dvd]⟩
  | h₃ a p ha' hp IH =>
    obtain ⟨x, y, N, rfl, hxb, hyb⟩ := IH ha'
    by_cases hpb : p ∣ b
    · exact ⟨x, y * p, N + 1, by ring, hxb, pow_succ b N ▸ mul_dvd_mul hyb hpb⟩
    · exact ⟨x * p, y, N, by ring, hxb.mul_left
        ((Nat.prime_iff.mpr hp).coprime_iff_not_dvd.mpr hpb), hyb⟩


/-- The "maximal `p`-quotient" of `(ℤ, +)` is `ℤ/⋂ₙ pⁿℤ = ℤ`, not a `p`-group. -/
lemma MaximalPQuotient.isPGroup_of_isTorsion
    (G : Type*) [Group G] (p : ℕ) (hG : Monoid.IsTorsion G) :
    IsPGroup p (MaximalPQuotient G p) := by
  intro x
  obtain ⟨x, rfl⟩ := MaximalPQuotient.mk_surjective x
  obtain ⟨n, m, N, h₁, h₂, k, hk⟩ :=
    Nat.exists_coprime_and_dvd_pow (orderOf x) p (hG x).orderOf_pos.ne'
  refine ⟨N, ?_⟩
  rw [hk, pow_mul, ← map_pow, MaximalPQuotient.mk_eq_zero_of_pow_eq_zero _ h₂.symm, one_pow]
  rw [← pow_mul', ← h₁, pow_orderOf_eq_one]

section

lemma Subgroup.IsFiniteRelIndex.of_finite {G : Type*} [Group G] (H₁ H₂ : Subgroup G)
    (h : Set.Finite (H₂ : Set G)) : H₁.IsFiniteRelIndex H₂ :=
  have : Finite H₂ := h
  Subgroup.isFiniteRelIndex_iff_finiteIndex.mpr inferInstance

@[simp]
lemma Subgroup.finiteIndex_bot_iff {G : Type*} [Group G] :
    (⊥ : Subgroup G).FiniteIndex ↔ Finite G :=
  Subgroup.finiteIndex_iff_finite_quotient.trans (QuotientGroup.quotientEquivSelf G).finite_iff

@[simp]
lemma Subgroup.isFiniteRelIndex_bot_iff {G : Type*} [Group G] {H : Subgroup G} :
    (⊥ : Subgroup G).IsFiniteRelIndex H ↔ Set.Finite (H : Set G) :=
  Subgroup.isFiniteRelIndex_iff_finiteIndex.trans (by simp; rfl)

@[simp]
lemma QuotientGroup.range_lift {G M : Type*} [Group G] [Group M]
    (N : Subgroup G) [N.Normal] (φ : G →* M) (HN : N ≤ φ.ker) :
    (QuotientGroup.lift N φ HN).range = φ.range := by
  ext; simp [QuotientGroup.mk_surjective.exists]

lemma Subgroup.finite_map_of_isFiniteRelIndex {G G' : Type*} [Group G] [Group G']
    (φ : G →* G') (H : Subgroup G) [φ.ker.IsFiniteRelIndex H] :
    Set.Finite (α := G') ↑(H.map φ) := by
  let φ' : (H ⧸ φ.ker.subgroupOf H) →* G' :=
    QuotientGroup.lift _ (φ.comp H.subtype) (fun x hx ↦ by simp_all)
  convert Set.finite_range φ'
  rw [← MonoidHom.coe_range, QuotientGroup.range_lift, MonoidHom.range_comp, Subgroup.range_subtype]

/-- First isomorphism theorem restricted to a subgroup. -/
noncomputable def Subgroup.quotientKerEquivMap {G G' : Type*} [Group G] [Group G']
    (φ : G →* G') (H : Subgroup G) :
    H ⧸ φ.ker.subgroupOf H ≃* H.map φ :=
  QuotientGroup.liftEquiv _ (φ := (φ.comp H.subtype).codRestrict _ (by aesop)) (fun _ ↦ by aesop)
    (by aesop)

lemma Subgroup.card_map_eq_relIndex_ker {G G' : Type*} [Group G] [Group G']
    (φ : G →* G') (H : Subgroup G) :
    Nat.card ↑(H.map φ) = φ.ker.relIndex H :=
  Nat.card_congr (Subgroup.quotientKerEquivMap φ H).symm

lemma orderOf_dvd_ncard {G : Type*} [Group G]
    {H : Subgroup G} (hH : Set.Finite (H : Set G)) {x : G} (hx : x ∈ H) :
    orderOf x ∣ Set.ncard (H : Set G) := by
  cases hH.nonempty_fintype
  simpa [← Nat.card_eq_fintype_card] using! orderOf_dvd_card (G := H) (x := ⟨x, hx⟩)

section

/-- If `K` is contained in the centralizer of `H`, then `H ⊔ K` is given by `HK` and the map
`H × K → HK` is a group homomorphism. -/
@[simps]
def Subgroup.prodToSupOfRight {G : Type*} [Group G] (H K : Subgroup G) (hK : K ≤ .centralizer H) :
    H × K →* ↑(H ⊔ K) where
  toFun hk := ⟨hk.1 * hk.2, Subgroup.mul_mem_sup hk.1.2 hk.2.2⟩
  map_one' := by simp
  map_mul' | ⟨h, k⟩, ⟨h', k'⟩ => by  simpa using Commute.mul_mul_mul_comm (hK k.2 _ h'.2) _ _

lemma Subgroup.prodToSupOfRight_surjective
    {G : Type*} [Group G] (H K : Subgroup G) (hK : K ≤ .centralizer H) :
    Function.Surjective (Subgroup.prodToSupOfRight H K hK) := by
  rw [← MonoidHom.range_eq_top, ← (Subgroup.map_injective (Subgroup.subtype_injective _)).eq_iff,
    ← MonoidHom.range_eq_map]
  refine (Subgroup.map_le_range ..).antisymm ?_
  simp only [Subgroup.range_subtype, ← MonoidHom.range_comp, sup_le_iff]
  refine ⟨fun x hx ↦ ⟨(⟨x, hx⟩, 1), by simp⟩, fun x hx ↦ ⟨(1, ⟨x, hx⟩), by simp⟩⟩

end

section

open MonoidHom QuotientGroup Function

variable {G : Type*} [Group G] {H : Type*} [Monoid H] (φ : G →* H)

/-- The induced map from the quotient by the kernel to the codomain. -/
@[to_additive /-- The induced map from the quotient by the kernel to the codomain. -/]
def QuotientGroup.kerLift' : G ⧸ ker φ →* H :=
  lift _ φ fun _g => mem_ker.mp

@[to_additive (attr := simp)]
theorem QuotientGroup.kerLift'_mk (g : G) : (kerLift' φ) g = φ g :=
  rfl

@[to_additive]
theorem QuotientGroup.kerLift'_injective : Injective (kerLift' φ) := fun a b =>
  Quotient.inductionOn₂' a b fun a b (h : φ a = φ b) =>
    Quotient.sound' <| by rw [leftRel_apply, mem_ker, φ.map_mul,
      ← h, ← map_mul, inv_mul_cancel, map_one]

end

lemma Subgroup.le_ker_of_le_ker_of_coprime_relIndex
    {G G' : Type*} [Group G] [CommMonoid G'] (φ : G →* G') (n : ℕ) (hn : φ ^ n = 1)
    {K₁ K₂ : Subgroup G} (hCoprime : n.Coprime (K₁.relIndex K₂))
    (hK₁ : K₁ ≤ φ.ker) : K₂ ≤ φ.ker := by
  wlog hK₁' : K₁ = ⊥ generalizing G
  · have := this (QuotientGroup.kerLift' φ) (by ext x; simpa using congr($hn x))
      (K₂ := K₂.map (QuotientGroup.mk' _)) (by
      rw [Subgroup.relIndex_bot_left, Subgroup.card_map_eq_relIndex_ker]
      exact .of_dvd_right (Subgroup.relIndex_dvd_of_le_left _ (by simpa)) hCoprime) bot_le
    simpa [(MonoidHom.ker_eq_bot_iff _).mpr, QuotientGroup.kerLift_injective, -le_bot_iff,
      Subgroup.map_le_iff_le_comap] using! this
  by_cases hφ : φ = 1
  · simp_all
  have hK₁K₂ : K₁.IsFiniteRelIndex K₂ := ⟨fun h ↦ by simp_all⟩
  have hK₂ : Finite K₂ := by simpa [hK₁'] using! hK₁K₂
  intro x hx
  simp only [hK₁', Subgroup.relIndex_bot_left] at hCoprime
  simpa using (hCoprime.symm.of_dvd_left ((orderOf_map_dvd φ x).trans
    (orderOf_dvd_ncard hK₂ hx))).eq_one_of_dvd
    (by simpa [orderOf_dvd_iff_pow_eq_one] using congr($hn x))

namespace MonoidHom

variable {G₁ G₂ G₃ : Type*} [Group G₁] [Monoid G₂] [Monoid G₃]
variable (f : G₁ →* G₂) (f_inv : G₂ → G₁)

/-- Auxiliary definition used to define `liftOfRightInverse` -/
@[to_additive /-- Auxiliary definition used to define `liftOfRightInverse` -/]
def liftOfRightInverseAux' (hf : Function.RightInverse f_inv f) (g : G₁ →* G₃)
    (hg : f.ker ≤ g.ker) :
    G₂ →* G₃ where
  toFun b := g (f_inv b)
  map_one' := hg (hf 1)
  map_mul' := by
    intro x y
    apply ((Group.isUnit (f_inv (x * y))⁻¹).map g).mul_left_injective
    simp only [← g.map_mul, mul_inv_cancel, map_one]
    refine (hg <| ((Group.isUnit (f_inv (x * y))).map f).mul_left_injective ?_).symm
    simp [← map_mul, mul_assoc]
    simp [hf _]

@[to_additive (attr := simp)]
theorem liftOfRightInverseAux'_comp_apply (hf : Function.RightInverse f_inv f) (g : G₁ →* G₃)
    (hg : f.ker ≤ g.ker) (x : G₁) : (f.liftOfRightInverseAux' f_inv hf g hg) (f x) = g x := by
  dsimp [liftOfRightInverseAux']
  apply ((Group.isUnit (f_inv (f x))⁻¹).map g).mul_left_injective
  simp only [← map_mul, mul_inv_cancel, map_one]
  refine (hg <| ((Group.isUnit (f_inv (f x))).map f).mul_left_injective ?_).symm
  simp [← map_mul]
  simp [hf _]

/-- `liftOfRightInverse f hf g hg` is the unique group homomorphism `φ`

* such that `φ.comp f = g` (`MonoidHom.liftOfRightInverse_comp`),
* where `f : G₁ →+* G₂` has a RightInverse `f_inv` (`hf`),
* and `g : G₂ →+* G₃` satisfies `hg : f.ker ≤ g.ker`.

See `MonoidHom.eq_liftOfRightInverse` for the uniqueness lemma.

```
   G₁.
   |  \
 f |   \ g
   |    \
   v     \⌟
   G₂----> G₃
      ∃!φ
```
-/
@[to_additive
      /-- `liftOfRightInverse f f_inv hf g hg` is the unique additive group homomorphism `φ`
      * such that `φ.comp f = g` (`AddMonoidHom.liftOfRightInverse_comp`),
      * where `f : G₁ →+ G₂` has a RightInverse `f_inv` (`hf`),
      * and `g : G₂ →+ G₃` satisfies `hg : f.ker ≤ g.ker`.
      See `AddMonoidHom.eq_liftOfRightInverse` for the uniqueness lemma.
      ```
         G₁.
         |  \
       f |   \ g
         |    \
         v     \⌟
         G₂----> G₃
            ∃!φ
      ``` -/]
def liftOfRightInverse' (hf : Function.RightInverse f_inv f) :
    { g : G₁ →* G₃ // f.ker ≤ g.ker } ≃ (G₂ →* G₃) where
  toFun g := f.liftOfRightInverseAux' f_inv hf g.1 g.2
  invFun φ := ⟨φ.comp f, fun x hx ↦ mem_ker.mpr <| by simp [mem_ker.mp hx]⟩
  left_inv g := by
    ext
    simp only [comp_apply, liftOfRightInverseAux'_comp_apply]
  right_inv φ := by
    ext b
    simp [liftOfRightInverseAux', hf b]

/-- A non-computable version of `MonoidHom.liftOfRightInverse` for when no computable right
inverse is available, that uses `Function.surjInv`. -/
@[to_additive (attr := simp)
      /-- A non-computable version of `AddMonoidHom.liftOfRightInverse` for when no
      computable right inverse is available. -/]
noncomputable abbrev liftOfSurjective' (hf : Function.Surjective f) :
    { g : G₁ →* G₃ // f.ker ≤ g.ker } ≃ (G₂ →* G₃) :=
  f.liftOfRightInverse' (Function.surjInv hf) (Function.rightInverse_surjInv hf)

@[to_additive (attr := simp)]
theorem liftOfRightInverse'_comp_apply (hf : Function.RightInverse f_inv f)
    (g : { g : G₁ →* G₃ // f.ker ≤ g.ker }) (x : G₁) :
    (f.liftOfRightInverse' f_inv hf g) (f x) = g.1 x :=
  f.liftOfRightInverseAux'_comp_apply f_inv hf g.1 g.2 x

@[to_additive (attr := simp)]
theorem liftOfRightInverse'_comp (hf : Function.RightInverse f_inv f)
    (g : { g : G₁ →* G₃ // f.ker ≤ g.ker }) : (f.liftOfRightInverse' f_inv hf g).comp f = g :=
  MonoidHom.ext <| f.liftOfRightInverse'_comp_apply f_inv hf g

@[to_additive]
theorem eq_liftOfRightInverse' (hf : Function.RightInverse f_inv f) (g : G₁ →* G₃)
    (hg : f.ker ≤ g.ker) (h : G₂ →* G₃) (hh : h.comp f = g) :
    h = f.liftOfRightInverse' f_inv hf ⟨g, hg⟩ := by
  simp_rw [← hh]
  exact ((f.liftOfRightInverse' f_inv hf).apply_symm_apply _).symm

end MonoidHom

end

@[simp]
lemma Subgroup.inclusion_mk {G : Type*} [Group G] {H K : Subgroup G} (h : H ≤ K)
    (x : G) (hx : x ∈ H) : Subgroup.inclusion h ⟨x, hx⟩ = ⟨x, h hx⟩ := rfl

lemma MonoidHom.ker_le_ker_comp {G₁ G₂ G₃ : Type*} [Group G₁] [Monoid G₂] [Monoid G₃]
    (f : G₁ →* G₂) (g : G₂ →* G₃) : f.ker ≤ (g.comp f).ker := fun x hx ↦ by simp_all

theorem ConjAct.toConjAct_inv_smul' {G : Type*} [Group G] (g h : G) :
    (ConjAct.toConjAct g)⁻¹ • h = g⁻¹ * h * g := by
  rw [← toConjAct_inv, toConjAct_inv_smul]

lemma map_inv_eq_iff {G H F : Type*} [FunLike F G H] [Group G] [Monoid H] [MonoidHomClass F G H]
    {f : F} {x y : G} : f x⁻¹ = f y⁻¹ ↔ f x = f y := by
  rw [← ((Group.isUnit x).map f).mul_left_inj, ← ((Group.isUnit y).map f).mul_right_inj]
  simp [← map_mul, eq_comm]

lemma map_inv_eq_map_comm
    {G H F : Type*} [FunLike F G H] [Group G] [Monoid H] [MonoidHomClass F G H]
    {f : F} {x y : G} : f x⁻¹ = f y ↔ f y⁻¹ = f x := by
  rw [← ((Group.isUnit x).map f).mul_left_inj, iff_comm, ← ((Group.isUnit y).map f).mul_right_inj]
  simp [← map_mul]

lemma Units.range_map_subtype {M : Type*} [Monoid M] {S : Submonoid M} :
    (Units.map S.subtype).range = S.units := by
  ext x
  constructor
  · rintro ⟨x, rfl⟩; simp [Submonoid.mem_units_iff]
  · rintro ⟨h₁, h₂⟩; exact ⟨⟨⟨x, h₁⟩, ⟨_, h₂⟩, by simp, by simp⟩, rfl⟩

lemma Subgroup.normal_of_le_center {G : Type*} [Group G] (H : Subgroup G)
    (hH : H ≤ .center G) : H.Normal where
  conj_mem h hh g := by simpa [mul_assoc, ← ((hH hh).comm g).eq]

instance {G H : Type*} [Group G] [Monoid H] [MulAction G H]
    [IsScalarTower G H H] [SMulCommClass G H H] :
    IsScalarTower G Hˣ Hˣ where
  smul_assoc x y z := by ext; simp [smul_mul_assoc]

lemma Group.dvd_natCard_iff_of_prime {G : Type*} [Group G] [Finite G] (p : ℕ) (hp : p.Prime) :
    p ∣ Nat.card G ↔ ∃ x : G, orderOf x = p :=
  ⟨exists_prime_orderOf_dvd_card' p (hp := ⟨hp⟩), fun h ↦ h.choose_spec ▸ orderOf_dvd_natCard _⟩

lemma Group.not_dvd_natCard_iff_of_prime {G : Type*} [Group G] [Finite G] (p : ℕ) (hp : p.Prime) :
    ¬ p ∣ Nat.card G ↔ ∀ x : G, orderOf x ≠ p := by
  simp [Group.dvd_natCard_iff_of_prime, hp]

lemma Subgroup.dvd_index_iff_of_prime {G : Type*} [Group G] {K : Subgroup G} [K.FiniteIndex]
    [K.Normal] (p : ℕ) (hp : p.Prime) :
    p ∣ K.index ↔ ∃ x ∉ K, x ^ p ∈ K := by
  simp [Subgroup.index, hp, Group.dvd_natCard_iff_of_prime,
    (QuotientGroup.mk'_surjective _).exists, orderOf_eq_prime_iff (hp := ⟨hp⟩),
    ← QuotientGroup.mk_pow, and_comm]

lemma Subgroup.dvd_relIndex_iff_of_prime {G : Type*} [Group G] {H K : Subgroup G}
    [(K.subgroupOf H).Normal] [K.IsFiniteRelIndex H] (p : ℕ) (hp : p.Prime) :
    p ∣ K.relIndex H ↔ ∃ x ∈ H, x ∉ K ∧ x ^ p ∈ K := by
  simp [Subgroup.relIndex, Subgroup.dvd_index_iff_of_prime, hp]; grind

instance Subgroup.mulActionMulOppositeNormalizerQuotient {G : Type*} [Group G] (H : Subgroup G) :
    MulAction (Subgroup.normalizer (H : Set G))ᵐᵒᵖ (G ⧸ H) where
  smul g := Quotient.map (· * g.unop) (by
    simp [QuotientGroup.leftRel_apply, mul_assoc,
      ← Subgroup.mem_normalizer_iff'.mp (inv_mem g.unop.2)])
  mul_smul x y m := QuotientGroup.induction_on m fun z ↦ QuotientGroup.eq.mpr (by group; simp)
  one_smul m := QuotientGroup.induction_on m fun z ↦ QuotientGroup.eq.mpr (by simp)

lemma normalizer_smul_mk {G : Type*} [Group G] (H : Subgroup G)
    (x : (Subgroup.normalizer (H : Set G))ᵐᵒᵖ) (y : G) : x • (y : G ⧸ H) = ↑(y * x.unop) := rfl

lemma mem_of_pow_mem_of_pow_mem_of_coprime {G : Type*} [Group G] {H : Subgroup G}
    {x : G} {m n : ℕ} (h : m.Coprime n) (hm : x ^ m ∈ H) (hn : x ^ n ∈ H) : x ∈ H := by
  rw [← zpow_one x, ← Nat.cast_one, ← h, ← Int.gcd_natCast_natCast, Int.gcd_eq_gcd_ab,
    zpow_add, zpow_mul, zpow_mul, zpow_natCast, zpow_natCast]
  exact mul_mem (zpow_mem hm _) (zpow_mem hn _)

lemma MonoidHom.range_comp_eq_range {M N P : Type*} [Group M] [Group N] [Group P]
    (f : M →* N) (g : N →* P) (hf : Function.Surjective f) :
    (g.comp f).range = g.range := by ext; simp [hf.exists]

@[simp]
lemma MonoidHom.range_comp_mulEquiv {M N P : Type*} [Group M] [Group N] [Group P]
    (f : M ≃* N) (g : N →* P) :
    (g.comp (f : M →* N)).range = g.range := MonoidHom.range_comp_eq_range _ g f.surjective

@[simp]
lemma IsUnit.unit_val_mul {M : Type*} [Monoid M] (a : Mˣ) (b : M) (H : IsUnit (a * b)) :
  H.unit = a * (show IsUnit b by simpa using H).unit := by ext; simp

@[to_additive (attr := simp)]
lemma MulEquivClass.coe_toMulEquiv {F M N : Type*} [Mul M] [Mul N] [EquivLike F M N]
    [MulEquivClass F M N]
    (f : F) : ⇑(MulEquivClass.toMulEquiv f) = f := rfl

lemma Units.range_val {M : Type*} [Monoid M] :
    Set.range Units.val = {x : M | IsUnit x} :=
  Set.ext fun _ ↦ ⟨fun ⟨u, hu⟩ ↦ hu ▸ u.isUnit, fun h ↦ ⟨h.unit, rfl⟩⟩
