import Mathlib

open CategoryTheory CategoryTheory.Limits

universe u

variable {k : Type u} [CommRing k] {G : Type u} [Group G]

/-! ### Double cosets `K \ G / H` -/

/-- `g` and `g'` lie in the same `(K, H)`-double coset iff `g' = a * g * b`
for some `a ∈ K`, `b ∈ H`. -/
def dosetSetoid (K H : Subgroup G) : Setoid G where
  r := fun g g' => ∃ a ∈ K, ∃ b ∈ H, g' = a * g * b
  iseqv :=
  { refl := fun g => ⟨1, K.one_mem, 1, H.one_mem, by group⟩
    symm := fun {g g'} h => by
      obtain ⟨a, ha, b, hb, rfl⟩ := h
      exact ⟨a⁻¹, K.inv_mem ha, b⁻¹, H.inv_mem hb, by group⟩
    trans := fun {g g' g''} h1 h2 => by
      obtain ⟨a, ha, b, hb, rfl⟩ := h1
      obtain ⟨c, hc, d, hd, rfl⟩ := h2
      exact ⟨c * a, K.mul_mem hc ha, b * d, H.mul_mem hb hd, by group⟩ }

/-- The double coset space `K \ G / H`. -/
abbrev DoubleCoset (K H : Subgroup G) : Type u := Quotient (dosetSetoid K H)

/-! ### The conjugate representation `ˢV` -/

/-- Conjugation by `s` restricts to an isomorphism `H ≃* sHs⁻¹`. -/
noncomputable def conjEquiv (H : Subgroup G) (s : G) :=
  H.equivMapOfInjective (MulAut.conj s : G →* G) (MulAut.conj s).injective

/-- The conjugate representation `ˢV`: if `V` is a representation of `H`, this is the
representation of `sHs⁻¹` on the same space where `x ∈ sHs⁻¹` acts the way `s⁻¹ x s` did. -/
noncomputable def conjFunctor (H : Subgroup G) (s : G) :
    Rep k H ⥤ Rep k (H.map (MulAut.conj s : G →* G)) :=
  Action.res (ModuleCat k) (MonCat.ofHom (conjEquiv H s).symm.toMonoidHom)

/-! ### Mackey's theorem (restriction of an induced representation) -/

/-- **Mackey decomposition / subgroup theorem.**

Given subgroups `H, K ≤ G` and a representation `V` of `H`, and writing `ind` for
induction (any left adjoint of restriction along an injective homomorphism):

  `Res_K (Ind_H^G V)  ≅  ∐_{s ∈ K\G/H}  Ind_{K ∩ sHs⁻¹}^K (Res (ˢV))`. -/
theorem mackey_restriction_of_induction
    (ind : ∀ {A B : Type u} [Group A] [Group B] (f : A →* B),
        Function.Injective f → (Rep k A ⥤ Rep k B))
    (adj : ∀ {A B : Type u} [Group A] [Group B] (f : A →* B) (hf : Function.Injective f),
        ind f hf ⊣ Action.res (ModuleCat k) (MonCat.ofHom f))
    (K H : Subgroup G) (V : Rep k H) :
    Nonempty
      ((Action.res (ModuleCat k) (MonCat.ofHom K.subtype)).obj
            ((ind H.subtype Subtype.val_injective).obj V)
        ≅ ∐ fun q : DoubleCoset K H =>
            (ind (Subgroup.inclusion
                    (inf_le_left : K ⊓ H.map (MulAut.conj q.out : G →* G) ≤ K))
                  (Subgroup.inclusion_injective _)).obj
              ((Action.res (ModuleCat k)
                  (MonCat.ofHom (Subgroup.inclusion
                    (inf_le_right : K ⊓ H.map (MulAut.conj q.out : G →* G)
                        ≤ H.map (MulAut.conj q.out : G →* G))))).obj
                ((conjFunctor H q.out).obj V))) := by
  sorry
