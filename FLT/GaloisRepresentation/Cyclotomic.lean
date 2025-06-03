import Mathlib.NumberTheory.Cyclotomic.CyclotomicCharacter
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import FLT.AutomorphicRepresentation.Example
import Mathlib.NumberTheory.Cyclotomic.Basic

variable (K : Type) [Field K]
variable (L : Type) [Field L] [Algebra K L] [CharZero L] [IsAlgClosed L]
  -- not even sure if i need it to be the alg closure at this point

lemma IsAlgClosed.card_rootsOfUnity (N : ℕ) [NeZero N] : Fintype.card (rootsOfUnity N L) = N := by
  obtain ⟨z, hz⟩ : ∃ z : L, IsPrimitiveRoot z N :=
    IsCyclotomicExtension.exists_isPrimitiveRoot L _ (show _ ∈ ⊤ by simp) (NeZero.ne N)
  exact IsPrimitiveRoot.card_rootsOfUnity hz

@[norm_cast]
lemma PNat.coe_dvd_iff (A B : ℕ+) : (A : ℕ) ∣ B ↔ A ∣ B := by exact Iff.symm dvd_iff

lemma rootsOfUnity.pow_eq_pow {a b c : ℕ} {G : Type} [Group G] {t : G} (h : t ^ a = 1)
    (h2 : b ≡ c [MOD a]) : t ^ b = t ^ c := by
  rw [pow_eq_pow_mod b h, pow_eq_pow_mod c h]
  exact congr_arg _ h2

lemma PNat.castHom_val_modEq {D : ℕ} {N : ℕ+} (h : D ∣ N) (e : ZMod N) :
    (ZMod.castHom h _ e : ZMod D).val ≡ e.val [MOD D] := by
  rw [ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.val_natCast]
  exact Nat.mod_modEq e.val D

/-- The cyclotomic character-/
noncomputable def CyclotomicCharacter_aux : (L ≃+* L) →* ZHat where
  toFun g := ⟨fun N ↦ modularCyclotomicCharacter L (IsAlgClosed.card_rootsOfUnity L N) g, by
    intros D M h
    apply modularCyclotomicCharacter.unique
    intros t htD
--    norm_cast at h
    rw [modularCyclotomicCharacter.spec L (IsAlgClosed.card_rootsOfUnity L M) g <|
          rootsOfUnity_le_of_dvd h htD]
    norm_cast
    apply rootsOfUnity.pow_eq_pow htD
    dsimp only
    symm
    apply PNat.castHom_val_modEq⟩
  map_one' := by ext; simp only [map_one]; rfl
  map_mul' _ _ := by ext; simp only [map_mul]; rfl

noncomputable def CyclotomicCharacterZHat : (L ≃+* L) →* ZHatˣ :=
  (CyclotomicCharacter_aux L).toHomUnits
