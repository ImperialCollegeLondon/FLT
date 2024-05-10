import Mathlib.NumberTheory.Cyclotomic.CyclotomicCharacter
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import FLT.AutomorphicRepresentation.Example

variable (K : Type) [Field K]
variable (L : Type) [Field L] [Algebra K L] [CharZero L] [IsAlgClosed L] -- not even sure if i need it to be the alg closure at this point

lemma IsAlgClosed.card_rootsOfUnity (N : ℕ+) : Fintype.card (rootsOfUnity N L) = N := by
  obtain ⟨z, hz⟩ : ∃ z : L, IsPrimitiveRoot z N :=
    IsCyclotomicExtension.exists_prim_root L (show _ ∈ ⊤ by simp)
  exact IsPrimitiveRoot.card_rootsOfUnity hz

@[norm_cast]
lemma PNat.coe_dvd_iff (A B : ℕ+) : (A : ℕ) ∣ B ↔ A ∣ B := by exact Iff.symm dvd_iff

lemma foo {a b c : ℕ} {G : Type} [Group G] {t : G} (h : t ^ a = 1) (h2 : b ≡ c [MOD a]) :
  t ^ b = t ^ c := by sorry

/-- The cyclotomic character-/
noncomputable def CyclotomicCharacter_aux : (L ≃+* L) →* ZHat where
  toFun g := ⟨fun N ↦ ModularCyclotomicCharacter L (IsAlgClosed.card_rootsOfUnity L N) g, by
    intros D M h
    apply ModularCyclotomicCharacter.unique
    intros t htD
    have hcoe := h
    norm_cast at h
    -- have foo : t ∈ rootsOfUnity M L := rootsOfUnity_le_of_dvd h htD
    rw [ModularCyclotomicCharacter.spec L (IsAlgClosed.card_rootsOfUnity L M) g <|
          rootsOfUnity_le_of_dvd h htD]
    -- Now we just have one fixed element `(x : (ZMod ↑M)ˣ)` and a `D`'th root of unity `t`
    -- and the claim is that t^x.val = t^(cast x to Z/DZ).val
    norm_cast
    change t ^ _ = 1 at htD
    apply foo htD
    dsimp only
    generalize (ModularCyclotomicCharacter L (IsAlgClosed.card_rootsOfUnity L M) g : ZMod M) = e
    /-
    hcoe : ↑D ∣ ↑M
    e : ZMod ↑M
    ⊢ (↑D).ModEq e.val e.cast.val
    -/
    sorry⟩
  map_one' := by ext; simp only [map_one]; rfl
  map_mul' _ _ := by ext; simp only [map_mul]; rfl

noncomputable def CyclotomicCharacter : (L ≃+* L) →* ZHatˣ := (CyclotomicCharacter_aux L).toHomUnits
