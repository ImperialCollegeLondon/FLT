import Mathlib.Algebra.Quaternion
import Mathlib.RingTheory.SimpleModule
variable (K : Type) [Field K]
variable (A : Type) [Ring A] [IsSimpleOrder (RingCon A)] [Algebra K A]
  (h : FiniteDimensional K A)


open MulOpposite

-- TODO : define
@[simps]
def toMOP (rel : RingCon A) : (RingCon Aᵐᵒᵖ) :=
{ r := fun a b ↦ rel b.unop a.unop
  iseqv :=
  { refl := fun a ↦ rel.refl a.unop
    symm := rel.symm
    trans := fun h1 h2 ↦ rel.trans h2 h1 }
  mul' := fun h1 h2 ↦ rel.mul h2 h1
  add' := rel.add }

@[simps]
def fromMOP (rel : RingCon Aᵐᵒᵖ) : (RingCon A) :=
{ r := fun a b ↦ rel (op b) (op a)
  iseqv :=
  { refl := fun a ↦ rel.refl (op a)
    symm := rel.symm
    trans := fun h1 h2 ↦ rel.trans h2 h1 }
  mul' := fun h1 h2 ↦ rel.mul h2 h1
  add' := rel.add }

@[simps]
def toMopOrderIso : (RingCon A) ≃o (RingCon Aᵐᵒᵖ) where
  toFun := toMOP A
  invFun := fromMOP A
  left_inv := unop_op
  right_inv := unop_op
  map_rel_iff' {a b} := by
    dsimp [toMOP]
    constructor <;>
    · intro h _ _ H
      exact h H

instance op_simple : IsSimpleOrder (RingCon (Aᵐᵒᵖ)) :=
  (toMopOrderIso A).symm.isSimpleOrder

lemma op_iso_end : Nonempty (Aᵐᵒᵖ ≃+* (Module.End A A)) := by
  sorry

lemma matrixop_iso_op (n : ℕ) (D :Type) (h : DivisionRing D) : Nonempty
  ((Matrix (Fin n) (Fin n) D) ≃+* (Matrix (Fin n) (Fin n) D)ᵐᵒᵖ) := by
  sorry

theorem Wedderburn_Artin : ∃(n : ℕ) (S : Type) (h : DivisionRing S),
  Nonempty (A ≃+* (Matrix (Fin n) (Fin n) (S))) := by
  sorry
