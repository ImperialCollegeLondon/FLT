import Mathlib.RingTheory.Ideal.Basic
import Mathlib.RingTheory.SimpleModule
import FLT.for_mathlib.Con

variable (K : Type*) [Field K]
variable (A : Type*) [Ring A]



-- Theorem 2.21
/-
Theorem 2.21. Let Mn(R) be a full matrix ring on the ring R, then any ideal I is of the form Mn(I)
for some ideal I of R.
Proof. If I is an ideal of R, then as scalar multiplication and matrix addition happen component-wise
it is clear that Mn(I) is an ideal of Mn(R). Further- more, if Mn(I1) = Mn(I2) for ideals I1,I2,
it is clear that I1 = I2 because matrices are equal if and only if each component is equal.
Next, suppose that J is an ideal of Mn(R). Let I denote the set of elements in the top left entry
of the matrices of J , then I is an ideal of R. This is because first, it’s trivially closed under
addition and secondly, if it’s not closed under multiplication of elements in R, then it contradicts
J is an ideal of Mn(R). Let eij be the matrix with 0 in every entry apart from the ijth entry.
Let M ∈ J , then e1jMej1 = mije11 ∈ J so that mij ∈ I and hence J ⊆ Mn(I). On the other hand, let N = (nij) ∈ Mn(I), and take M = (mij) ∈ J such that m11 = nij. Then nijeij = m11eij = ei1Me1j = m11eij ∈ J. Therefore, as J is closed under addition, and ij were arbitrary it follows that N ∈ J . Therefore, Mn(I) ⊆ I which means that Mn(I) = J .
-/

open BigOperators

section two_two_one

variable (n : ℕ) (hn : 0 < n)

local notation "M[" n "," R "]" => Matrix (Fin n) (Fin n) R

@[simps]
def RingCon.fromIdeal
    (carrier : Set A)
    (zero : 0 ∈ carrier)
    (add : ∀ a b, a ∈ carrier → b ∈ carrier → a + b ∈ carrier)
    (neg : ∀ a, a ∈ carrier → -a ∈ carrier)
    (left_absorb : ∀ a b, b ∈ carrier → a * b ∈ carrier)
    (right_absorb : ∀ a b, a ∈ carrier → a * b ∈ carrier) : RingCon A where
  r a b := a - b ∈ carrier
  iseqv :=
  { refl := fun a ↦ by simpa
    symm := fun {x y} h ↦ by
      simpa only [show y - x = -(x - y) by abel] using neg _ h
    trans := fun {a b c } h1 h2 ↦ by
      simpa only [show a - c = (a - b) + (b - c) by abel] using add _ _ h1 h2 }
  mul' {a b c d} h1 h2 := show _ - _ ∈ _ by
    change a * c - b * d ∈ carrier
    rw [show a * c - b * d = (a - b) * c + b * (c - d) by
      rw [sub_mul, mul_sub]; aesop]
    exact add _ _ (right_absorb _ _ h1) (left_absorb _ _ h2)
  add' {a b c d} h1 h2 := by
    change (a + c) - (b + d) ∈ carrier
    rw [show (a + c) - (b + d) = (a - b) + (c - d) by abel]
    exact add _ _ h1 h2

@[simps]
def RingCon.mapMatrix (I : RingCon A) : RingCon M[n, A] where
  r X Y := ∀ i j, I (X i j) (Y i j)
  iseqv :=
  { refl := fun X i j ↦ I.refl (X i j)
    symm := fun h i j ↦ I.symm (h i j)
    trans := fun h1 h2 i j ↦ I.trans (h1 i j) (h2 i j) }
  mul' h h' := fun i j ↦ by
    simpa only [Matrix.mul_apply] using I.sum fun k _ ↦ I.mul (h _ _) (h' _ _)
  add' {X X' Y Y'} h h' := fun i j ↦ by
    simpa only [Matrix.add_apply] using I.add (h _ _) (h' _ _)

lemma Matrix.ringCon_eq_ring_ringCon
    -- J is a two side ideal of Mₙ(R)
    (J : RingCon (M[n, A])) :
    ∃ (I : RingCon A), J = I.mapMatrix n := by
  let I : RingCon A := RingCon.fromIdeal A
    ((fun (x : M[n, A]) => x ⟨0, by omega⟩ ⟨0, by omega⟩) '' J)
    ⟨0, J.zero_mem, rfl⟩
    (by
      rintro _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
      exact ⟨x + y, J.add_mem hx hy, rfl⟩)
    (by
      rintro _ ⟨x, hx, rfl⟩
      exact ⟨-x, J.neg_mem hx, rfl⟩)
    (by
      rintro x _ ⟨y, hy, rfl⟩
      exact ⟨Matrix.diagonal (fun _ ↦ x) * y, J.mul_mem_left _ _ hy, by simp⟩)
    (by
      rintro _ y ⟨x, hx, rfl⟩
      exact ⟨x * Matrix.diagonal (fun _ ↦ y), J.mul_mem_right _ _ hx, by simp⟩)
  use I
  refine SetLike.ext fun x ↦ ?_
  constructor
  · intro hx i j
    change (x i j) ∈ I
    sorry
  · sorry


end two_two_one

open MulOpposite


variable [IsSimpleOrder (RingCon A)] [Algebra K A] (h : FiniteDimensional K A)


@[simps]
def toMop (rel : RingCon A) : (RingCon Aᵐᵒᵖ) :=
{ r := fun a b ↦ rel b.unop a.unop
  iseqv :=
  { refl := fun a ↦ rel.refl a.unop
    symm := rel.symm
    trans := fun h1 h2 ↦ rel.trans h2 h1 }
  mul' := fun h1 h2 ↦ rel.mul h2 h1
  add' := rel.add }

@[simps]
def fromMop (rel : RingCon Aᵐᵒᵖ) : (RingCon A) :=
{ r := fun a b ↦ rel (op b) (op a)
  iseqv :=
  { refl := fun a ↦ rel.refl (op a)
    symm := rel.symm
    trans := fun h1 h2 ↦ rel.trans h2 h1 }
  mul' := fun h1 h2 ↦ rel.mul h2 h1
  add' := rel.add }

@[simps]
def toMopOrderIso : (RingCon A) ≃o (RingCon Aᵐᵒᵖ) where
  toFun := toMop A
  invFun := fromMop A
  left_inv := unop_op
  right_inv := unop_op
  map_rel_iff' {a b} := by
    constructor <;>
    · intro h _ _ H
      exact h H

instance op_simple : IsSimpleOrder (RingCon (Aᵐᵒᵖ)) :=
  (toMopOrderIso A).symm.isSimpleOrder

@[simps]
def mopToEnd : Aᵐᵒᵖ →+* Module.End A A where
  toFun a :=
    { toFun := fun x ↦ x * a.unop
      map_add' := by simp [add_mul]
      map_smul' := by simp [mul_assoc] }
  map_zero' := by aesop
  map_one' := by aesop
  map_add' := by aesop
  map_mul' := by aesop


noncomputable def mopEquivEnd : Aᵐᵒᵖ ≃+* Module.End A A := by
  refine RingEquiv.ofBijective (mopToEnd A) ⟨?_, ?_⟩
  · rw [RingHom.injective_iff_ker_eq_bot]
    ext α
    constructor
    · intro ha
      change ((mopToEnd A) α) = 0 at ha
      rw [DFunLike.ext_iff] at ha
      specialize ha 1
      simp at ha
      exact ha

    · intro ha
      change α = 0 at ha
      ext ; simp [ha]

  · intro φ
    use (op (φ 1))
    ext ; simp

def maxtrixEquivMatrixMop (n : ℕ) (D : Type*) (h : DivisionRing D) :
    Matrix (Fin n) (Fin n) D ≃+* (Matrix (Fin n) (Fin n) D)ᵐᵒᵖ where
      toFun := fun a ↦ op a.transpose
      invFun := fun a ↦ a.unop.transpose  
      left_inv x := by simp only [unop_op, Matrix.transpose_transpose]
      right_inv x := by simp only [Matrix.transpose_transpose, op_unop]
      map_mul' x y := by 
        simp;
        have hxy : (x * y).transpose = y.transpose * x.transpose := sorry;
        rw [hxy]; simp
      map_add' x y := by simp


theorem Wedderburn_Artin : ∃(n : ℕ) (S : Type) (h : DivisionRing S),
  Nonempty (A ≃+* (Matrix (Fin n) (Fin n) (S))) := by
  sorry
