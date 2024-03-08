import Mathlib.Tactic
import Mathlib.RingTheory.TensorProduct
import Mathlib.RingTheory.HopfAlgebra
open Function
open scoped TensorProduct
set_option maxHeartbeats 5000000
set_option linter.unusedVariables false
/-!
# Algebra and Linear Homomorphisms of Bialgebras, Coalgebras and Algebras
The first part of this files provides proofs of all the Algebra homomorphism from a
R-Bialgebra A to a Commutative R-Algebra L (defined as Points R A L) forms a monoid with the binary
operation "*" defined by convolution product and "one" defined by the composition of unit of L and
counit of A ((Algebra.ofId R L).comp (Bialgebra.counitAlgHom R A)), while the second part proves
that all the linear homomorphisms from a R-Coalgebra C to a R-Algebra B also forms a monoid by
the linear convolution product and the identity "linone" defined by (one _ _ _).toLinearMap.

# Proof of  TensorProduct of two R-Bialgebras (A1 and A2) are R-Bialgebras
The third part of this file is a preparation of the proof of the Antipode of a Hopf R-Algebra is
indeed an antihomomorphism (namely S(ab) = S(b)*S(a)), to do that we defined α β: H ⊗[R] H →ₗ H
to be α : (a ⊗ b) ↦ S(ab) and β : (a ⊗ b) ↦ S(b)*S(a). But for that to work we need the fact that
H ⊗ H is a Bialgebra and we genralized it to the Bialgebra case (In fact, C ⊗ C is a Coalgebra
for C being R-Coalgebra but we kind of include that in our proof of Bialgebra).

# Proof of all Algebra Homomorphism from a Commutative Hopf Algebra to a R-Algebra forms a Group
The fourth part of the part proves that (Points R H L) is a group that inherits multiplication
and identity elements from the monoid structure proved in Part I with inverse given by f⁻¹ =
(S ∘ f). And to do that we need antipode is an antihomomorphism (hence under the condition of
commutativity, we have that the antipode is an Algebra Homomorphism), and we did that by showing
α * m = linone and m * β = linone where m is the multiplication of H. Therefore α = α * linone
= α * (m * β) = (α * m) * β = linone * β = β showing that the anipode S is indeed an
antihomomorphism in H, then everythings follows (proving the group axioms, etc.)

# Finishing the TO-DO list in Hopf Algebra Files
At the end of this file (some are proved within the previous parts), we proved that S² = id and S
is a Bijection when H is Commutative (the case where H is Co-Commutative is unproved yet) and the
proof of the uniqueness of antipode is in the proof of LinPoints forms a monoid named as
anti_unique.

## Main declarations
- `Points.Points R A L` is all the R-Algebra Homomorphisms A →ₐ[R] L
- `Points.Pointmul_assoc` is the associativity of R-Algebra Homomorphisms in `Points R A L` under
  convolution product "*".
- `HopfPoints.LinPoints R C B` is all the R-Linear Maps C →ₗ[R] B where C is R-Coalgbra
  and B is R-Algebra
- `HopfPoints.mul_id_val`: id_H * S = linone under linear convolution product
- `HopfPoints.id_mul_val`: S * id_H = linone under linear convolution product
- `HopfPoints.UniquenessAnti` : Any T : H →ₗ H, if T * id_H = id_H * T = linone, then
  T = antipode (uniqueness of antipode).
- `HopfPoints.comul_repr` is the seedler notation for comultiplication for R-Coalgebras, that is
  ∀ x ∈ C, comul x can be expressed as ∑ i in I, x1 i ⊗ x2 i
- `HopfPoints.αmul_eqone`: α * m = linone
- `HopfPoints.mulβ_eqone`: m * β = linone
- `HopfPoints.antihom` : S(ab) = S(b) * S(a)
- `HopfPoints.antipodemul` : Under a Commutative Hopf Algebra H, S(ab) = S(a) * S(b)
- `HopfPoints.S2isid` : S² = id_H
- `HopfPoints.bijectiveAntipode` : S is bijection.

## References
* <https://en.wikipedia.org/wiki/Hopf_algebra>
* Christian Kassel "Quantum Groups" (Springer GTM), around Prop III.3.1, Theorem III.3.4 etc.
* Dr.Adrian de Jesus Celestino Rodriguez "Cumulants in Non-commutative Probability via Hopf
  Algebras", 2022
-/
variable (R : Type)[CommRing R]
variable (A : Type)[Ring A][Bialgebra R A]
variable (L : Type)[CommRing L][Algebra R L]

variable {ψ φ ρ : A →ₐ[R] L}
-- Goal of the First Part is to Prove Points R A L is a monoid
namespace Points
-- Define Points to be all the algebra homomorphisms from a R-Bialgebra A to a
-- Commutative R-Algebra L
def Points := A →ₐ[R] L
noncomputable section
variable {R A L}{x : A}
instance : Coalgebra R A := by infer_instance
-- Define the multiplication for Points to be convolution product
def mul (ψ φ : Points R A L) : Points R A L :=
  (Algebra.TensorProduct.lmul' (S := L) R).comp
    ((Algebra.TensorProduct.map ψ φ).comp (Bialgebra.comulAlgHom R A))

lemma mul1(ψ φ : Points R A L) : mul ψ φ =
  (Algebra.TensorProduct.lmul' (S := L) R).comp
    ((Algebra.TensorProduct.map ψ φ).comp (Bialgebra.comulAlgHom R A)) := by rfl
variable {a b c : A}

instance : Mul (Points R A L) := ⟨mul⟩
instance : HMul (Points R A L) (Points R A L) (Points R A L) := ⟨mul⟩

lemma hmul1(ψ φ : Points R A L) : ψ * φ =
  (Algebra.TensorProduct.lmul' (S := L) R).comp
    ((Algebra.TensorProduct.map ψ φ).comp (Bialgebra.comulAlgHom R A)) := by rfl

-- The identity element in this monoid is unit comp counit which maps from
-- A -> R -> L
def one : Points R A L :=
  (Algebra.ofId R L).comp
    (Bialgebra.counitAlgHom R A) -- counit and then map from R to L

lemma oneval: one = (Algebra.ofId R L).comp
    (Bialgebra.counitAlgHom R A) := by rfl

instance : One (Points R A L) := ⟨one⟩

-- The purpose of these two instances are to prove the 'ext' lemma for elements
-- in Points such that we could use the 'ext' tactic
instance : FunLike (Points R A L) A L := by unfold Points; infer_instance

instance : AlgHomClass (Points R A L) R A L := by
  unfold Points
  infer_instance

@[ext]
lemma Pointext (ψ φ : Points R A L) (hx : ∀ x, ψ x = φ x): ψ = φ :=
  AlgHom.ext hx
-- 3 commutative R-algeberas A,B,C
-- two maps A ⊗ B -> C, R-algebra maps
-- if they're equal on all elements of the form a ⊗ₜ b
-- then they're equal

@[ext]
lemma AlgTensorExt (A1 A2 B : Type)[Ring B][Ring A2][Ring A1][Algebra R A1][Algebra R A2]
  [Algebra R B](F : A1 ⊗[R] A2 →ₐ[R] B)
  (G : A1 ⊗[R] A2 →ₐ[R] B) (h : ∀ a b, F (a ⊗ₜ b) = G (a ⊗ₜ b)) : F = G := by
  ext x <;> simp [h]

-- Breaking down the commutative diagram into small parts : this lemma shows that
-- (ψ * φ) ⊗ ρ = (m ⊗ id) ∘ (ψ ⊗ φ) ⊗ ρ ∘ (Δ ⊗ id) where m is the multiplication
-- of L and Δ is the comultiplication of A
lemma left_block_comm (ψ φ ρ : Points R A L) :
  Algebra.TensorProduct.map (ψ * φ) ρ = (Algebra.TensorProduct.map
    (Algebra.TensorProduct.lmul' (S := L) R) (AlgHom.id R L)).comp
    ((Algebra.TensorProduct.map (Algebra.TensorProduct.map ψ φ) ρ).comp
    (Algebra.TensorProduct.map (Bialgebra.comulAlgHom R A) (AlgHom.id R A))) := by
      symm
      rw [hmul1 ψ φ]
      ext x <;> simp

-- This lemma shows ψ ⊗ (φ * ρ) = (id ⊗ Δ) ∘ ψ ⊗ (φ ⊗ ρ) ∘ (id ⊗ m)
lemma right_block_comm (ψ φ ρ : Points R A L) :
  Algebra.TensorProduct.map ψ (φ * ρ) = (Algebra.TensorProduct.map
  (AlgHom.id R L) (Algebra.TensorProduct.lmul' (S := L) R)).comp
  ((Algebra.TensorProduct.map ψ (Algebra.TensorProduct.map φ ρ)).comp
  (Algebra.TensorProduct.map (AlgHom.id R A) (Bialgebra.comulAlgHom R A))) := by
  symm ; rw [hmul1 φ ρ]
  ext x <;> simp

-- We define maps that idetify the associativity of tensor products of A and L
-- respectively (here I should have used abbrev instead of def as kevin has pointed
-- out, but when I realized this it's already too many lines :)))
def assoc_a : (A ⊗[R] A) ⊗[R] A →ₐ[R] A ⊗[R] (A ⊗[R] A) :=
  (Algebra.TensorProduct.assoc R A A A).toAlgHom

def assoc_l : (L ⊗[R] L) ⊗[R] L →ₐ[R] L ⊗[R] (L ⊗[R] L) :=
  (Algebra.TensorProduct.assoc R L L L).toAlgHom

-- After decomposing the commutative diagram into small parts, we prove the upper
-- half first, which is: (Δ ⊗ id) ∘ Δ = (id ⊗ Δ) ∘ Δ which is the variation of one
-- of the axioms of Coalgebra.
lemma Coassoc : assoc_a ((Algebra.TensorProduct.map (Bialgebra.comulAlgHom R A)
  (AlgHom.id R A)).comp (Bialgebra.comulAlgHom R A) x) =
  (Algebra.TensorProduct.map  (AlgHom.id R A) (Bialgebra.comulAlgHom R A)).comp
  (Bialgebra.comulAlgHom R A) x := by
  repeat rw [AlgHom.comp_apply]
  simp_all only [Bialgebra.comulAlgHom_apply]
  have h0 := Coalgebra.coassoc_apply (R := R) (A := A) x
  change assoc_a ((LinearMap.rTensor A Coalgebra.comul) (Coalgebra.comul x)) =
  (LinearMap.lTensor A Coalgebra.comul) (Coalgebra.comul x) at h0
  exact h0

-- This is the middle part of the commutative diagram that explains the associativity
-- of maps which is : (ψ ⊗ φ) ⊗ ρ = ψ ⊗ (φ ⊗ ρ)
lemma Mapassoc' (ψ φ ρ : Points R A L):
  assoc_l.comp ((Algebra.TensorProduct.map (Algebra.TensorProduct.map ψ φ) ρ))
  = (Algebra.TensorProduct.map ψ (Algebra.TensorProduct.map φ ρ)).comp assoc_a := by
  ext x <;> rfl

-- This is the lemma above applied on elements in A ⊗ A ⊗ A
lemma Mapassoc (ψ φ ρ : Points R A L) (aaa : (A ⊗[R] A) ⊗[R] A):
  assoc_l (((Algebra.TensorProduct.map (Algebra.TensorProduct.map ψ φ) ρ)) aaa)
  = (Algebra.TensorProduct.map ψ (Algebra.TensorProduct.map φ ρ)) (assoc_a aaa)
  := by apply AlgHom.ext_iff.1 (Mapassoc' ψ φ ρ) aaa

open BigOperators
-- This is the lower part of the commutative diagram which is a variation of one
-- of the axioms of an Algebra : m ∘ (m ⊗ id) = m ∘ (id ⊗ m)
lemma Al_assoc : (Algebra.TensorProduct.lmul' R).comp ((Algebra.TensorProduct.map
  (Algebra.TensorProduct.lmul' R) (AlgHom.id R L))) =
  (Algebra.TensorProduct.lmul' R).comp ((Algebra.TensorProduct.map (AlgHom.id R L)
  (Algebra.TensorProduct.lmul' R)).comp assoc_l) := by
  ext x
  · delta assoc_l ; simp
  · delta assoc_l ; simp
  · delta assoc_l ; simp only [AlgHom.coe_comp, AlgHom.coe_restrictScalars', comp_apply,
      Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.map_tmul, map_one,
      AlgHom.coe_id, id_eq, Algebra.TensorProduct.lmul'_apply_tmul, one_mul,
      AlgEquiv.toAlgHom_eq_coe, AlgHom.coe_coe]
    rw [show (1 : L ⊗[R] L) = (1 ⊗ₜ[R] 1) by rfl]
    simp

-- The lemma above applied on elements of L ⊗ L ⊗ L
lemma Al_assoc_apply (lll : (L ⊗[R] L) ⊗[R] L) : (Algebra.TensorProduct.lmul' R)
  ((Algebra.TensorProduct.map (Algebra.TensorProduct.lmul' R) (AlgHom.id R L)) lll) =
  (Algebra.TensorProduct.lmul' R) ((Algebra.TensorProduct.map (AlgHom.id R L)
  (Algebra.TensorProduct.lmul' R)) (assoc_l lll)) := by
  have := Al_assoc (R := R) (L := L)
  exact congrFun (congrArg DFunLike.coe this) lll

-- Finally one of the big theorem! The associativity of the elements in Points under
-- convolution product!
lemma Pointmul_assoc (ψ φ ρ : Points R A L) : (ψ * φ) * ρ = ψ * (φ * ρ) := by
  rw [hmul1 (ψ*φ) ρ, hmul1 ψ (φ*ρ), left_block_comm, right_block_comm]
  ext x
  set aaa := (Algebra.TensorProduct.map (Bialgebra.comulAlgHom R A) (AlgHom.id R A)).comp
    (Bialgebra.comulAlgHom R A) x with aaa_eq
  have h0 : assoc_a aaa = (Algebra.TensorProduct.map (AlgHom.id R A)
    (Bialgebra.comulAlgHom R A)) ((Bialgebra.comulAlgHom R A) x) := by
    rw [Coassoc (R:=R) (A:=A) (x:=x)]; dsimp
  repeat rw [AlgHom.comp_apply]
  rw [AlgHom.comp_apply] at aaa_eq
  rw [←aaa_eq, ← h0]
  set lll := (Algebra.TensorProduct.map (Algebra.TensorProduct.map ψ φ) ρ) aaa
  have h1 : ((Algebra.TensorProduct.map ψ (Algebra.TensorProduct.map φ ρ))
    (assoc_a aaa)) = assoc_l lll := by rw [Mapassoc]
  rw [h1, Al_assoc_apply]

-- Next we started to prove the other axioms for a monoid : one_mul and mul_one.
/- Again, we decompose the (ψ * one) into a few small steps, and this lemma shows
(id ⊗ ε) ∘ Δ  = - ⊗ (1 : R) where ε is counit of A and "-" is any element in A. -/
lemma Pointmul_onel1 : (Algebra.TensorProduct.map (AlgHom.id R A)
  (Bialgebra.counitAlgHom R A)).comp (Bialgebra.comulAlgHom R A) =
  Algebra.TensorProduct.includeLeft := by
  ext x ; simp only [AlgHom.comp_apply, Bialgebra.comulAlgHom_apply,
    Algebra.TensorProduct.includeLeft_apply]
  exact Coalgebra.lTensor_counit_comul (R := R) (A := A) x

/- This lemma decomposes ψ ⊗ one = (id ⊗ η) ∘ (ψ ⊗ id) ∘ (id ⊗ ε) where η is unit of L -/
lemma Pointmul_onel2 : (Algebra.TensorProduct.map ψ one) =
  (Algebra.TensorProduct.map (AlgHom.id R L)
  (Algebra.ofId R L)).comp ((Algebra.TensorProduct.map ψ (AlgHom.id R R)).comp
  ((Algebra.TensorProduct.map (AlgHom.id R A)
  (Bialgebra.counitAlgHom R A)))) := by
  rw [oneval] ; ext aa <;> simp

/- This is the mul_one axiom of the monoid Points R A L-/
lemma Pointmul_one (ψ : Points R A L) : ψ * one = ψ := by
  rw [hmul1, Pointmul_onel2]
  have h1 := Pointmul_onel1 (R := R) (A := A) ; ext x
  have := congrFun (congrArg DFunLike.coe h1) x
  rw [AlgHom.comp_apply, AlgHom.comp_apply, AlgHom.comp_apply, AlgHom.comp_apply] at *
  rw [this] ; simp

/- This lemma shows (ε ⊗ id) ∘ Δ = (1 : R) ⊗ - where "-" is any element of A -/
lemma Pointone_mul1 : (Algebra.TensorProduct.map (Bialgebra.counitAlgHom R A)
  (AlgHom.id R A)).comp (Bialgebra.comulAlgHom R A) =
  Algebra.TensorProduct.includeRight := by
  ext x ; simp only [AlgHom.comp_apply, Bialgebra.comulAlgHom_apply,
    Algebra.TensorProduct.includeRight_apply]
  exact Coalgebra.rTensor_counit_comul (R := R) (A := A) x

/- This lemma decomposes (one ⊗ ψ) = (η ⊗ id) ∘ (id ⊗ ψ) ∘ (ε ⊗ id) -/
lemma Pointone_mul2 :  (Algebra.TensorProduct.map one ψ) =
  (Algebra.TensorProduct.map (Algebra.ofId R L) (AlgHom.id R L)).comp
  ((Algebra.TensorProduct.map (AlgHom.id R R) ψ).comp
  (Algebra.TensorProduct.map (Bialgebra.counitAlgHom R A) (AlgHom.id R A)))
  := by rw [oneval] ; ext aa <;> simp

/- This is the one_mul axiom of the monoid Points R A L-/
lemma Pointone_mul (ψ : Points R A L) : one * ψ = ψ := by
  rw [hmul1, Pointone_mul2]
  have h0 := Pointone_mul1 (R := R) (A := A)
  ext x ; have := congrFun (congrArg DFunLike.coe h0) x
  repeat rw [AlgHom.comp_apply] at *
  rw [this] ; simp

/- Finally we proved Points R A L is indeed a monoid! -/
instance : Monoid (Points R A L) :=
{ mul := mul,
  one := one,
  mul_assoc := Pointmul_assoc,
  one_mul := Pointone_mul,
  mul_one := Pointmul_one }
-- End of Part I
end
end Points

namespace HopfPoints
noncomputable section
-- This is the second part where I realized not only all Algebra Homomorphisms forms
-- a monoid, all the R-Linear Maps from a R-Coalgebra to an R-Algebra also forms a monoid.
variable (H : Type)[CommRing H][HopfAlgebra R H]
variable (L : Type)[CommRing L][Algebra R L]
variable (C : Type)[Ring C][Module R C][Coalgebra R C]
variable (B : Type)[Ring B][Algebra R B]
variable {H L}
variable (A1 A2 : Type)[Ring A1][Ring A2][Bialgebra R A1][Bialgebra R A2]
open HopfAlgebra
open Points
open BigOperators
set_option synthInstance.maxHeartbeats 500000
instance : Bialgebra R H := inferInstance
-- Proving for a Coalgebra C, Lin(C, A) is a monoid (actually it's an algebra)

/- LinPoints R C B are all the R-LinearMaps from C → B  -/
abbrev LinPoints := C →ₗ[R] B
def linmul (a b : LinPoints R C B) : LinPoints R C B := (LinearMap.mul' R B).comp
  ((TensorProduct.map a b).comp (Coalgebra.comul))

instance : Mul (LinPoints R C B) := ⟨linmul R C B⟩
instance : HMul (LinPoints R C B) (LinPoints R C B) (LinPoints R C B) := ⟨linmul R C B⟩

/- Definition of multiplication and identity element is the same as the algebra ones
   but just in linear version. -/
lemma linmul1 (a b : LinPoints R C B) : a * b = (LinearMap.mul' R B).comp
  ((TensorProduct.map a b).comp (Coalgebra.comul)) := rfl

def linone : LinPoints R C B :=
  ((Algebra.ofId R B).toLinearMap.comp (Coalgebra.counit))
instance : One (LinPoints R C B) := ⟨linone R C B⟩

lemma linone' : linone R C B = (Algebra.ofId R B).toLinearMap.comp (Coalgebra.counit) := rfl

lemma onedef (h : H) : (Algebra.ofId R H) (Coalgebra.counit h) = (linone R H H) h := rfl

/- The proofs are all similar, first decompose then prove each small block commutes
  individually-/
lemma lblockcomm (ψ φ ρ : LinPoints R C B) :
  TensorProduct.map (ψ * φ) ρ = (TensorProduct.map
    (LinearMap.mul' R B) (LinearMap.id)).comp
    ((TensorProduct.map (TensorProduct.map ψ φ) ρ).comp
    (TensorProduct.map (Coalgebra.comul) (LinearMap.id))) := by
      symm ; rw [linmul1] ; ext x y ; simp

lemma rblockcomm (ψ φ ρ : LinPoints R C B) :
  TensorProduct.map ψ (φ * ρ) = (TensorProduct.map
  (LinearMap.id) (LinearMap.mul' R B)).comp
  ((TensorProduct.map ψ (TensorProduct.map φ ρ)).comp
  (TensorProduct.map (LinearMap.id) (Coalgebra.comul))) := by
  symm ; rw [linmul1] ; ext x y ; simp

/- We also have the linear version of tensor-associativity maps -/
abbrev l_assoc_b := (TensorProduct.assoc R B B B).toLinearMap
abbrev l_assoc_c := (TensorProduct.assoc R C C C).toLinearMap

lemma linCoassoc (x : C): (l_assoc_c R C) ((TensorProduct.map (R := R) (Coalgebra.comul)
  (LinearMap.id)).comp (Coalgebra.comul) x) =
  (TensorProduct.map (LinearMap.id) (Coalgebra.comul)).comp
  (Coalgebra.comul) x := by
  repeat rw [LinearMap.comp_apply] ; simp_all only [LinearEquiv.coe_coe]
  exact Coalgebra.coassoc_apply (R := R) (A := C) x

lemma linMapassoc' (ψ φ ρ : LinPoints R C B):
  (l_assoc_b R B).comp ((TensorProduct.map (TensorProduct.map ψ φ) ρ))
  = (TensorProduct.map ψ (TensorProduct.map φ ρ)).comp (l_assoc_c R C) := by
  ext x ; rfl

lemma linMapassoc (ψ φ ρ : LinPoints R C B) (ccc : (C ⊗[R] C) ⊗[R] C):
  (l_assoc_b R B) (((TensorProduct.map (TensorProduct.map ψ φ) ρ)) ccc)
  = (TensorProduct.map ψ (TensorProduct.map φ ρ)) ((l_assoc_c R C) ccc) := by
  apply LinearMap.ext_iff.1 (linMapassoc' R C B ψ φ ρ) ccc

lemma linten_assoc : (LinearMap.mul' R B).comp ((TensorProduct.map
  (LinearMap.mul' R B) (LinearMap.id))) =
  (LinearMap.mul' R B).comp ((TensorProduct.map (R := R) (LinearMap.id (M := B))
  (LinearMap.mul' R B)).comp (l_assoc_b R B)) := by
  ext x1 x2 x3
  simp only [TensorProduct.AlgebraTensorModule.curry_apply, TensorProduct.curry_apply,
    LinearMap.coe_restrictScalars, LinearMap.comp_apply, TensorProduct.map_tmul,
    LinearMap.mul'_apply, LinearMap.id_coe, id_eq, LinearEquiv.coe_coe, TensorProduct.assoc_tmul]
  rw [mul_assoc]

lemma linten_assoc_apply (bbb : (B ⊗[R] B) ⊗[R] B) : (LinearMap.mul' R B)
  ((TensorProduct.map (LinearMap.mul' R B) (LinearMap.id)) bbb) =
  (LinearMap.mul' R B) ((TensorProduct.map (LinearMap.id)
  (LinearMap.mul' R B)) ((l_assoc_b R B) bbb)) := by
  have := linten_assoc (R := R) (B := B)
  rw [DFunLike.ext_iff] at this ; apply this

/- Associativity law of R-linear maps under convolution product-/
lemma lin_assoc (ψ φ ρ : LinPoints R C B) : (ψ * φ) * ρ = ψ * (φ * ρ) := by
  rw [linmul1 R C B (ψ*φ) ρ, linmul1 R C B ψ (φ*ρ), lblockcomm, rblockcomm]
  ext x ; simp only [LinearMap.comp_apply]
  set ccc := ((TensorProduct.map Coalgebra.comul LinearMap.id)
    (Coalgebra.comul (R := R) x)) with ccc_eq
  have h0 : (l_assoc_c R C) ccc = ((TensorProduct.map LinearMap.id Coalgebra.comul)
    (Coalgebra.comul x)) := linCoassoc R C x
  rw [←h0] ; set bbb := (TensorProduct.map (TensorProduct.map ψ φ) ρ) ccc
  have h1 : (l_assoc_b R B) bbb = (TensorProduct.map ψ (TensorProduct.map φ ρ))
    ((l_assoc_c R C) ccc) := linMapassoc R C B ψ φ ρ ccc
  rw [←h1, linten_assoc_apply]

lemma linmul_one1 (ψ : LinPoints R C B): (TensorProduct.map ψ (linone R C B)) =
  (TensorProduct.map (LinearMap.id (M := B)) (Algebra.ofId R B).toLinearMap).comp
  ((TensorProduct.map ψ (LinearMap.id)).comp
  ((TensorProduct.map (LinearMap.id) (Coalgebra.counit (A := C))))) := by
  unfold linone ; ext c1 c2 ; simp

/- mul_one lemma for R-linear maps -/
lemma linmul_one (ψ : LinPoints R C B) : ψ * linone R C B = ψ := by
  rw [linmul1 , linmul_one1]
  ext x
  have := (Coalgebra.lTensor_counit_comul (R := R) (A := C)) x
  simp only [LinearMap.comp_apply]
  have h1 : (TensorProduct.map LinearMap.id Coalgebra.counit) (Coalgebra.comul x)
    = x ⊗ₜ[R] 1 := by exact this
  rw [h1] ; simp

lemma linone_mull1 (ψ : LinPoints R C B): (TensorProduct.map (linone R C B) ψ) =
  (TensorProduct.map (Algebra.ofId R B).toLinearMap LinearMap.id).comp
  ((TensorProduct.map LinearMap.id ψ).comp
  (TensorProduct.map (Coalgebra.counit (A := C)) LinearMap.id)):= by
  unfold linone ; ext c1 c2 ;simp

/- one_mul lemma for R-linear maps -/
lemma linone_mul (ψ : LinPoints R C B) : linone R C B * ψ = ψ := by
  rw [linmul1 , linone_mull1] ; ext x
  have counitac := Coalgebra.rTensor_counit_comul (R := R) (A := C) x
  simp only [LinearMap.comp_apply]
  have h1 : (TensorProduct.map Coalgebra.counit LinearMap.id) (Coalgebra.comul x)
    = 1 ⊗ₜ[R] x := by exact counitac
  rw [h1] ; simp

instance : Monoid (LinPoints R C B) where
  mul := linmul R C B
  mul_assoc := lin_assoc R C B
  one := linone R C B
  one_mul := linone_mul R C B
  mul_one := linmul_one R C B

instance : Monoid (LinPoints R H H) := inferInstance
--End of Part II

-- Part III is some preparation for the final big theorem (Hom(H, A) forms a group) which is
-- mainly proving tensor product of R-Bialgebras is still a R-Bialgebra.

lemma repr (x : C) (ι : Type*) (I : Finset ι) (x1 x2 : ι → C)
  (h : Coalgebra.comul x = ∑ i in I, x1 i ⊗ₜ[R] x2 i)
  (f g: LinPoints R C B) : (f * g) x =  ∑ i in I, f (x1 i) * g (x2 i) := by
  rw [linmul1]
  simp only [LinearMap.comp_apply] ; symm ; rw [h]
  simp only [map_sum, TensorProduct.map_tmul, LinearMap.mul'_apply]

/-This is the sweedler notation of comultiplication, which is writing
  Δ x = ∑ i , x1 i ⊗ x2 i where Δ is comul of C -/
lemma comul_repr (x : C) : ∃ (I : Finset (C ⊗[R] C)) (x1 : C ⊗[R] C → C) (x2 : C ⊗[R] C → C),
  Coalgebra.comul (R := R) x = ∑ i in I, x1 i ⊗ₜ[R] x2 i := by
  -- make if ... then ... else work
  classical
  set cc := Coalgebra.comul (R := R) x with cc_eq
  have mem1 : cc ∈ (⊤ : Submodule R (C ⊗[R] C)) := ⟨⟩
  -- Use the fact that tensorproduct space is spanned by pure tensors
  rw [← TensorProduct.span_tmul_eq_top, mem_span_set] at mem1
  obtain ⟨r, hr, (eq1 : ∑ i in r.support, (_ • _) = _)⟩ := mem1
  choose a a' haa' using hr
  replace eq1 := calc _
    cc = ∑ i in r.support, r i • i := eq1.symm
    _ = ∑ i in r.support.attach, (r i : R) • (i : (C ⊗[R] C))
      := Finset.sum_attach _ _ |>.symm
    _ = ∑ i in r.support.attach, (r i • a i.2 ⊗ₜ[R] a' i.2) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [haa' i.2]
    _ = ∑ i in r.support.attach, ((r i • a i.2) ⊗ₜ[R] a' i.2) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [TensorProduct.smul_tmul']
  use r.support
  use fun i => if h : i ∈ r.support then r i • a h else 0
  use fun i => if h : i ∈ r.support then a' h else 0
  rw [eq1] ; conv_rhs => rw [← Finset.sum_attach]
  refine Finset.sum_congr rfl fun _ _ ↦ (by split_ifs with h <;> aesop)

-- This is used to define the Comul of A1 ⊗[R] A2
def Bialg_tensorequiv : (A1 ⊗[R] A1) ⊗[R] (A2 ⊗[R] A2) →ₗ[R] (A1 ⊗[R] A2) ⊗[R] (A1 ⊗[R] A2) :=
 (TensorProduct.assoc _ _ _ _).toLinearMap ∘ₗ
 LinearMap.rTensor A2
 ((TensorProduct.assoc _ _ _ _).symm.toLinearMap ∘ₗ
  LinearMap.lTensor A1 (TensorProduct.comm _ _ _).toLinearMap ∘ₗ
  (TensorProduct.assoc _ _ _ _).toLinearMap) ∘ₗ
 (TensorProduct.assoc _ _ _ _).symm.toLinearMap

-- Define the linear equivalence of (A1 ⊗[R] A1) ⊗[R] (A2 ⊗[R] A2) and
-- (A1 ⊗[R] A2) ⊗[R] (A1 ⊗[R] A2)
private noncomputable def reorder4 : (A1 ⊗[R] A1) ⊗[R] A2 ⊗[R] A2 ≃ₗ[R]
  (A1 ⊗[R] A2) ⊗[R] A1 ⊗[R] A2 :=
  LinearEquiv.ofLinear
    ((TensorProduct.assoc R A1 A2 (A1 ⊗[R] A2)).symm.toLinearMap ∘ₗ
      (TensorProduct.assoc R A2 A1 A2).toLinearMap.lTensor A1 ∘ₗ
      ((TensorProduct.comm R A1 A2).rTensor A2).lTensor A1 ∘ₗ
      (TensorProduct.assoc R A1 A2 A2).symm.toLinearMap.lTensor A1 ∘ₗ
      (TensorProduct.assoc R A1 A1 (A2 ⊗[R] A2)).toLinearMap)
    ((TensorProduct.assoc R A1 A1 (A2 ⊗[R] A2)).symm.toLinearMap ∘ₗ
      (TensorProduct.assoc R A1 A2 A2).toLinearMap.lTensor A1 ∘ₗ
      ((TensorProduct.comm R A2 A1).rTensor A2).lTensor A1 ∘ₗ
      (TensorProduct.assoc R A2 A1 A2).symm.toLinearMap.lTensor A1 ∘ₗ
      (TensorProduct.assoc R A1 A2 (A1 ⊗[R] A2)).toLinearMap)
    (by aesop) (by aesop)

-- Define the linear equivalence of  (A1 ⊗[R] A2) ⊗[R] (A1 ⊗[R] A2) ⊗[R] A1 ⊗[R] A2
-- and (A1 ⊗[R] A1 ⊗[R] A1) ⊗[R] A2 ⊗[R] A2 ⊗[R] A2
private noncomputable def reorder6 :
  (A1 ⊗[R] A2) ⊗[R] (A1 ⊗[R] A2) ⊗[R] A1 ⊗[R] A2 ≃ₗ[R]
  (A1 ⊗[R] A1 ⊗[R] A1) ⊗[R] A2 ⊗[R] A2 ⊗[R] A2 :=
  LinearEquiv.ofLinear
    ((TensorProduct.assoc _ _ _ _).toLinearMap ∘ₗ
      (TensorProduct.assoc _ _ _ _).toLinearMap ∘ₗ
      (((TensorProduct.assoc _ _ _ _).toLinearMap.rTensor A2).rTensor A2 ∘ₗ
        (TensorProduct.assoc _ _ _ _).symm.toLinearMap ∘ₗ
        (TensorProduct.assoc _ _ _ _).symm.toLinearMap ∘ₗ
        (TensorProduct.assoc _ _ _ _).symm.toLinearMap ∘ₗ
        (((TensorProduct.comm R (A2 ⊗[R] A2) A1).lTensor A1).lTensor A1) ∘ₗ
        (TensorProduct.assoc _ _ _ _).toLinearMap ∘ₗ
        (TensorProduct.assoc _ _ _ _).toLinearMap).rTensor A2 ∘ₗ
     (TensorProduct.assoc _ _ _ _).symm.toLinearMap ∘ₗ
     ((reorder4 R A1 A2).symm.rTensor (A1 ⊗[R] A2)) ∘ₗ
     (TensorProduct.assoc _ _ _ _).symm.toLinearMap)
    ((TensorProduct.assoc _ _ _ _).toLinearMap ∘ₗ
      ((reorder4 R A1 A2).rTensor (A1 ⊗[R] A2)) ∘ₗ
      (TensorProduct.assoc _ _ _ _).toLinearMap ∘ₗ
      LinearMap.rTensor A2
      ((TensorProduct.assoc _ _ _ _).symm.toLinearMap ∘ₗ
        (TensorProduct.assoc _ _ _ _).symm.toLinearMap ∘ₗ
        ((TensorProduct.comm R A1 (A2 ⊗[R] A2)).lTensor A1).lTensor A1 ∘ₗ
        (TensorProduct.assoc _ _ _ _).toLinearMap ∘ₗ
        (TensorProduct.assoc _ _ _ _).toLinearMap ∘ₗ
        (TensorProduct.assoc _ _ _ _).toLinearMap ∘ₗ
        ((TensorProduct.assoc _ _ _ _).symm.toLinearMap.rTensor A2).rTensor A2) ∘ₗ
      (TensorProduct.assoc _ _ _ _).symm.toLinearMap ∘ₗ
      (TensorProduct.assoc _ _ _ _).symm.toLinearMap)
 (by aesop) (by aesop)

-- How reorder acts elementwise
lemma reorder6_tmul (a1 a2 a3 : A1) (b1 b2 b3 : A2) :
  reorder6 R A1 A2 ((a1 ⊗ₜ[R] b1) ⊗ₜ[R] (a2 ⊗ₜ[R] b2) ⊗ₜ[R] (a3 ⊗ₜ[R] b3)) =
  (a1 ⊗ₜ[R] a2 ⊗ₜ[R] a3) ⊗ₜ[R] (b1 ⊗ₜ[R] b2 ⊗ₜ[R] b3) := rfl

-- Since comul is not allowed before proving that A1 ⊗[R] A2 is a bialgebra,
-- in order to fasten the speed, we had to define the comul map manually.
abbrev tcomul := (Bialg_tensorequiv R A1 A2).comp
  (TensorProduct.map (M := A1) (N := A2) (Bialgebra.comulAlgHom R (A := A1))
  (Bialgebra.comulAlgHom R (A := A2)))

lemma tcomul_eq : tcomul R A1 A2 =
  (Bialg_tensorequiv R A1 A2).comp
  (TensorProduct.map (M := A1) (N := A2) (Coalgebra.comul (R := R) (A := A1))
  (Coalgebra.comul (R := R) (A := A2))) := rfl

-- How tcomul acts elementwise
lemma tcomul_tmul (x : A1) (y : A2) :
  tcomul R A1 A2 (x ⊗ₜ y) = Bialg_tensorequiv R A1 A2
    (Coalgebra.comul x ⊗ₜ Coalgebra.comul y) := rfl

/- Same as comul_repr, we wrote our own sweedler notation for comul of A1 ⊗[R] A2 -/
lemma tcomul_repr (x : A1) (y : A2) {ι1 ι2 : Type*} (s1 : Finset ι1) (s2 : Finset ι2)
    (a1 a2 : ι1 → A1) (b1 b2 : ι2 → A2)
    (eq1 : Coalgebra.comul (R := R) x = ∑ i in s1, a1 i ⊗ₜ a2 i)
    (eq2 : Coalgebra.comul (R := R) y = ∑ i in s2, b1 i ⊗ₜ b2 i) :
    tcomul R A1 A2 (x ⊗ₜ y) =
    ∑ i in s1, ∑ j in s2, (a1 i ⊗ₜ b1 j) ⊗ₜ (a2 i ⊗ₜ b2 j) := by
      rw [tcomul_eq]
      simp only [LinearMap.coe_comp, comp_apply, TensorProduct.map_tmul, eq1, eq2,
        TensorProduct.tmul_sum, TensorProduct.sum_tmul, map_sum, Bialg_tensorequiv,
        TensorProduct.assoc_symm_tmul, LinearMap.rTensor_tmul, LinearEquiv.coe_coe,
        TensorProduct.assoc_tmul, LinearMap.lTensor_tmul, TensorProduct.comm_tmul]
      rw [Finset.sum_comm]


lemma Equiv_apply (x1 x1' : A1) (x2 x2' : A2) : Bialg_tensorequiv R A1 A2
  ((x1 ⊗ₜ[R] x1') ⊗ₜ[R] (x2 ⊗ₜ[R] x2')) = (x1 ⊗ₜ[R] x2) ⊗ₜ[R] (x1' ⊗ₜ[R] x2') := by
  simp [Bialg_tensorequiv]

/- As te introduction of this axiom of Bialgebra says, this is a weird way that lean uses to
  check the "map_mul" property of comul of (A1 ⊗ A2) by checking two bilinear maps are the
  same-/
lemma mul_comp₂_tencomul : LinearMap.compr₂ (LinearMap.mul R (A1 ⊗[R] A2)) (tcomul R A1 A2) =
  LinearMap.compl₁₂ (LinearMap.mul R ((A1 ⊗[R] A2) ⊗[R] A1 ⊗[R] A2))
  (tcomul R A1 A2) (tcomul R A1 A2) := by
  ext x1 x2 x1' x2' ; simp only [tcomul, AlgHom.toNonUnitalAlgHom_eq_coe,
    NonUnitalAlgHom.toDistribMulActionHom_eq_coe, TensorProduct.AlgebraTensorModule.curry_apply,
    TensorProduct.curry_apply, LinearMap.coe_restrictScalars, LinearMap.compr₂_apply,
    LinearMap.mul_apply', Algebra.TensorProduct.tmul_mul_tmul, LinearMap.coe_comp, comp_apply,
    TensorProduct.map_tmul, DistribMulActionHom.coe_toLinearMap,
    NonUnitalAlgHom.coe_to_distribMulActionHom, map_mul, NonUnitalAlgHom.coe_coe,
    Bialgebra.comulAlgHom_apply, LinearMap.compl₁₂_apply]
  obtain ⟨I1, x11, x12, h1⟩ := comul_repr R A1 x1
  obtain ⟨I1', x11', x12', h1'⟩ := comul_repr R A1 x1'
  obtain ⟨I2, x21, x22, h2⟩ := comul_repr R A2 x2
  obtain ⟨I2', x21', x22', h2'⟩ := comul_repr R A2 x2'
  rw [h1, h1', h2, h2', Finset.sum_mul_sum, Finset.sum_mul_sum]
  simp_rw [Algebra.TensorProduct.tmul_mul_tmul]
  rw [TensorProduct.sum_tmul, TensorProduct.sum_tmul, TensorProduct.sum_tmul]
  simp_rw [TensorProduct.tmul_sum]; simp_rw [TensorProduct.sum_tmul]
  simp_rw [map_sum, Equiv_apply R A1 A2] ; rw [Finset.sum_mul_sum]
  simp_rw [Finset.sum_mul_sum, Algebra.TensorProduct.tmul_mul_tmul]
  refine Finset.sum_congr rfl fun i1 hi1 ↦ ?_
  symm ; rw [Finset.sum_comm] ; refine Finset.sum_congr rfl fun _ _ ↦ Finset.sum_comm

/- Again, since counit of A1 ⊗ A2 can't be used, we use ten_counit just for convenience -/
abbrev ten_counit: A1 ⊗[R] A2 →ₐ[R] R := (Algebra.TensorProduct.lmul' R (S := R)).comp
  (Algebra.TensorProduct.map (Bialgebra.counitAlgHom R A1) (Bialgebra.counitAlgHom R A2))

-- The following three lemmas are the lemmas designed to help prove
-- "lTensor_counit_comp_comul" axiom of Bialgebra.

/- This is saying a * one(b) = ε(b) • a -/
lemma one_eq (a b : A1) : a * (Algebra.ofId R A1)
  (Coalgebra.counit (R := R) (A := A1) (b)) =
  Coalgebra.counit (R := R) (A := A1) (b) • a := by
  rw [← mul_one (Coalgebra.counit (R := R) (A := A1) (b)), ← Algebra.id.smul_eq_mul, map_smul,
    map_one, Algebra.mul_smul_comm, mul_one, smul_eq_mul, mul_one]

/- This lemma is one side of the sweedler notation of x which is:
  x = ∑ i ε(x2 i) • x1 i -/
lemma tensorId_eq (I1: Finset (A1 ⊗[R] A1)) (x1 x2 : A1 ⊗[R] A1 → A1) (x : A1)
  (hx: Coalgebra.comul x = ∑ i in I1, x1 i ⊗ₜ[R] x2 i):
  ∑ i in I1, (Coalgebra.counit (R := R) (A := A1) (x2 i)) • x1 i = x := by
  symm ; calc _
    x = (LinearMap.id (R := R) (M := A1)) x := rfl
    _ = ((LinearMap.id (R := R) (M := A1)) * linone R A1 A1) x := by rw [linmul_one]
    _ = (LinearMap.mul' R A1) ((TensorProduct.map
      (LinearMap.id (R := R) (M := A1)) (linone R A1 A1)) (Coalgebra.comul x)) := by
        rw [linmul1] ; simp only [LinearMap.comp_apply]
  rw [hx, linone'] ; simp only [map_sum, TensorProduct.map_tmul, LinearMap.id_coe, id_eq,
    LinearMap.comp_apply, AlgHom.toLinearMap_apply, LinearMap.mul'_apply]
  simp_rw [one_eq]

/- This is just one of the sub-result I need for lTensor, I copied this from the goal -/
lemma swap_equiv (I2: Finset (A2 ⊗[R] A2)) (I1: Finset (A1 ⊗[R] A1)) (x1 x2 : A1 ⊗[R] A1 → A1)
  (y1 y2 : A2 ⊗[R] A2 → A2) (x : A1) (y : A2) (hy: Coalgebra.comul y = ∑ i in I2, y1 i ⊗ₜ[R] y2 i)
  (hx: Coalgebra.comul x = ∑ i in I1, x1 i ⊗ₜ[R] x2 i):
  ∑ x in I2, ∑ x_1 in I1, (((Coalgebra.counit (R := R) (A := A1) (x2 x_1)) *
  (Coalgebra.counit (R := R) (A := A2) (y2 x))) • x1 x_1) ⊗ₜ[R] y1 x ⊗ₜ[R] (1 : R) =
    x ⊗ₜ[R] y ⊗ₜ[R] 1 := by
      have : ∑ x in I2, ∑ x_1 in I1, (((Coalgebra.counit (R := R) (A := A1) (x2 x_1)) *
      (Coalgebra.counit (R := R) (A := A2) (y2 x))) • x1 x_1) ⊗ₜ[R] y1 x ⊗ₜ[R] (1 : R) =
      ∑ x in I2, ∑ x_1 in I1, (((Coalgebra.counit (R := R) (A := A2) (y2 x)) *
      (Coalgebra.counit (R := R) (A := A1) (x2 x_1))) • x1 x_1) ⊗ₜ[R] y1 x ⊗ₜ[R] (1 : R) := by
        apply Finset.sum_congr rfl ; intro x hx
        apply Finset.sum_congr rfl ; intro x_1 hx_1
        rw [mul_comm]
      rw [this] ; simp_rw [← smul_smul, ← TensorProduct.sum_tmul, ← Finset.smul_sum]
      rw [tensorId_eq R A1 I1 x1 x2 x hx]; simp_rw [TensorProduct.smul_tmul]
      simp_rw [TensorProduct.smul_tmul', ← TensorProduct.tmul_sum, ← TensorProduct.sum_tmul]
      rw [tensorId_eq R A2 I2 y1 y2 y hy]

/- This is one of the axioms of Bialgebra : (id ⊗ ε) ∘ Δ = id ⊗ (1 : R) where ε is the
  counit of A1 ⊗ A2 -/
lemma lTensor_tensor : LinearMap.lTensor (A1 ⊗[R] A2) (ten_counit R A1 A2) ∘ₗ (tcomul R A1 A2) =
  (LinearMap.flip (TensorProduct.mk R (A1 ⊗[R] A2) R)) 1 := by
  ext x y ; simp only [ten_counit, tcomul, Bialg_tensorequiv,AlgHom.toNonUnitalAlgHom_eq_coe,
    NonUnitalAlgHom.toDistribMulActionHom_eq_coe, TensorProduct.AlgebraTensorModule.curry_apply,
    TensorProduct.curry_apply, LinearMap.coe_restrictScalars, LinearMap.coe_comp,
    LinearEquiv.coe_coe, comp_apply, TensorProduct.map_tmul, DistribMulActionHom.coe_toLinearMap,
    NonUnitalAlgHom.coe_to_distribMulActionHom, NonUnitalAlgHom.coe_coe,
    Bialgebra.comulAlgHom_apply, LinearMap.flip_apply, TensorProduct.mk_apply]
  obtain ⟨I1, x1, x2, hx⟩ := comul_repr R A1 x
  obtain ⟨I2, y1, y2, hy⟩ := comul_repr R A2 y ; rw [hx, hy]
  rw [TensorProduct.tmul_sum] ; simp_rw [TensorProduct.sum_tmul]
  simp only [map_sum, TensorProduct.assoc_symm_tmul, LinearMap.rTensor_tmul, LinearMap.coe_comp,
    LinearEquiv.coe_coe, comp_apply, TensorProduct.assoc_tmul, LinearMap.lTensor_tmul,
    TensorProduct.comm_tmul, DistribMulActionHom.coe_toLinearMap,
    NonUnitalAlgHom.coe_to_distribMulActionHom, NonUnitalAlgHom.coe_coe, AlgHom.coe_comp,
    Algebra.TensorProduct.map_tmul, Bialgebra.counitAlgHom_apply,
    Algebra.TensorProduct.lmul'_apply_tmul]
  simp_rw [← TensorProduct.assoc_symm_tmul, ← map_sum, ← Algebra.id.smul_eq_mul,
    TensorProduct.tmul_smul]
  calc _
    (LinearEquiv.symm (TensorProduct.assoc R A1 A2 R)) (∑ x in I2, ∑ x_1 in I1,
    (Coalgebra.counit (R := R) (A := A1) (x2 x_1)) • x1 x_1 ⊗ₜ[R] y1 x ⊗ₜ[R]
    (Coalgebra.counit (R := R) (A := A2) (y2 x))) =
    (LinearEquiv.symm (TensorProduct.assoc R A1 A2 R)) (∑ x in I2, ∑ x_1 in I1,
    (Coalgebra.counit (R := R) (A := A1) (x2 x_1)) • x1 x_1 ⊗ₜ[R] y1 x ⊗ₜ[R]
    (Coalgebra.counit (y2 x) * (1 : R))) := by simp only [mul_one]
  simp_rw [← Algebra.id.smul_eq_mul, TensorProduct.tmul_smul, TensorProduct.smul_tmul', smul_smul]
  rw [swap_equiv R A1 A2 I2 I1 x1 x2 y1 y2 x y hy hx]

-- The following two lemmas are designed to help improve my proof of "rTensor_counit_comp_comul"
/- This is saying one(a) * b = ε(a) • b -/
lemma eq_one (a b : A1) :
  (Algebra.ofId R A1) (Coalgebra.counit (R := R) (A := A1) (a)) * b =
  (Coalgebra.counit (R := R) (A := A1) (a)) • b := by
  rw [← mul_one (Coalgebra.counit (R := R) (A := A1) (a)), ← Algebra.id.smul_eq_mul, map_smul,
    map_one, Algebra.smul_mul_assoc, one_mul, smul_eq_mul, mul_one]

/- This lemma shows another side of the sweedler notation of x which is:
  x = ∑ i ε(x1 i) • x2 i -/
lemma tensorEq_id (I1 : Finset (A1 ⊗[R] A1)) (x1 x2 : A1 ⊗[R] A1 → A1) (x : A1)
  (hx: Coalgebra.comul x = ∑ i in I1, x1 i ⊗ₜ[R] x2 i):
  ∑ a in I1, (Coalgebra.counit (R := R) (A := A1) (x1 a)) • x2 a = x := by
  symm ; calc _
    x = (LinearMap.id (R := R) (M := A1)) x := rfl
    _ = ((linone R A1 A1) * (LinearMap.id (R := R) (M := A1))) x := by rw [linone_mul]
    _ = (LinearMap.mul' R A1) ((TensorProduct.map
      (linone R A1 A1) (LinearMap.id (R := R) (M := A1))) (Coalgebra.comul x)) := by
        rw [linmul1] ; simp only [LinearMap.comp_apply]
  rw [hx, linone'] ; simp only [map_sum, TensorProduct.map_tmul, LinearMap.coe_comp, comp_apply,
    AlgHom.toLinearMap_apply, LinearMap.id_coe, id_eq, LinearMap.mul'_apply]
  simp_rw [eq_one R A1]

/- Again, this is another axiom of Bialgebra which is just a opposite direction of
  lTensor : (ε ⊗ id) ∘ Δ = (1 : R) ⊗ id -/
lemma rTensor_tensor : LinearMap.rTensor (A1 ⊗[R] A2)
  (ten_counit R A1 A2) ∘ₗ (tcomul R A1 A2) =
  (TensorProduct.mk R R (A1 ⊗[R] A2)) 1 := by
  ext x y ; unfold ten_counit ; unfold tcomul ; unfold Bialg_tensorequiv
  simp only [AlgHom.toNonUnitalAlgHom_eq_coe, NonUnitalAlgHom.toDistribMulActionHom_eq_coe,
    TensorProduct.AlgebraTensorModule.curry_apply, TensorProduct.curry_apply,
    LinearMap.coe_restrictScalars, LinearMap.coe_comp, LinearEquiv.coe_coe, comp_apply,
    TensorProduct.map_tmul, DistribMulActionHom.coe_toLinearMap,
    NonUnitalAlgHom.coe_to_distribMulActionHom, NonUnitalAlgHom.coe_coe,
    Bialgebra.comulAlgHom_apply, TensorProduct.mk_apply]
  obtain ⟨I1, x1, x2, hx⟩ := comul_repr R A1 x
  obtain ⟨I2, y1, y2, hy⟩ := comul_repr R A2 y ; rw [hx, hy]
  rw [TensorProduct.tmul_sum] ; simp_rw [TensorProduct.sum_tmul]
  simp only [map_sum, TensorProduct.assoc_symm_tmul, LinearMap.rTensor_tmul, LinearMap.coe_comp,
    LinearEquiv.coe_coe, comp_apply, TensorProduct.assoc_tmul, LinearMap.lTensor_tmul,
    TensorProduct.comm_tmul, DistribMulActionHom.coe_toLinearMap,
    NonUnitalAlgHom.coe_to_distribMulActionHom, NonUnitalAlgHom.coe_coe, AlgHom.coe_comp,
    Algebra.TensorProduct.map_tmul, Bialgebra.counitAlgHom_apply,
    Algebra.TensorProduct.lmul'_apply_tmul]
  simp_rw [← Algebra.id.smul_eq_mul, TensorProduct.smul_tmul, TensorProduct.smul_tmul']
  simp_rw [← TensorProduct.tmul_sum, ← TensorProduct.sum_tmul]
  rw [tensorEq_id R A1 I1 x1 x2 x hx]
  calc _
    ∑ x_1 in I2, (Coalgebra.counit (R := R) (A := A2) (y1 x_1)) ⊗ₜ[R] x ⊗ₜ[R] y2 x_1 =
    ∑ x_1 in I2, ((Coalgebra.counit (R := R) (A := A2) (y1 x_1)) *
      (1 : R)) ⊗ₜ[R] x ⊗ₜ[R] y2 x_1 := by simp only [mul_one]
  simp_rw [← Algebra.id.smul_eq_mul, TensorProduct.smul_tmul, TensorProduct.smul_tmul']
  simp_rw [← TensorProduct.tmul_sum, TensorProduct.smul_tmul, ← TensorProduct.tmul_sum]
  rw [tensorEq_id R A2 I2 y1 y2 y hy]

open TensorProduct in

/- This is the coassoc axiom for Bialgebra(I probably should put a Coalgebra instance
  first because the proof of this is really complicated...) Jujiang helped a lot with
  this proof :)) -/

set_option tactic.skipAssignedInstances false
lemma tensor_coassoc : ↑(TensorProduct.assoc R (A1 ⊗[R] A2) (A1 ⊗[R] A2) (A1 ⊗[R] A2)) ∘ₗ
    LinearMap.rTensor (A1 ⊗[R] A2) (tcomul R A1 A2) ∘ₗ (tcomul R A1 A2) =
    LinearMap.lTensor (A1 ⊗[R] A2) (tcomul R A1 A2) ∘ₗ (tcomul R A1 A2) := by
  set LL := _; set RR := _; change LL = RR -- LL and RR are left and right hand side repectively

  -- This is using the property that reorder6 is a linear equivalence (actually injective would
  -- probably be enough ...?)
  suffices (reorder6 R A1 A2).toLinearMap ∘ₗ LL = (reorder6 R A1 A2).toLinearMap ∘ₗ RR by
    rw [← LinearEquiv.toLinearMap_symm_comp_eq, ← LinearMap.comp_assoc] at this
    simp [← this]

  -- This is just the tensor product of the coassoc property of each of A1 and A2
  -- (Tensor product of the equation)
  have EQ := congr_arg₂ TensorProduct.map
    (Coalgebra.coassoc (R := R) (A := A1)) (Coalgebra.coassoc (R := R) (A := A2))

  -- Again, setting LLEQ and RREQ to be the left and right hand side of EQ
  set LLEQ := _; set RREQ := _; change LLEQ = RREQ at EQ

  -- The proof is done by proving the left and right hand side of the goal is in fact
  -- the left and right hand side of EQ (tensor product of individual coassocs)
  have eq1 : LLEQ = (reorder6 R A1 A2).toLinearMap ∘ₗ LL
  -- Proving left hand side equality
  · ext x y
    obtain ⟨I1, x1, x2, hx⟩ := comul_repr R A1 x
    obtain ⟨I2, y1, y2, hy⟩ := comul_repr R A2 y
    simp (config :=
      { zetaDelta := true, zeta := false }) only [TensorProduct.AlgebraTensorModule.curry_apply,
      TensorProduct.curry_apply, LinearMap.coe_restrictScalars, TensorProduct.map_tmul,
      LinearMap.coe_comp, LinearEquiv.coe_coe, comp_apply, hx, map_sum, LinearMap.rTensor_tmul, hy,
      TensorProduct.tmul_sum, TensorProduct.sum_tmul, AlgHom.toNonUnitalAlgHom_eq_coe,
      NonUnitalAlgHom.toDistribMulActionHom_eq_coe, DistribMulActionHom.coe_toLinearMap,
      NonUnitalAlgHom.coe_to_distribMulActionHom, NonUnitalAlgHom.coe_coe,
      Bialgebra.comulAlgHom_apply]
    -- [TensorProduct.curry_apply,
    --   LinearMap.coe_restrictScalars, map_tmul, LinearMap.coe_comp, LinearEquiv.coe_coe, comp_apply,
    --   hx, map_sum, LinearMap.rTensor_tmul, hy, tmul_sum, sum_tmul, AlgHom.toNonUnitalAlgHom_eq_coe,
    --   NonUnitalAlgHom.toDistribMulActionHom_eq_coe, DistribMulActionHom.coe_toLinearMap,
    --   NonUnitalAlgHom.coe_to_distribMulActionHom, NonUnitalAlgHom.coe_coe,
    --   Bialgebra.comulAlgHom_apply, Bialg_tensorequiv, assoc_symm_tmul, assoc_tmul,
    --   LinearMap.lTensor_tmul, comm_tmul]
    refine Finset.sum_congr rfl fun i1 hi1 ↦ Finset.sum_congr rfl fun i2 hi2 ↦ ?_
    obtain ⟨I, x11, x12, hx1⟩ := comul_repr R A1 (x1 i2)
    obtain ⟨J, y11, y12, hy1⟩ := comul_repr R A2 (y1 i1)
    simp only [hx1, TensorProduct.sum_tmul, map_sum, TensorProduct.assoc_tmul, hy1,
      TensorProduct.tmul_sum, Bialg_tensorequiv, LinearMap.coe_comp, LinearEquiv.coe_coe,
      comp_apply, TensorProduct.assoc_symm_tmul, LinearMap.rTensor_tmul, LinearMap.lTensor_tmul,
      TensorProduct.comm_tmul, AlgHom.toNonUnitalAlgHom_eq_coe,
      NonUnitalAlgHom.toDistribMulActionHom_eq_coe, TensorProduct.map_tmul,
      DistribMulActionHom.coe_toLinearMap, NonUnitalAlgHom.coe_to_distribMulActionHom,
      NonUnitalAlgHom.coe_coe, Bialgebra.comulAlgHom_apply, reorder6_tmul,
      NonUnitalAlgHom.toDistribMulActionHom_eq_coe, TensorProduct.map_tmul,
      DistribMulActionHom.coe_toLinearMap, NonUnitalAlgHom.coe_to_distribMulActionHom,
      NonUnitalAlgHom.coe_coe, Bialgebra.comulAlgHom_apply, reorder6_tmul]

  have eq2 : RREQ = (reorder6 R A1 A2).toLinearMap ∘ₗ RR
  -- Proving right hand side equality
  · ext x y
    obtain ⟨I1, x1, x2, hx⟩ := comul_repr R A1 x
    obtain ⟨I2, y1, y2, hy⟩ := comul_repr R A2 y
    simp (config :=
      { zetaDelta := true, zeta := false }) only [TensorProduct.AlgebraTensorModule.curry_apply,
      TensorProduct.curry_apply, LinearMap.coe_restrictScalars, TensorProduct.map_tmul,
      LinearMap.coe_comp, comp_apply, hx, map_sum, LinearMap.lTensor_tmul, hy,
      TensorProduct.tmul_sum, TensorProduct.sum_tmul, LinearEquiv.coe_coe, Bialg_tensorequiv,
      AlgHom.toNonUnitalAlgHom_eq_coe, NonUnitalAlgHom.toDistribMulActionHom_eq_coe,
      DistribMulActionHom.coe_toLinearMap, NonUnitalAlgHom.coe_to_distribMulActionHom,
      NonUnitalAlgHom.coe_coe, Bialgebra.comulAlgHom_apply, TensorProduct.assoc_symm_tmul,
      LinearMap.rTensor_tmul, TensorProduct.assoc_tmul, TensorProduct.comm_tmul]
    -- [AlgebraTensorModule.curry_apply, TensorProduct.curry_apply,
    --   LinearMap.coe_restrictScalars, map_tmul, LinearMap.coe_comp, LinearEquiv.coe_coe, comp_apply,
    --   hx, map_sum, LinearMap.rTensor_tmul, hy, tmul_sum, sum_tmul, AlgHom.toNonUnitalAlgHom_eq_coe,
    --   NonUnitalAlgHom.toDistribMulActionHom_eq_coe, DistribMulActionHom.coe_toLinearMap,
    --   NonUnitalAlgHom.coe_to_distribMulActionHom, NonUnitalAlgHom.coe_coe,
    --   Bialgebra.comulAlgHom_apply, Bialg_tensorequiv, assoc_symm_tmul, assoc_tmul,
    --   LinearMap.lTensor_tmul, comm_tmul]
    refine Finset.sum_congr rfl fun i1 hi1 ↦ Finset.sum_congr rfl fun i2 hi2 ↦ ?_
    obtain ⟨I, x11, x12, hx1⟩ := comul_repr R A1 (x2 i2)
    obtain ⟨J, y11, y12, hy1⟩ := comul_repr R A2 (y2 i1)
    simp only [hx1, TensorProduct.sum_tmul, map_sum, TensorProduct.assoc_tmul, hy1, 
      TensorProduct.tmul_sum, TensorProduct.assoc_symm_tmul,
      LinearMap.rTensor_tmul, LinearMap.coe_comp, LinearEquiv.coe_coe, comp_apply,
      LinearMap.lTensor_tmul, TensorProduct.comm_tmul, reorder6_tmul]

  rw [← eq1, ← eq2, EQ]

/- Big Thoerem! Tensor product of Bialgebra is indeed a Bialgebra! -/
instance : Bialgebra R (A1 ⊗[R] A2) where
  comul := tcomul R A1 A2
  counit := ten_counit R A1 A2
  coassoc := tensor_coassoc R A1 A2
  rTensor_counit_comp_comul := rTensor_tensor R A1 A2
  lTensor_counit_comp_comul := lTensor_tensor R A1 A2
  -- this shows ε(1) = (1 : R) for 1 ∈ A1 ⊗ A2
  counit_one := by simp only [AlgHom.toNonUnitalAlgHom_eq_coe,
    NonUnitalAlgHom.toDistribMulActionHom_eq_coe, DistribMulActionHom.coe_toLinearMap,
    NonUnitalAlgHom.coe_to_distribMulActionHom, NonUnitalAlgHom.coe_coe, map_one]
  -- showing counit is indeed an algebra homomorphism ε(ab) = ε(a) * ε(b)
  mul_compr₂_counit := by
    simp only [AlgHom.toNonUnitalAlgHom_eq_coe,
    NonUnitalAlgHom.toDistribMulActionHom_eq_coe]
    ext x1 x2 x1' x2'
    simp only [TensorProduct.AlgebraTensorModule.curry_apply, TensorProduct.curry_apply,
      LinearMap.coe_restrictScalars, LinearMap.compr₂_apply, LinearMap.mul_apply',
      Algebra.TensorProduct.tmul_mul_tmul, DistribMulActionHom.coe_toLinearMap,
      NonUnitalAlgHom.coe_to_distribMulActionHom, NonUnitalAlgHom.coe_coe, AlgHom.comp_apply,
      Algebra.TensorProduct.map_tmul, map_mul, Bialgebra.counitAlgHom_apply,
      Algebra.TensorProduct.lmul'_apply_tmul, LinearMap.compl₁₂_apply]
    rw [← mul_assoc, ← mul_assoc]; congr 1;
    rw [mul_assoc, mul_assoc, mul_comm]
    symm; rw [mul_comm] ; congr 1; rw [mul_comm]
  -- This shows Δ (1 : A1 ⊗ A2) = (1 : (A1 ⊗ A2) ⊗ (A1 ⊗ A2))
  comul_one := by
    rw [show (1 : A1 ⊗[R] A2) = (1 ⊗ₜ[R] 1) by rfl]
    rw [show (1 : (A1 ⊗[R] A2) ⊗[R] A1 ⊗[R] A2) = (1 ⊗ₜ[R] 1) ⊗ₜ[R] (1 ⊗ₜ[R] 1) by rfl]
    simp only [AlgHom.toNonUnitalAlgHom_eq_coe, NonUnitalAlgHom.toDistribMulActionHom_eq_coe,
      LinearMap.comp_apply, TensorProduct.map_tmul, DistribMulActionHom.coe_toLinearMap,
      NonUnitalAlgHom.coe_to_distribMulActionHom, NonUnitalAlgHom.coe_coe, map_one]
    rw [show (1 : A1 ⊗[R] A1) = (1 ⊗ₜ[R] 1) by rfl]
    rw [show (1 : A2 ⊗[R] A2) = (1 ⊗ₜ[R] 1) by rfl]; unfold Bialg_tensorequiv
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, comp_apply, TensorProduct.assoc_symm_tmul,
      LinearMap.rTensor_tmul, TensorProduct.assoc_tmul, LinearMap.lTensor_tmul,
      TensorProduct.comm_tmul]
  mul_compr₂_comul := mul_comp₂_tencomul R A1 A2
-- End of Prat III

-- Part IV is proving result from the TODO list like S is unique, an anti-homomorphism, etc.
-- as well as the final big theorem: Points H L is a group! (for H be a commutative Hopf Algebra
-- and L is a Commutative R-Algebra)

/- α and β is the R-linear maps from H ⊗ H → H where α maps a ⊗ b to S(a*b) and β maps
  a ⊗ b to S(b)*S(a), we show that the antipode S is an anti-homomorphism by showing
    α = β -/
abbrev α : LinPoints R (H ⊗[R] H) H := (antipode (R := R) (A := H)).comp (LinearMap.mul' R H)
abbrev β : LinPoints R (H ⊗[R] H) H := (LinearMap.mul' R H).comp
  ((TensorProduct.map (antipode (A := H)) (antipode (A := H))).comp
    (TensorProduct.comm R H H).toLinearMap)

/- These instances are made by kevin in order to improve the speed of compiling my
  codes since typechecking takes forever and obviously even after the improvements
  it's still slow :( sorry I did my best-/
instance : AddMonoidHomClass ((H ⊗[R] H) ⊗[R] H ⊗[R] H ≃ₗ[R] ((H ⊗[R] H) ⊗[R] H) ⊗[R] H)
   ((H ⊗[R] H) ⊗[R] H ⊗[R] H) (((H ⊗[R] H) ⊗[R] H) ⊗[R] H) :=
 inferInstance

instance : AddMonoidHomClass ((H ⊗[R] H) ⊗[R] H ⊗[R] H →ₗ[R] H ⊗[R] H)
   ((H ⊗[R] H) ⊗[R] H ⊗[R] H) (H ⊗[R] H) :=
 inferInstance

instance : AddMonoidHomClass (((H ⊗[R] H) ⊗[R] H) ⊗[R] H →ₗ[R] ((H ⊗[R] H) ⊗[R] H) ⊗[R] H)
   (((H ⊗[R] H) ⊗[R] H) ⊗[R] H) (((H ⊗[R] H) ⊗[R] H) ⊗[R] H) :=
 inferInstance

/- id_H * S = linone -/
lemma mul_id_val : (antipode (A := H)) * LinearMap.id
  = linone R H H := by
  ext x ; unfold linone
  simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply]
  have h0 := HopfAlgebra.mul_antipode_rTensor_comul (R := R) (A := H)
  have h2 : (LinearMap.mul' R H ∘ₗ antipode.rTensor H ∘ₗ Coalgebra.comul) x
    = (Algebra.linearMap R H ∘ₗ Coalgebra.counit) x :=
    congrFun (congrArg DFunLike.coe h0) x
  simp only [LinearMap.comp_apply] at h2 ; exact h2

/- id_H * S = linone -/
lemma id_mul_val : LinearMap.id * (antipode (R := R) (A := H))
  = linone R H H := by
  ext x ; unfold linone ; simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply]
  have h1 := HopfAlgebra.mul_antipode_lTensor_comul (R := R) (A := H)
  have h2 : (LinearMap.mul' R H ∘ₗ LinearMap.lTensor H antipode ∘ₗ Coalgebra.comul) x
    = (Algebra.linearMap R H ∘ₗ Coalgebra.counit) x :=
    congrFun (congrArg DFunLike.coe h1) x
  simp only [LinearMap.comp_apply] at h2 ; exact h2

/- S * id_H = id_H * S -/
lemma idcomp : (antipode (R := R) (A := H)) * LinearMap.id =
  LinearMap.id * (antipode (R := R) (A := H)):= by
  rw [mul_id_val, id_mul_val]

--Uniqueness
theorem anti_unique (T : LinPoints R H H): T * LinearMap.id = linone R H H ∧
  LinearMap.id * T = linone R H H → T = (antipode (A := H) : LinPoints R H H) := by
  rintro ⟨h1, h2⟩ ; ext x ; symm
  calc antipode (A := H) x =
    ((antipode (R := R) (A := H)) * (linone R H H)) x := by rw [linmul_one]
    _ = ((antipode (A := H) : LinPoints R H H) *
      ((LinearMap.id (R := R) (M := H)) * T)) x := by rw [← h2]
    _ = (((antipode (R := R) (A := H)) * (LinearMap.id (R := R)
      (M := H))) * T) x := by rw [←lin_assoc]
    _ = ((linone R H H) * T) x := by rw [mul_id_val R (H := H)]
    _ = T x := by rw [linone_mul]

-- S(1) = 1
lemma antione : (antipode (R := R) (A := H)) (1 : H) = 1 := by
  have h0 : (LinearMap.mul' R H ∘ₗ (antipode.rTensor H) ∘ₗ Coalgebra.comul) 1 = 1 := by
    rw [mul_antipode_rTensor_comul (R := R) (A := H), LinearMap.comp_apply, Bialgebra.counit_one,
      Algebra.linearMap_apply, map_one]
  simp at h0 ; rw [Algebra.TensorProduct.one_def] at h0 ; simp at h0
  exact h0

-- linone is also algebra homomorphism
def linone_alg : Points R H H where
  toFun := linone R H H
  map_one' := by unfold linone ; simp
  map_mul' := by intro x y; unfold linone; simp
  map_zero' := LinearMap.map_zero (linone R H H)
  map_add' := fun x y => LinearMap.map_add (linone R H H) x y
  commutes' := by intro r; unfold linone; simp ; rfl

lemma linoneval (h : H) : linone R H H h = linone_alg R h := by rfl

/- This is showing α * m = linone where m is the multplication of H -/
lemma αmul_eqone : (α R) * (LinearMap.mul' R H) = linone R (H ⊗[R] H) H := by
  rw [linmul1]; ext a b
  simp only [TensorProduct.AlgebraTensorModule.curry_apply, TensorProduct.curry_apply,
    LinearMap.coe_restrictScalars, LinearMap.comp_apply];
  have comuldef : Coalgebra.comul (R := R) (A:= H ⊗[R] H) = (Bialg_tensorequiv R H H).comp (TensorProduct.map
    (Bialgebra.comulAlgHom R H) (Bialgebra.comulAlgHom R H)) := by rfl
  rw [comuldef] ; simp only [AlgHom.toNonUnitalAlgHom_eq_coe,
    NonUnitalAlgHom.toDistribMulActionHom_eq_coe, LinearMap.comp_apply,
    TensorProduct.map_tmul, DistribMulActionHom.coe_toLinearMap,
    NonUnitalAlgHom.coe_to_distribMulActionHom, NonUnitalAlgHom.coe_coe,
    Bialgebra.comulAlgHom_apply] ; clear comuldef
  obtain ⟨I1, a1, a2, ha⟩ := comul_repr R H a
  obtain ⟨I2, b1, b2, hb⟩ := comul_repr R H b
  rw [ha, hb]; unfold Bialg_tensorequiv
  repeat rw [LinearMap.comp_apply]
  dsimp only [LinearEquiv.coe_coe] ; rw [TensorProduct.tmul_sum]; rw [map_sum]
  simp_rw [TensorProduct.sum_tmul]; simp_rw [map_sum]
  simp only [TensorProduct.assoc_symm_tmul, LinearMap.rTensor_tmul, LinearMap.coe_comp,
    LinearEquiv.coe_coe, comp_apply, TensorProduct.assoc_tmul, LinearMap.lTensor_tmul,
    TensorProduct.comm_tmul, TensorProduct.map_tmul, LinearMap.mul'_apply]
  symm; unfold linone
  have tencounit : Coalgebra.counit (R := R) (A := H ⊗[R] H) =
    (Algebra.TensorProduct.lmul' R (S := R)).comp (Algebra.TensorProduct.map
    (Bialgebra.counitAlgHom R H) (Bialgebra.counitAlgHom R H)) := rfl
  rw [tencounit] ; simp only [AlgHom.toNonUnitalAlgHom_eq_coe,
    NonUnitalAlgHom.toDistribMulActionHom_eq_coe, LinearMap.coe_comp,
    DistribMulActionHom.coe_toLinearMap, NonUnitalAlgHom.coe_to_distribMulActionHom,
    NonUnitalAlgHom.coe_coe, AlgHom.coe_comp, comp_apply, Algebra.TensorProduct.map_tmul,
    Bialgebra.counitAlgHom_apply, Algebra.TensorProduct.lmul'_apply_tmul,
    AlgHom.toLinearMap_apply, map_mul] ; clear tencounit
  rw [onedef R a, onedef R b, linoneval, linoneval]
  rw [← map_mul, ← linoneval, ← mul_id_val, linmul1]; simp only [LinearMap.comp_apply,
    Bialgebra.comul_mul]
  rw [ha, hb]; rw [Finset.sum_mul_sum]; repeat rw [map_sum]
  simp_rw [Algebra.TensorProduct.tmul_mul_tmul]; simp_rw [map_sum]
  simp only [TensorProduct.map_tmul, LinearMap.id_coe, id_eq, LinearMap.mul'_apply]
  exact Finset.sum_comm

/- This is a sweedler notation for one (or linone, their value are the same) :
  one(b) = ∑ i b1 i * S(b2 i) (actually = ∑ i S(b1 i) * b2 i as well, but that's
  secretly included in the previous lemma) -/
lemma sum_idS_eqone (I2: Finset (H ⊗[R] H)) (b1 b2 : H ⊗[R] H → H) (b : H)
  (hb: Coalgebra.comul b = ∑ i in I2, b1 i ⊗ₜ[R] b2 i) :
  ∑ i in I2, b1 i * (antipode (R := R) (A := H)) (b2 i) = linone R H H b := by
  symm ; rw [← id_mul_val, linmul1, LinearMap.comp_apply, LinearMap.comp_apply, hb]
  simp only [map_sum, TensorProduct.map_tmul, LinearMap.id_coe, id_eq,
    LinearMap.mul'_apply]

/- This is m * β = linone, now we have all the ingredient -/
lemma mulβ_eqone : (LinearMap.mul' R H) * (β R) = linone R (H ⊗[R] H) H:= by
  rw [linmul1]; ext a b
  simp only [TensorProduct.AlgebraTensorModule.curry_apply, TensorProduct.curry_apply,
    LinearMap.coe_restrictScalars, LinearMap.coe_comp, comp_apply]
  change (LinearMap.mul' R H) ((TensorProduct.map (LinearMap.mul' R H) (β R))
    ((Bialg_tensorequiv R H H).comp (TensorProduct.map
    (Bialgebra.comulAlgHom R H) (Bialgebra.comulAlgHom R H)) (a ⊗ₜ[R] b))) =
    (linone R (H ⊗[R] H) H) (a ⊗ₜ[R] b)
  unfold Bialg_tensorequiv; simp only [AlgHom.toNonUnitalAlgHom_eq_coe,
    NonUnitalAlgHom.toDistribMulActionHom_eq_coe, LinearMap.coe_comp, LinearEquiv.coe_coe,
    comp_apply, TensorProduct.map_tmul, DistribMulActionHom.coe_toLinearMap,
    NonUnitalAlgHom.coe_to_distribMulActionHom, NonUnitalAlgHom.coe_coe,
    Bialgebra.comulAlgHom_apply]
  repeat rw [LinearMap.comp_apply]
  obtain ⟨I1, a1, a2, ha⟩ := comul_repr R H a
  obtain ⟨I2, b1, b2, hb⟩ := comul_repr R H b
  rw [ha, hb]; repeat rw [LinearMap.comp_apply]
  rw [TensorProduct.tmul_sum]; repeat rw [map_sum]
  simp_rw [TensorProduct.sum_tmul]; simp_rw [map_sum]
  simp only [TensorProduct.assoc_symm_tmul, LinearMap.rTensor_tmul, LinearMap.coe_comp,
    LinearEquiv.coe_coe, comp_apply, TensorProduct.assoc_tmul, LinearMap.lTensor_tmul,
    TensorProduct.comm_tmul, TensorProduct.map_tmul, LinearMap.mul'_apply]
  symm ; unfold linone ; rw [LinearMap.comp_apply]
  change (AlgHom.toLinearMap (Algebra.ofId R H)) (
    (Algebra.TensorProduct.lmul' R (S := R)).comp (Algebra.TensorProduct.map
    (Bialgebra.counitAlgHom R H) (Bialgebra.counitAlgHom R H)) (a ⊗ₜ[R] b)) =
    ∑ x in I2, ∑ x_1 in I1,
      a1 x_1 * b1 x * ((antipode (R :=R) (A := H)) (b2 x) * (antipode (R := R) (A := H)) (a2 x_1))
  simp only [AlgHom.comp_apply, Algebra.TensorProduct.map_tmul, Bialgebra.counitAlgHom_apply,
    Algebra.TensorProduct.lmul'_apply_tmul, AlgHom.toLinearMap_apply, map_mul]
  symm ; simp_rw [mul_assoc] ; rw [Finset.sum_comm] ; simp_rw [← Finset.mul_sum]
  simp_rw [← mul_assoc] ; simp_rw [← Finset.sum_mul]
  rw [sum_idS_eqone R I2 b1 b2 b hb] ; rw [linone', LinearMap.comp_apply]
  rw [← mul_one (Coalgebra.counit b), ← Algebra.id.smul_eq_mul]
  rw [map_smul (AlgHom.toLinearMap (Algebra.ofId R H)) (Coalgebra.counit b) (1 : R)]
  simp only [AlgHom.toLinearMap_apply, map_one, Algebra.smul_mul_assoc, one_mul,
    Algebra.mul_smul_comm, smul_eq_mul, mul_one] ; simp_rw [← Finset.smul_sum]
  rw [sum_idS_eqone R I1 a1 a2 a ha] ; rw [← mul_one (Coalgebra.counit b)]
  rw [← Algebra.id.smul_eq_mul, map_smul (Algebra.ofId R H) (Coalgebra.counit b) (1 : R)]
  rw [linone'] ; simp only [smul_eq_mul, mul_one, LinearMap.coe_comp, comp_apply,
    AlgHom.toLinearMap_apply, map_one, Algebra.mul_smul_comm]

/- This theorem is done by calculation which is :
  α = α * one = α * (m * β) = (α * m) * β = one * β = β -/
theorem αβ_eq : α R (H := H) = β R := by
  ext x1 x2 ; simp only [TensorProduct.AlgebraTensorModule.curry_apply,
    TensorProduct.curry_apply, LinearMap.coe_restrictScalars]
  calc _
    (α R) (x1 ⊗ₜ[R] x2) = ((α R (H := H)) *
      (linone R (H ⊗[R] H) H)) (x1 ⊗ₜ[R] x2) := by rw [linmul_one]
    _ = ((α R (H := H)) * ((LinearMap.mul' R H) *
      (β R (H := H)))) (x1 ⊗ₜ[R] x2) := by rw [← mulβ_eqone]
    _ = ((α R (H := H)) * (LinearMap.mul' R H) *
      (β R (H := H))) (x1 ⊗ₜ[R] x2) := by rw [mul_assoc]
    _ = (linone R (H ⊗[R] H) H * (β R (H := H))) (x1 ⊗ₜ[R] x2) := by rw [αmul_eqone]
    _ = (β R (H := H)) (x1 ⊗ₜ[R] x2) := by rw [linone_mul]

/- S(a * b) = S(b) * S(a), S is an antihomomorphism -/
theorem antihom (h l : H) : (antipode (R := R) (A := H)) (h * l) =
  (antipode (R := R) (A := H)) l * (antipode (R := R) (A := H)) h := by
  calc _
    (antipode (R := R) (A := H)) (h * l) =
      ((antipode (R := R) (A := H)).comp (LinearMap.mul' R H)) (h ⊗ₜ[R] l) := by rfl
    _ = α R (H := H) (h ⊗ₜ[R] l) := by rfl
    _ = β R (H := H) (h ⊗ₜ[R] l) := by rw [αβ_eq]
    _ = (LinearMap.mul' R H).comp
        ((TensorProduct.map (antipode (A := H)) (antipode (A := H))).comp
        (TensorProduct.comm R H H).toLinearMap) (h ⊗ₜ[R] l):= by rfl
    _ = (antipode (R := R) (A := H)) l * (antipode (R := R) (A := H)) h := by
      simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, comp_apply,
        TensorProduct.comm_tmul, TensorProduct.map_tmul, LinearMap.mul'_apply]

/- S is an algebra homomorphism under the assumption of S being commutative -/
lemma antipodemul (h l: H): (antipode (R := R) (A := H)) (h*l) =
  (antipode (R := R) (A := H)) h * (antipode (R := R) (A := H)) l := by
  rw [antihom, mul_comm]

lemma antipode_commute(r : R): (antipode (R := R) (A := H)) ((algebraMap R H) r) =
  (algebraMap R H) r := by
  rw [Algebra.algebraMap_eq_smul_one, LinearMap.map_smul, antione]

def S : Points R H H where
  toFun := (antipode (R := R) (A := H))
  map_one' := antione R
  map_mul' := by simp only; intro x y; exact antipodemul R x y
  map_zero' := (antipode (R := R) (A := H)).map_zero
  map_add' := by simp
  commutes' := antipode_commute R

lemma Antival (h : H) : S R h = (antipode (R := R) (A := H)) h := by rfl

-- Define the inverse of elements in Points to be ∀ f ∈ Points, f⁻¹ =  (S ∘ f)
def inv (f : Points R H L) : Points R H L := f.comp (S R)
instance : Inv (Points R H L) := ⟨inv R L⟩
lemma invval (f : Points R H L) : f⁻¹ = f.comp (S R) := rfl

lemma tensordecomp (f : Points R H L) : Algebra.TensorProduct.map (AlgHom.comp f
  (S R)) f = (Algebra.TensorProduct.map f f).comp (Algebra.TensorProduct.map (S R)
  (AlgHom.id R H)) := by
  ext x
  · rw [Algebra.TensorProduct.map_comp_includeLeft]
    repeat rw [AlgHom.comp_apply]
    repeat rw [Algebra.TensorProduct.includeLeft_apply]
    rw [Algebra.TensorProduct.map_tmul, map_one]
    simp only [Algebra.TensorProduct.map_tmul, map_one]
  · repeat rw [AlgHom.comp_apply]
    simp only [Algebra.TensorProduct.includeRight_apply, AlgHom.coe_restrictScalars',
      Algebra.TensorProduct.map_tmul, map_one, AlgHom.comp_apply, AlgHom.coe_id, id_eq]


lemma lemmainv3 (ψ: Points R H L): AlgHom.comp (Algebra.TensorProduct.lmul' R)
    (AlgHom.comp (Algebra.TensorProduct.map ψ ψ)
    (Algebra.TensorProduct.map (S R) (AlgHom.id R H))) =
    AlgHom.comp ψ (AlgHom.comp (Algebra.TensorProduct.lmul' R)
    (Algebra.TensorProduct.map (S R) (AlgHom.id R H))) := by
    ext x <;> simp

lemma lemmainv4 (ψ: Points R H L): AlgHom.comp (AlgHom.comp
    (Algebra.TensorProduct.lmul' R)
    (Algebra.TensorProduct.map (S R) (AlgHom.id R H))) (Bialgebra.comulAlgHom R H) =
    linone_alg R := by
    ext h ; rw [← linoneval R (H := H) h, ← mul_id_val, linmul1, LinearMap.comp_apply,
      LinearMap.comp_apply]
    simp only [AlgHom.comp_apply, Bialgebra.comulAlgHom_apply]
    obtain ⟨I1, h1, h2, h0⟩ := comul_repr R H h
    simp only [h0, map_sum, map_smul, Algebra.TensorProduct.map_tmul, AlgHom.coe_id,
      id_eq, Algebra.TensorProduct.lmul'_apply_tmul, TensorProduct.map_tmul, LinearMap.id_coe,
      LinearMap.mul'_apply]
    refine Finset.sum_congr rfl fun _ _ ↦ rfl

lemma Algoneval : linone_alg R = one (R := R) (A := H) (L := H) := by rfl

/- f ∘ one = one -/
lemma compone_eq_one (f : Points R H L): f.comp one = (one : Points R H L) := by
  ext x; rw [AlgHom.comp_apply]
  have h0 := f.commutes
  unfold one; rw [AlgHom.comp_apply, AlgHom.comp_apply, Bialgebra.counitAlgHom_apply]
  exact h0 (Coalgebra.counit x)

/- f⁻¹ * f = one -/
lemma leftinv(f: Points R H L) : f⁻¹ * f = one := by
  rw [hmul1, invval, oneval, tensordecomp, ← AlgHom.comp_assoc, lemmainv3,
  AlgHom.comp_assoc , lemmainv4 R H, Algoneval, compone_eq_one, ← oneval]
  exact S R

instance : Group (Points R H L) where
  mul := mul (R := R) (A := H) (L := L)
  mul_assoc := Pointmul_assoc
  one := one
  one_mul := Pointone_mul
  mul_one := Pointmul_one
  inv := inv R L
  mul_left_inv := leftinv R L

instance: Group (Points R H H) := inferInstance

/- Since the inverse in a group is unique, S⁻¹ must equal id !-/
lemma anti_inverseunique: (S R (H := H))⁻¹ = AlgHom.id R H := by
  rw [inv_eq_iff_mul_eq_one]
  exact mul_eq_one_iff_eq_inv.mpr rfl

/- Since S² also satisfies S² * S is also one, by the uniqueness of inverse
  S² must be equal to id -/
lemma antisquare_is_id: (S R (H := H)).comp (S R (H := H)) = AlgHom.id R H := by
  rw [← anti_inverseunique]
  exact rfl

/- If H is commutative, S is a bijection (Co-commutative should work as well,
  but I got tired :)) -/
lemma anti_bijection: Bijective (S R (H := H)) := by
  constructor
  · intro x y h ; rw [← id_eq x, ← id_eq y, ← AlgHom.coe_id R, ← antisquare_is_id,
    AlgHom.comp_apply, h]; rfl
  · intro x ; use (S R (H := H)) x
    refine by rw [← AlgHom.comp_apply, antisquare_is_id] ; rfl

-- Thanks for reading! I know it's long and takes long time to compile :(, hope you found our
-- work intersting ! :))
end
end HopfPoints
