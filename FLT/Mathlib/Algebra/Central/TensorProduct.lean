import Mathlib.Algebra.Central.TensorProduct
import Mathlib.Algebra.Algebra.Subalgebra.Centralizer
import Mathlib.LinearAlgebra.TensorProduct.Subalgebra

open scoped TensorProduct

@[simp]
lemma Subalgebra.sup_includeLeft_includeRight_eq_top
    {k A B : Type*} [CommSemiring k]
    [Semiring A] [Algebra k A] [Semiring B] [Algebra k B] :
    Algebra.TensorProduct.includeLeft.range ⊔ Algebra.TensorProduct.includeRight.range
    = (⊤ : Subalgebra k (A ⊗[k] B)) := by
  ext x
  simp only [Algebra.mem_top, iff_true]
  refine TensorProduct.induction_on x (by simp) (fun a b ↦ ?_) (fun _ _ ↦ AddMemClass.add_mem)
  have : a ⊗ₜ[k] b = a ⊗ₜ[k] 1 * 1 ⊗ₜ[k] b := by simp
  rw [this]
  exact Subalgebra.mul_mem _
    (Algebra.mem_sup_left <| Set.mem_range_self _)
    (Algebra.mem_sup_right <| Set.mem_range_self _)

lemma Subalgebra.center_tensorProduct_eq_inf
    {k : Type*} [Field k]
    {A B : Type*} [Ring A] [Algebra k A] [Ring B] [Algebra k B] :
    Subalgebra.center k (A ⊗[k] B)
    = (Algebra.TensorProduct.map (Subalgebra.center k A).val (AlgHom.id k B)).range
      ⊓ (Algebra.TensorProduct.map (AlgHom.id k A) (Subalgebra.center k B).val).range := by
  rw [← Subalgebra.centralizer_coe_range_includeLeft_eq_center_tensorProduct,
    ← Subalgebra.centralizer_range_includeRight_eq_center_tensorProduct,
    ← Subalgebra.centralizer_coe_sup]
  simp

lemma Submodule.tensorProduct_inf_eq_range_map
    {k : Type*} [Field k]
    {A B : Type*} [AddCommGroup A] [Module k A] [AddCommGroup B] [Module k B]
    (S : Submodule k A) (T : Submodule k B) :
    LinearMap.range (TensorProduct.map S.subtype LinearMap.id) ⊓
    LinearMap.range (TensorProduct.map LinearMap.id T.subtype) =
    LinearMap.range (TensorProduct.map S.subtype T.subtype) := by
  refine le_antisymm ?_
    (le_inf (TensorProduct.range_map_mono le_rfl (by simp))
      (TensorProduct.range_map_mono (by simp) le_rfl))
  rintro x ⟨⟨u, hux⟩, ⟨v, hvx⟩⟩
  let qS := S.linearProjOfIsCompl S.exists_isCompl.choose S.exists_isCompl.choose_spec
  let qT := T.linearProjOfIsCompl T.exists_isCompl.choose T.exists_isCompl.choose_spec
  have hxS : TensorProduct.map (S.subtype.comp qS) LinearMap.id x = x := by
    rw [← hux]
    exact TensorProduct.induction_on u (by simp)
      (fun _ _ ↦ by simp_all [qS]) (fun _ _ ↦ by simp_all)
  have hxT : TensorProduct.map LinearMap.id (T.subtype.comp qT) x = x := by
    rw [← hvx]
    exact TensorProduct.induction_on v (by simp)
      (fun _ _ ↦ by simp_all [qT]) (fun _ _ ↦ by simp_all)
  have hxST : TensorProduct.map (S.subtype.comp qS) (T.subtype.comp qT) x = x := by
    conv_rhs => rw [← hxS, ← hxT]
    simp [← TensorProduct.map_comp, ← LinearMap.comp_apply]
  use TensorProduct.map qS qT x;
  simpa [← TensorProduct.map_comp, ← LinearMap.comp_apply] using hxST

lemma Subalgebra.tensorProduct_inf_eq_range_map
    {k : Type*} [Field k]
    {A B : Type*} [Ring A] [Algebra k A] [Ring B] [Algebra k B]
    (S : Subalgebra k A) (T : Subalgebra k B) :
    (Algebra.TensorProduct.map S.val (AlgHom.id k B)).range ⊓
    (Algebra.TensorProduct.map (AlgHom.id k A) T.val).range =
    (Algebra.TensorProduct.map S.val T.val).range :=
  Subalgebra.toSubmodule_injective <|
    Submodule.tensorProduct_inf_eq_range_map S.toSubmodule T.toSubmodule

lemma Subalgebra.center_tensorProduct
    {k : Type*} [Field k]
    {A B : Type*} [Ring A] [Algebra k A] [Ring B] [Algebra k B] :
    Subalgebra.center k (A ⊗[k] B)
    = (Algebra.TensorProduct.map (Subalgebra.center k A).val
      (Subalgebra.center k B).val).range := by
  have := Subalgebra.center_tensorProduct_eq_inf (k := k) (A := A) (B := B)
  simp_all [Subalgebra.tensorProduct_inf_eq_range_map]

instance (k A B : Type*) [Field k] [CommRing A] [Ring B]
    [Algebra k A] [Algebra k B]
    [Algebra.IsCentral k B] :
    Algebra.IsCentral A (A ⊗[k] B) := ⟨fun x hx ↦ by
  have :
      x ∈ (Algebra.TensorProduct.map
        (Subalgebra.center k A).val (Subalgebra.center k B).val).range := by
    simpa [← Subalgebra.center_tensorProduct] using hx
  rw [Algebra.IsCentral.center_eq_bot k B] at this
  obtain ⟨ab, rfl⟩ := this
  refine TensorProduct.induction_on ab (by simp)
    (fun a ⟨b, hb⟩ ↦ ?_) (fun _ _ ↦ by simpa using AddMemClass.add_mem)
  obtain ⟨kb, rfl⟩ := Algebra.mem_bot.mp hb
  refine Algebra.mem_bot.mpr ⟨kb • a, ?_⟩
  simp [-TensorProduct.tmul_smul, TensorProduct.smul_tmul, Algebra.smul_def kb (1 : B)]⟩
