import Mathlib.Topology.Homeomorph

-- elsewhere
theorem _root_.Homeomorph.coinducing {A B : Type*} [τA : TopologicalSpace A]
    [τB : TopologicalSpace B] (e : A ≃ₜ B) : τB = τA.coinduced e := by
  ext U
  nth_rw 2 [isOpen_coinduced]
  exact e.isOpen_preimage.symm

theorem Homeomorph.symm_apply_eq {M N : Type*} [TopologicalSpace M]
    [TopologicalSpace N] (e : M ≃ₜ N) {x : N} {y : M} :
  e.symm x = y ↔ x = e y := Equiv.symm_apply_eq _

def Homeomorph.sumPiEquivProdPi (S T : Type*) (A : S ⊕ T → Type*)
    [∀ st, TopologicalSpace (A st)] :
    (∀ (st : S ⊕ T), A st) ≃ₜ (∀ (s : S), A (.inl s)) × (∀ (t : T), A (.inr t)) where
  __ := Equiv.sumPiEquivProdPi _
  continuous_toFun := Continuous.prod_mk (by fun_prop) (by fun_prop)
  continuous_invFun := continuous_pi <| by rintro (s | t) <;> simp <;> fun_prop

def Homeomorph.pUnitPiEquiv (f : PUnit → Type*) [∀ x, TopologicalSpace (f x)] :
    (∀ t, f t) ≃ₜ f () where
  toFun a := a ()
  invFun a _t := a
  left_inv x := rfl
  right_inv x := rfl
  continuous_toFun := by simp; fun_prop
  continuous_invFun := by simp; fun_prop
