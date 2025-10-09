import Mathlib

open TensorProduct

variable (G M' : Type) [AddCommGroup M'] [Group G] (M : Rep ℤ G) (δ : Representation ℤ G M')

noncomputable def newRep : Representation ℤ G (M ⊗[ℤ] δ.asModule) where
  toFun g := LinearMap.lTensor _ (δ g)
  map_one' := by ext; simp
  map_mul' _ _ := by ext; simp
