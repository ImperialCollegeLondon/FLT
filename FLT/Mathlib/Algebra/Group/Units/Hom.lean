import Mathlib.Algebra.Group.Units.Hom

variable {M N : Type*} [Monoid M] [Monoid N]

@[to_additive (attr := simp)]
lemma Units.map_mk (f : M →* N) (val inv : M) (val_inv inv_val) :
    map f (mk val inv val_inv inv_val) = mk (f val) (f inv)
      (by rw [← f.map_mul, val_inv, f.map_one]) (by rw [← f.map_mul, inv_val, f.map_one]) := rfl
