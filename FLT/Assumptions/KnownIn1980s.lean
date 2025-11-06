import Mathlib.Init

axiom knownin1980s {P : Prop} : P

-- **TODO** can we make it red like `sorry`?
macro "knownin1980s" : tactic => `(tactic| exact knownin1980s)
