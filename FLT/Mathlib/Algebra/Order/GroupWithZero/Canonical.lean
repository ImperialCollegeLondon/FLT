import Mathlib.Algebra.Order.GroupWithZero.Canonical

namespace WithZero

open Multiplicative in
theorem toAdd_unzero_lt_of_lt_ofAdd {α : Type*} [Preorder α]
    {a : WithZero (Multiplicative α)} {b : α} (ha : a ≠ 0) (h : a < ofAdd b) :
    toAdd (unzero ha) < b := by
  rwa [← coe_unzero ha, coe_lt_coe, ← toAdd_lt, toAdd_ofAdd] at h

open Multiplicative in
theorem lt_ofAdd_of_toAdd_unzero_lt {α : Type*} [Preorder α]
    {a : WithZero (Multiplicative α)} {b : α} (ha : a ≠ 0) (h : toAdd (unzero ha) < b) :
    a < ofAdd b := by
  rwa [← coe_unzero ha, coe_lt_coe, ← ofAdd_toAdd (unzero ha), ofAdd_lt]

open Multiplicative in
theorem lt_ofAdd_iff {α : Type*} [Preorder α]
    {a : WithZero (Multiplicative α)} {b : α} (ha : a ≠ 0)  :
    a < ofAdd b ↔ toAdd (unzero ha) < b :=
  ⟨toAdd_unzero_lt_of_lt_ofAdd ha, lt_ofAdd_of_toAdd_unzero_lt ha⟩

open Multiplicative in
theorem toAdd_unzero_le_of_lt_ofAdd {α : Type*} [Preorder α]
    {a : WithZero (Multiplicative α)} {b : α} (ha : a ≠ 0) (h : a ≤ ofAdd b) :
    toAdd (unzero ha) ≤ b := by
  rwa [← coe_unzero ha, coe_le_coe, ← toAdd_le, toAdd_ofAdd] at h

open Multiplicative in
theorem le_ofAdd_of_toAdd_unzero_le {α : Type*} [Preorder α]
    {a : WithZero (Multiplicative α)} {b : α} (ha : a ≠ 0) (h : toAdd (unzero ha) ≤ b) :
    a ≤ ofAdd b := by
  rwa [← coe_unzero ha, coe_le_coe, ← ofAdd_toAdd (unzero ha), ofAdd_le]

open Multiplicative in
theorem le_ofAdd_iff {α : Type*} [Preorder α]
    {a : WithZero (Multiplicative α)} {b : α} (ha : a ≠ 0)  :
    a ≤ ofAdd b ↔ toAdd (unzero ha) ≤ b :=
  ⟨toAdd_unzero_le_of_lt_ofAdd ha, le_ofAdd_of_toAdd_unzero_le ha⟩

end WithZero
