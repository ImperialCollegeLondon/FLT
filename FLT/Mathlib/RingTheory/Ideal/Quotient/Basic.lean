module

public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.Ideal.Span
public import Mathlib.Algebra.Ring.Divisibility.Basic
import Mathlib.RingTheory.Ideal.Quotient.Basic

@[expose] public section

variable {R : Type*} [Ring R] (I : Ideal R) [I.IsTwoSided]

theorem Ideal.Quotient.out_sub (x : R) : (Ideal.Quotient.mk I x).out - x ∈ I := by
  rw [← Ideal.Quotient.eq, Ideal.Quotient.mk_out]

/-- For a commutative domain `R` and nonzero `α : R`, there is a bijection
`(R ⧸ (α)) × (R ⧸ (β)) ≃ R ⧸ (α * β)` sending `(i, j)` to
`i.out + α * j.out`. -/
noncomputable def Ideal.Quotient.prodEquivSpanMul {R : Type*} [CommRing R] [IsDomain R]
    {α β : R} (hα : α ≠ 0) :
    (R ⧸ Ideal.span ({α} : Set R)) × (R ⧸ Ideal.span ({β} : Set R)) ≃
      R ⧸ Ideal.span ({α * β} : Set R) := by
  refine Equiv.ofBijective
    (fun p : (R ⧸ Ideal.span ({α} : Set R)) × (R ⧸ Ideal.span ({β} : Set R)) =>
      Ideal.Quotient.mk (Ideal.span ({α * β} : Set R)) (p.1.out + α * p.2.out)) ⟨?_, ?_⟩
  · -- injectivity
    rintro ⟨i₁, j₁⟩ ⟨i₂, j₂⟩ h
    simp only at h
    rw [Ideal.Quotient.eq, Ideal.mem_span_singleton] at h
    have hαβ : α * β ∣ (i₁.out - i₂.out) + α * (j₁.out - j₂.out) := by
      have hrew : (i₁.out + α * j₁.out) - (i₂.out + α * j₂.out)
          = (i₁.out - i₂.out) + α * (j₁.out - j₂.out) := by ring
      rw [hrew] at h; exact h
    have hα_dvd : α ∣ (i₁.out - i₂.out) := by
      have h1 : α ∣ (i₁.out - i₂.out) + α * (j₁.out - j₂.out) :=
        dvd_trans ⟨β, rfl⟩ hαβ
      have h2 : α ∣ α * (j₁.out - j₂.out) := ⟨_, rfl⟩
      have h3 : α ∣ α * (j₁.out - j₂.out) + (i₁.out - i₂.out) := by
        rw [add_comm]; exact h1
      exact (dvd_add_right h2).mp h3
    have hi : i₁ = i₂ := by
      have hmem : i₁.out - i₂.out ∈ Ideal.span ({α} : Set R) :=
        Ideal.mem_span_singleton.mpr hα_dvd
      have heq : Ideal.Quotient.mk (Ideal.span ({α} : Set R)) i₁.out
          = Ideal.Quotient.mk (Ideal.span ({α} : Set R)) i₂.out := by
        rw [Ideal.Quotient.eq]; exact hmem
      have e1 : (Ideal.Quotient.mk (Ideal.span ({α} : Set R))) i₁.out = i₁ := Quotient.out_eq i₁
      have e2 : (Ideal.Quotient.mk (Ideal.span ({α} : Set R))) i₂.out = i₂ := Quotient.out_eq i₂
      rw [e1, e2] at heq
      exact heq
    subst hi
    have hdvd2 : α * β ∣ α * (j₁.out - j₂.out) := by
      have heq3 : (i₁.out + α * j₁.out) - (i₁.out + α * j₂.out)
          = α * (j₁.out - j₂.out) := by ring
      rw [heq3] at h; exact h
    have hβ_dvd : β ∣ (j₁.out - j₂.out) := by
      rcases hdvd2 with ⟨c, hc⟩
      have heqc : α * (j₁.out - j₂.out) = α * (β * c) := by rw [hc]; ring
      have hcancel : j₁.out - j₂.out = β * c := mul_left_cancel₀ hα heqc
      exact ⟨c, hcancel⟩
    have hj : j₁ = j₂ := by
      have hmem : j₁.out - j₂.out ∈ Ideal.span ({β} : Set R) :=
        Ideal.mem_span_singleton.mpr hβ_dvd
      have heq : Ideal.Quotient.mk (Ideal.span ({β} : Set R)) j₁.out
          = Ideal.Quotient.mk (Ideal.span ({β} : Set R)) j₂.out := by
        rw [Ideal.Quotient.eq]; exact hmem
      have e1 : (Ideal.Quotient.mk (Ideal.span ({β} : Set R))) j₁.out = j₁ := Quotient.out_eq j₁
      have e2 : (Ideal.Quotient.mk (Ideal.span ({β} : Set R))) j₂.out = j₂ := Quotient.out_eq j₂
      rw [e1, e2] at heq
      exact heq
    rw [hj]
  · -- surjectivity
    intro k
    set i : R ⧸ Ideal.span ({α} : Set R) :=
      Ideal.Quotient.mk (Ideal.span ({α} : Set R)) k.out with hi_def
    have hmem_α : k.out - i.out ∈ Ideal.span ({α} : Set R) := by
      have hs := Ideal.Quotient.out_sub (Ideal.span ({α} : Set R)) k.out
      have hneg : -(i.out - k.out) ∈ Ideal.span ({α} : Set R) := neg_mem hs
      have heqn : k.out - i.out = -(i.out - k.out) := by ring
      rw [heqn]; exact hneg
    have hdvd : α ∣ k.out - i.out := Ideal.mem_span_singleton.mp hmem_α
    set m : R := Classical.choose hdvd with hm_def
    have hm : k.out - i.out = α * m := Classical.choose_spec hdvd
    set j : R ⧸ Ideal.span ({β} : Set R) :=
      Ideal.Quotient.mk (Ideal.span ({β} : Set R)) m with hj_def
    refine ⟨(i, j), ?_⟩
    change Ideal.Quotient.mk (Ideal.span ({α * β} : Set R)) (i.out + α * j.out) = k
    rw [show k = Ideal.Quotient.mk (Ideal.span ({α * β} : Set R)) k.out from
      (Quotient.out_eq k).symm]
    rw [Ideal.Quotient.eq, Ideal.mem_span_singleton]
    have hjmem : j.out - m ∈ Ideal.span ({β} : Set R) := by
      have hs := Ideal.Quotient.out_sub (Ideal.span ({β} : Set R)) m
      exact hs
    rw [Ideal.mem_span_singleton] at hjmem
    obtain ⟨c, hc⟩ := hjmem
    have hjout_eq : j.out = m + β * c := by
      have : j.out = (j.out - m) + m := by ring
      rw [this, hc]; ring
    have hkout : k.out = i.out + α * m := by
      have : k.out = (k.out - i.out) + i.out := by ring
      rw [this, hm]; ring
    refine ⟨c, ?_⟩
    rw [hjout_eq, hkout]
    ring
