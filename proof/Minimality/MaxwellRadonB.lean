module

public import Mathlib

@[expose] public section


namespace Minimality.MRB

open Real Finset

noncomputable def mrb_sx (w φ : ℕ → ℝ) (s : Finset ℕ) : ℝ := ∑ m ∈ s, -(w m * sin (φ m))
noncomputable def mrb_sy (w φ : ℕ → ℝ) (s : Finset ℕ) : ℝ := ∑ m ∈ s, w m * cos (φ m)

theorem mrb_cross_eq (w φ : ℕ → ℝ) (A B : Finset ℕ) :
    mrb_sx w φ A * mrb_sy w φ B - mrb_sy w φ A * mrb_sx w φ B
      = ∑ a ∈ A, ∑ b ∈ B, w a * w b * sin (φ b - φ a) := by
  unfold mrb_sx mrb_sy
  rw [Finset.sum_mul_sum, Finset.sum_mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [sin_sub]; ring

theorem mrb_three (w φ : ℕ → ℝ) (A B C : Finset ℕ)
    (hA : A.Nonempty) (hB : B.Nonempty) (hC : C.Nonempty)
    (hwA : ∀ m ∈ A, 0 < w m) (hwB : ∀ m ∈ B, 0 < w m) (hwC : ∀ m ∈ C, 0 < w m)
    (hx : mrb_sx w φ A + mrb_sx w φ B + mrb_sx w φ C = 0)
    (hy : mrb_sy w φ A + mrb_sy w φ B + mrb_sy w φ C = 0)
    (hs : ∀ a ∈ A, ∀ b ∈ B, ∀ c ∈ C,
      0 < sin (φ b - φ a) + sin (φ c - φ b) + sin (φ a - φ c)) :
    0 < mrb_sx w φ A * mrb_sy w φ B - mrb_sy w φ A * mrb_sx w φ B := by
  set X := mrb_sx w φ A * mrb_sy w φ B - mrb_sy w φ A * mrb_sx w φ B with hX
  have hX2 : X = mrb_sx w φ B * mrb_sy w φ C - mrb_sy w φ B * mrb_sx w φ C := by
    have h1 : mrb_sx w φ C = -mrb_sx w φ A - mrb_sx w φ B := by linarith
    have h2 : mrb_sy w φ C = -mrb_sy w φ A - mrb_sy w φ B := by linarith
    rw [h1, h2, hX]; ring
  have hX3 : X = mrb_sx w φ C * mrb_sy w φ A - mrb_sy w φ C * mrb_sx w φ A := by
    have h1 : mrb_sx w φ C = -mrb_sx w φ A - mrb_sx w φ B := by linarith
    have h2 : mrb_sy w φ C = -mrb_sy w φ A - mrb_sy w φ B := by linarith
    rw [h1, h2, hX]; ring
  rw [mrb_cross_eq] at hX2 hX3 hX
  set WA := ∑ m ∈ A, w m
  set WB := ∑ m ∈ B, w m
  set WC := ∑ m ∈ C, w m
  have e1 : X * WC = ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, w a * w b * w c * sin (φ b - φ a) := by
    rw [hX, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    ring
  have e2 : WA * X = ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, w a * w b * w c * sin (φ c - φ b) := by
    rw [hX2, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    ring
  have e3 : X * WB = ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, w a * w b * w c * sin (φ a - φ c) := by
    have : X * WB = ∑ c ∈ C, ∑ a ∈ A, ∑ b ∈ B, w a * w b * w c * sin (φ a - φ c) := by
      rw [hX3, Finset.sum_mul]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      ring
    rw [this, Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_comm]
  have hpos : 0 < ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, w a * w b * w c *
      (sin (φ b - φ a) + sin (φ c - φ b) + sin (φ a - φ c)) := by
    refine Finset.sum_pos (fun a ha => ?_) hA
    refine Finset.sum_pos (fun b hb => ?_) hB
    refine Finset.sum_pos (fun c hc => ?_) hC
    have := hwA a ha; have := hwB b hb; have := hwC c hc
    have := hs a ha b hb c hc
    positivity
  have hsum : X * (WA + WB + WC) = ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, w a * w b * w c *
      (sin (φ b - φ a) + sin (φ c - φ b) + sin (φ a - φ c)) := by
    have : X * (WA + WB + WC) = X * WC + WA * X + X * WB := by ring
    rw [this, e1, e2, e3, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_
    ring
  have hW : 0 < WA + WB + WC := by
    have h1 : 0 < WA := Finset.sum_pos hwA hA
    have h2 : 0 < WB := Finset.sum_pos hwB hB
    have h3 : 0 < WC := Finset.sum_pos hwC hC
    linarith
  rw [← hsum] at hpos
  exact (pos_iff_pos_of_mul_pos hpos).2 hW

end Minimality.MRB
