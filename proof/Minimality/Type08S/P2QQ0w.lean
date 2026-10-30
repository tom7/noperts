module

public import Minimality.Type08S.G3p

@[expose] public section

set_option relaxedAutoImplicit true
set_option autoImplicit true
namespace Minimality
namespace Type08Sp

set_option maxHeartbeats 4000000 in
theorem polyAw (a1 b1 a4 g4 b6 g6 : ℝ) (p0 : 0 < a1) (p1 : 0 < b1) (p2 : 0 < a4) (p3 : 0 < g4) (p4 : 0 < b6) (p5 : 0 < g6) (e1 : 0 < a1 + b1 - 1) (e2 : 0 < a4 + g4 - 1) (e3 : 0 < b6 + g6 - 1) (dA : 0 < -1 + g6) (dB : 0 < -1 + a1) (ga : 0 ≤ -a1 + a1 * g4 - b1 * a4 + a4) (gb : 0 ≤ a1 * b6 + b1 - b1 * g6 - b6) (f1 : 0 < a1 * g4 * b6 + b1 * a4 * g6 + b1 * g4 - b1 * g6 - g4 * b6) (f2 : 0 < a1 * g4 + b1 * g4 - g4) (f3 : 0 < -b1 + b1 * a4 + b1 * g4) (f4 : 0 < a1 * g6 + b1 * g6 - g6) (f5 : 0 < -a1 * g4 + a1 * g4 * b6 + a1 * g6 + b1 * a4 * g6 - a4 * g6) (f6 : 0 < -a1 + a1 * b6 + a1 * g6) (f7 : 0 < a4 * b6 + g4 * b6 - b6) (f8 : 0 < -a4 + a4 * b6 + a4 * g6) (f9 : 0 < a1 * g4 * b6 - a1 * b6 - b1 * a4 + b1 * a4 * g6 + a4 * b6) (f10 : 0 < a1 * g4 * b6 + b1 * a4 * g6 + b1 * g4 - b1 * g6 - g4 * b6) (f11 : 0 < -a1 * g4 + a1 * g4 * b6 + a1 * g6 + b1 * a4 * g6 - a4 * g6) (f12 : 0 < a1 * g4 * b6 - a1 * b6 - b1 * a4 + b1 * a4 * g6 + a4 * b6) :
    0 < -a1 + a1 * b6 + a1 * g6 ∧ 0 < -a4 + a4 * b6 + a4 * g6 ∧ 0 < -1 + b6 + g6 ∧ 0 < -a1 + a1 * g4 * b6 + a1 * g6 - b1 * a4 + b1 * a4 * g6 + a4 - a4 * g6 ∧ 0 < 1 - a1 + a1 * g6 - b1 + b1 * g6 - g6 ∧ 0 < -a1 + a1 * g6 ∧ 0 < a1 * g4 * b6 - a1 * b6 - b1 * a4 + b1 * a4 * g6 + a4 * b6 ∧ 0 < a1 * g4 * b6 + b1 - b1 * a4 + b1 * a4 * g6 - b1 * g6 - g4 * b6 ∧ 0 < a1 * g4 * b6 - b1 * a4 + b1 * a4 * g6 ∧ 0 < a4 * b6 + g4 * b6 - b6 ∧ 0 < a4 * b6 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · first | linarith [mul_pos p0 p4, mul_pos p0 dA] | nlinarith [mul_pos p0 p4, mul_pos p0 dA]
  · first | linarith [mul_pos p2 dA, mul_pos p2 p4] | nlinarith [mul_pos p2 dA, mul_pos p2 p4]
  · first | linarith [p4, dA] | nlinarith [p4, dA]
  · first | linarith [ga, f11] | nlinarith [ga, f11]
  · first | linarith [mul_pos dA dB, mul_pos p1 dA] | nlinarith [mul_pos dA dB, mul_pos p1 dA]
  · first | linarith [mul_pos p0 dA] | nlinarith [mul_pos p0 dA]
  · first | linarith [mul_nonneg (p4).le ga, mul_pos (mul_pos p1 p2) p4, mul_pos (mul_pos p1 p2) dA] | nlinarith [mul_nonneg (p4).le ga, mul_pos (mul_pos p1 p2) p4, mul_pos (mul_pos p1 p2) dA]
  · first | linarith [mul_pos f3 dA, mul_nonneg (p3).le gb] | nlinarith [mul_pos f3 dA, mul_nonneg (p3).le gb]
  · first | linarith [mul_pos (mul_pos p0 p3) p4, mul_pos (mul_pos p1 p2) dA] | nlinarith [mul_pos (mul_pos p0 p3) p4, mul_pos (mul_pos p1 p2) dA]
  · first | linarith [mul_pos p4 e2] | nlinarith [mul_pos p4 e2]
  · first | linarith [mul_pos p2 p4] | nlinarith [mul_pos p2 p4]

set_option maxHeartbeats 4000000 in
theorem polyBw (a1 b1 a4 g4 b6 g6 : ℝ) (p0 : 0 < a1) (p1 : 0 < b1) (p2 : 0 < a4) (p3 : 0 < g4) (p4 : 0 < b6) (p5 : 0 < g6) (e1 : 0 < a1 + b1 - 1) (e2 : 0 < a4 + g4 - 1) (e3 : 0 < b6 + g6 - 1) (dA : 0 < 1 - g6) (dB : 0 < -1 + a1) (ga : 0 ≤ -a1 + a1 * g4 - b1 * a4 + a4) (gb : 0 ≤ a1 * b6 + b1 - b1 * g6 - b6) (f1 : 0 < a1 * g4 * b6 + b1 * a4 * g6 + b1 * g4 - b1 * g6 - g4 * b6) (f2 : 0 < a1 * g4 + b1 * g4 - g4) (f3 : 0 < -b1 + b1 * a4 + b1 * g4) (f4 : 0 < a1 * g6 + b1 * g6 - g6) (f5 : 0 < -a1 * g4 + a1 * g4 * b6 + a1 * g6 + b1 * a4 * g6 - a4 * g6) (f6 : 0 < -a1 + a1 * b6 + a1 * g6) (f7 : 0 < a4 * b6 + g4 * b6 - b6) (f8 : 0 < -a4 + a4 * b6 + a4 * g6) (f9 : 0 < a1 * g4 * b6 - a1 * b6 - b1 * a4 + b1 * a4 * g6 + a4 * b6) (f10 : 0 < a1 * g4 * b6 + b1 * a4 * g6 + b1 * g4 - b1 * g6 - g4 * b6) (f11 : 0 < -a1 * g4 + a1 * g4 * b6 + a1 * g6 + b1 * a4 * g6 - a4 * g6) (f12 : 0 < a1 * g4 * b6 - a1 * b6 - b1 * a4 + b1 * a4 * g6 + a4 * b6) :
    0 < a1 * g4 ∧ 0 < a1 ∧ 0 < a1 * g6 ∧ 0 < -a1 + a1 * g4 + a4 ∧ 0 < a1 * g4 - g4 ∧ 0 < a1 * g4 - a1 * g6 + a4 * g6 ∧ 0 < a4 ∧ 0 < -1 + a4 + g4 ∧ 0 < a4 - a4 * g6 ∧ 0 < 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · first | linarith [mul_pos p0 p3] | nlinarith [mul_pos p0 p3]
  · first | linarith [p0] | nlinarith [p0]
  · first | linarith [mul_pos p0 p5] | nlinarith [mul_pos p0 p5]
  · first | linarith [mul_nonneg ((mul_pos p5 p5)).le ga, mul_pos p1 p2, mul_nonneg ((mul_pos dA dA)).le ga, mul_nonneg ((mul_pos p5 dA)).le ga] | nlinarith [mul_nonneg ((mul_pos p5 p5)).le ga, mul_pos p1 p2, mul_nonneg ((mul_pos dA dA)).le ga, mul_nonneg ((mul_pos p5 dA)).le ga]
  · first | linarith [mul_pos p3 dB] | nlinarith [mul_pos p3 dB]
  · first | linarith [mul_nonneg (p5).le ga, mul_pos (mul_pos p0 p3) dA, mul_pos (mul_pos p1 p2) p5] | nlinarith [mul_nonneg (p5).le ga, mul_pos (mul_pos p0 p3) dA, mul_pos (mul_pos p1 p2) p5]
  · first | linarith [p2] | nlinarith [p2]
  · first | linarith [e2] | nlinarith [e2]
  · first | linarith [mul_pos p2 dA] | nlinarith [mul_pos p2 dA]
  · first | linarith [p5, dA] | nlinarith [p5, dA]

set_option maxHeartbeats 4000000 in
theorem polyCw (a1 b1 a4 g4 b6 g6 : ℝ) (p0 : 0 < a1) (p1 : 0 < b1) (p2 : 0 < a4) (p3 : 0 < g4) (p4 : 0 < b6) (p5 : 0 < g6) (e1 : 0 < a1 + b1 - 1) (e2 : 0 < a4 + g4 - 1) (e3 : 0 < b6 + g6 - 1) (dA : 0 < 1 - g6) (dB : 0 < 1 - a1) (ga : 0 ≤ -a1 + a1 * g4 - b1 * a4 + a4) (gb : 0 ≤ a1 * b6 + b1 - b1 * g6 - b6) (f1 : 0 < a1 * g4 * b6 + b1 * a4 * g6 + b1 * g4 - b1 * g6 - g4 * b6) (f2 : 0 < a1 * g4 + b1 * g4 - g4) (f3 : 0 < -b1 + b1 * a4 + b1 * g4) (f4 : 0 < a1 * g6 + b1 * g6 - g6) (f5 : 0 < -a1 * g4 + a1 * g4 * b6 + a1 * g6 + b1 * a4 * g6 - a4 * g6) (f6 : 0 < -a1 + a1 * b6 + a1 * g6) (f7 : 0 < a4 * b6 + g4 * b6 - b6) (f8 : 0 < -a4 + a4 * b6 + a4 * g6) (f9 : 0 < a1 * g4 * b6 - a1 * b6 - b1 * a4 + b1 * a4 * g6 + a4 * b6) (f10 : 0 < a1 * g4 * b6 + b1 * a4 * g6 + b1 * g4 - b1 * g6 - g4 * b6) (f11 : 0 < -a1 * g4 + a1 * g4 * b6 + a1 * g6 + b1 * a4 * g6 - a4 * g6) (f12 : 0 < a1 * g4 * b6 - a1 * b6 - b1 * a4 + b1 * a4 * g6 + a4 * b6) :
    0 < g4 ∧ 0 < 1 ∧ 0 < g6 ∧ 0 < -1 + a4 + g4 ∧ 0 < a4 * g6 + g4 - g6 ∧ 0 < -a1 * g4 + g4 ∧ 0 < a4 ∧ 0 < a4 - a4 * g6 ∧ 0 < -a1 + a1 * g4 + a4 ∧ 0 < a1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · first | linarith [p3] | nlinarith [p3]
  · first | linarith [p5, dA] | nlinarith [p5, dA]
  · first | linarith [p5] | nlinarith [p5]
  · first | linarith [mul_pos (mul_pos (mul_pos p0 e2) dA) dB, mul_pos (mul_pos (mul_pos e2 dA) dB) dB, mul_pos (mul_pos (mul_pos p5 p5) e2) dB, mul_pos p0 e2, mul_pos (mul_pos (mul_pos p5 e2) dA) dB] | nlinarith [mul_pos (mul_pos (mul_pos p0 e2) dA) dB, mul_pos (mul_pos (mul_pos e2 dA) dB) dB, mul_pos (mul_pos (mul_pos p5 p5) e2) dB, mul_pos p0 e2, mul_pos (mul_pos (mul_pos p5 e2) dA) dB]
  · first | linarith [mul_pos (mul_pos (mul_pos p3 dA) dB) dB, mul_pos (mul_pos (mul_pos p0 p3) dA) dB, mul_pos (mul_pos p5 p5) e2, mul_pos (mul_pos p5 e2) dA, mul_pos (mul_pos p0 p3) dA] | nlinarith [mul_pos (mul_pos (mul_pos p3 dA) dB) dB, mul_pos (mul_pos (mul_pos p0 p3) dA) dB, mul_pos (mul_pos p5 p5) e2, mul_pos (mul_pos p5 e2) dA, mul_pos (mul_pos p0 p3) dA]
  · first | linarith [mul_pos p3 dB] | nlinarith [mul_pos p3 dB]
  · first | linarith [p2] | nlinarith [p2]
  · first | linarith [mul_pos p2 dA] | nlinarith [mul_pos p2 dA]
  · first | linarith [mul_pos (mul_pos (mul_pos p0 p0) e2) dB, mul_pos (mul_pos (mul_pos p0 e2) dB) dB, mul_pos (mul_pos (mul_pos p0 p0) p0) e2, mul_pos (mul_pos (mul_pos p2 dA) dB) dB, mul_pos (mul_pos (mul_pos p0 p2) dA) dB, mul_pos (mul_pos p2 p5) dB] | nlinarith [mul_pos (mul_pos (mul_pos p0 p0) e2) dB, mul_pos (mul_pos (mul_pos p0 e2) dB) dB, mul_pos (mul_pos (mul_pos p0 p0) p0) e2, mul_pos (mul_pos (mul_pos p2 dA) dB) dB, mul_pos (mul_pos (mul_pos p0 p2) dA) dB, mul_pos (mul_pos p2 p5) dB]
  · first | linarith [p0] | nlinarith [p0]


set_option maxHeartbeats 4000000 in
theorem facts08w0 (θ : Fin 6 → ℝ) (hθ : ∀ k, k ≠ 9 → k ≠ 10 → k ≠ 11 → 0 < ineq08 θ k) :
    0 < θ 0 ∧ 0 < θ 1 ∧ 0 < θ 2 ∧ 0 < θ 3 ∧ 0 < θ 4 ∧ 0 < θ 5 ∧ 1 < θ 0 + θ 1 ∧ 1 < θ 2 + θ 3 ∧ 1 < θ 4 + θ 5 ∧
    0 < fc08 θ 0 3 5 1 ∧ 0 < fc08 θ 0 3 5 2 ∧ 0 < fc08 θ 0 3 5 4 ∧
    0 < fc08 θ 1 2 5 0 ∧ 0 < fc08 θ 1 2 5 3 ∧ 0 < fc08 θ 1 2 5 4 ∧
    0 < fc08 θ 1 3 4 0 ∧ 0 < fc08 θ 1 3 4 2 ∧ 0 < fc08 θ 1 3 4 5 ∧
    fc08 θ 1 3 5 0 < 0 ∧ fc08 θ 1 3 5 2 < 0 ∧ fc08 θ 1 3 5 4 < 0 := by
  have p0 := hθ 0 (by decide) (by decide) (by decide); have p1 := hθ 1 (by decide) (by decide) (by decide); have p2 := hθ 2 (by decide) (by decide) (by decide); have p3 := hθ 3 (by decide) (by decide) (by decide); have p4 := hθ 4 (by decide) (by decide) (by decide); have p5 := hθ 5 (by decide) (by decide) (by decide)
  have p6 := hθ 6 (by decide) (by decide) (by decide); have p7 := hθ 7 (by decide) (by decide) (by decide); have p8 := hθ 8 (by decide) (by decide) (by decide)
  have h12 := hθ 12 (by decide) (by decide) (by decide); have h13 := hθ 13 (by decide) (by decide) (by decide); have h14 := hθ 14 (by decide) (by decide) (by decide)
  have h15 := hθ 15 (by decide) (by decide) (by decide); have h16 := hθ 16 (by decide) (by decide) (by decide); have h17 := hθ 17 (by decide) (by decide) (by decide)
  have h18 := hθ 18 (by decide) (by decide) (by decide); have h19 := hθ 19 (by decide) (by decide) (by decide); have h20 := hθ 20 (by decide) (by decide) (by decide)
  have h21 := hθ 21 (by decide) (by decide) (by decide); have h22 := hθ 22 (by decide) (by decide) (by decide); have h23 := hθ 23 (by decide) (by decide) (by decide)
  simp only [ineq08, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Matrix.head_cons] at p0 p1 p2 p3 p4 p5 p6 p7 p8 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23
  have d1 : fc08 θ 0 3 5 6 = θ 1 * θ 3 := by
    simp only [fc08, cdet, cp08]; simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Matrix.head_cons]; ring
  have d2 : fc08 θ 1 2 5 6 = θ 0 * θ 5 := by
    simp only [fc08, cdet, cp08]; simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Matrix.head_cons]; ring
  have d3 : fc08 θ 1 3 4 6 = θ 2 * θ 4 := by
    simp only [fc08, cdet, cp08]; simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Matrix.head_cons]; ring
  have d4 : fc08 θ 1 3 5 6 = -(θ 0 * θ 3 * θ 4 + θ 1 * θ 2 * θ 5) := by
    simp only [fc08, cdet, cp08]; simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Matrix.head_cons]; ring
  have e1 : 0 < fc08 θ 0 3 5 6 := by rw [d1]; positivity
  have e2 : 0 < fc08 θ 1 2 5 6 := by rw [d2]; positivity
  have e3 : 0 < fc08 θ 1 3 4 6 := by rw [d3]; positivity
  have e4 : fc08 θ 1 3 5 6 < 0 := by rw [d4]; have : 0 < θ 0 * θ 3 * θ 4 + θ 1 * θ 2 * θ 5 := by positivity
                                     linarith
  refine ⟨p0, p1, p2, p3, p4, p5, by linarith, by linarith, by linarith, ?_⟩
  refine ⟨(pos_iff_pos_of_mul_pos h12).mpr e1, (pos_iff_pos_of_mul_pos h13).mpr e1,
    (pos_iff_pos_of_mul_pos h14).mpr e1, (pos_iff_pos_of_mul_pos h15).mpr e2,
    (pos_iff_pos_of_mul_pos h16).mpr e2, (pos_iff_pos_of_mul_pos h17).mpr e2,
    (pos_iff_pos_of_mul_pos h18).mpr e3, (pos_iff_pos_of_mul_pos h19).mpr e3,
    (pos_iff_pos_of_mul_pos h20).mpr e3, (neg_iff_neg_of_mul_pos h21).mpr e4,
    (neg_iff_neg_of_mul_pos h22).mpr e4, (neg_iff_neg_of_mul_pos h23).mpr e4⟩

theorem facts08w (θ : Fin 6 → ℝ) (hθ : ∀ k, k ≠ 9 → k ≠ 10 → k ≠ 11 → 0 < ineq08 θ k) (hga : 0 ≤ gWa θ) (hgb : 0 ≤ gWb θ) :
    0 < θ 0 ∧ 0 < θ 1 ∧ 0 < θ 2 ∧ 0 < θ 3 ∧ 0 < θ 4 ∧ 0 < θ 5 ∧ 1 < θ 0 + θ 1 ∧ 1 < θ 2 + θ 3 ∧ 1 < θ 4 + θ 5 ∧
    0 < fc08 θ 0 3 5 1 ∧ 0 < fc08 θ 0 3 5 2 ∧ 0 < fc08 θ 0 3 5 4 ∧
    0 < fc08 θ 1 2 5 0 ∧ 0 < fc08 θ 1 2 5 3 ∧ 0 < fc08 θ 1 2 5 4 ∧
    0 < fc08 θ 1 3 4 0 ∧ 0 < fc08 θ 1 3 4 2 ∧ 0 < fc08 θ 1 3 4 5 ∧
    fc08 θ 1 3 5 0 < 0 ∧ fc08 θ 1 3 5 2 < 0 ∧ fc08 θ 1 3 5 4 < 0 :=
  facts08w0 θ hθ

/-- `[b c] < 0` needs no sign on `gWa`, `gWb` (facets only). -/
theorem gWU_neg_w0 (θ : Fin 6 → ℝ) (hθ : ∀ k, k ≠ 9 → k ≠ 10 → k ≠ 11 → 0 < ineq08 θ k) : gWU θ < 0 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, f10, -, -⟩ := facts08w0 θ hθ
  simp only [fc08, cdet, cp08, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
    Matrix.head_cons] at f10
  unfold gWU; nlinarith [f10]

set_option maxHeartbeats 4000000 in
theorem common08w (θ : Fin 6 → ℝ) (hθ : ∀ k, k ≠ 9 → k ≠ 10 → k ≠ 11 → 0 < ineq08 θ k) (hga : 0 ≤ gWa θ) (hgb : 0 ≤ gWb θ) :
    0 < (θ 0) ∧ 0 < (θ 1) ∧ 0 < (θ 2) ∧ 0 < (θ 3) ∧ 0 < (θ 4) ∧ 0 < (θ 5) ∧ 0 < (θ 0) + (θ 1) - 1 ∧ 0 < (θ 2) + (θ 3) - 1 ∧ 0 < (θ 4) + (θ 5) - 1 ∧ 0 ≤ -(θ 0) + (θ 0) * (θ 3) - (θ 1) * (θ 2) + (θ 2) ∧ 0 ≤ (θ 0) * (θ 4) + (θ 1) - (θ 1) * (θ 5) - (θ 4) ∧ 0 < (θ 0) * (θ 3) * (θ 4) + (θ 1) * (θ 2) * (θ 5) + (θ 1) * (θ 3) - (θ 1) * (θ 5) - (θ 3) * (θ 4) ∧ 0 < (θ 0) * (θ 3) + (θ 1) * (θ 3) - (θ 3) ∧ 0 < -(θ 1) + (θ 1) * (θ 2) + (θ 1) * (θ 3) ∧ 0 < (θ 0) * (θ 5) + (θ 1) * (θ 5) - (θ 5) ∧ 0 < -(θ 0) * (θ 3) + (θ 0) * (θ 3) * (θ 4) + (θ 0) * (θ 5) + (θ 1) * (θ 2) * (θ 5) - (θ 2) * (θ 5) ∧ 0 < -(θ 0) + (θ 0) * (θ 4) + (θ 0) * (θ 5) ∧ 0 < (θ 2) * (θ 4) + (θ 3) * (θ 4) - (θ 4) ∧ 0 < -(θ 2) + (θ 2) * (θ 4) + (θ 2) * (θ 5) ∧ 0 < (θ 0) * (θ 3) * (θ 4) - (θ 0) * (θ 4) - (θ 1) * (θ 2) + (θ 1) * (θ 2) * (θ 5) + (θ 2) * (θ 4) ∧ 0 < (θ 0) * (θ 3) * (θ 4) + (θ 1) * (θ 2) * (θ 5) + (θ 1) * (θ 3) - (θ 1) * (θ 5) - (θ 3) * (θ 4) ∧ 0 < -(θ 0) * (θ 3) + (θ 0) * (θ 3) * (θ 4) + (θ 0) * (θ 5) + (θ 1) * (θ 2) * (θ 5) - (θ 2) * (θ 5) ∧ 0 < (θ 0) * (θ 3) * (θ 4) - (θ 0) * (θ 4) - (θ 1) * (θ 2) + (θ 1) * (θ 2) * (θ 5) + (θ 2) * (θ 4) := by
  obtain ⟨p0, p1, p2, p3, p4, p5, q6, q7, q8, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12⟩ :=
    facts08w θ hθ hga hgb
  simp only [fc08, cdet, cp08, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
    Matrix.head_cons] at f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12
  unfold gWa at hga; unfold gWb at hgb
  refine ⟨p0, p1, p2, p3, p4, p5, by linarith, by linarith, by linarith, by linarith, by linarith, by linarith, by linarith, by linarith, by linarith, by linarith, by linarith, by linarith, by linarith, by linarith, by linarith, by linarith, by linarith⟩


set_option maxHeartbeats 4000000 in
theorem q2polyw (θ : Fin 6 → ℝ) (hθ : ∀ k, k ≠ 9 → k ≠ 10 → k ≠ 11 → 0 < ineq08 θ k) (hga : 0 ≤ gWa θ) (hgb : 0 ≤ gWb θ) (h6 : 1 < θ 5) :
    0 < θ 3 * θ 4 * (θ 0 - 1) + θ 1 * (θ 2 - 1) * (θ 5 - 1) := by
  obtain ⟨p0, p1, p2, p3, p4, p5, e1, e2, e3, ga, gb, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12⟩ :=
    common08w θ hθ hga hgb
  have dA : 0 < -1 + θ 5 := by linarith
  have dB : 0 < -1 + θ 0 := by
    have h : 0 < θ 4 * (θ 0 - 1) := by nlinarith [mul_pos p1 dA, gb]
    linarith [(pos_iff_pos_of_mul_pos h).mp p4]
  nlinarith [mul_pos p3 p4, mul_pos (mul_pos p3 p4) dB, mul_pos p1 dA, mul_pos p2 p1,
    mul_pos (mul_pos p1 p2) dA, mul_pos p1 dA, mul_pos p0 dA, mul_pos p3 dA, mul_pos p4 dA]



/-- The density curve `θ + t (e₃ − e₅)`: `κ_a`, `κ_b` grow linearly, so a weak point is a limit of strict ones. -/
def curve08 (θ : Fin 6 → ℝ) (t : ℝ) : Fin 6 → ℝ := fun k => if k = 3 then θ 3 + t else if k = 5 then θ 5 - t else θ k

theorem gWa_curve (θ : Fin 6 → ℝ) (t : ℝ) : gWa (curve08 θ t) = gWa θ + t * θ 0 := by
  simp [gWa, curve08]; ring

theorem gWb_curve (θ : Fin 6 → ℝ) (t : ℝ) : gWb (curve08 θ t) = gWb θ + t * θ 1 := by
  simp [gWb, curve08]; ring

/-- `[b c] < 0` is automatic in the normal form (from the facets alone). -/
theorem gWU_neg_w (θ : Fin 6 → ℝ) (hθ : ∀ k, k ≠ 9 → k ≠ 10 → k ≠ 11 → 0 < ineq08 θ k)
    (hga : 0 ≤ gWa θ) (hgb : 0 ≤ gWb θ) : gWU θ < 0 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, f10, -, -⟩ := facts08w θ hθ hga hgb
  simp only [fc08, cdet, cp08, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
    Matrix.head_cons] at f10
  unfold gWU; nlinarith [f10]

end Type08Sp
end Minimality
