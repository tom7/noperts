module

public import Mathlib

@[expose] public section

set_option autoImplicit true
set_option relaxedAutoImplicit true

/-! Lemma PX (TQPROOF24.md, third pass): pure real algebra.  Indices a,b,c = 0,1,2 of the Gram
matrix `G` (with `G t = h2 1`); `th = a3 / s3` is the first coordinate of `X = (th, 1 - th, 0)`. -/

namespace Minimality.T24.PX

/-- The PX identity over the entries of `G` (`Gcc` does not occur). -/
theorem px_id (Gaa Gab Gac Gbb Gbc ta tb tc h2 a3 b3 c3 th : ℝ)
    (hs : ta + tb + tc = 1)
    (r0 : Gaa * ta + Gab * tb + Gac * tc = h2)
    (r1 : Gab * ta + Gbb * tb + Gbc * tc = h2)
    (hth : a3 = th * (a3 + b3 + c3 - 1)) :
    tb * ((c3 * ta - a3 * tc) * ((Gaa * th + Gab * (1 - th)) - (Gab * th + Gbb * (1 - th)))
      + tc * (a3 * (Gaa * th + Gab * (1 - th)) + (b3 - 1) * (Gab * th + Gbb * (1 - th))
        + c3 * (Gac * th + Gbc * (1 - th))))
    = -h2 * (c3 * (1 - th - tb) - tc * (b3 + c3 - 1))
      + ((c3 * ta - a3 * tc) + tc * (1 - b3) + tb * c3) *
        (Gab * ((1 - th) * ta - th * tb) + Gbc * tc * (1 - th)) := by
  have hta : ta = 1 - tb - tc := by linarith
  subst hta
  linear_combination (tb * c3 * th) * r0
    + (-((c3 * (1 - tb - tc) - a3 * tc) + tc * (1 - b3)) * (1 - th)) * r1 + (h2 * tc) * hth

/-- **Lemma PX**, entry form: `alpha (z0 - z2) + t_c (z3 - z2) < 0` at `X`, where the two forms are
`(e_a - e_b)^T G X` and `(y3 - e_b)^T G X`. -/
theorem px_neg (Gaa Gab Gac Gbb Gbc ta tb tc h2 a3 b3 c3 th : ℝ)
    (hta0 : 0 < ta) (htb : 0 < tb) (htc : 0 < tc)
    (hs : ta + tb + tc = 1) (hh : 0 < h2)
    (r0 : Gaa * ta + Gab * tb + Gac * tc = h2)
    (r1 : Gab * ta + Gbb * tb + Gbc * tc = h2)
    (hab : Gab ≤ 0) (hbc : Gbc ≤ 0) (hb3 : b3 < 1) (hc3 : 0 < c3)
    (ha3 : 0 < a3) (ha3s : a3 < a3 + b3 + c3 - 1)
    (hth : a3 = th * (a3 + b3 + c3 - 1))
    (hta : th < ta) (hal : a3 * tc ≤ c3 * ta) :
    (c3 * ta - a3 * tc) * ((Gaa * th + Gab * (1 - th)) - (Gab * th + Gbb * (1 - th)))
      + tc * (a3 * (Gaa * th + Gab * (1 - th)) + (b3 - 1) * (Gab * th + Gbb * (1 - th))
        + c3 * (Gac * th + Gbc * (1 - th))) < 0 := by
  have hid := px_id Gaa Gab Gac Gbb Gbc ta tb tc h2 a3 b3 c3 th hs r0 r1 hth
  have hs3 : 0 < a3 + b3 + c3 - 1 := by linarith
  have hth0 : 0 < th := by
    by_contra h
    have h' := not_lt.1 h
    nlinarith [mul_nonneg (neg_nonneg.2 h') hs3.le]
  have hth1 : th < 1 := by
    by_contra h
    have h' := not_lt.1 h
    nlinarith
  have hV : 0 < c3 * (1 - th - tb) - tc * (b3 + c3 - 1) := by
    have h1 : tc < 1 - th - tb := by linarith
    nlinarith [mul_pos hc3 (sub_pos.2 h1), mul_pos htc (sub_pos.2 hb3)]
  have hK : 0 < (c3 * ta - a3 * tc) + tc * (1 - b3) + tb * c3 := by
    nlinarith [mul_pos htc (sub_pos.2 hb3), mul_pos htb hc3]
  have h1 : 0 ≤ (1 - th) * ta - th * tb := by
    nlinarith [mul_pos htb hth0]
  have h2' : Gab * ((1 - th) * ta - th * tb) + Gbc * tc * (1 - th) ≤ 0 := by
    have := mul_nonpos_of_nonpos_of_nonneg hab h1
    have := mul_nonpos_of_nonpos_of_nonneg hbc (mul_pos htc (sub_pos.2 hth1)).le
    nlinarith
  by_contra hL
  have hL' := not_lt.1 hL
  have h3 := mul_nonneg htb.le hL'
  rw [hid] at h3
  linarith [mul_nonpos_of_nonneg_of_nonpos hK.le h2', mul_pos hh hV]

/-- **Lemma PX**, matrix form (as in the report): `G` symmetric, `G t = h2 1`, `G_ab, G_bc <= 0`
(`G_ac` free), `b3 < 1`, `0 < a3 < s3`, `th = a3 / s3 < t_a`, `alpha >= 0`;
`X = (th, 1 - th, 0)`, forms `e0 - e1` and `y3 - e1`. -/
theorem px_matrix (G : Matrix (Fin 3) (Fin 3) ℝ) (hG : G.IsSymm) (t : Fin 3 → ℝ) (h2 : ℝ)
    (ht : G.mulVec t = fun _ => h2) (ht0 : 0 < t 0) (ht1 : 0 < t 1) (ht2 : 0 < t 2)
    (hs : t 0 + t 1 + t 2 = 1) (hh : 0 < h2) (hab : G 0 1 ≤ 0) (hbc : G 1 2 ≤ 0)
    (a3 b3 c3 th : ℝ) (hb3 : b3 < 1) (hc3 : 0 < c3) (ha3 : 0 < a3)
    (ha3s : a3 < a3 + b3 + c3 - 1) (hth : a3 = th * (a3 + b3 + c3 - 1))
    (hta : th < t 0) (hal : a3 * t 2 ≤ c3 * t 0) :
    (c3 * t 0 - a3 * t 2) * (![1, -1, 0] ⬝ᵥ G.mulVec ![th, 1 - th, 0])
      + t 2 * (![a3, b3 - 1, c3] ⬝ᵥ G.mulVec ![th, 1 - th, 0]) < 0 := by
  have s01 : G 1 0 = G 0 1 := by simpa using (Matrix.IsSymm.apply hG 0 1)
  have s02 : G 2 0 = G 0 2 := by simpa using (Matrix.IsSymm.apply hG 0 2)
  have s12 : G 2 1 = G 1 2 := by simpa using (Matrix.IsSymm.apply hG 1 2)
  have r0 := congrFun ht 0
  have r1 := congrFun ht 1
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_three, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at r0 r1 ⊢
  rw [s01] at r1
  have := px_neg (G 0 0) (G 0 1) (G 0 2) (G 1 1) (G 1 2) (t 0) (t 1) (t 2) h2 a3 b3 c3 th ht0 ht1
    ht2 hs hh r0 r1 hab hbc hb3 hc3 ha3 ha3s hth hta hal
  rw [s01, s02, s12]
  linarith

/-- **Corollary**: a negative nonnegative combination gives `z0 < z2` or `z3 < z2`
(`alpha >= 0`, `t_c > 0`; wiring: `z i = <x i, X>`). -/
theorem px_cor {z0 z2 z3 al tc : ℝ} (hal : 0 ≤ al) (htc : 0 < tc)
    (h : al * (z0 - z2) + tc * (z3 - z2) < 0) : z0 < z2 ∨ z3 < z2 := by
  by_contra hc
  push Not at hc
  nlinarith [mul_nonneg hal (sub_nonneg.2 hc.1), mul_nonneg htc.le (sub_nonneg.2 hc.2)]

end Minimality.T24.PX
