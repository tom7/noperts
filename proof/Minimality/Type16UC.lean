module

public import Minimality.Type16UB

@[expose] public section


/-!
# U1: the TT leaf `LBE (6,1,4)` (`FreeTT B E G G 6 1 4`) and its σ-image `LAE (0,2,4)`

Leaf literal: `φE(1,5) > 0`, i.e. `fE(1) < fE(5)`.  This alone implies (type 16, normal form) `fE(5) < fE(3)`,
`fE(1) < fE(3)`, `fB(4) < fB(0)` and that `2` is inside the triangle; the other literals of the tree
(`ζ < 0`, `φF(0,6) ≤ 0`) are not needed.  Hypothesis `hdep`: distinct depths of `6, 1, 4` along every view in the
line of the planes of `B` and `E` (the `DepthOK` ties are leftover).
-/

set_option autoImplicit true
set_option linter.unusedVariables false
open scoped RealInnerProductSpace
open Finset Filter

namespace Minimality
namespace H16U
open V2

variable {x : Fin 7 → ℝ³}

theorem nf_tt_g1 (N : NF16 x) (h : N.q * N.d < (N.p + N.r - 1) * (N.g - 1)) : 1 < N.p + N.r := by
  have ha := N.ha; have hb := N.hb; have hg := N.hg; have hd := N.hd; have hp := N.hp; have hq := N.hq
  have hr := N.hr; have hab := N.hab; have hgd := N.hgd; have t046_5 := N.t046_5; have t0246 := N.t0246
  have t0146 := N.t0146; have t024_1 := N.t024_1; have t146_2 := N.t146_2; have t245_6 := N.t245_6
  have t145_0 := N.t145_0; have tB125 := N.tB125
  by_contra hc
  push_neg at hc
  have hg1 : N.g < 1 := by nlinarith [mul_pos hq hd]
  nlinarith [mul_pos hq hd]

theorem nf_tt_c1 (N : NF16 x) (h : N.q * N.d < (N.p + N.r - 1) * (N.g - 1)) : 1 < N.p := by
  have G := nf_tt_g1 N h
  have ha := N.ha; have hb := N.hb; have hg := N.hg; have hd := N.hd; have hp := N.hp; have hq := N.hq
  have hr := N.hr; have hab := N.hab; have hgd := N.hgd; have t046_5 := N.t046_5; have t0246 := N.t0246
  have t0146 := N.t0146; have t024_1 := N.t024_1; have t146_2 := N.t146_2; have t245_6 := N.t245_6
  have t145_0 := N.t145_0; have tB125 := N.tB125
  by_contra hc
  push_neg at hc
  nlinarith [mul_pos hq hd, mul_pos hp hq, mul_pos hq hr]

theorem nf_tt_c3 (N : NF16 x) (h : N.q * N.d < (N.p + N.r - 1) * (N.g - 1)) :
    N.p * (N.q * (1 - N.a) + (N.p + N.r - 1) * N.b) +
      (N.a - N.p) * (N.q * (1 - N.d) + (N.p + N.r - 1) * N.g) < 0 := by
  have G := nf_tt_g1 N h
  have c1 := nf_tt_c1 N h
  have ha := N.ha; have hb := N.hb; have hg := N.hg; have hd := N.hd; have hp := N.hp; have hq := N.hq
  have hr := N.hr; have hab := N.hab; have hgd := N.hgd; have t046_5 := N.t046_5; have t0246 := N.t0246
  have t0146 := N.t0146; have t024_1 := N.t024_1; have t146_2 := N.t146_2; have t245_6 := N.t245_6
  have t145_0 := N.t145_0; have tB125 := N.tB125
  nlinarith [mul_pos hq hd, mul_pos hp hq, mul_pos hq hr, mul_pos ha hb, mul_pos hg hd]

/-- **TT leaf `LBE (6,1,4)`.** -/
theorem h16u_tt_LBE_cell (T : Type16 x) (h : T.ff 4 (x 1) < T.ff 4 (x 5))
    {r : ℝ³} (hr : r ≠ 0) (hPr : ⟪T.fN 1, r⟫ = 0) (hQr : ⟪T.fN 4, r⟫ = 0) (hd : DepthOK x r 6 1 4) :
    HasLexCellAt (univ.image x) r := by
  obtain ⟨P⟩ := exists_par T
  have hq := P.N.hq
  have he3 := P.he3
  have hb0 := P.hb0
  set N := P.N
  set s : ℝ := (N.p + N.r - 1) / N.q with hs
  have hsq : s * N.q = N.p + N.r - 1 := by rw [hs]; field_simp
  -- the literal in the parameters
  have hlit : N.q * N.d < (N.p + N.r - 1) * (N.g - 1) := by
    rw [P.eE1, P.eE5] at h
    have h' : 1 + s < 1 - N.d + s * N.g := by
      by_contra hc; push_neg at hc
      have := mul_le_mul_of_nonpos_left hc he3.le
      linarith
    have : N.d < s * (N.g - 1) := by linarith
    have := mul_lt_mul_of_pos_left this hq
    have e : N.q * (s * (N.g - 1)) = (N.p + N.r - 1) * (N.g - 1) := by rw [← hsq]; ring
    linarith
  have G := nf_tt_g1 N hlit
  have c1 := nf_tt_c1 N hlit
  have c3 := nf_tt_c3 N hlit
  have hspos : 0 < s := by
    have : 0 < s * N.q := by rw [hsq]; linarith
    exact pos_of_mul_pos_left this hq.le
  refine freeTT_cell T (P := 1) (Q := 4) (eP := 6) (eQ := 6) (w := 6) (a := 1) (b := 4) ?_ hr hPr hQr hd
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, ?_⟩
  intro j hj6 hj1 hj4
  fin_cases j
  · -- j = 0: Q-side
    refine Or.inr (Or.inr ⟨by decide, by decide, ?_, by decide⟩)
    show T.ff 1 (x 4) < T.ff 1 (x 0)
    rw [P.eB4, P.eB0]; nlinarith
  · exact absurd rfl hj1
  · -- j = 2: inside
    refine Or.inl ⟨by decide, by decide, ?_⟩
    show T.ff 4 (x 2) * T.ff 1 (x 4) + T.ff 1 (x 2) * T.ff 4 (x 1) < T.ff 4 (x 1) * T.ff 1 (x 4)
    rw [P.eE2, P.eE1, P.eB4, P.eB2]
    have e : N.p * (1 - N.a + s * N.b) + (N.a - N.p) * (1 - N.d + s * N.g) < 0 := by
      have := c3
      have h2 : N.q * (N.p * (1 - N.a + s * N.b) + (N.a - N.p) * (1 - N.d + s * N.g)) < 0 := by
        have : N.q * (N.p * (1 - N.a + s * N.b) + (N.a - N.p) * (1 - N.d + s * N.g)) =
            N.p * (N.q * (1 - N.a) + (N.p + N.r - 1) * N.b) +
              (N.a - N.p) * (N.q * (1 - N.d) + (N.p + N.r - 1) * N.g) := by
          rw [← hsq]; ring
        rw [this]; exact c3
      by_contra hc; push_neg at hc; nlinarith
    have hp := N.hp
    have : 0 < P.e3 * P.b0 := mul_pos_of_neg_of_neg he3 hb0
    nlinarith [mul_pos this (neg_pos.2 e)]
  · -- j = 3: P-side
    refine Or.inr (Or.inl ⟨by decide, by decide, ?_, by decide⟩)
    show T.ff 4 (x 1) < T.ff 4 (x 3)
    rw [P.eE1, P.eE3]
    have : 0 < s * N.g - N.d := by
      have h3 : N.q * N.d < (N.p + N.r - 1) * N.g := by nlinarith [N.hg]
      have : N.d < s * N.g := by
        by_contra hc; push_neg at hc
        have := mul_le_mul_of_nonneg_left hc hq.le
        have e : N.q * (s * N.g) = (N.p + N.r - 1) * N.g := by rw [← hsq]; ring
        linarith
      linarith
    nlinarith [mul_neg_of_neg_of_pos he3 this]
  · exact absurd rfl hj4
  · -- j = 5: P-side
    exact Or.inr (Or.inl ⟨by decide, by decide, h, by decide⟩)
  · exact absurd rfl hj6

end H16U
end Minimality
