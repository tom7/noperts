module

public import Minimality.Type08S.L2.K92A

@[expose] public section

set_option maxHeartbeats 1000000

set_option autoImplicit true
set_option relaxedAutoImplicit true
namespace Minimality.Type08Sp.C2

set_option maxHeartbeats 6400000 in
theorem k92_c_fL (u v m x y : ℝ) (hu : 0 < u) (hv : 0 < v) (hm : 0 < m) (hx : 0 < x) (hy : 0 < y) (_hWN : 0 < u^2*x + u^2*y + u*v*x + u*v*y^2 + u*v*y + 2*u*x + 2*u*y - v^2*x*y - v*x*y + v*x + v*y + x + y) (hl : 0 ≤ (1+v)*x - u*y) (_hlK : 0 ≤ ((1+v)*x - u*y)*(v^2*x*y + v*x*y - (u+v+1)*(x+y))) (_hsig : 0 < m*(u+v+1) - v) :
    0 < m*u^2*x + m*u^2*y - m*u*v*x*y + m*u*v*x + m*u*v*y + 2*m*u*x + 2*m*u*y + m*v^2*x^2 + m*v*x^2 + m*v*x + m*v*y + m*x + m*y + v^2*x*y := by
  linear_combination 1 * (mul_pos hm hx) + 1 * (mul_pos hm hy) + 2 * (mul_pos (mul_pos hu hm) hx) + 2 * (mul_pos (mul_pos hu hm) hy) + 1 * (mul_pos (mul_pos hv hm) hx) + 1 * (mul_pos (mul_pos hv hm) hy) + 1 * (mul_pos (mul_pos (mul_pos hu hu) hm) hx) + 1 * (mul_pos (mul_pos (mul_pos hu hu) hm) hy) + 1 * (mul_pos (mul_pos (mul_pos hu hv) hm) hx) + 1 * (mul_pos (mul_pos (mul_pos hu hv) hm) hy) + 1 * (mul_pos (mul_pos (mul_pos hv hv) hx) hy) + 1 * (mul_nonneg ((mul_pos (mul_pos hv hm) hx)).le hl)


set_option maxHeartbeats 6400000 in
theorem k92_c_fF2 (u v m x y : ℝ) (hu : 0 < u) (hv : 0 < v) (hm : 0 < m) (hx : 0 < x) (hy : 0 < y) (_hWN : 0 < u^2*x + u^2*y + u*v*x + u*v*y^2 + u*v*y + 2*u*x + 2*u*y - v^2*x*y - v*x*y + v*x + v*y + x + y) (hl : 0 ≤ (1+v)*x - u*y) (_hlK : 0 ≤ ((1+v)*x - u*y)*(v^2*x*y + v*x*y - (u+v+1)*(x+y))) (_hsig : 0 < m*(u+v+1) - v) :
    0 < m*u^2*v*x^2 + m*u^2*v*x*y + m*u^2*x*y + m*u^2*y^2 + m*u*v^2*x^2 + m*u*v^2*x*y + 2*m*u*v*x^2 - m*u*v*x*y^2 + 3*m*u*v*x*y + m*u*v*y^2 + 2*m*u*x*y + 2*m*u*y^2 + m*v^2*x^2*y + m*v^2*x^2 + m*v^2*x*y + m*v*x^2*y + m*v*x^2 + 2*m*v*x*y + m*v*y^2 + m*x*y + m*y^2 + v^3*x^2*y + v^2*x^2*y + v^2*x*y^2 := by
  linear_combination 1 * (mul_pos (mul_pos hm hx) hy) + 1 * (mul_pos (mul_pos hm hy) hy) + 2 * (mul_pos (mul_pos (mul_pos hu hm) hx) hy) + 2 * (mul_pos (mul_pos (mul_pos hu hm) hy) hy) + 1 * (mul_pos (mul_pos (mul_pos hv hm) hx) hx) + 2 * (mul_pos (mul_pos (mul_pos hv hm) hx) hy) + 1 * (mul_pos (mul_pos (mul_pos hv hm) hy) hy) + 1 * (mul_pos (mul_pos (mul_pos (mul_pos hu hu) hm) hx) hy) + 1 * (mul_pos (mul_pos (mul_pos (mul_pos hu hu) hm) hy) hy) + 2 * (mul_pos (mul_pos (mul_pos (mul_pos hu hv) hm) hx) hx) + 3 * (mul_pos (mul_pos (mul_pos (mul_pos hu hv) hm) hx) hy) + 1 * (mul_pos (mul_pos (mul_pos (mul_pos hu hv) hm) hy) hy) + 1 * (mul_pos (mul_pos (mul_pos (mul_pos hv hv) hm) hx) hx) + 1 * (mul_pos (mul_pos (mul_pos (mul_pos hv hv) hm) hx) hy) + 1 * (mul_pos (mul_pos (mul_pos (mul_pos hv hv) hx) hx) hy) + 1 * (mul_pos (mul_pos (mul_pos (mul_pos hv hv) hx) hy) hy) + 1 * (mul_pos (mul_pos (mul_pos (mul_pos (mul_pos hu hu) hv) hm) hx) hx) + 1 * (mul_pos (mul_pos (mul_pos (mul_pos (mul_pos hu hu) hv) hm) hx) hy) + 1 * (mul_pos (mul_pos (mul_pos (mul_pos (mul_pos hu hv) hv) hm) hx) hx) + 1 * (mul_pos (mul_pos (mul_pos (mul_pos (mul_pos hu hv) hv) hm) hx) hy) + 1 * (mul_pos (mul_pos (mul_pos (mul_pos (mul_pos hv hv) hv) hx) hx) hy) + 1 * (mul_nonneg ((mul_pos (mul_pos (mul_pos hv hm) hx) hy)).le hl)


set_option maxHeartbeats 6400000 in
theorem k92_c_fzA (u v m x y : ℝ) (hu : 0 < u) (hv : 0 < v) (hm : 0 < m) (hx : 0 < x) (hy : 0 < y) (_hWN : 0 < u^2*x + u^2*y + u*v*x + u*v*y^2 + u*v*y + 2*u*x + 2*u*y - v^2*x*y - v*x*y + v*x + v*y + x + y) (hl : 0 ≤ (1+v)*x - u*y) (_hlK : 0 ≤ ((1+v)*x - u*y)*(v^2*x*y + v*x*y - (u+v+1)*(x+y))) (hsig : 0 < m*(u+v+1) - v) :
    0 < m*u^2*x*y + m*u^2*y^2 + m*u*v^2*x^2 - m*u*v^2*x*y^2 + m*u*v^2*x*y + m*u*v*x^2 - m*u*v*x*y^2 + 3*m*u*v*x*y + 2*m*u*v*y^2 + 2*m*u*x*y + 2*m*u*y^2 + m*v^3*x^2*y + m*v^3*x^2 + m*v^3*x*y + 2*m*v^2*x^2*y + 2*m*v^2*x^2 + 3*m*v^2*x*y + m*v^2*y^2 + m*v*x^2*y + m*v*x^2 + 3*m*v*x*y + 2*m*v*y^2 + m*x*y + m*y^2 - u*v*x*y - u*v*y^2 + v^3*x*y^2 + v^2*x*y^2 - v^2*x*y - v^2*y^2 - v*x*y - v*y^2 := by
  linear_combination 1 * (mul_pos (mul_pos (mul_pos hv hm) hx) hx) + 1 * (mul_pos (mul_pos (mul_pos hv hm) hx) hy) + 1 * (mul_pos (mul_pos (mul_pos (mul_pos hu hv) hm) hx) hx) + 1 * (mul_pos (mul_pos (mul_pos (mul_pos hu hv) hm) hx) hy) + 2 * (mul_pos (mul_pos (mul_pos (mul_pos hv hv) hm) hx) hx) + 2 * (mul_pos (mul_pos (mul_pos (mul_pos hv hv) hm) hx) hy) + 1 * (mul_pos (mul_pos (mul_pos (mul_pos hv hv) hx) hy) hy) + 1 * (mul_pos (mul_pos (mul_pos (mul_pos (mul_pos hu hv) hv) hm) hx) hx) + 1 * (mul_pos (mul_pos (mul_pos (mul_pos (mul_pos hu hv) hv) hm) hx) hy) + 1 * (mul_pos (mul_pos (mul_pos (mul_pos (mul_pos hv hv) hv) hm) hx) hx) + 1 * (mul_pos (mul_pos (mul_pos (mul_pos (mul_pos hv hv) hv) hm) hx) hy) + 1 * (mul_pos (mul_pos (mul_pos (mul_pos (mul_pos hv hv) hv) hx) hy) hy) + 1 * (mul_nonneg ((mul_pos (mul_pos (mul_pos hv hm) hx) hy)).le hl) + 1 * (mul_nonneg ((mul_pos (mul_pos (mul_pos (mul_pos hv hv) hm) hx) hy)).le hl) + 1 * (mul_pos (mul_pos hx hy) hsig) + 1 * (mul_pos (mul_pos hy hy) hsig) + 1 * (mul_pos (mul_pos (mul_pos hu hx) hy) hsig) + 1 * (mul_pos (mul_pos (mul_pos hu hy) hy) hsig) + 1 * (mul_pos (mul_pos (mul_pos hv hx) hy) hsig) + 1 * (mul_pos (mul_pos (mul_pos hv hy) hy) hsig)


set_option maxHeartbeats 6400000 in
theorem k92_c_fzB (u v m x y : ℝ) (hu : 0 < u) (hv : 0 < v) (hm : 0 < m) (hx : 0 < x) (hy : 0 < y) (hWN : 0 < u^2*x + u^2*y + u*v*x + u*v*y^2 + u*v*y + 2*u*x + 2*u*y - v^2*x*y - v*x*y + v*x + v*y + x + y) (hl : 0 ≤ (1+v)*x - u*y) (_hlK : 0 ≤ ((1+v)*x - u*y)*(v^2*x*y + v*x*y - (u+v+1)*(x+y))) (_hsig : 0 < m*(u+v+1) - v) :
    0 < m*u^3*x^2 + m*u^3*x*y + m*u^2*v*x^2 + m*u^2*v*x*y^2 + m*u^2*v*x*y + 2*m*u^2*x^2 + 2*m*u^2*x*y - m*u*v^2*x^2*y - m*u*v*x^2*y + m*u*v*x^2 + m*u*v*x*y + m*u*x^2 + m*u*x*y + u^2*x*y + u^2*y^2 + u*v^2*x^2*y - u*v^2*x*y^2 + u*v*x^2*y + u*v*x*y + u*v*y^2 + 2*u*x*y + 2*u*y^2 + v^3*x^2*y + 2*v^2*x^2*y + v*x^2*y + v*x*y + v*y^2 + x*y + y^2 := by
  linear_combination 1 * (mul_pos hx hy) + 1 * (mul_pos hy hy) + 2 * (mul_pos (mul_pos hu hx) hy) + 2 * (mul_pos (mul_pos hu hy) hy) + 1 * (mul_pos (mul_pos hv hx) hy) + 1 * (mul_pos (mul_pos hv hy) hy) + 1 * (mul_pos (mul_pos (mul_pos hu hu) hx) hy) + 1 * (mul_pos (mul_pos (mul_pos hu hu) hy) hy) + 1 * (mul_pos (mul_pos (mul_pos hu hv) hx) hy) + 1 * (mul_pos (mul_pos (mul_pos hu hv) hy) hy) + 1 * (mul_pos (mul_pos (mul_pos hv hx) hx) hy) + 1 * (mul_pos (mul_pos (mul_pos (mul_pos hu hv) hx) hx) hy) + 1 * (mul_pos (mul_pos (mul_pos (mul_pos hv hv) hx) hx) hy) + 1 * (mul_pos (mul_pos (mul_pos (mul_pos (mul_pos hu hv) hv) hx) hx) hy) + 1 * (mul_pos (mul_pos (mul_pos hu hm) hx) hWN) + 1 * (mul_nonneg ((mul_pos (mul_pos (mul_pos hv hv) hx) hy)).le hl)


set_option maxHeartbeats 6400000 in
theorem k92_c_TB (u v x y : ℝ) (hu : 0 < u) (hv : 0 < v) (hx : 0 < x) (hy : 0 < y) (_hWN : 0 < u^2*x + u^2*y + u*v*x + u*v*y^2 + u*v*y + 2*u*x + 2*u*y - v^2*x*y - v*x*y + v*x + v*y + x + y) (hl : 0 ≤ -u*y + x*(v + 1)) (_hlK : 0 ≤ (-u*y + x*(v + 1))*(v^2*x*y + v*x*y - (x + y)*(u + v + 1))) :
    0 < u^2*x + u^2*y - u*v^2*x*y - u*v*x*y + 2*u*v*x + 2*u*v*y + 2*u*x + 2*u*y + v^3*x^2 + 2*v^2*x^2 + v^2*x + v^2*y + v*x^2 + 2*v*x + 2*v*y + x + y := by
  linear_combination 1 * hx + 1 * hy + 2 * (mul_pos hu hx) + 2 * (mul_pos hu hy) + 2 * (mul_pos hv hx) + 2 * (mul_pos hv hy) + 1 * (mul_pos (mul_pos hu hu) hx) + 1 * (mul_pos (mul_pos hu hu) hy) + 2 * (mul_pos (mul_pos hu hv) hx) + 2 * (mul_pos (mul_pos hu hv) hy) + 1 * (mul_pos (mul_pos hv hv) hx) + 1 * (mul_pos (mul_pos hv hv) hy) + 1 * (mul_nonneg ((mul_pos hv hx)).le hl) + 1 * (mul_nonneg ((mul_pos (mul_pos hv hv) hx)).le hl)


set_option maxHeartbeats 6400000 in
theorem k92_c_TP (u v x y : ℝ) (hu : 0 < u) (hv : 0 < v) (hx : 0 < x) (hy : 0 < y) (_hWN : 0 < u^2*x + u^2*y + u*v*x + u*v*y^2 + u*v*y + 2*u*x + 2*u*y - v^2*x*y - v*x*y + v*x + v*y + x + y) (hl : 0 ≤ -u*y + x*(v + 1)) (_hlK : 0 ≤ (-u*y + x*(v + 1))*(v^2*x*y + v*x*y - (x + y)*(u + v + 1))) :
    0 < u^2*x + u^2*y - u*v^2*x*y - u*v*x*y + u*v*x + u*v*y + 2*u*x + 2*u*y + v^3*x^2 + 2*v^2*x^2 + v*x^2 + v*x + v*y + x + y := by
  linear_combination 1 * hx + 1 * hy + 2 * (mul_pos hu hx) + 2 * (mul_pos hu hy) + 1 * (mul_pos hv hx) + 1 * (mul_pos hv hy) + 1 * (mul_pos (mul_pos hu hu) hx) + 1 * (mul_pos (mul_pos hu hu) hy) + 1 * (mul_pos (mul_pos hu hv) hx) + 1 * (mul_pos (mul_pos hu hv) hy) + 1 * (mul_nonneg ((mul_pos hv hx)).le hl) + 1 * (mul_nonneg ((mul_pos (mul_pos hv hv) hx)).le hl)


set_option maxHeartbeats 12800000 in
theorem k92_signs (u v m x y : ℝ) (hu : 0 < u) (hv : 0 < v) (hm : 0 < m) (hx : 0 < x) (hy : 0 < y)
    (hWn : 0 < k92Wn u v x y) (hl : 0 ≤ k92l u v x y) (hlK : 0 ≤ k92l u v x y * k92K u v x y)
    (hX3 : k92K u v x y * k92M3 u v x y ≤ 0) (hK : k92K u v x y ≠ 0) (hsig : 0 < m*(u+v+1) - v) :
    k92Ac u v m x y < 0 ∧ 0 < k92Bc u v m x y ∧
    k92Rin u v m x y u (v+1) 0 < 0 ∧ k92Rin u v m x y (u+1) v 0 < 0 ∧
    k92Rin u v m x y 1 0 0 < 0 ∧ k92Rin u v m x y 0 1 0 < 0 ∧
    (k92Rin u v m x y (-u) 0 (-(v+1)) = 0 → 0 < k92G u v x y u 0 (v+1) 1 0 0) ∧
    (0 < -u*k92Ac u v m x y - (v+1)*k92Bc u v m x y →
      0 < k92G u v x y (u+1) (-((v+1)*m)) (v+1-(1+u*m)) 0 0 1) ∧
    (0 ≤ (u+1)*k92Ac u v m x y + v*k92Bc u v m x y →
      k92G u v x y (u+1) (-((v+1)*m)) (v+1-(1+u*m)) 0 0 1 < 0) ∧
    (-u*k92Ac u v m x y - (v+1)*k92Bc u v m x y = 0 → k92Rin u v m x y (-u) 0 (-(v+1)) ≤ 0) := by
  have hxy : 0 < x + y := by positivity
  have hW0 : k92Wn u v x y ≠ 0 := hWn.ne'
  have hPm : 0 < k92Pm u v m x y := by
    unfold k92Pm; have : 0 < v*y*(v*x+x+y) := by positivity
    nlinarith [mul_pos hm hWn]
  have hP0 := hPm.ne'
  have hWN' : 0 < u^2*x + u^2*y + u*v*x + u*v*y^2 + u*v*y + 2*u*x + 2*u*y - v^2*x*y - v*x*y + v*x + v*y + x + y := hWn
  have hl' : 0 ≤ (1+v)*x - u*y := hl
  have hlK' : 0 ≤ ((1+v)*x - u*y)*(v^2*x*y + v*x*y - (u+v+1)*(x+y)) := hlK
  have hl2 : 0 ≤ -u*y + x*(v + 1) := by linarith
  have hlK2 : 0 ≤ (-u*y + x*(v + 1))*(v^2*x*y + v*x*y - (x + y)*(u + v + 1)) := by nlinarith [hlK']
  have cL := k92_c_fL u v m x y hu hv hm hx hy hWN' hl' hlK' hsig
  have cF2 := k92_c_fF2 u v m x y hu hv hm hx hy hWN' hl' hlK' hsig
  have cA := k92_c_fzA u v m x y hu hv hm hx hy hWN' hl' hlK' hsig
  have cB := k92_c_fzB u v m x y hu hv hm hx hy hWN' hl' hlK' hsig
  have cTB := k92_c_TB u v x y hu hv hx hy hWN' hl2 hlK2
  have cTP := k92_c_TP u v x y hu hv hx hy hWN' hl2 hlK2
  have hTB : 0 < k92TB u v x y := cTB
  have hTP : 0 < k92TP u v x y := cTP
  have hAc : k92Ac u v m x y < 0 := by
    unfold k92Ac; apply div_neg_of_neg_of_pos _ hWn
    have : 0 < (u+v+1)*k92Pm u v m x y := by positivity
    linarith
  have hBc : 0 < k92Bc u v m x y := by
    unfold k92Bc; exact div_pos cL (by positivity)
  refine ⟨hAc, hBc, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [k92_F1 u v m x y hv hx hy hW0 hP0]
    have : 0 < (u+v+1)*(m*u^2*v*x^2 + m*u^2*v*x*y + m*u^2*x^2 + 2*m*u^2*x*y + m*u^2*y^2 + m*u*v^2*x^2 + m*u*v^2*x*y + 2*m*u*v*x^2 + 3*m*u*v*x*y + m*u*v*y^2 + m*u*x^2 + 2*m*u*x*y + m*u*y^2 + u*x*y + u*y^2 + v^3*x^2*y + 2*v^2*x^2*y + v*x^2*y + v*x*y + v*y^2 + x*y + y^2)/k92Wn u v x y := by positivity
    linarith
  · rw [k92_F2 u v m x y hv hx hy hW0 hP0]
    have : 0 < (u+v+1)*(m*u^2*v*x^2 + m*u^2*v*x*y + m*u^2*x*y + m*u^2*y^2 + m*u*v^2*x^2 + m*u*v^2*x*y + 2*m*u*v*x^2 - m*u*v*x*y^2 + 3*m*u*v*x*y + m*u*v*y^2 + 2*m*u*x*y + 2*m*u*y^2 + m*v^2*x^2*y + m*v^2*x^2 + m*v^2*x*y + m*v*x^2*y + m*v*x^2 + 2*m*v*x*y + m*v*y^2 + m*x*y + m*y^2 + v^3*x^2*y + v^2*x^2*y + v^2*x*y^2)/k92Wn u v x y := by
      apply div_pos _ hWn; exact mul_pos (by positivity) cF2
    linarith
  · rw [k92_zA u v m x y hv hx hy hW0 hP0]; have := div_pos cA hWn; linarith
  · rw [k92_zB u v m x y hv hx hy hW0 hP0]; have := div_pos cB hWn; linarith
  · intro h0
    rw [k92_zab u v m x y hv hx hy hW0 hP0] at h0
    have hl0 : 0 < k92l u v x y := by
      by_contra hn
      have : k92l u v x y = 0 := le_antisymm (not_lt.1 hn) hl
      have hy' := h0
      rw [this] at hy'
      have h2 : (u+v+1)*(m*0 - y)*k92K u v x y/k92Wn u v x y = -((u+v+1)*y*k92K u v x y/k92Wn u v x y) := by ring
      rw [h2] at hy'
      have : (u+v+1)*y*k92K u v x y/k92Wn u v x y = 0 := by linarith
      have h3 : (u+v+1)*y*k92K u v x y = 0 := by
        rcases div_eq_zero_iff.1 this with h | h
        · exact h
        · exact absurd h hW0
      have : (u+v+1)*y ≠ 0 := by positivity
      exact hK ((mul_eq_zero.1 h3).resolve_left this)
    have hKpos : 0 < k92K u v x y := by
      rcases lt_or_gt_of_ne hK with h | h
      · exfalso; nlinarith [mul_pos hl0 (neg_pos.2 h)]
      · exact h
    rw [k92_DP u v m x y hv hx hy hW0 hP0]
    exact div_pos (mul_pos (by positivity) hKpos) hWn
  · intro hB
    rw [k92_PB u v m x y hv hx hy hW0 hP0] at hB
    rw [k92_Q1 u v m x y hv hx hy hW0 hP0]
    have hN : 0 < v^2*y*k92l u v x y*k92K u v x y - k92Wn u v x y*k92TB u v x y*m := by
      have hd : 0 < v*(x+y)*k92Wn u v x y := by positivity
      exact (div_pos_iff_of_pos_right hd).1 hB
    have hid : k92TB u v x y * (v^2*y^2 - m*k92Wn u v x y) = (v^2*y*k92l u v x y*k92K u v x y - k92Wn u v x y*k92TB u v x y*m) + v^2*y*(v+1)*(x+y)^2*(u+v+1) := by
      simp only [k92Wn, k92K, k92l, k92TB]; ring
    have h1 : 0 < k92TB u v x y * (v^2*y^2 - m*k92Wn u v x y) := by
      rw [hid]; have : 0 < v^2*y*(v+1)*(x+y)^2*(u+v+1) := by positivity
      linarith
    have h2 := pos_of_mul_pos_right h1 hTB.le
    exact div_pos h2 (by positivity)
  · intro hC
    rw [k92_PC u v m x y hv hx hy hW0 hP0] at hC
    rw [k92_Q1 u v m x y hv hx hy hW0 hP0]
    have hd : 0 < (x+y)*k92Wn u v x y := by positivity
    have hN : 0 ≤ -v*y*k92Q u v x y + v*x*k92l u v x y*k92Wn u v x y*m := (div_nonneg_iff.1 hC).elim (fun h => h.1) (fun h => absurd h.2 (not_le.2 hd))
    have hid : (v*x*k92l u v x y*k92Wn u v x y) * (m*k92Wn u v x y - v^2*y^2) = k92Wn u v x y * (-v*y*k92Q u v x y + v*x*k92l u v x y*k92Wn u v x y*m) + v*y*(u+1)*(x+y)^2*(u+v+1)*k92Wn u v x y := by
      simp only [k92Wn, k92Q, k92l]; ring
    have h1 : 0 < (v*x*k92l u v x y*k92Wn u v x y) * (m*k92Wn u v x y - v^2*y^2) := by
      rw [hid]; have : 0 < v*y*(u+1)*(x+y)^2*(u+v+1)*k92Wn u v x y := by positivity
      have := mul_nonneg hWn.le hN
      linarith
    have hB' : 0 ≤ v*x*k92l u v x y*k92Wn u v x y := by positivity
    have h2 : 0 < m*k92Wn u v x y - v^2*y^2 := by
      by_contra hn
      have := mul_nonpos_of_nonneg_of_nonpos hB' (not_lt.1 hn)
      linarith
    exact div_neg_of_neg_of_pos (by linarith) (by positivity)
  · intro hB
    rw [k92_PB u v m x y hv hx hy hW0 hP0] at hB
    rw [k92_zab u v m x y hv hx hy hW0 hP0]
    have hd : 0 < v*(x+y)*k92Wn u v x y := by positivity
    have hN : v^2*y*k92l u v x y*k92K u v x y - k92Wn u v x y*k92TB u v x y*m = 0 := by
      rcases div_eq_zero_iff.1 hB with h | h
      · exact h
      · exact absurd h hd.ne'
    have hidT : v^2*(k92l u v x y)^2*k92K u v x y - k92Wn u v x y*k92TB u v x y = k92TP u v x y * k92M3 u v x y := by
      simp only [k92Wn, k92K, k92l, k92TB, k92TP, k92M3]; ring
    have hmain : k92Wn u v x y * k92TB u v x y * ((m*k92l u v x y - y)*k92K u v x y) = y * k92TP u v x y * (k92K u v x y * k92M3 u v x y) := by
      linear_combination (-(k92l u v x y * k92K u v x y)) * hN + (y*k92K u v x y) * hidT
    have hle : (m*k92l u v x y - y)*k92K u v x y ≤ 0 := by
      by_contra hn
      have h1 : 0 < k92Wn u v x y * k92TB u v x y * ((m*k92l u v x y - y)*k92K u v x y) := mul_pos (mul_pos hWn hTB) (not_le.1 hn)
      have h2 : y * k92TP u v x y * (k92K u v x y * k92M3 u v x y) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) hX3
      linarith
    have : (u+v+1)*(m*k92l u v x y - y)*k92K u v x y = (u+v+1)*((m*k92l u v x y - y)*k92K u v x y) := by ring
    rw [this]
    exact div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos (by positivity) hle) hWn.le
end Minimality.Type08Sp.C2
