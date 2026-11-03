module

public import Mathlib

@[expose] public section

set_option maxHeartbeats 1000000

namespace Minimality.Type08Sp.C2

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option maxHeartbeats 4000000

theorem k28h5h_Q3 (u1 u2 qr a1 b1 b6 g6 : ℝ) (ha : 0 < a1 - 1) (hb : 0 < b1 - 1) (hb6 : 0 < b6) (hg6 : 0 < g6)
    (hb61 : 0 < 1 - b6) (hg61 : 0 < 1 - g6) (hs : 0 < b6 + g6 - b1) (hu1 : 0 < u1) (hu2 : 0 < u2)
    (hm : 0 < u1*u2 + qr*(u1+u2))
    (L1 : 0 ≤ b6*qr - (1-g6)*(u2+qr)) (L2 : 0 ≤ g6*qr - (1-b6)*(u1+qr)) :
    0 < b6*(b1+a1-1)*u1*(u1+u2) + a1*b1*(b6+g6-1)*qr*(u1+u2) - (b6+g6-1)*(a1-1)*(b1-1)*(u1*u2+qr*(u1+u2)) := by
  linear_combination 1 * (mul_nonneg ((mul_pos ha hu1)).le L1) + 1 * (mul_nonneg ((mul_pos ha hu2)).le L2) + 1 * (mul_pos (mul_pos hb hb6) hm) + 1 * (mul_pos (mul_pos hb61 hs) hm) + 1 * (mul_pos (mul_pos hg61 hu1) hu2) + 1 * (mul_pos (mul_pos (mul_pos ha hb6) hu1) hu1) + 1 * (mul_pos (mul_pos (mul_pos hb hb6) hu1) hu1) + 1 * (mul_pos (mul_pos (mul_pos hb hg6) hg6) hm) + 1 * (mul_pos (mul_pos (mul_pos hb hg61) hu1) hu2) + 1 * (mul_pos (mul_pos (mul_pos hb6 hb61) hu1) hu1) + 1 * (mul_pos (mul_pos (mul_pos hb6 hg61) hs) hm) + 1 * (mul_pos (mul_pos (mul_pos hg6 hg61) hu1) hu1) + 1 * (mul_nonneg ((mul_pos (mul_pos hg6 hg61) hu1)).le L2) + 1 * (mul_nonneg ((mul_pos (mul_pos hg6 hg61) hu2)).le L2) + 1 * (mul_pos (mul_pos (mul_pos hg6 hs) hu1) hu1) + 1 * (mul_nonneg ((mul_pos (mul_pos hg6 hs) hu1)).le L2) + 1 * (mul_nonneg ((mul_pos (mul_pos hg6 hs) hu2)).le L2) + 2 * (mul_pos (mul_pos (mul_pos (mul_pos ha hb) hb61) hu1) hu2) + 2 * (mul_pos (mul_pos (mul_pos (mul_pos ha hb6) hg61) hu1) hu2) + 1 * (mul_pos (mul_pos (mul_pos (mul_pos ha hg6) hg61) hu1) hu2) + 1 * (mul_pos (mul_pos (mul_pos (mul_pos ha hg6) hs) hu1) hu2) + 1 * (mul_pos (mul_pos (mul_pos (mul_pos ha hb61) hb61) hu1) hu2) + 2 * (mul_pos (mul_pos (mul_pos (mul_pos ha hb61) hg61) hu1) hu2) + 1 * (mul_pos (mul_pos (mul_pos (mul_pos ha hb61) hs) hu1) hu2) + 1 * (mul_pos (mul_pos (mul_pos (mul_pos hb hb6) hg6) hu1) hu1) + 1 * (mul_pos (mul_pos (mul_pos (mul_pos hb6 hb6) hg61) hu1) hu1) + 1 * (mul_pos (mul_pos (mul_pos (mul_pos hg6 hg6) hg61) hu1) hu2) + 1 * (mul_pos (mul_pos (mul_pos (mul_pos hg6 hg6) hs) hu1) hu2)

theorem k28h5h_H3 (pp pq qq qr rr a1 b1 b6 g6 : ℝ) (ha : 1 < a1) (hb : 1 < b1) (hb6 : 0 < b6) (hg6 : 0 < g6)
    (hb61 : b6 < 1) (hg61 : g6 < 1) (hs : b1 < b6 + g6) (hu1 : 0 < qq - qr) (hu2 : 0 < rr - qr)
    (hm : 0 < qq*rr - qr^2)
    (hrel : a1*pq*(qq+rr-2*qr) = -(b1-1)*(qq*rr-qr^2))
    (hT : 0 ≤ (a1-1)*pp + b1*pq)
    (L1 : 0 ≤ b6*qr - (1-g6)*rr) (L2 : 0 ≤ g6*qr - (1-b6)*qq) :
    0 < ((a1-1)^2*pp+2*(a1-1)*b1*pq+b1^2*qq)*b6*(b1+a1-1)
      + ((a1-1)^2*pp+2*(a1-1)*b1*pq+b1^2*qr)*(b6*(1-b1-a1)+a1*b1*(b6+g6-1)) := by
  have hQ := k28h5h_Q3 (qq-qr) (rr-qr) qr a1 b1 b6 g6 (by linarith) (by linarith) hb6 hg6 (by linarith) (by linarith)
    (by linarith) hu1 hu2 (by nlinarith) (by linarith) (by linarith)
  have hW : 0 < qq + rr - 2*qr := by linarith
  have hA : 0 < a1 - 1 := by linarith
  have hsg : 0 < b6 + g6 - 1 := by linarith
  have key : (qq+rr-2*qr) * (((a1-1)^2*pp+2*(a1-1)*b1*pq+b1^2*qq)*b6*(b1+a1-1)
      + ((a1-1)^2*pp+2*(a1-1)*b1*pq+b1^2*qr)*(b6*(1-b1-a1)+a1*b1*(b6+g6-1)))
      = (qq+rr-2*qr) * a1*b1*(b6+g6-1)*(a1-1)*((a1-1)*pp+b1*pq)
        + b1^2*(b6*(b1+a1-1)*(qq-qr)*((qq-qr)+(rr-qr)) + a1*b1*(b6+g6-1)*qr*((qq-qr)+(rr-qr)) - (b6+g6-1)*(a1-1)*(b1-1)*((qq-qr)*(rr-qr)+qr*((qq-qr)+(rr-qr)))) := by
    linear_combination (b1^2*(b6+g6-1)*(a1-1)) * hrel
  have h2 : 0 ≤ (qq+rr-2*qr) * a1*b1*(b6+g6-1)*(a1-1)*((a1-1)*pp+b1*pq) := by positivity
  have h3 : 0 < (qq+rr-2*qr) * (((a1-1)^2*pp+2*(a1-1)*b1*pq+b1^2*qq)*b6*(b1+a1-1)
      + ((a1-1)^2*pp+2*(a1-1)*b1*pq+b1^2*qr)*(b6*(1-b1-a1)+a1*b1*(b6+g6-1))) := by
    rw [key]; have : 0 < b1^2 := by positivity
    nlinarith [mul_pos this hQ]
  exact pos_of_mul_pos_right h3 hW.le

end Minimality.Type08Sp.C2
