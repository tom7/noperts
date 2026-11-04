module

public import Minimality.Type08S.L2.K91R

@[expose] public section

set_option maxHeartbeats 1000000

set_option autoImplicit true
set_option relaxedAutoImplicit true
namespace Minimality.Type08Sp.C2

theorem k91_q2 {u v t x b6 g6 lam pp pq qq qr rr : ℝ}
    (hu : 0 < u) (hv : 0 < v) (ht : 0 < t) (hx : 0 < x) (hb6 : 0 < b6) (hg6 : 0 < g6)
    (W : ℝ) (hWdef : W = v*(v+1)*x - t*(u+v+1)) (hW : 0 < W)
    (hpp : pp * u = (v+1) * t) (hpq : pq = -t) (hqr : qr * (v+1) = u * t) (hqq : qq = x + qr)
    (hrr : (rr - qr) * W = t*(u+v+1)*x)
    (hg0 : b6*u = (v+1)*(g6-1)) (hcb : u + 1 ≤ v * lam)
    (hlam : lam * k91G pp pq qq qr rr 1 0 0 (-(u+1)) b6 (g6-(v+1)) =
      - k91G pp pq qq qr rr 0 1 0 (-(u+1)) b6 (g6-(v+1))) :
    0 < k91G pp pq qq qr rr (-(u+1)) b6 (g6-(v+1)) 0 0 1 := by
  have hu0 : u ≠ 0 := hu.ne'
  have hv1 : v + 1 ≠ 0 := by positivity
  have hW0 : W ≠ 0 := hW.ne'
  have e_pp : pp = (v+1)*t/u := by rw [eq_div_iff hu0]; exact hpp
  have e_qr : qr = u*t/(v+1) := by rw [eq_div_iff hv1]; exact hqr
  have e_rr : rr = t*(u+v+1)*x/W + qr := by
    have : rr - qr = t*(u+v+1)*x/W := by rw [eq_div_iff hW0]; exact hrr
    linarith
  have e_g : g6 = 1 + u*b6/(v+1) := by
    have : g6 - 1 = u*b6/(v+1) := by rw [eq_div_iff hv1]; linarith
    linarith
  subst hpq hqq e_pp e_rr
  subst e_qr
  subst e_g
  clear hpp hqr hrr hg0
  have hbp : 0 < b6*u + v + 1 := by positivity
  have eAv : k91G ((v+1)*t/u) (-t) (x + u*t/(v+1)) (u*t/(v+1)) (t*(u+v+1)*x/W + u*t/(v+1)) 1 0 0 (-(u+1)) b6 (1 + u*b6/(v+1) - (v+1)) = -(t*(u+v+1)*(b6*u+v+1)/(u*(v+1))) := by
    unfold k91G; field_simp; ring
  have key : (u+1) * k91G ((v+1)*t/u) (-t) (x + u*t/(v+1)) (u*t/(v+1)) (t*(u+v+1)*x/W + u*t/(v+1)) 1 0 0 (-(u+1)) b6 (1 + u*b6/(v+1) - (v+1)) + v * k91G ((v+1)*t/u) (-t) (x + u*t/(v+1)) (u*t/(v+1)) (t*(u+v+1)*x/W + u*t/(v+1)) 0 1 0 (-(u+1)) b6 (1 + u*b6/(v+1) - (v+1)) = (v*b6*u*(v+1)^2*x - t*(u+v+1)^2*(b6*u+v+1))/(u*(v+1)^2) := by
    unfold k91G; field_simp; ring
  generalize k91G ((v+1)*t/u) (-t) (x + u*t/(v+1)) (u*t/(v+1)) (t*(u+v+1)*x/W + u*t/(v+1)) 1 0 0 (-(u+1)) b6 (1 + u*b6/(v+1) - (v+1)) = Av at *
  generalize k91G ((v+1)*t/u) (-t) (x + u*t/(v+1)) (u*t/(v+1)) (t*(u+v+1)*x/W + u*t/(v+1)) 0 1 0 (-(u+1)) b6 (1 + u*b6/(v+1) - (v+1)) = Bv at *
  have hAneg : Av < 0 := by rw [eAv]; have : 0 < t*(u+v+1)*(b6*u+v+1)/(u*(v+1)) := by positivity
                            linarith
  have h1 := mul_le_mul_of_nonpos_right hcb hAneg.le
  have h2 : v * lam * Av = -(v * Bv) := by rw [mul_assoc, hlam]; ring
  have hN : 0 ≤ v*b6*u*(v+1)^2*x - t*(u+v+1)^2*(b6*u+v+1) := by
    by_contra hneg; push_neg at hneg
    have : (v*b6*u*(v+1)^2*x - t*(u+v+1)^2*(b6*u+v+1))/(u*(v+1)^2) < 0 := div_neg_of_neg_of_pos hneg (by positivity)
    rw [← key] at this; nlinarith
  have eQ : k91G ((v+1)*t/u) (-t) (x + u*t/(v+1)) (u*t/(v+1)) (t*(u+v+1)*x/W + u*t/(v+1)) (-(u+1)) b6 (1 + u*b6/(v+1) - (v+1)) 0 0 1 = t*(u+v+1)*(b6*u*(v+1)^2*x - t*(u+v+1)*(b6*u+v+1))/((v+1)^2*W) := by
    unfold k91G; field_simp; subst hWdef; ring
  rw [eQ]
  have hF : 0 < b6*u*(v+1)^2*x - t*(u+v+1)*(b6*u+v+1) := by
    have h3 : 0 < t*(u+v+1)*(b6*u+v+1)*(u+1) := by positivity
    have h4 : v * (b6*u*(v+1)^2*x - t*(u+v+1)*(b6*u+v+1)) = (v*b6*u*(v+1)^2*x - t*(u+v+1)^2*(b6*u+v+1)) + t*(u+v+1)*(b6*u+v+1)*(u+1) := by ring
    by_contra hh; push_neg at hh
    nlinarith [mul_nonneg hv.le (neg_nonneg.2 hh)]
  positivity
end Minimality.Type08Sp.C2
