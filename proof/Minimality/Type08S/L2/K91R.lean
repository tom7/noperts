module

public import Mathlib

@[expose] public section

set_option maxHeartbeats 1000000

set_option autoImplicit true
set_option relaxedAutoImplicit true
namespace Minimality.Type08Sp.C2

def k91G (pp s qq qr rr x1 x2 x3 y1 y2 y3 : ℝ) : ℝ :=
  x1*y1*pp + (x1*y2+x2*y1)*s + (x1*y3+x3*y1)*s + x2*y2*qq + (x2*y3+x3*y2)*qr + x3*y3*rr

/-- Real core of the type 08 U0 chart (all Gram data in terms of u v t x). -/
theorem k91_core {u v t x b6 g6 nu pp pq qq qr rr : ℝ}
    (hu : 0 < u) (hv : 0 < v) (ht : 0 < t) (hx : 0 < x) (hb6 : 0 < b6) (hg6 : 0 < g6)
    (W : ℝ) (hWdef : W = v*(v+1)*x - t*(u+v+1)) (hW : 0 < W)
    (hpp : pp * u = (v+1) * t) (hpq : pq = -t) (hqr : qr * (v+1) = u * t) (hqq : qq = x + qr)
    (hrr : (rr - qr) * W = t*(u+v+1)*x)
    (hnu : nu * k91G pp pq qq qr rr 1 (-b6) (-g6) 1 0 0 = (v+1) * (- k91G pp pq qq qr rr 1 (-b6) (-g6) 0 0 1)) :
    u < nu ∧
    (0 ≤ k91G pp pq qq qr rr (u+1) (v+1-b6) (-g6) (u+1) 0 v →
      0 ≤ (u+1)*(v+1) - v*nu) ∧
    0 < k91G pp pq qq qr rr u 0 (v+1) (nu/(v+1)) 0 1 ∧
    0 < k91G pp pq qq qr rr (u+1) 0 v (nu/(v+1)) 0 1 ∧
    (0 < b6*u - (v+1)*(g6-1) → 0 < k91G pp pq qq qr rr 0 (-b6) (1-g6) (nu/(v+1)) 0 1) ∧
    k91G pp pq qq qr rr u (v+1) 0 (nu/(v+1)) 0 1 = 0 := by
  have hu0 : u ≠ 0 := hu.ne'
  have hv1 : v + 1 ≠ 0 := by positivity
  have hW0 : W ≠ 0 := hW.ne'
  have e_pp : pp = (v+1)*t/u := by rw [eq_div_iff hu0]; exact hpp
  have e_qr : qr = u*t/(v+1) := by rw [eq_div_iff hv1]; exact hqr
  have e_rr : rr = t*(u+v+1)*x/W + qr := by
    have : rr - qr = t*(u+v+1)*x/W := by rw [eq_div_iff hW0]; exact hrr
    linarith
  subst hpq hqq e_pp e_rr
  subst e_qr
  clear hpp hqr hrr
  have hD : 0 < b6*u + g6*u + v + 1 := by positivity
  have hDe : k91G ((v+1)*t/u) (-t) (x + u*t/(v+1)) (u*t/(v+1))
      (t*(u+v+1)*x/W + u*t/(v+1)) 1 (-b6) (-g6) 1 0 0 =
      t*(b6*u + g6*u + v + 1)/u := by
    unfold k91G; field_simp; subst hWdef; ring
  have hnu' : nu = t*(-b6*t*u^2 - b6*t*u*v - b6*t*u + b6*u*v^2*x + b6*u*v*x - g6*t*u^2 - g6*t*u*v - g6*t*u + g6*u*v^2*x + 2*g6*u*v*x + g6*u*x + g6*v^2*x + 2*g6*v*x + g6*x - t*u*v - t*u - t*v^2 - 2*t*v - t + v^3*x + 2*v^2*x + v*x)/W / (t*(b6*u + g6*u + v + 1)/u) := by
    rw [hDe] at hnu
    have : nu = (v+1) * (- k91G ((v+1)*t/u) (-t) (x + u*t/(v+1)) (u*t/(v+1))
      (t*(u+v+1)*x/W + u*t/(v+1)) 1 (-b6) (-g6) 0 0 1) / (t*(b6*u + g6*u + v + 1)/u) := by
      rw [eq_div_iff (by positivity)]; exact hnu
    rw [this]
    congr 1
    unfold k91G; field_simp; subst hWdef; ring
  clear hnu hDe
  subst hnu'
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · have : t*(-b6*t*u^2 - b6*t*u*v - b6*t*u + b6*u*v^2*x + b6*u*v*x - g6*t*u^2 - g6*t*u*v - g6*t*u + g6*u*v^2*x + 2*g6*u*v*x + g6*u*x + g6*v^2*x + 2*g6*v*x + g6*x - t*u*v - t*u - t*v^2 - 2*t*v - t + v^3*x + 2*v^2*x + v*x)/W / (t*(b6*u + g6*u + v + 1)/u) - u = g6*u*x*(v+1)*(u+v+1)/((b6*u + g6*u + v + 1)*W) := by
      field_simp; subst hWdef; ring
    have h2 : 0 < g6*u*x*(v+1)*(u+v+1)/((b6*u + g6*u + v + 1)*W) := by positivity
    linarith
  · intro hH
    have e1 : k91G ((v+1)*t/u) (-t) (x + u*t/(v+1)) (u*t/(v+1))
      (t*(u+v+1)*x/W + u*t/(v+1)) (u+1) (v+1-b6) (-g6) (u+1) 0 v =
      t*(u+v+1)*(-b6*t*u^2 - b6*t*u*v - b6*t*u + b6*u*v^2*x + b6*u*v*x - g6*t*u^2 - g6*t*u*v - g6*t*u - t*u*v - t*u - t*v^2 - 2*t*v - t + v^3*x + 2*v^2*x + v*x)/(u*(v+1)*W) := by
      unfold k91G; field_simp; subst hWdef; ring
    have e2 : (u+1)*(v+1) - v*(t*(-b6*t*u^2 - b6*t*u*v - b6*t*u + b6*u*v^2*x + b6*u*v*x - g6*t*u^2 - g6*t*u*v - g6*t*u + g6*u*v^2*x + 2*g6*u*v*x + g6*u*x + g6*v^2*x + 2*g6*v*x + g6*x - t*u*v - t*u - t*v^2 - 2*t*v - t + v^3*x + 2*v^2*x + v*x)/W / (t*(b6*u + g6*u + v + 1)/u)) =
      (u+v+1)*(-b6*t*u^2 - b6*t*u*v - b6*t*u + b6*u*v^2*x + b6*u*v*x - g6*t*u^2 - g6*t*u*v - g6*t*u - t*u*v - t*u - t*v^2 - 2*t*v - t + v^3*x + 2*v^2*x + v*x)/((b6*u + g6*u + v + 1)*W) := by
      field_simp; subst hWdef; ring
    rw [e1] at hH; rw [e2]
    have hn : 0 ≤ (u+v+1)*(-b6*t*u^2 - b6*t*u*v - b6*t*u + b6*u*v^2*x + b6*u*v*x - g6*t*u^2 - g6*t*u*v - g6*t*u - t*u*v - t*u - t*v^2 - 2*t*v - t + v^3*x + 2*v^2*x + v*x) := by
      have h3 : 0 ≤ t*(u+v+1)*(-b6*t*u^2 - b6*t*u*v - b6*t*u + b6*u*v^2*x + b6*u*v*x - g6*t*u^2 - g6*t*u*v - g6*t*u - t*u*v - t*u - t*v^2 - 2*t*v - t + v^3*x + 2*v^2*x + v*x) := by
        have := (div_nonneg_iff.1 hH)
        rcases this with ⟨h, _⟩ | ⟨h, h'⟩
        · exact h
        · exfalso; have : 0 < u*(v+1)*W := by positivity
          linarith
      nlinarith [ht, h3]
    positivity
  · have : k91G ((v+1)*t/u) (-t) (x + u*t/(v+1)) (u*t/(v+1))
      (t*(u+v+1)*x/W + u*t/(v+1)) u 0 (v+1) (t*(-b6*t*u^2 - b6*t*u*v - b6*t*u + b6*u*v^2*x + b6*u*v*x - g6*t*u^2 - g6*t*u*v - g6*t*u + g6*u*v^2*x + 2*g6*u*v*x + g6*u*x + g6*v^2*x + 2*g6*v*x + g6*x - t*u*v - t*u - t*v^2 - 2*t*v - t + v^3*x + 2*v^2*x + v*x)/W / (t*(b6*u + g6*u + v + 1)/u)/(v+1)) 0 1 = t*x*(v+1)*(u+v+1)/W := by
      unfold k91G; field_simp; subst hWdef; ring
    rw [this]; positivity
  · have : k91G ((v+1)*t/u) (-t) (x + u*t/(v+1)) (u*t/(v+1))
      (t*(u+v+1)*x/W + u*t/(v+1)) (u+1) 0 v (t*(-b6*t*u^2 - b6*t*u*v - b6*t*u + b6*u*v^2*x + b6*u*v*x - g6*t*u^2 - g6*t*u*v - g6*t*u + g6*u*v^2*x + 2*g6*u*v*x + g6*u*x + g6*v^2*x + 2*g6*v*x + g6*x - t*u*v - t*u - t*v^2 - 2*t*v - t + v^3*x + 2*v^2*x + v*x)/W / (t*(b6*u + g6*u + v + 1)/u)/(v+1)) 0 1 = t*x*(u+v+1)*(b6*u*v + g6*u*v + g6*u + g6*v + g6 + v^2 + v)/((b6*u + g6*u + v + 1)*W) := by
      unfold k91G; field_simp; subst hWdef; ring
    rw [this]; positivity
  · intro hg
    have : k91G ((v+1)*t/u) (-t) (x + u*t/(v+1)) (u*t/(v+1))
      (t*(u+v+1)*x/W + u*t/(v+1)) 0 (-b6) (1-g6) (t*(-b6*t*u^2 - b6*t*u*v - b6*t*u + b6*u*v^2*x + b6*u*v*x - g6*t*u^2 - g6*t*u*v - g6*t*u + g6*u*v^2*x + 2*g6*u*v*x + g6*u*x + g6*v^2*x + 2*g6*v*x + g6*x - t*u*v - t*u - t*v^2 - 2*t*v - t + v^3*x + 2*v^2*x + v*x)/W / (t*(b6*u + g6*u + v + 1)/u)/(v+1)) 0 1 = t*x*(u+v+1)*(b6*u - (v+1)*(g6-1))/((b6*u + g6*u + v + 1)*W) := by
      unfold k91G; field_simp; subst hWdef; ring
    rw [this]; positivity
  · unfold k91G; field_simp; subst hWdef; ring
end Minimality.Type08Sp.C2
