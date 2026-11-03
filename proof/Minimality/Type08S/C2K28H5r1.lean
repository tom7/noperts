module

public import Mathlib

@[expose] public section

set_option maxHeartbeats 1000000
set_option autoImplicit true
set_option relaxedAutoImplicit true

set_option maxHeartbeats 1000000 in
theorem k28h5rb_core (P t u1 u2 M al be ob og sg b g A B T L2 L3 : ℝ)
    (hal : 0 < al) (hbe : 0 < be) (hob : 0 < ob) (hog : 0 < og) (hsg : 0 < sg)
    (hb : 0 < b) (hg : 0 < g) (hA : 0 < A) (hB : 0 < B)
    (hu1 : 0 < u1) (hu2 : 0 < u2) (ht : 0 < t)
    (hT0 : 0 ≤ T) (hL20 : 0 ≤ L2) (hL30 : 0 ≤ L3)
    (eb : b = 1 - ob) (eg : g = 1 - og) (eA : A = 1 + al) (eB : B = 1 + be)
    (esg : sg = 1 - ob - og - be)
    (eT : T = al*P - B*t)
    (eL2 : L2 = g*M - ob*(u1+M))
    (eL3 : L3 = -A*t + (B-b)*(u1+M) - g*M)
    (hrel : A * t * (u1 + u2) = be * (u1*u2 + M*(u1+u2))) :
    0 < g*al*be*B*u1 + A*(g*(al^2*P - 2*al*B*t + B^2*M)
        - ob*(al^2*P - 2*al*B*t + B^2*(u1+M))) := by
  have hid : g*al*be*B*u1 + A*(g*(al^2*P - 2*al*B*t + B^2*M)
        - ob*(al^2*P - 2*al*B*t + B^2*(u1+M))) =
      T*al*sg + T*al*al*be + T*al*al*sg + T*al*be*ob + T*al*be*b
      + L2 + L2*al + 2*(L2*be) + L2*al*be + L2*al*sg + L2*be*be + L2*al*be*b + L2*al*be*g
      + L3*al*be*be + L3*al*be*ob + L3*al*be*b + L3*al*sg*B := by
    subst eb eg eA eB esg eT eL2 eL3
    ring
  by_contra hcon
  push_neg at hcon
  have q1 : 0 ≤ T*al*sg := by positivity
  have q2 : 0 ≤ T*al*al*be := by positivity
  have q3 : 0 ≤ T*al*al*sg := by positivity
  have q4 : 0 ≤ T*al*be*ob := by positivity
  have q5 : 0 ≤ T*al*be*b := by positivity
  have q6 : 0 ≤ L2*al := by positivity
  have q7 : 0 ≤ L2*be := by positivity
  have q8 : 0 ≤ L2*al*be := by positivity
  have q9 : 0 ≤ L2*al*sg := by positivity
  have q10 : 0 ≤ L2*be*be := by positivity
  have q11 : 0 ≤ L2*al*be*b := by positivity
  have q12 : 0 ≤ L2*al*be*g := by positivity
  have q13 : 0 ≤ L3*al*be*be := by positivity
  have q14 : 0 ≤ L3*al*be*ob := by positivity
  have q15 : 0 ≤ L3*al*be*b := by positivity
  have q16 : 0 ≤ L3*al*sg*B := by positivity
  have z1 : T*al*sg = 0 := by linarith
  have z2 : L2*be = 0 := by linarith
  have z3 : L3*al*be*be = 0 := by linarith
  have hT : T = 0 := by
    rcases mul_eq_zero.1 z1 with h | h
    · rcases mul_eq_zero.1 h with h | h
      · exact h
      · exact absurd h hal.ne'
    · exact absurd h hsg.ne'
  have hL2 : L2 = 0 := (mul_eq_zero.1 z2).resolve_right hbe.ne'
  have hL3 : L3 = 0 := by
    have : L3 * (al*be*be) = 0 := by linarith
    exact (mul_eq_zero.1 this).resolve_right (by positivity)
  have hAt : A * t = be * (u1 + M) := by
    have e3 : -A*t + (B-b)*(u1+M) - g*M = 0 := by rw [← eL3]; exact hL3
    have e2 : g*M - ob*(u1+M) = 0 := by rw [← eL2]; exact hL2
    subst eb eB
    linear_combination (-1:ℝ)*e3 + (-1:ℝ)*e2
  have h2 : be * ((u1 + M) * (u1 + u2) - (u1*u2 + M*(u1+u2))) = 0 := by
    linear_combination hrel - (u1+u2)*hAt
  have h3 : be * u1^2 = 0 := by nlinarith [h2]
  have : 0 < be * u1^2 := by positivity
  linarith
