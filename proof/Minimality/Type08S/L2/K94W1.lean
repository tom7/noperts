module

public import Mathlib

@[expose] public section

set_option maxHeartbeats 1000000

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option maxHeartbeats 40000000

noncomputable def k94_kap (e qr rr : ℝ) : ℝ := e*(qr+rr)
noncomputable def k94_lam (e s rr : ℝ) : ℝ := e*(rr-s)
noncomputable def k94_sA (pp s qq qr rr e : ℝ) : ℝ :=
  (e*(qr+rr))*(e^2*(qr+rr-2*s)) - (e*(rr-s))*(e^2*(qq+2*qr+rr))
noncomputable def k94_zb (pp s qq qr rr e : ℝ) : ℝ :=
  (e*(qr+rr))*(e^2*(pp-2*s+rr)) - (e*(rr-s))*(e^2*(qr+rr-2*s))
noncomputable def k94_zc (pp s qq qr rr e : ℝ) : ℝ :=
  (e*(qr+rr))*(e^2*(pp-2*s+qr)) - (e*(rr-s))*(e^2*(qq+qr-2*s))
noncomputable def k94_cRB (s qq qr rr : ℝ) : ℝ := (qq-qr)*(-s) + (qr+s)*qr - (qq+s)*rr
noncomputable def k94_b1RB (pp s qq qr rr e : ℝ) : ℝ :=
  e*(((qq-qr)*pp + (qr+s)*(-s) - (qq+s)*(-s)) + k94_cRB s qq qr rr)

theorem k94_w1 (s pp qq qr rr e : ℝ) (hs : 0 < s) (hpp : 0 < pp) (hqx : qr < qq) (hqy : qr < rr)
    (he1 : 1 < e)
    (hrel : e*s*(qq+rr-2*qr) = (e-1)*(qq*rr-qr^2))
    (hppE : pp*((e-1)*rr+e*qr) = s*((e+e-1)*s+e*(rr-qr)))
    (hD : 0 < qq*rr-qr^2) (hD2 : s^2 < pp*qq)
    (hF1 : (e-1)*s = e*qr) :
    0 < qr + s ∧ 0 < k94_kap e qr rr ∧ 0 < k94_lam e s rr ∧ k94_sA pp s qq qr rr e < 0 ∧
      0 < k94_zb pp s qq qr rr e ∧ k94_zc pp s qq qr rr e < 0 := by
  have hqq0 : 0 < qq := by
    have : 0 < pp*qq := lt_of_le_of_lt (sq_nonneg s) hD2
    exact (pos_iff_pos_of_mul_pos this).1 hpp
  have hrr0 : 0 < rr := by
    by_contra hc; push_neg at hc
    nlinarith [mul_nonpos_of_nonneg_of_nonpos hqq0.le hc, sq_nonneg qr]
  have hqrE : pp*qr = s^2 := by
    have h : e*(rr+s)*(pp*qr - s^2) = 0 := by linear_combination s*hppE - (pp*rr - s^2)*hF1
    have h1 : e*(rr+s) ≠ 0 := (mul_pos (by linarith) (by linarith)).ne'
    have := (mul_eq_zero.1 h).resolve_left h1
    linarith
  obtain ⟨t, Y, Z, ht, hY, hZ, hst, hqqt, hrrt, hqrt⟩ : ∃ t Y Z : ℝ, 0 < t ∧ 0 < Y ∧ 0 < Z ∧ s = t*pp ∧
      qq = pp*(t^2+Y) ∧ rr = pp*(t^2+Z) ∧ qr = pp*t^2 :=
    ⟨s/pp, (qq-qr)/pp, (rr-qr)/pp, by positivity, div_pos (by linarith) hpp, div_pos (by linarith) hpp,
      by field_simp, by field_simp; nlinarith [hqrE], by field_simp; nlinarith [hqrE],
      by field_simp; nlinarith [hqrE]⟩
  subst hst hqqt hrrt hqrt
  have he' : e - 1 - e*t = 0 := by
    have h : (t*pp)*(e - 1 - e*t) = 0 := by linear_combination hF1
    exact (mul_eq_zero.1 h).resolve_left (by positivity)
  have hw : 0 < 1 - t := by
    by_contra hc; push_neg at hc
    nlinarith [mul_nonpos_of_nonneg_of_nonpos (by linarith : (0:ℝ) ≤ e) hc]
  obtain ⟨w1, hwd⟩ : ∃ w1, w1 = 1 - t := ⟨_, rfl⟩
  rw [← hwd] at hw
  have hee : e = 1/w1 := by
    rw [eq_div_iff hw.ne']; rw [hwd]; linarith
  have hYZ : Y*Z - (1-t^2)*(Y+Z) = 0 := by
    have h : (e*t*pp^2)*(Y*Z - (1-t^2)*(Y+Z)) = 0 := by
      linear_combination (-1)*hrel - pp^2*(Y*Z+t^2*(Y+Z))*he'
    exact (mul_eq_zero.1 h).resolve_left (by positivity)
  have hk0 : 0 < 1 - t^2 := by nlinarith
  obtain ⟨v, hv, hvd⟩ : ∃ v, 0 < v ∧ Y = (1-t^2) + v := by
    refine ⟨Y - (1-t^2), ?_, by ring⟩
    by_contra hc; push_neg at hc
    have : Z*(Y-(1-t^2)) = (1-t^2)*Y := by linear_combination hYZ
    nlinarith [mul_nonpos_of_nonneg_of_nonpos hZ.le hc, mul_pos hk0 hY]
  have hZe : Z = (1-t^2)*((1-t^2)+v)/v := by
    rw [eq_div_iff hv.ne']
    subst hvd
    linear_combination hYZ
  subst hvd
  subst hZe
  subst hee
  have hwne := hw.ne'
  have hvne := hv.ne'
  have e_Lam : pp*t^2 + t*pp = pp*t*(t+1) := by ring
  have e_kap : k94_kap (1/w1) (pp*t^2) (pp*(t^2+(1-t^2)*((1-t^2)+v)/v)) = pp*(w1^2*(1+t)^2+v*(1+t^2))/(v*w1) := by
    unfold k94_kap; field_simp; subst hwd; ring
  have e_lam : k94_lam (1/w1) (t*pp) (pp*(t^2+(1-t^2)*((1-t^2)+v)/v)) = pp*(v+(1+t)^2*w1)/v := by
    unfold k94_lam; field_simp; subst hwd; ring
  have e_sA : k94_sA pp (t*pp) (pp*(t^2+((1-t^2)+v))) (pp*t^2) (pp*(t^2+(1-t^2)*((1-t^2)+v)/v)) (1/w1)
      = -(pp^2*(v+w1*(1+t))*(t^2+2*t+v+1)/(v*w1^2)) := by
    unfold k94_sA; field_simp; subst hwd; ring
  have e_zb : k94_zb pp (t*pp) (pp*(t^2+((1-t^2)+v))) (pp*t^2) (pp*(t^2+(1-t^2)*((1-t^2)+v)/v)) (1/w1)
      = pp^2*(1+t)^2*(v+w1*(1+t))/(v*w1^2) := by
    unfold k94_zb; field_simp; subst hwd; ring
  have e_zc : k94_zc pp (t*pp) (pp*(t^2+((1-t^2)+v))) (pp*t^2) (pp*(t^2+(1-t^2)*((1-t^2)+v)/v)) (1/w1)
      = -(pp^2*(v+w1*(1+t))/w1^2) := by
    unfold k94_zc; field_simp; subst hwd; ring
  refine ⟨by rw [e_Lam]; positivity, by rw [e_kap]; positivity, by rw [e_lam]; positivity, ?_, ?_, ?_⟩
  · rw [e_sA]; have : 0 < pp^2*(v+w1*(1+t))*(t^2+2*t+v+1)/(v*w1^2) := by positivity
    linarith
  · rw [e_zb]; positivity
  · rw [e_zc]; have : 0 < pp^2*(v+w1*(1+t))/w1^2 := by positivity
    linarith
