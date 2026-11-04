module

public import Mathlib

@[expose] public section

set_option maxHeartbeats 1000000

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option maxHeartbeats 40000000

theorem k94_F1 (s pp qq qr rr m al be : ℝ) (hs : 0 < s) (hpp : 0 < pp) (hm : 0 < m) (hqx : qr < qq) (hqy : qr < rr)
    (hal : 1 < al) (hbe : 1 < be)
    (hrel : al*s*(qq+rr-2*qr) = (be-1)*(qq*rr-qr^2))
    (hppE : pp*((al-1)*rr+be*qr) = s*((al+be-1)*s+be*(rr-qr)))
    (hD : 0 < qq*rr-qr^2) (hD2 : s^2 < pp*qq)
    (hcx0 : 0 < -(al-1)*(s+pp) + be*(qq+s)) (hcxB : -(al-1)*(s+pp) + be*(qq+s) < pp + 2*s + qq)
    (hF1 : (al-1)*s = be*qr) (hmα : m*(be+1-al) = 1) (hne : al ≠ be) :
    ∃ B P W dx cx ex : ℝ, B = pp + 2*s + qq ∧ P = (be*m)*(qq+s) + (1+(al-1)*m)*(qr+s) + s + pp ∧
      W = -(al-1)*(s+pp) + be*(qr+s) ∧ dx = s + pp ∧ cx = -(al-1)*(s+pp) + be*(qq+s) ∧ ex = pp + 2*s + qr ∧
      0 < B ∧ 0 < dx ∧ dx < B ∧ 0 < cx ∧ cx < B ∧
      (1+(al-1)*m) * ex + (B - P) * 1 < (1+(al-1)*m) * B ∧ (be - (1+(al-1)*m)) * ex + (P - W) * 1 < P * be - W * (1+(al-1)*m) ∧ -be * ex + W * 1 < 0 ∧
      W ≤ 0 ∧ ((be < (1+(al-1)*m) ∧ B < P) ∨ ((1+(al-1)*m) < be ∧ W < 0 ∧ B ≤ P) ∨
        ((1+(al-1)*m) < be ∧ W = 0 ∧ B * (be - (1+(al-1)*m)) < P * be ∧ 0 < P)) := by
  have hmα0 := hmα
  have hqq0 : 0 < qq := by
    have : 0 < pp*qq := lt_of_le_of_lt (sq_nonneg s) hD2
    exact (pos_iff_pos_of_mul_pos this).1 hpp
  have hrr0 : 0 < rr := by
    by_contra hc; push_neg at hc
    nlinarith [mul_nonpos_of_nonneg_of_nonpos hqq0.le hc, sq_nonneg qr]
  have hqrE : pp*qr = s^2 := by
    have h : be*(rr+s)*(pp*qr - s^2) = 0 := by linear_combination s*hppE - (pp*rr - s^2)*hF1
    have h1 : be*(rr+s) ≠ 0 := (mul_pos (by linarith) (by linarith)).ne'
    have := (mul_eq_zero.1 h).resolve_left h1
    linarith
  obtain ⟨t, Y, Z, ht, hY, hZ, hst, hqqt, hrrt, hqrt⟩ : ∃ t Y Z : ℝ, 0 < t ∧ 0 < Y ∧ 0 < Z ∧ s = t*pp ∧
      qq = pp*(t^2+Y) ∧ rr = pp*(t^2+Z) ∧ qr = pp*t^2 :=
    ⟨s/pp, (qq-qr)/pp, (rr-qr)/pp, by positivity, div_pos (by linarith) hpp, div_pos (by linarith) hpp,
      by field_simp, by field_simp; nlinarith [hqrE], by field_simp; nlinarith [hqrE],
      by field_simp; nlinarith [hqrE]⟩
  subst hst hqqt hrrt hqrt
  have hal' : al = 1 + be*t := by
    have h : (t*pp)*(al - 1 - be*t) = 0 := by linear_combination hF1
    have := (mul_eq_zero.1 h).resolve_left (by positivity)
    linarith
  have hbeE : be*(Y*Z) = Y*Z + t*(1+t)*(Y+Z) := by
    have h : pp^2*(be*(Y*Z) - (Y*Z + t*(1+t)*(Y+Z))) = 0 := by
      rw [hal'] at hrel; linear_combination (-1)*hrel
    have := (mul_eq_zero.1 h).resolve_left (by positivity)
    linarith
  have hβe : be = (Y*Z + t*(1+t)*(Y+Z))/(Y*Z) := by
    rw [eq_div_iff (by positivity)]; exact hbeE
  have hm1 : m*(be*(1-t)) = 1 := by rw [hal'] at hmα; linear_combination hmα
  have hw : 0 < 1 - t := by
    by_contra hc; push_neg at hc
    have := mul_nonpos_of_nonneg_of_nonpos (mul_pos hm (by linarith : (0:ℝ) < be)).le hc
    nlinarith
  obtain ⟨w, hwd⟩ : ∃ w, w = 1 - t := ⟨_, rfl⟩
  rw [← hwd] at hw hm1
  have hwne := hw.ne'
  have hme : m = 1/(be*w) := by
    rw [eq_div_iff (by positivity)]; linarith
  have hne' : be ≠ 1+(al-1)*m := by
    intro h
    have h3 : be*(m-1) = 0 := by linear_combination hmα0 - h
    have h4 : m = 1 := by have := (mul_eq_zero.1 h3).resolve_left (by linarith); linarith
    apply hne; rw [h4] at hmα0; linarith
  have hY0 : 0 < Y*Z := by positivity
  have e_B : (pp + 2*(t*pp) + pp*(t^2+Y)) = pp*(Y+t^2+2*t+1) := by ring
  have r_B : 0 < (pp + 2*(t*pp) + pp*(t^2+Y)) := by rw [e_B]; positivity
  have r_dx : 0 < ((t*pp)+pp) := by positivity
  have e_Bdx : ((pp + 2*(t*pp) + pp*(t^2+Y)) - ((t*pp)+pp)) = pp*(Y+t^2+t) := by ring
  have r_Bdx : 0 < ((pp + 2*(t*pp) + pp*(t^2+Y)) - ((t*pp)+pp)) := by rw [e_Bdx]; positivity
  have e_in3 : ((1+(al-1)*m)*(pp + 2*(t*pp) + pp*(t^2+Y)) - (1+(al-1)*m)*(pp + 2*(t*pp) + pp*t^2) - ((pp + 2*(t*pp) + pp*(t^2+Y)) - ((be*m)*(pp*(t^2+Y)+(t*pp)) + (1+(al-1)*m)*(pp*t^2+(t*pp)) + (t*pp) + pp))) = pp*(t+1)*(Y+t^2+t)/w := by
    simp only [hal', hβe, hme]; field_simp; subst hwd; ring
  have r_in3 : 0 < ((1+(al-1)*m)*(pp + 2*(t*pp) + pp*(t^2+Y)) - (1+(al-1)*m)*(pp + 2*(t*pp) + pp*t^2) - ((pp + 2*(t*pp) + pp*(t^2+Y)) - ((be*m)*(pp*(t^2+Y)+(t*pp)) + (1+(al-1)*m)*(pp*t^2+(t*pp)) + (t*pp) + pp))) := by
    rw [e_in3]; positivity
  have e_in4 : (((be*m)*(pp*(t^2+Y)+(t*pp)) + (1+(al-1)*m)*(pp*t^2+(t*pp)) + (t*pp) + pp)*be - (-(al-1)*((t*pp)+pp) + be*(pp*t^2+(t*pp)))*(1+(al-1)*m) - (be-(1+(al-1)*m))*(pp + 2*(t*pp) + pp*t^2) - (((be*m)*(pp*(t^2+Y)+(t*pp)) + (1+(al-1)*m)*(pp*t^2+(t*pp)) + (t*pp) + pp) - (-(al-1)*((t*pp)+pp) + be*(pp*t^2+(t*pp))))) = pp*t*(t+1)*(Y^2+Y*Z*t+2*Y*Z+Y*t^3+2*Y*t^2+Y*t+Z*t^3+2*Z*t^2+Z*t)/(Y*Z*w) := by
    simp only [hal', hβe, hme]; field_simp; subst hwd; ring
  have r_in4 : 0 < (((be*m)*(pp*(t^2+Y)+(t*pp)) + (1+(al-1)*m)*(pp*t^2+(t*pp)) + (t*pp) + pp)*be - (-(al-1)*((t*pp)+pp) + be*(pp*t^2+(t*pp)))*(1+(al-1)*m) - (be-(1+(al-1)*m))*(pp + 2*(t*pp) + pp*t^2) - (((be*m)*(pp*(t^2+Y)+(t*pp)) + (1+(al-1)*m)*(pp*t^2+(t*pp)) + (t*pp) + pp) - (-(al-1)*((t*pp)+pp) + be*(pp*t^2+(t*pp))))) := by
    rw [e_in4]; positivity
  have e_in5 : (be*(pp + 2*(t*pp) + pp*t^2) - (-(al-1)*((t*pp)+pp) + be*(pp*t^2+(t*pp)))) = pp*(t+1)^2*(Y*Z+Y*t^2+Y*t+Z*t^2+Z*t)/(Y*Z) := by
    simp only [hal', hβe]; field_simp; ring
  have r_in5 : 0 < (be*(pp + 2*(t*pp) + pp*t^2) - (-(al-1)*((t*pp)+pp) + be*(pp*t^2+(t*pp)))) := by
    rw [e_in5]; positivity
  have e_PB : (((be*m)*(pp*(t^2+Y)+(t*pp)) + (1+(al-1)*m)*(pp*t^2+(t*pp)) + (t*pp) + pp) - (pp + 2*(t*pp) + pp*(t^2+Y))) = pp*t*(Y+t^2+2*t+1)/w := by
    simp only [hal', hβe, hme]; field_simp; subst hwd; ring
  have r_PB : 0 < (((be*m)*(pp*(t^2+Y)+(t*pp)) + (1+(al-1)*m)*(pp*t^2+(t*pp)) + (t*pp) + pp) - (pp + 2*(t*pp) + pp*(t^2+Y))) := by
    rw [e_PB]; positivity
  have e_W : (-(al-1)*((t*pp)+pp) + be*(pp*t^2+(t*pp))) = 0 := by
    simp only [hal']; ring
  have e_X : (((be*m)*(pp*(t^2+Y)+(t*pp)) + (1+(al-1)*m)*(pp*t^2+(t*pp)) + (t*pp) + pp)*be - (pp + 2*(t*pp) + pp*(t^2+Y))*(be-(1+(al-1)*m))) = pp*(t+1)*(Y*Z+Y*t^2+Z*t^2)*(Y+t^2+2*t+1)/(Y*Z*w) := by
    simp only [hal', hβe, hme]; field_simp; subst hwd; ring
  have r_X : 0 < (((be*m)*(pp*(t^2+Y)+(t*pp)) + (1+(al-1)*m)*(pp*t^2+(t*pp)) + (t*pp) + pp)*be - (pp + 2*(t*pp) + pp*(t^2+Y))*(be-(1+(al-1)*m))) := by
    rw [e_X]; positivity
  refine ⟨_, _, _, _, _, _, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · linarith [r_B]
  · linarith [r_dx]
  · linarith [r_Bdx]
  · exact hcx0
  · exact hcxB
  · nlinarith [r_in3]
  · nlinarith [r_in4]
  · nlinarith [r_in5]
  · linarith [e_W]
  · rcases lt_or_gt_of_ne hne' with h | h
    · left; exact ⟨h, by linarith [r_PB, r_B]⟩
    · right; right
      exact ⟨h, e_W, by nlinarith [r_X], by linarith [r_PB, r_B]⟩
