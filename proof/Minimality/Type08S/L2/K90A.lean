module

public import Mathlib

@[expose] public section

set_option maxHeartbeats 1000000

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option maxHeartbeats 4000000

theorem k90_class (s pp qq qr rr m al be : ℝ) (hs : 0 < s) (hm : 0 < m) (hqq : qr < qq) (hal : 1 < al) (hbe : 1 < be)
    (hrel : al*s*(qq+rr-2*qr) = (be-1)*(qq*rr-qr^2))
    (hppE : pp*((al-1)*rr+be*qr) = s*((al+be-1)*s+be*(rr-qr)))
    (hW : 0 < (al-1)*rr+be*qr)
    (hAv : -al*pp - be*m*s + be*s - (1+(al-1)*m)*s < 0)
    (hZab : al*be*m*pp*qq - al*be*m*s^2 + al*pp*qr*(m*(al - 1) + 1) - al*s^2*(m*(al - 1) + 1) - be^2*m*qq*s + be^2*m*qr*s - be*m*pp*qq + be*m*s^2 + be*pp*qr - be*s^2 - pp*qr*(m*(al - 1) + 1) + s^2*(m*(al - 1) + 1) = 0)
    (hZba : -al*be*m*pp*qq + al*be*m*s^2 + al*pp*qq - al*pp*qr*(m*(al - 1) + 1) + al*s^2*(m*(al - 1) + 1) - al*s^2 + be^2*m*qq*s - be^2*m*qr*s - be*qq*s + be*qr*s + qq*s*(m*(al - 1) + 1) - qr*s*(m*(al - 1) + 1) = 0) :
    m*(be+1-al) = 1 ∧ ((al-1)*s = be*qr ∨ qq = rr) := by
  have hbp : 0 < be := by linarith
  have hden : al*s-(be-1)*qq ≠ 0 := by
    intro h
    have h1 : (be-1)*(qq-qr)^2 = 0 := by linear_combination hrel - (rr+qq-2*qr)*h
    have h2 : 0 < (be-1)*(qq-qr)^2 := mul_pos (by linarith) (pow_pos (by linarith) 2)
    linarith
  have hba : s*(qq-qr)*(al+be-1)*(al^3*m*s^2 - 2*al^2*be*m*qr*s + al^2*be*m*s^2 + al^2*m*qq*s - al^2*m*qr*s - al^2*m*s^2 - al^2*s^2 - al*be^2*m*qq*s + al*be^2*m*qr^2 - al*be^2*m*qr*s + 2*al*be*m*qr*s + al*be*qq*s + al*be*qr*s - al*m*qq*s - al*m*qr^2 + al*m*qr*s - 2*al*qr*s + be^3*m*qq*qr - be^2*m*qr^2 - be^2*qq*qr - be*m*qq*qr + be*qq*qr + be*qr^2 + m*qr^2 - qr^2) = 0 := by
    linear_combination (-(al^2*rr*s - al*be*qq*rr + al*be*qr*s + al*qq*rr - al*rr*s - be^2*qq*qr + be*qq*qr + be*qq*rr - qq*rr))*hZba + (-al^3*m*qr*s + al^2*be*m*qq*qr - al^2*be*m*qq*s - al^2*m*qq*qr + al^2*m*qr*s + al^2*qq*s - al^2*qr*s + al*be^2*m*qq^2 - al*be*m*qq^2 - al*be*m*qq*qr - al*be*qq^2 + al*be*qq*qr + al*m*qq*qr + al*qq^2 - al*qq*qr)*hppE + (al^3*m*s^2 - al^2*be*m*qr*s + al^2*be*m*s^2 + al^2*m*qq*s - al^2*m*qr*s - 2*al^2*m*s^2 - al*be^2*m*qr*s + al*be*m*qr*s - al*be*m*s^2 - 2*al*m*qq*s + 2*al*m*qr*s + al*m*s^2 + al*qq*s - al*qr*s - be^2*m*qq*s + be^2*m*qr*s + be*qq*s - be*qr*s + m*qq*s - m*qr*s - qq*s + qr*s)*hrel
  have hab : s*(qq-qr)*(al+be-1)*(al*s - be*qr - s)*(al^2*m*s - al*be*m*qr + al*be*m*s + al*m*qr - al*m*s + al*s - be^2*m*qq + be*m*qq + be*m*qr - be*qr - m*qr + qr) = 0 := by
    linear_combination (al^2*rr*s - al*be*qq*rr + al*be*qr*s + al*qq*rr - al*rr*s - be^2*qq*qr + be*qq*qr + be*qq*rr - qq*rr)*hZab - (al^3*m*qr*s - al^2*be*m*qq*qr + al^2*be*m*qq*s + al^2*m*qq*qr - 2*al^2*m*qr*s + al^2*qr*s - al*be^2*m*qq^2 + al*be*m*qq^2 + 2*al*be*m*qq*qr - al*be*m*qq*s - al*be*qq*qr + al*be*qr*s - 2*al*m*qq*qr + al*m*qr*s + al*qq*qr - al*qr*s + be^2*m*qq^2 - be^2*qq*qr - be*m*qq^2 - be*m*qq*qr + 2*be*qq*qr + m*qq*qr - qq*qr)*hppE - (-al^3*m*s^2 + al^2*be*m*qr*s - al^2*be*m*s^2 + 3*al^2*m*s^2 - al^2*s^2 + al*be^2*m*qr*s - 2*al*be*m*qr*s + 2*al*be*m*s^2 + al*be*qr*s - al*be*s^2 - 3*al*m*s^2 + 2*al*s^2 - be^2*m*qr*s + be^2*qr*s + be*m*qr*s - be*m*s^2 - be*qr*s + be*s^2 + m*s^2 - s^2)*hrel
  have hAvN : s*(al+be-1)*(al^2*m*qq*s - 2*al^2*m*qr*s - al^2*s^2 + al*be*m*qr^2 - al*be*m*qr*s + al*be*qq*s + al*be*qr*s - al*m*qq*s - al*m*qr^2 + 2*al*m*qr*s - 2*al*qr*s + be^2*m*qq*qr - be^2*qq*qr - be*m*qq*qr - be*m*qr^2 + be*qq*qr + be*qr^2 + m*qr^2 - qr^2) = 0 → False := by
    intro h
    have : ((((al-1)*rr+be*qr))*((al*s-(be-1)*qq)))*(-al*pp - be*m*s + be*s - (1+(al-1)*m)*s) = 0 := by
      linear_combination h + (-al^2*s + al*be*qq - al*qq)*hppE + (-al^2*m*s - al*be*m*s + 2*al*m*s - al*s + be*m*s - be*s - m*s + s)*hrel
    have hM : ((((al-1)*rr+be*qr))*((al*s-(be-1)*qq))) ≠ 0 := mul_ne_zero hW.ne' hden
    exact (lt_irrefl _ (lt_of_lt_of_eq hAv ((mul_eq_zero.1 this).resolve_left hM).symm))
  have hp0 : s*(qq-qr)*(al+be-1) ≠ 0 := (mul_pos (mul_pos hs (by linarith)) (by linarith)).ne'
  have hLa : al^3*m*s^2 - 2*al^2*be*m*qr*s + al^2*be*m*s^2 + al^2*m*qq*s - al^2*m*qr*s - al^2*m*s^2 - al^2*s^2 - al*be^2*m*qq*s + al*be^2*m*qr^2 - al*be^2*m*qr*s + 2*al*be*m*qr*s + al*be*qq*s + al*be*qr*s - al*m*qq*s - al*m*qr^2 + al*m*qr*s - 2*al*qr*s + be^3*m*qq*qr - be^2*m*qr^2 - be^2*qq*qr - be*m*qq*qr + be*qq*qr + be*qr^2 + m*qr^2 - qr^2 = 0 := (mul_eq_zero.1 hba).resolve_left hp0
  have hFL : (al*s - be*qr - s)*(al^2*m*s - al*be*m*qr + al*be*m*s + al*m*qr - al*m*s + al*s - be^2*m*qq + be*m*qq + be*m*qr - be*qr - m*qr + qr) = 0 := by
    have := hab; rw [mul_assoc, mul_assoc] at this; exact (mul_eq_zero.1 (by simpa [mul_assoc] using this)).resolve_left hp0
  rcases mul_eq_zero.1 hFL with hF1 | hLc
  · have hG : al*be*s + al*s - be^2*qq - s ≠ 0 := by
      intro hG1
      have : be^6*((al*s-(be-1)*qq))*(((al*s-(be-1)*qq))*(((al-1)*rr+be*qr))) = 0 := by linear_combination (al^2*be^6*s - al*be^7*qq + al*be^6*qq - al*be^6*s + be^7*qq - be^6*qq)*hrel + (al^3*be^2*s^2 - al^2*be^5*qq*s + 2*al^2*be^5*qr*s + al^2*be^4*qq*s - 2*al^2*be^4*qr*s + al^2*be^3*s^2 - 2*al^2*be^2*s^2 - al*be^6*qr^2 + al*be^6*qr*s + al*be^5*qq*s + 2*al*be^5*qr^2 - 3*al*be^5*qr*s - al*be^4*qq*s - al*be^4*qr^2 + 3*al*be^4*qr*s - al*be^3*qr*s - al*be^3*s^2 + al*be^2*s^2 - be^7*qq*qr + 2*be^6*qq*qr + be^6*qr^2 - be^5*qq*qr - 2*be^5*qr^2 + be^5*qr*s + be^4*qr^2 - 2*be^4*qr*s + be^3*qr*s)*hG1 + (-al^3*be^3*s^2 - al^3*be^2*s^2 + al^2*be^4*qr*s - al^2*be^4*s^2 - al^2*be^3*qr*s + 2*al^2*be^2*s^2 + al*be^5*qr*s - 3*al*be^4*qr*s + 2*al*be^3*qr*s + al*be^3*s^2 - al*be^2*s^2 - be^5*qr*s + 2*be^4*qr*s - be^3*qr*s)*hF1
      have : be^6*((al*s-(be-1)*qq))*(((al*s-(be-1)*qq))*(((al-1)*rr+be*qr))) ≠ 0 := mul_ne_zero (mul_ne_zero (pow_pos hbp 6).ne' hden) (mul_ne_zero hden hW.ne')
      exact this (by assumption)
    have hk : -al^3*be*m*s^2 - al^3*m*s^2 + al^2*be^2*m*qq*s + 2*al^2*be*m*s^2 - al^2*be*s^2 + 3*al^2*m*s^2 - al^2*s^2 + al*be^3*m*s^2 - 2*al*be^2*m*qq*s + al*be^2*m*s^2 + al*be^2*qq*s - al*be^2*s^2 - al*be*m*s^2 - 3*al*m*s^2 + 2*al*s^2 - be^4*m*qq*s + be^3*qq*s + be^2*m*qq*s - be^2*m*s^2 - be^2*qq*s + be*s^2 + m*s^2 - s^2 = 0 := by linear_combination (be^2)*hLa - (al^2*be^2*m*s + al^2*be*m*s + al^2*m*s - al*be^3*m*qr + al*be^3*m*s - al*be^2*s + al*be*m*qr - al*be*m*s + al*be*s - 2*al*m*s + al*s - be^4*m*qq + be^3*m*qr + be^3*qq + be^2*m*qq - be^2*m*s - be^2*qq - be^2*qr - be*m*qr + be*qr + be*s + m*s - s)*hF1
    have hk2 : (al*m-be*m-m+1) = 0 := by
      have hq : s*(al+be-1)*(al*be*s + al*s - be^2*qq - s) ≠ 0 := mul_ne_zero (mul_pos hs (by linarith)).ne' hG
      have : (s*(al+be-1)*(al*be*s + al*s - be^2*qq - s))*(al*m-be*m-m+1) = 0 := by linear_combination (-1)*hk
      exact (mul_eq_zero.1 this).resolve_left hq
    exact ⟨by linarith, Or.inl (by linarith)⟩
  · have hLc2 := hLc
    have hres : (al*s - be*qr + qr)*(2*al*s - (be - 1)*(qq + qr))*(al^2*s - al*be*qr + al*be*s - al*s - be^2*qq + be*qr) = 0 := by linear_combination (-(al^2*s - al*be*qr + al*be*s + al*qr - al*s - be^2*qq + be*qq + be*qr - qr))*hLa + (al^3*s^2 - 2*al^2*be*qr*s + al^2*be*s^2 + al^2*qq*s - al^2*qr*s - al^2*s^2 - al*be^2*qq*s + al*be^2*qr^2 - al*be^2*qr*s + 2*al*be*qr*s - al*qq*s - al*qr^2 + al*qr*s + be^3*qq*qr - be^2*qr^2 - be*qq*qr + qr^2)*hLc
    rcases mul_eq_zero.1 hres with h12 | hF4
    · rcases mul_eq_zero.1 h12 with hF2 | hF3
      · exfalso
        have h1 : m*(al^2*s - al*be*qr + al*be*s + al*qr - al*s - be^2*qq + be*qq + be*qr - qr) = 0 := by linear_combination hLc - hF2
        have h2 : al^2*s - al*be*qr + al*be*s + al*qr - al*s - be^2*qq + be*qq + be*qr - qr = 0 := (mul_eq_zero.1 h1).resolve_left hm.ne'
        have h3 : be*(be-1)*((al*s-(be-1)*qq)) = 0 := by linear_combination (-(1 - be))*h2 + (-al*be + al + be - 1)*hF2
        exact (mul_ne_zero (mul_pos (by linarith) (by linarith)).ne' hden) h3
      · have hk : be^3*m*qq^3*s^2 - be^3*m*qq^2*qr*s^2 - 2*be^3*m*qq^2*s^3 - be^3*m*qq*qr^2*s^2 + 4*be^3*m*qq*qr*s^3 + be^3*m*qr^3*s^2 - 2*be^3*m*qr^2*s^3 - be^2*m*qq^3*s^2 + be^2*m*qq^2*qr*s^2 - 2*be^2*m*qq^2*s^3 + be^2*m*qq*qr^2*s^2 + 4*be^2*m*qq*qr*s^3 - be^2*m*qr^3*s^2 - 2*be^2*m*qr^2*s^3 + 2*be^2*qq^2*s^3 - 4*be^2*qq*qr*s^3 + 2*be^2*qr^2*s^3 - be*m*qq^3*s^2 + be*m*qq^2*qr*s^2 + 2*be*m*qq^2*s^3 + be*m*qq*qr^2*s^2 - 4*be*m*qq*qr*s^3 - be*m*qr^3*s^2 + 2*be*m*qr^2*s^3 + m*qq^3*s^2 - m*qq^2*qr*s^2 + 2*m*qq^2*s^3 - m*qq*qr^2*s^2 - 4*m*qq*qr*s^3 + m*qr^3*s^2 + 2*m*qr^2*s^3 - 2*qq^2*s^3 + 4*qq*qr*s^3 - 2*qr^2*s^3 = 0 := by linear_combination (8*s^3)*hLa - (4*al^2*m*s^4 + 2*al*be*m*qq*s^3 - 6*al*be*m*qr*s^3 + 4*al*be*m*s^4 + 2*al*m*qq*s^3 - 6*al*m*qr*s^3 - 4*al*m*s^4 - 4*al*s^4 + be^2*m*qq^2*s^2 - 2*be^2*m*qq*qr*s^2 - 2*be^2*m*qq*s^3 + be^2*m*qr^2*s^2 - 2*be^2*m*qr*s^3 - 4*be*m*qq*s^3 + 4*be*m*qr*s^3 + 2*be*qq*s^3 + 2*be*qr*s^3 - m*qq^2*s^2 + 2*m*qq*qr*s^2 - 2*m*qq*s^3 - m*qr^2*s^2 + 6*m*qr*s^3 + 2*qq*s^3 - 6*qr*s^3)*hF3
        have hq : s^2*(be-1)*(be+1)*(qq-qr)^2 ≠ 0 := (mul_pos (mul_pos (mul_pos (pow_pos hs 2) (by linarith)) (by linarith)) (pow_pos (by linarith) 2)).ne'
        have hK : (-be*m*qq - be*m*qr + 2*be*m*s + m*qq + m*qr + 2*m*s - 2*s) = 0 := by
          have : (s^2*(be-1)*(be+1)*(qq-qr)^2)*(-be*m*qq - be*m*qr + 2*be*m*s + m*qq + m*qr + 2*m*s - 2*s) = 0 := by linear_combination (-1)*hk
          exact (mul_eq_zero.1 this).resolve_left hq
        have hqr : be*qq^2*s - be*qq*qr*s - be*qq*rr*s + be*qr*rr*s - qq^2*s + qq*qr*s + qq*rr*s - qr*rr*s = 0 := by linear_combination (2*s)*hrel - (qq*s - 2*qr*s + rr*s)*hF3
        refine ⟨?_, Or.inr ?_⟩
        · have : 2*s*(m*(be+1-al)-1) = 0 := by linear_combination hK - m*hF3
          have := (mul_eq_zero.1 this).resolve_left (by positivity)
          linarith
        · have h5 : s*(be-1)*(qq-qr)*(qq-rr) = 0 := by linear_combination hqr
          have h6 : s*(be-1)*(qq-qr) ≠ 0 := (mul_pos (mul_pos hs (by linarith)) (by linarith)).ne'
          have := (mul_eq_zero.1 (by linear_combination h5 : (s*(be-1)*(qq-qr))*(qq-rr) = 0)).resolve_left h6
          linarith
    · exfalso
      have hX : -be*(al^2*m*s + al*be*m*s + al*be*s - al*m*s - be^2*qr + be*qr) = 0 := by linear_combination (-be^2)*hLc - (-be^2*m + be*m)*hF4
      have hX0 : (al^2*m*s + al*be*m*s + al*be*s - al*m*s - be^2*qr + be*qr) = 0 := by
        have : be*(al^2*m*s + al*be*m*s + al*be*s - al*m*s - be^2*qr + be*qr) = 0 := by linear_combination (-1)*hX
        exact (mul_eq_zero.1 this).resolve_left hbp.ne'
      have hN : (al^2*m*qq*s - 2*al^2*m*qr*s - al^2*s^2 + al*be*m*qr^2 - al*be*m*qr*s + al*be*qq*s + al*be*qr*s - al*m*qq*s - al*m*qr^2 + 2*al*m*qr*s - 2*al*qr*s + be^2*m*qq*qr - be^2*qq*qr - be*m*qq*qr - be*m*qr^2 + be*qq*qr + be*qr^2 + m*qr^2 - qr^2) = 0 := by
        have : (-be^2)*(al^2*m*qq*s - 2*al^2*m*qr*s - al^2*s^2 + al*be*m*qr^2 - al*be*m*qr*s + al*be*qq*s + al*be*qr*s - al*m*qq*s - al*m*qr^2 + 2*al*m*qr*s - 2*al*qr*s + be^2*m*qq*qr - be^2*qq*qr - be*m*qq*qr - be*m*qr^2 + be*qq*qr + be*qr^2 + m*qr^2 - qr^2) = 0 := by linear_combination (al^2*m*s + al*be*s - al*m*s + be^2*m*qr - be^2*qr - be*m*qr + be*qr)*hF4 + (-al*(al*s - be*qr - s))*hX0
        exact (mul_eq_zero.1 this).resolve_left (neg_ne_zero.2 (pow_pos hbp 2).ne')
      exact hAvN (by rw [hN]; ring)
