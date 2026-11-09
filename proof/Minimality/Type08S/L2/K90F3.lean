module

public import Minimality.Type08S.L2.K90A

@[expose] public section

set_option maxHeartbeats 1000000

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option maxHeartbeats 40000000

theorem k90_pos_of (a b c : ℝ) (ha : 0 < a) (hc : 0 < c) (h : 0 < a*b/c) : 0 < b := by
  by_contra hb; push Not at hb
  have h1 : a*b ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ha.le hb
  have := div_nonpos_of_nonpos_of_nonneg h1 hc.le
  linarith

theorem k90_nonneg_of (a b c : ℝ) (ha : 0 < a) (hc : 0 < c) (h : 0 ≤ a*b/c) : 0 ≤ b := by
  by_contra hb; push Not at hb
  have h1 : a*b < 0 := mul_neg_of_pos_of_neg ha hb
  have := div_neg_of_neg_of_pos h1 hc
  linarith

theorem k90_F3 (s pp qq qr rr m al be : ℝ) (hs : 0 < s) (hpp : 0 < pp) (hm : 0 < m) (hqx : qr < qq)
    (hbe : 1 < be)
    (hrel : al*s*(qq+rr-2*qr) = (be-1)*(qq*rr-qr^2))
    (hppE : pp*((al-1)*rr+be*qr) = s*((al+be-1)*s+be*(rr-qr)))
    (hdet : 0 < pp*(qq*rr-qr^2) - s^2*(qq+rr-2*qr))
    (hg6 : 1 < 1+(al-1)*m) (hσ : be < be*m + (1+(al-1)*m))
    (hAv : -al*pp - (be*m)*s + be*s - (1+(al-1)*m)*s < 0)
    (hX4 : 0 ≤ al^2*pp - 2*al*be*s - al*pp + al*s + be^2*qr - be*qr + be*s - s)
    (hcx0 : 0 < -(al-1)*(s+pp) + be*(qq+s)) (hcxB : -(al-1)*(s+pp) + be*(qq+s) < pp + 2*s + qq)
    (hq3 : qq = rr) (hmα : m*(be+1-al) = 1) (hne : al ≠ be) :
    ∃ B P W dx cx ex : ℝ, B = pp + 2*s + qq ∧ P = (be*m)*(qq+s) + (1+(al-1)*m)*(qr+s) + s + pp ∧
      W = -(al-1)*(s+pp) + be*(qr+s) ∧ dx = s + pp ∧ cx = -(al-1)*(s+pp) + be*(qq+s) ∧ ex = pp + 2*s + qr ∧
      0 < B ∧ 0 < dx ∧ dx < B ∧ 0 < cx ∧ cx < B ∧
      (1+(al-1)*m) * ex + (B - P) * 1 < (1+(al-1)*m) * B ∧ (be - (1+(al-1)*m)) * ex + (P - W) * 1 < P * be - W * (1+(al-1)*m) ∧ -be * ex + W * 1 < 0 ∧
      W ≤ 0 ∧ ((be < (1+(al-1)*m) ∧ B < P) ∨ ((1+(al-1)*m) < be ∧ W < 0 ∧ B ≤ P) ∨
        ((1+(al-1)*m) < be ∧ W = 0 ∧ B * (be - (1+(al-1)*m)) < P * be ∧ 0 < P)) := by
  rw [← hq3] at hrel hppE hdet
  have hy0 : 0 < pp*(qq+qr)-2*s^2 := by
    have e : (qq-qr)*(pp*(qq+qr)-2*s^2) = pp*(qq*qq-qr^2) - s^2*(qq+qq-2*qr) := by ring
    rw [← e] at hdet
    exact (mul_pos_iff_of_pos_left (sub_pos.2 hqx)).1 hdet
  have hmα0 := hmα
  obtain ⟨u, y, k, hu, hy, hk, hsu, hqqu, hqru⟩ : ∃ u y k : ℝ, 0 < u ∧ 0 < y ∧ 0 < k ∧ s = u*pp ∧
      qq = pp*(u^2+y+k) ∧ qr = pp*(u^2+y-k) :=
    ⟨s/pp, (pp*(qq+qr)-2*s^2)/(2*pp^2), (qq-qr)/(2*pp), by positivity,
      div_pos hy0 (by positivity), div_pos (by linarith) (by positivity),
      by field_simp, by field_simp; ring, by field_simp; ring⟩
  subst hsu hqqu hqru
  have E2 : al*u - (y+u^2)*(be-1) = 0 := by
    have h : (4*k*pp^2)*(al*u - (y+u^2)*(be-1)) = 0 := by linear_combination hrel
    exact (mul_eq_zero.1 h).resolve_left (by positivity)
  have E1 : al*(k+y) - be*(2*k*u+k-y) - k - y = 0 := by
    have h : pp^2*(al*(k+y) - be*(2*k*u+k-y) - k - y) = 0 := by linear_combination hppE
    exact (mul_eq_zero.1 h).resolve_left (by positivity)
  have E3 : be*(y^2 + y*k + y*u^2 + y*u - k*u^2 - k*u) = (y+k)*(y+u^2+u) := by linear_combination u*E1 - (y+k)*E2
  have hD : 0 < y^2 + y*k + y*u^2 + y*u - k*u^2 - k*u := by
    by_contra hc; push Not at hc
    have := mul_nonpos_of_nonneg_of_nonpos (by linarith : (0:ℝ) ≤ be) hc
    have : 0 < (y+k)*(y+u^2+u) := by positivity
    linarith
  have hDx := hD
  generalize hDv : (y^2 + y*k + y*u^2 + y*u - k*u^2 - k*u) = Dv at hD E3
  have hDne := hD.ne'
  have hyune : y+u^2+u ≠ 0 := by positivity
  have hβe : be = (y+k)*(y+u^2+u)/Dv := by
    rw [eq_div_iff hD.ne']; exact E3
  have hαe : al = 2*k*(u+1)*(y+u^2)/Dv := by
    rw [eq_div_iff hD.ne']
    have h : u*(al*Dv - 2*k*(u+1)*(y+u^2)) = 0 := by
      have E3' := E3
      rw [← hDv] at E3' ⊢
      linear_combination (y^2 + y*k + y*u^2 + y*u - k*u^2 - k*u)*E2 + (y+u^2)*E3'
    have := (mul_eq_zero.1 h).resolve_left hu.ne'
    linarith
  have e1 : be+1-al = 2*(y-k*u)*(y+u^2+u)/Dv := by
    rw [hβe, hαe]; field_simp; subst hDv; ring
  rw [e1] at hmα
  have hS2 : 0 < y - k*u := by
    by_contra hc; push Not at hc
    have h1 : 2*(y-k*u)*(y+u^2+u) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
    have h2 := div_nonpos_of_nonpos_of_nonneg h1 hD.le
    have := mul_nonpos_of_nonneg_of_nonpos hm.le h2
    linarith
  have hSx := hS2
  have hMx := hyune
  generalize hSv : (y - k*u) = Sv at hS2 hmα
  generalize hMv : (y+u^2+u) = Mv at hyune hmα
  have hS2ne := hS2.ne'
  have hme : m = Dv/(2*Sv*Mv) := by
    rw [eq_div_iff (by positivity)]
    rw [← mul_div_assoc, div_eq_one_iff_eq hD.ne'] at hmα
    exact hmα
  have a_G : (al-1)*m = (-y+2*k*u+k)/(2*Sv) := by (try simp only [hαe, hme]); field_simp; try (subst hDv hSv hMv; ring)
  have a_Av : (-al*(pp) - (be*m)*(u*pp) + be*(u*pp) - (1+(al-1)*m)*(u*pp)) = -(k*pp*(u+1)*(y^2*u + 2*y^2 - y*k*u + y*u^3 + y*u^2 - k*u^3 - k*u^2))/(Sv*Dv) := by (try simp only [hαe, hβe, hme]); field_simp; try (subst hDv hSv hMv; ring)
  have a_S : (be*m + (1+(al-1)*m)) - be = (k*(y+k)*(u+1)*(y + u^2 - u))/(Sv*Dv) := by (try simp only [hαe, hβe, hme]); field_simp; try (subst hDv hSv hMv; ring)
  have a_X : (al^2*pp - 2*al*be*(u*pp) - al*pp + al*(u*pp) + be^2*(pp*(u^2+y-k)) - be*(pp*(u^2+y-k)) + be*(u*pp) - (u*pp)) = (2*k*pp*(u+1)*(y+u^2+u)*Sv*(k-y))/(Dv^2) := by (try simp only [hαe, hβe]); field_simp; try (subst hDv hSv hMv; ring)

  have hG1 : 0 < -y+2*k*u+k := by
    have h : 0 < (al-1)*m := by linarith
    rw [a_G] at h; exact (div_pos_iff_of_pos_right (by positivity)).1 h
  have hHH : 0 < y^2*u + 2*y^2 - y*k*u + y*u^3 + y*u^2 - k*u^3 - k*u^2 := by
    have h : 0 < k*pp*(u+1)*(y^2*u + 2*y^2 - y*k*u + y*u^3 + y*u^2 - k*u^3 - k*u^2)/(Sv*Dv) := by
      have h2 : (-al*pp - (be*m)*(u*pp) + be*(u*pp) - (1+(al-1)*m)*(u*pp)) < 0 := hAv
      rw [a_Av, neg_div] at h2; linarith
    exact k90_pos_of _ _ _ (by positivity) (by positivity) h
  have hSG : 0 < y + u^2 - u := by
    have h : 0 < k*(y+k)*(u+1)*(y + u^2 - u)/(Sv*Dv) := by rw [← a_S]; linarith
    exact k90_pos_of _ _ _ (by positivity) (by positivity) h
  have hGH : 0 ≤ k - y := by
    have h : 0 ≤ 2*k*pp*(u+1)*(y+u^2+u)*Sv*(k-y)/(Dv^2) := by rw [← a_X]; exact hX4
    exact k90_nonneg_of _ _ _ (by positivity) (by positivity) h
  have hN4 : 0 < -y^2 + 2*y*k*u^2 + 5*y*k*u + y*k + k^2*u + 2*k*u^4 + 4*k*u^3 + 2*k*u^2 := by
    linear_combination 2 * (mul_pos (mul_pos hu hu) hk) + 5 * (mul_pos (mul_pos hu hy) hy) + 1 * (mul_pos (mul_pos hu hk) hk) + 4 * (mul_pos (mul_pos (mul_pos hu hu) hu) hk) + 2 * (mul_pos (mul_pos (mul_pos hu hu) hy) hk) + 2 * (mul_pos (mul_pos (mul_pos (mul_pos hu hu) hu) hu) hy) + 1 * (mul_nonneg (hy).le hGH) + 5 * (mul_nonneg ((mul_pos hu hy)).le hGH) + 2 * (mul_nonneg ((mul_pos (mul_pos (mul_pos hu hu) hu) hu)).le hGH)
  have e_B : (pp + 2*(u*pp) + pp*(u^2+y+k)) = (1)*pp^1*(k + u^2 + 2*u + y + 1)^1 := by field_simp; try (subst hDv hSv hMv; ring)
  have p_B : 0 < (1)*pp^1*(k + u^2 + 2*u + y + 1)^1 := by positivity
  have r_B : 0 < (pp + 2*(u*pp) + pp*(u^2+y+k)) := by rw [e_B]; exact p_B
  have e_dx : ((u*pp)+pp) = (1)*pp^1*(u + 1)^1 := by field_simp
  have p_dx : 0 < (1)*pp^1*(u + 1)^1 := by positivity
  have r_dx : 0 < ((u*pp)+pp) := by rw [e_dx]; exact p_dx
  have e_Bdx : ((pp + 2*(u*pp) + pp*(u^2+y+k)) - ((u*pp)+pp)) = (1)*pp^1*(k + u^2 + u + y)^1 := by field_simp; try (subst hDv hSv hMv; ring)
  have p_Bdx : 0 < (1)*pp^1*(k + u^2 + u + y)^1 := by positivity
  have r_Bdx : 0 < ((pp + 2*(u*pp) + pp*(u^2+y+k)) - ((u*pp)+pp)) := by rw [e_Bdx]; exact p_Bdx
  have e_in3 : ((1+(al-1)*m)*(pp + 2*(u*pp) + pp*(u^2+y+k)) - (1+(al-1)*m)*(pp + 2*(u*pp) + pp*(u^2+y-k)) - ((pp + 2*(u*pp) + pp*(u^2+y+k)) - ((be*m)*(pp*(u^2+y+k)+(u*pp)) + (1+(al-1)*m)*(pp*(u^2+y-k)+(u*pp)) + (u*pp) + pp))) = ((1)*k^1*pp^1*(u + 1)^1*(k + u^2 + u + y)^1)/((Sv)^1) := by (try simp only [hαe, hβe, hme]); field_simp; try (subst hDv hSv hMv; ring)
  have p_in3 : 0 < ((1)*k^1*pp^1*(u + 1)^1*(k + u^2 + u + y)^1)/((Sv)^1) := by positivity
  have r_in3 : 0 < ((1+(al-1)*m)*(pp + 2*(u*pp) + pp*(u^2+y+k)) - (1+(al-1)*m)*(pp + 2*(u*pp) + pp*(u^2+y-k)) - ((pp + 2*(u*pp) + pp*(u^2+y+k)) - ((be*m)*(pp*(u^2+y+k)+(u*pp)) + (1+(al-1)*m)*(pp*(u^2+y-k)+(u*pp)) + (u*pp) + pp))) := by rw [e_in3]; exact p_in3
  have e_in4 : (((be*m)*(pp*(u^2+y+k)+(u*pp)) + (1+(al-1)*m)*(pp*(u^2+y-k)+(u*pp)) + (u*pp) + pp)*be - (-(al-1)*((u*pp)+pp) + be*(pp*(u^2+y-k)+(u*pp)))*(1+(al-1)*m) - (be-(1+(al-1)*m))*(pp + 2*(u*pp) + pp*(u^2+y-k)) - (((be*m)*(pp*(u^2+y+k)+(u*pp)) + (1+(al-1)*m)*(pp*(u^2+y-k)+(u*pp)) + (u*pp) + pp) - (-(al-1)*((u*pp)+pp) + be*(pp*(u^2+y-k)+(u*pp))))) = ((1)*k^1*pp^1*(u + 1)^1*(-y^2 + 2*y*k*u^2 + 5*y*k*u + y*k + k^2*u + 2*k*u^4 + 4*k*u^3 + 2*k*u^2)^1)/((Sv)^1*(Dv)^1) := by (try simp only [hαe, hβe, hme]); field_simp; try (subst hDv hSv hMv; ring)
  have p_in4 : 0 < ((1)*k^1*pp^1*(u + 1)^1*(-y^2 + 2*y*k*u^2 + 5*y*k*u + y*k + k^2*u + 2*k*u^4 + 4*k*u^3 + 2*k*u^2)^1)/((Sv)^1*(Dv)^1) := by positivity
  have r_in4 : 0 < (((be*m)*(pp*(u^2+y+k)+(u*pp)) + (1+(al-1)*m)*(pp*(u^2+y-k)+(u*pp)) + (u*pp) + pp)*be - (-(al-1)*((u*pp)+pp) + be*(pp*(u^2+y-k)+(u*pp)))*(1+(al-1)*m) - (be-(1+(al-1)*m))*(pp + 2*(u*pp) + pp*(u^2+y-k)) - (((be*m)*(pp*(u^2+y+k)+(u*pp)) + (1+(al-1)*m)*(pp*(u^2+y-k)+(u*pp)) + (u*pp) + pp) - (-(al-1)*((u*pp)+pp) + be*(pp*(u^2+y-k)+(u*pp))))) := by rw [e_in4]; exact p_in4
  have e_in5 : (be*(pp + 2*(u*pp) + pp*(u^2+y-k)) - (-(al-1)*((u*pp)+pp) + be*(pp*(u^2+y-k)+(u*pp)))) = ((2)*k^1*pp^1*(u + 1)^2*(u^2 + u + y)^1)/((Dv)^1) := by (try simp only [hαe, hβe]); field_simp; try (subst hDv hSv hMv; ring)
  have p_in5 : 0 < ((2)*k^1*pp^1*(u + 1)^2*(u^2 + u + y)^1)/((Dv)^1) := by positivity
  have r_in5 : 0 < (be*(pp + 2*(u*pp) + pp*(u^2+y-k)) - (-(al-1)*((u*pp)+pp) + be*(pp*(u^2+y-k)+(u*pp)))) := by rw [e_in5]; exact p_in5
  have e_PB : (((be*m)*(pp*(u^2+y+k)+(u*pp)) + (1+(al-1)*m)*(pp*(u^2+y-k)+(u*pp)) + (u*pp) + pp) - (pp + 2*(u*pp) + pp*(u^2+y+k))) = ((1)*k^1*pp^1*u^1*(k + u^2 + 2*u + y + 1)^1)/((Sv)^1) := by (try simp only [hαe, hβe, hme]); field_simp; try (subst hDv hSv hMv; ring)
  have p_PB : 0 < ((1)*k^1*pp^1*u^1*(k + u^2 + 2*u + y + 1)^1)/((Sv)^1) := by positivity
  have r_PB : 0 < (((be*m)*(pp*(u^2+y+k)+(u*pp)) + (1+(al-1)*m)*(pp*(u^2+y-k)+(u*pp)) + (u*pp) + pp) - (pp + 2*(u*pp) + pp*(u^2+y+k))) := by rw [e_PB]; exact p_PB
  have e_W : -(-(al-1)*((u*pp)+pp) + be*(pp*(u^2+y-k)+(u*pp))) = ((1)*pp^1*(k - y)^1*(u^2 + u + y)^1*(k + u^2 + 2*u + y + 1)^1)/((Dv)^1) := by (try simp only [hαe, hβe]); field_simp; try (subst hDv hSv hMv; ring)
  have p_W : 0 ≤ ((1)*pp^1*(k - y)^1*(u^2 + u + y)^1*(k + u^2 + 2*u + y + 1)^1)/((Dv)^1) := by positivity
  have p_Wneg : 0 < k - y → 0 < ((1)*pp^1*(k - y)^1*(u^2 + u + y)^1*(k + u^2 + 2*u + y + 1)^1)/((Dv)^1) := fun hGHp => by positivity
  have e_Wz : k - y = 0 → (-(al-1)*((u*pp)+pp) + be*(pp*(u^2+y-k)+(u*pp))) = 0 := fun h => by
    have h3 : -((-(al-1)*((u*pp)+pp) + be*(pp*(u^2+y-k)+(u*pp)))) = 0 := by rw [e_W, h]; simp
    linarith
  have a_Av : (-al*(pp) - (be*m)*(u*pp) + be*(u*pp) - (1+(al-1)*m)*(u*pp)) = -((1)*k^1*pp^1*(u + 1)^1*(y^2*u + 2*y^2 - y*k*u + y*u^3 + y*u^2 - k*u^3 - k*u^2)^1)/((Sv)^1*(Dv)^1) := by (try simp only [hαe, hβe, hme]); field_simp; try (subst hDv hSv hMv; ring)

  have hQ : 0 < 1+(al-1)*m := by linarith
  have hne' : be ≠ 1+(al-1)*m := by
    intro h
    have h3 : be*(m-1) = 0 := by linear_combination hmα0 - h
    have h4 : m = 1 := by have := (mul_eq_zero.1 h3).resolve_left (by linarith); linarith
    apply hne; rw [h4] at hmα0; linarith
  refine ⟨_, _, _, _, _, _, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · linarith [r_B]
  · linarith [r_dx]
  · linarith [r_Bdx]
  · exact hcx0
  · exact hcxB
  · nlinarith [r_in3]
  · nlinarith [r_in4]
  · nlinarith [r_in5]
  · linarith [p_W, e_W]
  · rcases lt_or_gt_of_ne hne' with h | h
    · left; exact ⟨h, by linarith [r_PB, r_B]⟩
    · right
      rcases eq_or_lt_of_le hGH with h0 | h1
      · right
        have hW0 := e_Wz h0.symm
        refine ⟨h, hW0, ?_, ?_⟩
        · nlinarith [r_PB, r_B]
        · linarith [r_PB, r_B]
      · left
        refine ⟨h, ?_, by linarith [r_PB, r_B]⟩
        have := p_Wneg h1
        nlinarith [e_W]
