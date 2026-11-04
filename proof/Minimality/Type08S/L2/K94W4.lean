module

public import Minimality.Type08S.L2.K94W3

@[expose] public section

set_option maxHeartbeats 1000000

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option maxHeartbeats 40000000

def K94WC (pp s qq qr rr e : ℝ) : Prop :=
    (0 < qr + s → 0 < k94_kap e qr rr ∧ 0 < k94_lam e s rr ∧ k94_sA pp s qq qr rr e < 0 ∧
      0 < k94_zb pp s qq qr rr e ∧ k94_zc pp s qq qr rr e < 0) ∧
    (qr + s < 0 → 0 < qq + s ∧ k94_cRB s qq qr rr < 0 ∧ 0 < k94_b1RB pp s qq qr rr e) ∧
    (qr + s = 0 → ∃ t μ : ℝ, 1 < t ∧ t ≤ 5/3 ∧ 0 < μ ∧ pp = μ ∧ qq = μ ∧ rr = μ ∧
      -s = -μ * ((t-1)/(2*t)) ∧ -s = -μ * ((t-1)/(2*t)) ∧ qr = -μ * ((t-1)/(2*t)) ∧ e = (t+1)/(3-t))

theorem k94_w3d (s pp qq qr rr e : ℝ) (hs : 0 < s) (hpp : 0 < pp) (hqx : qr < qq) (he1 : 1 < e)
    (hrel : e*s*(qq+rr-2*qr) = (e-1)*(qq*rr-qr^2))
    (hppE : pp*((e-1)*rr+e*qr) = s*((e+e-1)*s+e*(rr-qr)))
    (hdet : 0 < pp*(qq*rr-qr^2) - s^2*(qq+rr-2*qr))
    (hX4 : 0 ≤ e^2*pp - 2*e*e*s - e*pp + e*s + e^2*qr - e*qr + e*s - s)
    (hk17 : e ≤ 2) (hq3 : qq = rr) : K94WC pp s qq qr rr e := by
  subst hq3
  have hy0 : 0 < pp*(qq+qr)-2*s^2 := by
    have e : (qq-qr)*(pp*(qq+qr)-2*s^2) = pp*(qq*qq-qr^2) - s^2*(qq+qq-2*qr) := by ring
    rw [← e] at hdet
    exact (mul_pos_iff_of_pos_left (sub_pos.2 hqx)).1 hdet
  obtain ⟨u, y, k, hu, hy, hk, hsu, hqqu, hqru⟩ : ∃ u y k : ℝ, 0 < u ∧ 0 < y ∧ 0 < k ∧ s = u*pp ∧
      qq = pp*(u^2+y+k) ∧ qr = pp*(u^2+y-k) :=
    ⟨s/pp, (pp*(qq+qr)-2*s^2)/(2*pp^2), (qq-qr)/(2*pp), by positivity,
      div_pos hy0 (by positivity), div_pos (by linarith) (by positivity),
      by field_simp, by field_simp; ring, by field_simp; ring⟩
  subst hsu hqqu hqru
  have E2 : e*u - (y+u^2)*(e-1) = 0 := by
    have h : (4*k*pp^2)*(e*u - (y+u^2)*(e-1)) = 0 := by linear_combination hrel
    exact (mul_eq_zero.1 h).resolve_left (by positivity)
  have E1 : 2*e*(y-k*u) - k - y = 0 := by
    have h : pp^2*(e*(k+y) - e*(2*k*u+k-y) - k - y) = 0 := by linear_combination hppE
    have := (mul_eq_zero.1 h).resolve_left (by positivity)
    linear_combination this
  obtain ⟨g, hgd⟩ : ∃ g, g = y+u^2-u := ⟨_, rfl⟩
  have hEg : e*g - (y+u^2) = 0 := by rw [hgd]; linear_combination (-1)*E2
  have hg : 0 < g := by
    by_contra hc; push Not at hc
    nlinarith [mul_nonpos_of_nonneg_of_nonpos (by linarith : (0:ℝ) ≤ e) hc, mul_pos hu hu]
  have hgne := hg.ne'
  have he : e = (u+g)/g := by
    rw [eq_div_iff hgne]; linarith [hEg, hgd]
  have hkq : k*(2*(u+g)*u+g) = y*(2*u+g) := by
    have : k*(2*(y+u^2)*u+g) = y*((y+u^2)+u) := by
      linear_combination (-g)*E1 + 2*(y-k*u)*hEg + (-y)*hgd
    have hw : y + u^2 = u + g := by linarith
    rw [hw] at this; linarith
  have hQ : 0 < 2*(u+g)*u+g := by positivity
  have hk' : k = y*(2*u+g)/(2*(u+g)*u+g) := by
    rw [eq_div_iff hQ.ne']; exact hkq
  have hw1 : u + g ≤ 1 := by
    have eX : e^2*pp - 2*e*e*(u*pp) - e*pp + e*(u*pp) + e^2*(pp*(u^2+y-k)) - e*(pp*(u^2+y-k)) + e*(u*pp) - (u*pp)
        = pp*u*y*(1-(u+g))/(g*(2*(u+g)*u+g)) := by
      rw [he, hk']; field_simp; subst hgd; ring
    rw [eX] at hX4
    by_contra hc; push Not at hc
    have : pp*u*y*(1-(u+g))/(g*(2*(u+g)*u+g)) < 0 :=
      div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (by positivity) (by linarith)) (by positivity)
    linarith
  exact k94_w3f pp u y g k e (u*pp) (pp*(u^2+y+k)) (pp*(u^2+y-k)) (pp*(u^2+y+k)) hpp hu hy hg hgd hw1 hk17
    rfl hk' rfl rfl rfl he

theorem k94_wcore (s pp qq qr rr e : ℝ) (hs : 0 < s) (hpp : 0 < pp) (hqx : qr < qq) (hqy : qr < rr) (he1 : 1 < e)
    (hrel : e*s*(qq+rr-2*qr) = (e-1)*(qq*rr-qr^2))
    (hppE : pp*((e-1)*rr+e*qr) = s*((e+e-1)*s+e*(rr-qr)))
    (hD : 0 < qq*rr-qr^2) (hD2 : s^2 < pp*qq)
    (hdet : 0 < pp*(qq*rr-qr^2) - s^2*(qq+rr-2*qr))
    (hX4 : 0 ≤ e^2*pp - 2*e*e*s - e*pp + e*s + e^2*qr - e*qr + e*s - s)
    (hk17 : e ≤ 2) (hbr : (e-1)*s = e*qr ∨ qq = rr) : K94WC pp s qq qr rr e := by
  rcases hbr with hF1 | hq3
  · obtain ⟨hL, h1, h2, h3, h4, h5⟩ := k94_w1 s pp qq qr rr e hs hpp hqx hqy he1 hrel hppE hD hD2 hF1
    exact ⟨fun _ => ⟨h1, h2, h3, h4, h5⟩, fun h => absurd h (not_lt.2 hL.le), fun h => absurd h hL.ne'⟩
  · exact k94_w3d s pp qq qr rr e hs hpp hqx he1 hrel hppE hdet hX4 hk17 hq3
