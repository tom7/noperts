module

public import Minimality.Type08S.L2.K94W1

@[expose] public section

set_option maxHeartbeats 1000000

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option maxHeartbeats 40000000

theorem k94_w3f (pp u y g k e s qq qr rr : ℝ) (hpp : 0 < pp) (hu : 0 < u) (hy : 0 < y) (hg : 0 < g)
    (hgd : g = y+u^2-u) (hw1 : u+g ≤ 1) (hk17 : e ≤ 2)
    (hs : s = u*pp) (hk : k = y*(2*u+g)/(2*(u+g)*u+g)) (hqq : qq = pp*(u^2+y+k)) (hrr : rr = qq)
    (hqr : qr = pp*(u^2+y-k)) (he : e = (u+g)/g) :
    (0 < qr + s → 0 < k94_kap e qr rr ∧ 0 < k94_lam e s rr ∧ k94_sA pp s qq qr rr e < 0 ∧
      0 < k94_zb pp s qq qr rr e ∧ k94_zc pp s qq qr rr e < 0) ∧
    (qr + s < 0 → 0 < qq + s ∧ k94_cRB s qq qr rr < 0 ∧ 0 < k94_b1RB pp s qq qr rr e) ∧
    (qr + s = 0 → ∃ t μ : ℝ, 1 < t ∧ t ≤ 5/3 ∧ 0 < μ ∧ pp = μ ∧ qq = μ ∧ rr = μ ∧
      -s = -μ * ((t-1)/(2*t)) ∧ -s = -μ * ((t-1)/(2*t)) ∧ qr = -μ * ((t-1)/(2*t)) ∧ e = (t+1)/(3-t)) := by
  have hgne := hg.ne'
  have hQ : 0 < 2*(u+g)*u+g := by positivity
  have hQne := hQ.ne'
  obtain ⟨d1, hd1, hd1d⟩ : ∃ d1, 0 ≤ d1 ∧ d1 = 1 - u - g := ⟨1-u-g, by linarith, rfl⟩
  have e_Lam : qr + s = pp*u*(g+2*u)*(2*g+3*u-1)/(2*(u+g)*u+g) := by
    simp only [hs, hqr, hk]; field_simp; subst hgd; ring
  have e_kap : k94_kap e qr rr = 2*pp*(g+u)^2/g := by
    unfold k94_kap; simp only [hrr, hqq, hqr, hk, he]; field_simp; subst hgd; ring
  have e_lam : k94_lam e s rr = pp*(g+u)*(2*g^2*u+2*g^2+g*u^2+3*g*u+2*u^2*(g+d1))/(g*(2*(u+g)*u+g)) := by
    unfold k94_lam; simp only [hs, hrr, hqq, hk, he]; field_simp; subst hd1d hgd; ring
  have e_sA : k94_sA pp s qq qr rr e = -(4*pp^2*(g+u)^4*(g+2*u)*y/(g^3*(2*(u+g)*u+g))) := by
    unfold k94_sA; simp only [hs, hrr, hqq, hqr, hk, he]; field_simp; subst hgd; ring
  have e_zb : k94_zb pp s qq qr rr e = 2*pp^2*(g+u)^3*y*(3*g*u+g+4*u^2)/(g^3*(2*(u+g)*u+g)) := by
    unfold k94_zb; simp only [hs, hrr, hqq, hqr, hk, he]; field_simp; subst hgd; ring
  have e_zc : k94_zc pp s qq qr rr e = -(2*pp^2*(g+u)^3*y*(2*g+3*u-1)/(g^2*(2*(u+g)*u+g))) := by
    unfold k94_zc; simp only [hs, hrr, hqq, hqr, hk, he]; field_simp; subst hgd; ring
  have e_qb : qq + s = pp*(g+2*u)*(2*g+u)*(u+1)/(2*(u+g)*u+g) := by
    simp only [hs, hqq, hk]; field_simp; subst hgd; ring
  have e_cRB : k94_cRB s qq qr rr = -(4*pp^2*(g+2*u)^2*y/(2*(u+g)*u+g)) := by
    unfold k94_cRB; simp only [hs, hrr, hqq, hqr, hk]; field_simp; subst hgd; ring
  have e_b1 : k94_b1RB pp s qq qr rr e = 2*pp^2*(g+u)*(g+2*u)*y*(1-2*g-3*u)/(g*(2*(u+g)*u+g)) := by
    unfold k94_b1RB k94_cRB; simp only [hs, hrr, hqq, hqr, hk, he]; field_simp; subst hgd; ring
  refine ⟨?_, ?_, ?_⟩
  · intro hL
    rw [e_Lam] at hL
    have h2 : 0 < 2*g+3*u-1 := by
      by_contra hc; push_neg at hc
      have : pp*u*(g+2*u)*(2*g+3*u-1)/(2*(u+g)*u+g) ≤ 0 :=
        div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos (by positivity) hc) hQ.le
      linarith
    refine ⟨by rw [e_kap]; positivity, by rw [e_lam]; positivity, ?_, by rw [e_zb]; positivity, ?_⟩
    · rw [e_sA]; have : 0 < 4*pp^2*(g+u)^4*(g+2*u)*y/(g^3*(2*(u+g)*u+g)) := by positivity
      linarith
    · rw [e_zc]; have : 0 < 2*pp^2*(g+u)^3*y*(2*g+3*u-1)/(g^2*(2*(u+g)*u+g)) := by positivity
      linarith
  · intro hL
    rw [e_Lam] at hL
    have h2 : 0 < 1-2*g-3*u := by
      by_contra hc; push_neg at hc
      have : 0 ≤ pp*u*(g+2*u)*(2*g+3*u-1)/(2*(u+g)*u+g) :=
        div_nonneg (mul_nonneg (by positivity) (by linarith)) hQ.le
      linarith
    refine ⟨by rw [e_qb]; positivity, ?_, by rw [e_b1]; positivity⟩
    rw [e_cRB]; have : 0 < 4*pp^2*(g+2*u)^2*y/(2*(u+g)*u+g) := by positivity
    linarith
  · intro hL
    rw [e_Lam] at hL
    have hc0 : 2*g+3*u-1 = 0 := by
      have h1 : pp*u*(g+2*u)*(2*g+3*u-1) = 0 := by
        rcases div_eq_zero_iff.1 hL with h | h
        · exact h
        · exact absurd h hQne
      have hne : pp*u*(g+2*u) ≠ 0 := by positivity
      exact (mul_eq_zero.1 h1).resolve_left hne
    have hqs : qr = -s := by
      have : qr + s = 0 := by rw [e_Lam]; rw [hc0]; simp
      linarith
    have hkw : k = u^2+y+u := by
      have h : pp*(u^2+y-k+u) = 0 := by
        have : qr + s = 0 := by rw [e_Lam]; rw [hc0]; simp
        rw [hqr, hs] at this; linarith
      have := (mul_eq_zero.1 h).resolve_left hpp.ne'
      linarith
    have hqqp : qq = pp := by
      rw [hqq, hkw]
      have : y = g + u - u^2 := by linarith
      have h3 : 2*(u^2+y)+u = 1 := by rw [this]; nlinarith
      nlinarith [h3]
    have hu3 : u < 1/3 := by linarith
    have hug : u ≤ g := by
      have h2e : (u+g)/g ≤ 2 := by rw [← he]; exact hk17
      rw [div_le_iff₀ hg] at h2e; linarith
    have hu5 : u ≤ 1/5 := by linarith
    have h12 : 0 < 1 - 2*u := by linarith
    have hs' : s = u*pp := hs
    obtain ⟨t, ht⟩ : ∃ t : ℝ, t*(1-2*u) = 1 := ⟨1/(1-2*u), by field_simp⟩
    have htpos : 0 < t := by
      by_contra hc; push_neg at hc
      nlinarith [mul_nonpos_of_nonpos_of_nonneg hc h12.le]
    have hkey : (t-1)/(2*t) = u := by
      rw [div_eq_iff (by positivity)]; nlinarith [ht]
    have ht1 : 1 < t := by nlinarith [ht]
    have ht53 : t ≤ 5/3 := by nlinarith [ht]
    refine ⟨t, pp, ht1, ht53, hpp, rfl, hqqp, by rw [hrr, hqqp], ?_, ?_, ?_, ?_⟩
    · rw [hkey, hs']; ring
    · rw [hkey, hs']; ring
    · rw [hkey, hqs, hs']; ring
    · rw [he, div_eq_div_iff hgne (by linarith)]
      have : g = (1-3*u)/2 := by linarith
      rw [this]
      nlinarith [ht]
