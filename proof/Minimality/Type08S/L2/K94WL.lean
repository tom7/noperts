module

public import Minimality.Type08S.L2.K94C
public import Minimality.Type08S.L2.K94W4
public import Minimality.Type08S.L2.K89W

@[expose] public section

set_option maxHeartbeats 1000000

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option maxHeartbeats 8000000
open scoped RealInnerProductSpace
open Minimality Minimality.Type08Sp Minimality.Type08Sp.C2

theorem k94_wall {a a' b b' c c' d : ℝ³} {α1 β1 β6 γ6 : ℝ}
    (hC : K6mCoords a a' b b' c c' d α1 β1 β6 γ6) (hM : K6sM a a' b b' c c' d)
    (hrel : K16Rel a b c d α1 β1) (hα : 1 < α1) (hβ : 1 < β1) (hX4 : 0 ≤ ⟪c' - a, b' - c⟫)
    (hz1 : ⟪a - a', k28l2aU0 a b c d α1 β1⟫ = 0)
    (hz2 : ⟪a', k28l2aU0 a b c d α1 β1⟫ = ⟪c, k28l2aU0 a b c d α1 β1⟫)
    (hgWb : β6 * (α1 - 1) = β1 * (γ6 - 1))
    (hzab : ⟪a - b', k61_R a a' b b' d⟫ = 0) (hzba : ⟪a' - b, k61_R a a' b b' d⟫ = 0)
    (hwall : α1 = β1) (hk17 : (α1 - 1) * (β1 - 1) * (β6 + γ6 - 1) ≤ α1 + β1 - 1) :
    HasLexCell (V8 a a' b b' c c' d) ∨ IsRupert (V8 a a' b b' c c' d) := by
  have hC0 := hC
  subst hwall
  obtain ⟨hAv, -⟩ := k71_facts hC hM hrel hα hβ hz1 hz2 hgWb
  obtain ⟨pp, s, qq, qr, rr, m, hpp_d, hs_d, hpr_d, hqq_d, hqr_d, hrr_d, hb6m, hg6m, hs, hpp, hm, hqx, hqy,
    hrel', hppE, hW, hD, hdet, hD2⟩ := k71_gram hC hM hrel hα hβ hz1 hz2 hgWb
  have h1 : ⟪a-d,a-d⟫ = pp := hpp_d.symm
  have h2 : ⟪a-d,b-d⟫ = -s := by linarith
  have h3 : ⟪a-d,c-d⟫ = -s := hpr_d
  have h4 : ⟪b-d,b-d⟫ = qq := hqq_d.symm
  have h5 : ⟪b-d,c-d⟫ = qr := hqr_d.symm
  have h6 : ⟪c-d,c-d⟫ = rr := hrr_d.symm
  obtain ⟨cB, cP, cW, cdx, ccx, cex, cAv, cX3, cX4, cH, cac⟩ := k88_chart hC h1 h2 h3 h4 h5 h6
  obtain ⟨Zab, Zba⟩ := k88_Z hC h1 h2 h3 h4 h5 h6 hAv.ne hzab hzba
  rw [cAv] at hAv
  rw [cX4] at hX4
  have hAv2 := hAv
  rw [hb6m, hg6m] at hAv2
  rw [hb6m, hg6m] at Zab Zba
  obtain ⟨hmα, hbr⟩ := k90_class s pp qq qr rr m α1 α1 hs hm hqx hα hβ hrel' hppE hW (by linarith [hAv2])
    (by linear_combination Zab) (by linear_combination Zba)
  have hm1 : m = 1 := by have := hmα; ring_nf at this; linarith
  have hb6e : β6 = α1 := by rw [hb6m, hm1]; ring
  have hg6e : γ6 = α1 := by rw [hg6m, hm1]; ring
  have he2 : α1 ≤ 2 := by
    by_contra hc; push_neg at hc
    rw [hb6e, hg6e] at hk17
    nlinarith [mul_pos (by linarith : (0:ℝ) < α1 - 2) (by linarith : (0:ℝ) < α1 - 1), mul_pos (mul_pos (by linarith : (0:ℝ) < α1 - 2) (by linarith : (0:ℝ) < α1 - 1)) (by linarith : (0:ℝ) < 2*α1-1)]
  have hWC := k94_wcore s pp qq qr rr α1 hs hpp hqx hqy hα hrel' hppE hD hD2 hdet hX4 he2 hbr
  -- inner products
  have hC1 := hC0
  obtain ⟨-, hc', hb', ha', -⟩ := hC1
  rw [hb6e, hg6e] at ha'
  have ev : ∀ {u v : ℝ³} {x y z x' y' z' : ℝ}, u = x • (a-d) + y • (b-d) + z • (c-d) →
      v = x' • (a-d) + y' • (b-d) + z' • (c-d) →
      ⟪u, v⟫ = x*x'*pp - (x*y'+y*x')*s - (x*z'+z*x')*s + y*y'*qq + (y*z'+z*y')*qr + z*z'*rr :=
    fun hu hv => k88_ev h1 h2 h3 h4 h5 h6 hu hv
  have va : a' - d = (0:ℝ) • (a-d) + α1 • (b-d) + α1 • (c-d) := by rw [ha']; module
  have vb : b' - d = α1 • (a-d) + (0:ℝ) • (b-d) + α1 • (c-d) := by rw [hb']; module
  have vc : c' - d = α1 • (a-d) + α1 • (b-d) + (0:ℝ) • (c-d) := by rw [hc']; module
  have vcc : c - d = (0:ℝ) • (a-d) + (0:ℝ) • (b-d) + (1:ℝ) • (c-d) := by module
  have vbb : b - d = (0:ℝ) • (a-d) + (1:ℝ) • (b-d) + (0:ℝ) • (c-d) := by module
  have vba : b - a = (-1:ℝ) • (a-d) + (1:ℝ) • (b-d) + (0:ℝ) • (c-d) := by module
  have hkap : ⟪c-d, a'-d⟫ = k94_kap α1 qr rr := by
    rw [ev vcc va]; unfold k94_kap; ring
  have hlam : ⟪c-d, b'-d⟫ = k94_lam α1 s rr := by
    rw [ev vcc vb]; unfold k94_lam; ring
  have hLam : ⟪c-d, b-a⟫ = qr + s := by rw [ev vcc vba]; ring
  have vRA : k89_RA a' b' c d = ((α1*(qr+rr))*α1) • (a-d) + (-((α1*(rr-s))*α1)) • (b-d)
      + (((α1*(qr+rr))-(α1*(rr-s)))*α1) • (c-d) := by
    unfold k89_RA
    have e1 := hkap; have e2 := hlam
    unfold k94_kap at e1; unfold k94_lam at e2
    rw [e1, e2, vb, va]; module
  have hsA : ⟪a'-d, k89_RA a' b' c d⟫ = k94_sA pp s qq qr rr α1 := by
    rw [ev va vRA]; unfold k94_sA; ring
  have hzb : ⟪b'-d, k89_RA a' b' c d⟫ = k94_zb pp s qq qr rr α1 := by
    rw [ev vb vRA]; unfold k94_zb; ring
  have hzc : ⟪c'-d, k89_RA a' b' c d⟫ = k94_zc pp s qq qr rr α1 := by
    rw [ev vc vRA]; unfold k94_zc; ring
  have vRB : k89_RB a b c d = (qq-qr) • (a-d) + (qr+s) • (b-d) + (-(qq+s)) • (c-d) := by
    unfold k89_RB; rw [h4, h5, h2]; module
  have hqb : ⟪b-d, b-a⟫ = qq + s := by rw [ev vbb vba]; ring
  have hcRB : ⟪c-d, k89_RB a b c d⟫ = k94_cRB s qq qr rr := by
    rw [ev vcc vRB]; unfold k94_cRB; ring
  have hb1 : ⟪b'-d, k89_RB a b c d⟫ = k94_b1RB pp s qq qr rr α1 := by
    rw [ev vb vRB]; unfold k94_b1RB k94_cRB; ring
  have hbg : β6 = γ6 := by rw [hb6e, hg6e]
  refine k89_wall hC0 hM hα hgWb rfl hbg ?_ ?_ ?_
  · intro hL
    rw [hLam] at hL
    obtain ⟨p1, p2, p3, p4, p5⟩ := hWC.1 hL
    rw [hkap, hlam, hsA, hzb, hzc]
    exact ⟨p1, p2, p3, p4, p5⟩
  · intro hL
    rw [hLam] at hL
    obtain ⟨p1, p2, p3⟩ := hWC.2.1 hL
    rw [hqb, hcRB, hb1]
    exact ⟨p1, p2, p3⟩
  · intro hL
    rw [hLam] at hL
    obtain ⟨t, μ, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10⟩ := hWC.2.2 hL
    refine ⟨t, μ, q1, q2, q3, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [h1]; exact q4
    · rw [h4]; exact q5
    · rw [h6]; exact q6
    · rw [h2]; exact q7
    · rw [h3]; exact q8
    · rw [h5]; exact q9
    · exact q10
