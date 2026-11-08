module

public import Minimality.Type08S.L2.K94B
public import Minimality.Type08S.L2.K88D

@[expose] public section

set_option maxHeartbeats 1000000

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option maxHeartbeats 4000000
open scoped RealInnerProductSpace
open Minimality Minimality.Type08Sp Minimality.Type08Sp.C2

theorem k94_corner {a a' b b' c c' d : ℝ³} {α1 β1 β6 γ6 : ℝ}
    (hC : K6mCoords a a' b b' c c' d α1 β1 β6 γ6) (hM : K6sM a a' b b' c c' d)
    (hrel : K16Rel a b c d α1 β1) (hα : 1 < α1) (hβ : 1 < β1) (hβ6 : 1 < β6) (hγ6 : 1 < γ6)
    (hσ : β1 < β6 + γ6) (hX3 : ⟪a - c', a - b'⟫ ≤ 0) (hX4 : 0 ≤ ⟪c' - a, b' - c⟫)
    (hH : 0 ≤ ⟪c' - a', b' - c⟫) (hac : 0 < ⟪a - c', d - a'⟫)
    (hz1 : ⟪a - a', k28l2aU0 a b c d α1 β1⟫ = 0)
    (hz2 : ⟪a', k28l2aU0 a b c d α1 β1⟫ = ⟪c, k28l2aU0 a b c d α1 β1⟫)
    (hgWb : β6 * (α1 - 1) = β1 * (γ6 - 1))
    (hzab : ⟪a - b', k61_R a a' b b' d⟫ = 0) (hzba : ⟪a' - b, k61_R a a' b b' d⟫ = 0) (hne : α1 ≠ β1)
    (hacL : 0 < 1 - α1 + β1 * k61_lam a a' b b' d) (hcbL : 0 < α1 - (β1 - 1) * k61_lam a a' b b' d) :
    IsRupert (V8 a a' b b' c c' d) := by
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
  have hN : ⟪b-d, a'-b'⟫ = α1*s + β6*qq + (γ6-β1)*qr := by
    obtain ⟨-, hc', hb', ha', -⟩ := hC
    exact (k88_ev h1 h2 h3 h4 h5 h6 (x := 0) (y := 1) (z := 0) (x' := -α1) (y' := β6) (z' := -β1+γ6)
      (u := b - d) (v := a' - b') (by module) (by subst hc' hb' ha'; module)).trans (by ring)
  have hAvne : (-α1*pp - β6*s + β1*s - γ6*s) ≠ 0 := by rw [← cAv]; exact hAv.ne
  have hlam : k61_lam a a' b b' d * (-α1*pp - β6*s + β1*s - γ6*s) = -(α1*s + β6*qq + (γ6-β1)*qr) := by
    unfold k61_lam; rw [hN, cAv, div_mul_cancel₀ _ hAvne]
  obtain ⟨hcx, hBcx⟩ := k94_ac α1 β1 β6 γ6 pp s qq qr (k61_lam a a' b b' d) hAvne hlam Zab Zba
  have hsp : 0 < s + pp := by linarith
  have hcx0 : 0 < -(α1-1)*(s+pp) + β1*(qq+s) := by rw [hcx]; exact mul_pos hsp hacL
  have hcxB : -(α1-1)*(s+pp) + β1*(qq+s) < pp + 2*s + qq := by
    have := mul_pos hsp hcbL; linarith
  rw [cAv] at hAv
  rw [cX3] at hX3
  rw [cX4] at hX4
  rw [cH] at hH
  rw [cac] at hac
  obtain ⟨B, P, W, dx, cx, ex, eB, eP, eW, edx, ecx, eex, hB, hd0, hd1, hc0, hc1, hin3, hin4, hin5, hW0, hcase⟩ :=
    k94_alg α1 β1 β6 γ6 pp s qq qr rr m hs hpp hm hqx hqy hα hβ hb6m hg6m hrel' hppE hW hD hdet hD2 hβ6 hγ6 hσ
      hAv hX3 hX4 hH hac Zab Zba hne hcx0 hcxB
  exact k88_of_screen hC (by rw [cAv]; exact hAv) hzab hzba B P W dx cx ex (by rw [eB, cB]; ring) (by rw [eP, cP]; ring)
    (by rw [eW, cW]; ring) (by rw [edx, cdx]; ring) (by rw [ecx, ccx]; ring) (by rw [eex, cex]; ring) hB (by linarith) (by linarith)
    hd0 hd1 hc0 hc1 hin3 hin4 hin5 hW0 hcase

