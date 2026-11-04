module

public import Minimality.Type08S.L2.K88D

@[expose] public section

set_option maxHeartbeats 1000000

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option maxHeartbeats 1000000
open scoped RealInnerProductSpace
open Minimality Minimality.Type08Sp Minimality.Type08Sp.C2

/-- The remaining PURE-REAL statement (chart algebra of the corner F1 u F3). -/
def K88Alg : Prop := ∀ (α1 β1 β6 γ6 pp s qq qr rr m : ℝ),
  0 < s → 0 < pp → 0 < m → qr < qq → qr < rr → 1 < α1 → 1 < β1 → β6 = β1 * m → γ6 = 1 + (α1 - 1) * m →
  α1 * s * (qq + rr - 2 * qr) = (β1 - 1) * (qq * rr - qr ^ 2) →
  pp * ((α1 - 1) * rr + β1 * qr) = s * ((α1 + β1 - 1) * s + β1 * (rr - qr)) →
  0 < (α1 - 1) * rr + β1 * qr → 0 < qq * rr - qr ^ 2 →
  0 < pp * (qq * rr - qr ^ 2) - s ^ 2 * (qq + rr - 2 * qr) → s ^ 2 < pp * qq →
  1 < β6 → 1 < γ6 → β1 < β6 + γ6 →
  (-α1*pp - β6*s + β1*s - γ6*s < 0) →
  (α1^2*pp - 2*α1*β1*s - 2*α1*pp + β1^2*qr + 2*β1*s + pp ≤ 0) →
  (0 ≤ α1^2*pp - 2*α1*β1*s - α1*pp + α1*s + β1^2*qr - β1*qr + β1*s - s) →
  (0 ≤ α1^2*pp + α1*β6*s - 2*α1*β1*s + α1*γ6*s + α1*s - β6*β1*qr + β6*qr + β1^2*qr - β1*γ6*rr - β1*qr + γ6*rr) →
  (0 < -α1*β6*s - α1*γ6*s + β6*β1*qq + β6*s + β1*γ6*qr + γ6*s) →
  (α1*β6*pp*qq - α1*β6*s^2 + α1*γ6*pp*qr - α1*γ6*s^2 - β6*β1*qq*s + β6*β1*qr*s - β6*pp*qq + β6*s^2 + β1*pp*qr - β1*s^2 - γ6*pp*qr + γ6*s^2 = 0) → (-α1*β6*pp*qq + α1*β6*s^2 - α1*γ6*pp*qr + α1*γ6*s^2 + α1*pp*qq - α1*s^2 + β6*β1*qq*s - β6*β1*qr*s - β1*qq*s + β1*qr*s + γ6*qq*s - γ6*qr*s = 0) → α1 ≠ β1 →
  ∃ B P W dx cx ex : ℝ, B = pp + 2*s + qq ∧ P = β6*(qq+s) + γ6*(qr+s) + s + pp ∧
    W = -(α1-1)*(s+pp) + β1*(qr+s) ∧ dx = s + pp ∧ cx = -(α1-1)*(s+pp) + β1*(qq+s) ∧ ex = pp + 2*s + qr ∧
    0 < B ∧ 0 < dx ∧ dx < B ∧ 0 < cx ∧ cx < B ∧
    γ6 * ex + (B - P) * 1 < γ6 * B ∧ (β1 - γ6) * ex + (P - W) * 1 < P * β1 - W * γ6 ∧ -β1 * ex + W * 1 < 0 ∧
    W ≤ 0 ∧ ((β1 < γ6 ∧ B < P) ∨ (γ6 < β1 ∧ W < 0 ∧ B ≤ P) ∨
      (γ6 < β1 ∧ W = 0 ∧ B * (β1 - γ6) < P * β1 ∧ 0 < P))

theorem k88_corner {a a' b b' c c' d : ℝ³} {α1 β1 β6 γ6 : ℝ} (halg : K88Alg)
    (hC : K6mCoords a a' b b' c c' d α1 β1 β6 γ6) (hM : K6sM a a' b b' c c' d)
    (hrel : K16Rel a b c d α1 β1) (hα : 1 < α1) (hβ : 1 < β1) (hβ6 : 1 < β6) (hγ6 : 1 < γ6)
    (hσ : β1 < β6 + γ6) (hX3 : ⟪a - c', a - b'⟫ ≤ 0) (hX4 : 0 ≤ ⟪c' - a, b' - c⟫)
    (hH : 0 ≤ ⟪c' - a', b' - c⟫) (hac : 0 < ⟪a - c', d - a'⟫)
    (hz1 : ⟪a - a', k28l2aU0 a b c d α1 β1⟫ = 0)
    (hz2 : ⟪a', k28l2aU0 a b c d α1 β1⟫ = ⟪c, k28l2aU0 a b c d α1 β1⟫)
    (hgWb : β6 * (α1 - 1) = β1 * (γ6 - 1))
    (hzab : ⟪a - b', k61_R a a' b b' d⟫ = 0) (hzba : ⟪a' - b, k61_R a a' b b' d⟫ = 0) (hne : α1 ≠ β1) :
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
  rw [cAv] at hAv
  rw [cX3] at hX3
  rw [cX4] at hX4
  rw [cH] at hH
  rw [cac] at hac
  obtain ⟨B, P, W, dx, cx, ex, eB, eP, eW, edx, ecx, eex, hB, hd0, hd1, hc0, hc1, hin3, hin4, hin5, hW0, hcase⟩ :=
    halg α1 β1 β6 γ6 pp s qq qr rr m hs hpp hm hqx hqy hα hβ hb6m hg6m hrel' hppE hW hD hdet hD2 hβ6 hγ6 hσ
      hAv hX3 hX4 hH hac Zab Zba hne
  exact k88_of_screen hC (by rw [cAv]; exact hAv) hzab hzba B P W dx cx ex (by rw [eB, cB]; ring) (by rw [eP, cP]; ring)
    (by rw [eW, cW]; ring) (by rw [edx, cdx]; ring) (by rw [ecx, ccx]; ring) (by rw [eex, cex]; ring) hB (by linarith) (by linarith)
    hd0 hd1 hc0 hc1 hin3 hin4 hin5 hW0 hcase
