module

public import Minimality.Type08S.L2.K90F3
public import Minimality.Type08S.L2.K94F1

@[expose] public section

set_option maxHeartbeats 1000000

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option maxHeartbeats 40000000

/-- K88Alg with the two extra geometric hypotheses `0 < cx`, `cx < B`. -/
def K94Alg : Prop := ∀ (α1 β1 β6 γ6 pp s qq qr rr m : ℝ),
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
  0 < -(α1-1)*(s+pp) + β1*(qq+s) → -(α1-1)*(s+pp) + β1*(qq+s) < pp + 2*s + qq →
  ∃ B P W dx cx ex : ℝ, B = pp + 2*s + qq ∧ P = β6*(qq+s) + γ6*(qr+s) + s + pp ∧
    W = -(α1-1)*(s+pp) + β1*(qr+s) ∧ dx = s + pp ∧ cx = -(α1-1)*(s+pp) + β1*(qq+s) ∧ ex = pp + 2*s + qr ∧
    0 < B ∧ 0 < dx ∧ dx < B ∧ 0 < cx ∧ cx < B ∧
    γ6 * ex + (B - P) * 1 < γ6 * B ∧ (β1 - γ6) * ex + (P - W) * 1 < P * β1 - W * γ6 ∧ -β1 * ex + W * 1 < 0 ∧
    W ≤ 0 ∧ ((β1 < γ6 ∧ B < P) ∨ (γ6 < β1 ∧ W < 0 ∧ B ≤ P) ∨
      (γ6 < β1 ∧ W = 0 ∧ B * (β1 - γ6) < P * β1 ∧ 0 < P))

theorem k94_alg : K94Alg := by
  intro α1 β1 β6 γ6 pp s qq qr rr m hs hpp hm hqx hqy hα hβ hb6m hg6m hrel hppE hW hD hdet hD2 hβ6 hγ6 hσ
    hAv hX3 hX4 hH hac hZab hZba hne hcx0 hcxB
  subst hb6m hg6m
  obtain ⟨hmα, hbr⟩ := k90_class s pp qq qr rr m α1 β1 hs hm hqx hα hβ hrel hppE hW hAv
    (by linear_combination hZab) (by linear_combination hZba)
  rcases hbr with hF1 | hq3
  · exact k94_F1 s pp qq qr rr m α1 β1 hs hpp hm hqx hqy hα hβ hrel hppE hD hD2 hcx0 hcxB hF1 hmα hne
  · exact k90_F3 s pp qq qr rr m α1 β1 hs hpp hm hqx hβ hrel hppE hdet hγ6 hσ hAv hX4 hcx0 hcxB hq3 hmα hne

/-- relation between the screen parameter `lam` and the chart: `cx = (s+pp)*ac`, `B - cx = (s+pp)*cb`. -/
theorem k94_ac (al be b6 g6 pp s qq qr lam : ℝ)
    (hAv : -al*pp - b6*s + be*s - g6*s ≠ 0)
    (hlam : lam * (-al*pp - b6*s + be*s - g6*s) = -(al*s + b6*qq + (g6-be)*qr))
    (hZab : al*b6*pp*qq - al*b6*s^2 + al*g6*pp*qr - al*g6*s^2 - b6*be*qq*s + b6*be*qr*s - b6*pp*qq + b6*s^2 + be*pp*qr - be*s^2 - g6*pp*qr + g6*s^2 = 0)
    (hZba : -al*b6*pp*qq + al*b6*s^2 - al*g6*pp*qr + al*g6*s^2 + al*pp*qq - al*s^2 + b6*be*qq*s - b6*be*qr*s - be*qq*s + be*qr*s + g6*qq*s - g6*qr*s = 0) :
    -(al-1)*(s+pp) + be*(qq+s) = (s+pp)*(1-al+be*lam) ∧
    (pp + 2*s + qq) - (-(al-1)*(s+pp) + be*(qq+s)) = (s+pp)*(al-(be-1)*lam) := by
  constructor
  · apply mul_right_cancel₀ hAv
    linear_combination (-be)*hZab + (-be)*hZba - (s+pp)*be*hlam
  · apply mul_right_cancel₀ hAv
    linear_combination (be-1)*hZab + (be-1)*hZba + (s+pp)*(be-1)*hlam
