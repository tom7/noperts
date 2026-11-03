module

public import Minimality.Type08S.C2K35H2
public import Minimality.Type08S.C2K35H3
public import Minimality.Type08S.C2K24H1CA
public import Minimality.Type08S.C2K14P
public import Minimality.Type08S.C2K16N
public import Minimality.Type08S.C2K20HI
public import Minimality.Type08S.C2K6PA

@[expose] public section

set_option maxHeartbeats 1000000

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.unusedVariables false
open scoped RealInnerProductSpace Topology

namespace Minimality
namespace Type08Sp
namespace C2

set_option maxHeartbeats 4000000 in
theorem k28h5b_H23 {a a' b b' c c' d : ℝ³} {α1 β1 β6 γ6 : ℝ}
    (hC : K6mCoords a a' b b' c c' d α1 β1 β6 γ6) (hM : K6sM a a' b b' c c' d)
    (hrel : K16Rel a b c d α1 β1) (h5 : K20mH5c a a' b b' c c' d α1 β1 β6 γ6) :
    0 < γ6 * ⟪c' - a, b' - a⟫ + ⟪c' - a, c' - a⟫ * (γ6 * (α1 - 1) + α1 * β6) ∧
    0 < ⟪c' - a, c' - a⟫ * β6 * (β1 + α1 - 1) + ⟪c' - a, b' - a⟫ *
      (β6 * (1 - β1 - α1) + α1 * β1 * (β6 + γ6 - 1)) := by
  obtain ⟨hdet, hc', hb', ha', hα1p, hβ1p, h1, hβ6p, hγ6p, h3⟩ := hC
  obtain ⟨hpq, hcb, hbc⟩ := hM
  obtain ⟨⟨⟨⟨⟨hα, hβ, hσ, hβ61, hγ61⟩, hT⟩, L1, L2⟩, -, -⟩, hL5, -⟩ := h5
  obtain ⟨hr1, hr2⟩ := hrel
  have ee : c' - a = (α1-1) • (a-d) + β1 • (b-d) := by rw [hc']; module
  have ff : b' - a = (α1-1) • (a-d) + β1 • (c-d) := by rw [hb']; module
  have ac : a - c' = -((α1-1) • (a-d) + β1 • (b-d)) := by rw [hc']; module
  have e1 : c - a' = -β6 • (b-d) + (1-γ6) • (c-d) := by rw [ha']; module
  have e2 : d - c = -(c-d) := by module
  have e3 : b - a' = (1-β6) • (b-d) - γ6 • (c-d) := by rw [ha']; module
  have e4 : d - b = -(b-d) := by module
  have bc : b - c = (b-d) - (c-d) := by module
  have cd : c' - d = α1 • (a-d) + β1 • (b-d) := by rw [hc']; module
  have bd : b' - d = α1 • (a-d) + β1 • (c-d) := by rw [hb']; module
  rw [e1, e2] at L1
  rw [e3, e4] at L2
  rw [bc] at hpq hcb hbc
  rw [cd] at hcb
  rw [bd] at hbc
  rw [ac] at hT
  rw [ee, ff]
  generalize a - d = p at *
  generalize b - d = q at *
  generalize c - d = r at *
  have c1 : ⟪q,p⟫ = ⟪p,q⟫ := real_inner_comm _ _
  have c2 : ⟪r,p⟫ = ⟪p,r⟫ := real_inner_comm _ _
  have c3 : ⟪r,q⟫ = ⟪q,r⟫ := real_inner_comm _ _
  simp only [inner_add_left, inner_add_right, inner_sub_left, inner_sub_right, inner_neg_left, inner_neg_right, real_inner_smul_left, real_inner_smul_right, c1, c2, c3] at hpq hcb hbc hr1 hr2 hT L1 L2 ⊢
  have hpr : ⟪p, r⟫ = ⟪p, q⟫ := by linarith
  simp only [hpr] at hcb hbc hr1 hr2 hT L1 L2 ⊢
  generalize ⟪p, p⟫ = pp at *
  generalize ⟪p, q⟫ = pq at *
  generalize ⟪q, q⟫ = qq at *
  generalize ⟪q, r⟫ = qr at *
  generalize ⟪r, r⟫ = rr at *
  have hu1 : 0 < qq - qr := by
    by_contra h; push_neg at h; nlinarith [mul_nonneg hβ1p.le (neg_nonneg.2 h)]
  have hu2 : 0 < rr - qr := by
    by_contra h; push_neg at h; nlinarith [mul_nonneg hβ1p.le (neg_nonneg.2 h)]
  have hT' : 0 ≤ (α1-1)*pp + β1*pq := by linarith
  have hrel' : α1*pq*(qq+rr-2*qr) = -(β1-1)*(qq*rr-qr^2) := by linear_combination hr1
  have hs' : β1 < β6 + γ6 := hσ
  constructor
  · have := k28h5h_H2 pp pq qq qr rr α1 β1 β6 γ6 hα hβ hβ6p hγ6p hβ61 hγ61 hs' hu1 hu2 hr2 hrel' hT'
      (by linarith) (by linarith)
    nlinarith [this]
  · have := k28h5h_H3 pp pq qq qr rr α1 β1 β6 γ6 hα hβ hβ6p hγ6p hβ61 hγ61 hs' hu1 hu2 hr2 hrel' hT'
      (by linarith) (by linarith)
    nlinarith [this]

theorem k28h5b_H2 {a a' b b' c c' d : ℝ³} {α1 β1 β6 γ6 : ℝ}
    (hC : K6mCoords a a' b b' c c' d α1 β1 β6 γ6) (hM : K6sM a a' b b' c c' d)
    (hrel : K16Rel a b c d α1 β1) (h5 : K20mH5c a a' b b' c c' d α1 β1 β6 γ6) :
    0 < γ6 * ⟪c' - a, b' - a⟫ + ⟪c' - a, c' - a⟫ * (γ6 * (α1 - 1) + α1 * β6) :=
  (k28h5b_H23 hC hM hrel h5).1

theorem k28h5b_H3 {a a' b b' c c' d : ℝ³} {α1 β1 β6 γ6 : ℝ}
    (hC : K6mCoords a a' b b' c c' d α1 β1 β6 γ6) (hM : K6sM a a' b b' c c' d)
    (hrel : K16Rel a b c d α1 β1) (h5 : K20mH5c a a' b b' c c' d α1 β1 β6 γ6) :
    0 < ⟪c' - a, c' - a⟫ * β6 * (β1 + α1 - 1) + ⟪c' - a, b' - a⟫ *
      (β6 * (1 - β1 - α1) + α1 * β1 * (β6 + γ6 - 1)) :=
  (k28h5b_H23 hC hM hrel h5).2

end C2
end Type08Sp
end Minimality
