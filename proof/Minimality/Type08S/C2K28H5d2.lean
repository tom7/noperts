module

public import Minimality.Type08S.C2K28H5d1
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

theorem k28h5d2_gram (p q r : ℝ³) (x1 x2 x3 y1 y2 y3 : ℝ) :
    ⟪x1 • p + x2 • q + x3 • r, y1 • p + y2 • q + y3 • r⟫ =
      x1*y1*⟪p,p⟫ + (x1*y2 + x2*y1)*⟪p,q⟫ + (x1*y3 + x3*y1)*⟪p,r⟫ + x2*y2*⟪q,q⟫
        + (x2*y3 + x3*y2)*⟪q,r⟫ + x3*y3*⟪r,r⟫ := by
  have h1 : ⟪q,p⟫ = ⟪p,q⟫ := real_inner_comm _ _
  have h2 : ⟪r,p⟫ = ⟪p,r⟫ := real_inner_comm _ _
  have h3 : ⟪r,q⟫ = ⟪q,r⟫ := real_inner_comm _ _
  simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right, h1, h2, h3]
  ring

set_option maxHeartbeats 4000000 in
theorem k28h5a_hD2 {a a' b b' c c' d : ℝ³} {α1 β1 β6 γ6 : ℝ}
    (hC : K6mCoords a a' b b' c c' d α1 β1 β6 γ6) (hM : K6sM a a' b b' c c' d)
    (hrel : K16Rel a b c d α1 β1) (h5 : K20mH5c a a' b b' c c' d α1 β1 β6 γ6)
    (hS : 0 < ⟪c' - a, b' - a⟫) :
    0 < ⟪c' - a, b' - a⟫ * ⟪a - a', c' - a⟫ - ⟪c' - a, c' - a⟫ * ⟪a - a', b' - a⟫ := by
  obtain ⟨hdet, hc', hb', ha', hα1p, hβ1p, h1, hβ6p, hγ6p, h3⟩ := hC
  obtain ⟨hpq, hcb, hbc⟩ := hM
  obtain ⟨⟨⟨⟨⟨hα, hβ, hσ, hβ61, hγ61⟩, hT⟩, -, -⟩, -, -⟩, hL5, -⟩ := h5
  obtain ⟨hr1, hr2⟩ := hrel
  have ee : c' - a = (α1-1) • (a-d) + β1 • (b-d) := by rw [hc']; module
  have ff : b' - a = (α1-1) • (a-d) + β1 • (c-d) := by rw [hb']; module
  have aa : a - a' = (a-d) - β6 • (b-d) - γ6 • (c-d) := by rw [ha']; module
  have ac : a - c' = -((α1-1) • (a-d) + β1 • (b-d)) := by rw [hc']; module
  have cd : c' - d = α1 • (a-d) + β1 • (b-d) := by rw [hc']; module
  have bd : b' - d = α1 • (a-d) + β1 • (c-d) := by rw [hb']; module
  have bc : b - c = (b-d) - (c-d) := by module
  have v3 : k20V3 a c d α1 (β6 + γ6 - β1) = α1 • (a-d) - (β6+γ6-β1) • (c-d) := rfl
  have hr2' := hr2
  have hr1' := hr1
  rw [bc] at hpq hcb hbc
  rw [cd] at hcb
  rw [bd] at hbc
  rw [ee] at hS ⊢
  rw [ac] at hT
  rw [ff, v3] at hL5
  rw [ff] at hS ⊢
  rw [aa] at ⊢
  generalize a - d = p at *
  generalize b - d = q at *
  generalize c - d = r at *
  have c1 : ⟪q,p⟫ = ⟪p,q⟫ := real_inner_comm _ _
  have c2 : ⟪r,p⟫ = ⟪p,r⟫ := real_inner_comm _ _
  have c3 : ⟪r,q⟫ = ⟪q,r⟫ := real_inner_comm _ _
  simp only [inner_add_left, inner_add_right, inner_sub_left, inner_sub_right, inner_neg_left, inner_neg_right, real_inner_smul_left, real_inner_smul_right, c1, c2, c3] at hpq hcb hbc hT hS hL5 hr1 hr2 ⊢
  have hpr : ⟪p, r⟫ = ⟪p, q⟫ := by linarith
  simp only [hpr] at hcb hbc hT hS hL5 hr1 hr2 ⊢
  generalize ⟪p, p⟫ = pp at *
  generalize ⟪p, q⟫ = pq at *
  generalize ⟪q, q⟫ = qq at *
  generalize ⟪q, r⟫ = qr at *
  generalize ⟪r, r⟫ = rr at *
  have hu1 : 0 < qq - qr := by
    by_contra h; push_neg at h; nlinarith [mul_nonneg hβ1p.le (neg_nonneg.2 h)]
  have hu2 : 0 < rr - qr := by
    by_contra h; push_neg at h; nlinarith [mul_nonneg hβ1p.le (neg_nonneg.2 h)]
  have hm2 : 0 < qq * rr - qr ^ 2 := hr2
  have ht : 0 < -pq := by
    by_contra h; push_neg at h
    have h' : 0 ≤ pq := by linarith
    nlinarith [mul_nonneg (mul_nonneg hα1p.le h') (add_pos hu1 hu2).le, mul_pos (by linarith : (0:ℝ) < β1 - 1) hm2]
  have key := k28h5d2_core pp (-pq) (qq - qr) (rr - qr) qr (α1 - 1) (β1 - 1) (1 - β6) (1 - γ6)
    (β6 + γ6 - β1) β6 γ6 α1 β1 ((α1 - 1) * pp + β1 * pq)
    (-(α1 * ((α1 - 1) * pp + β1 * pq) - (β6 + γ6 - β1) * (β1 * rr + (α1 - 1) * pq)))
    (qq * rr - qr ^ 2) ((α1 - 1) ^ 2 * pp + 2 * (α1 - 1) * β1 * pq + β1 ^ 2 * qr)
    (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
    (by linarith) hβ1p hu1 hu2 ht hm2 (by linarith) (by linarith) (by linarith)
    (by ring) (by ring) (by ring) (by ring) (by ring) (by ring) (by ring) (by ring) (by ring)
    (by linarith)
  rw [← mul_pos_iff_of_pos_left hα1p]
  have := mul_pos hβ1p key
  convert this using 1
  ring

end C2
end Type08Sp
end Minimality
