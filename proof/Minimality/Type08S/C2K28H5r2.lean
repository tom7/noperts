module

public import Minimality.Type08S.C2K28H5r1
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
theorem k28h5rb_hrb {a a' b b' c c' d : ℝ³} {α1 β1 β6 γ6 : ℝ}
    (hC : K6mCoords a a' b b' c c' d α1 β1 β6 γ6) (hM : K6sM a a' b b' c c' d)
    (hrel : K16Rel a b c d α1 β1) (h5 : K20mH5c a a' b b' c c' d α1 β1 β6 γ6) :
    ∀ κ g : ℝ, κ = ⟪c' - a, b' - a⟫ / ⟪c' - a, c' - a⟫ → g = (α1 - 1) * (1 - κ) / β1 →
      0 < γ6 * g * (β1 - 1) + α1 * (β6 + γ6 * κ - 1) := by
  intro κ g hκ hg
  obtain ⟨hdet, hc', hb', ha', hα1p, hβ1p, h1, hβ6p, hγ6p, h3⟩ := hC
  obtain ⟨hpq, hcb, hbc⟩ := hM
  obtain ⟨⟨⟨⟨⟨hα, hβ, hσ, hβ61, hγ61⟩, hT⟩, -, hL2⟩, hL3, -⟩, -, -⟩ := h5
  obtain ⟨hr1, hr2⟩ := hrel
  have ee : c' - a = (α1-1) • (a-d) + β1 • (b-d) := by rw [hc']; module
  have ff : b' - a = (α1-1) • (a-d) + β1 • (c-d) := by rw [hb']; module
  have ac : a - c' = -((α1-1) • (a-d) + β1 • (b-d)) := by rw [hc']; module
  have cd : c' - d = α1 • (a-d) + β1 • (b-d) := by rw [hc']; module
  have bd : b' - d = α1 • (a-d) + β1 • (c-d) := by rw [hb']; module
  have bc : b - c = (b-d) - (c-d) := by module
  have e3 : c' - a' = α1 • (a-d) + (β1 - β6) • (b-d) - γ6 • (c-d) := by rw [hc', ha']; module
  have e4 : d - b = -(b-d) := by module
  have e5 : b - a' = (1 - β6) • (b-d) - γ6 • (c-d) := by rw [ha']; module
  have hdet' := hdet
  have hene : c' - a ≠ 0 := by
    intro h0
    rw [ee] at h0
    have hd2 : det3 (a-d) ((α1-1) • (a-d) + β1 • (b-d)) (c-d) = β1 * det3 (a-d) (b-d) (c-d) := by
      simp only [det3_expand, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring
    have : det3 (a-d) ((α1-1) • (a-d) + β1 • (b-d)) (c-d) = 0 := by rw [h0]; simp [det3_expand]
    rw [hd2] at this
    exact hdet ((mul_eq_zero.1 this).resolve_left hβ1p.ne')
  have hE0 : 0 < ⟪c' - a, c' - a⟫ := real_inner_self_pos.2 hene
  rw [bc] at hpq hcb hbc
  rw [cd] at hcb
  rw [bd] at hbc
  rw [ac] at hT
  rw [e3, e4] at hL3
  rw [e5, e4] at hL2
  rw [ee, ff] at hκ
  rw [ee] at hE0
  generalize a - d = p at *
  generalize b - d = q at *
  generalize c - d = r at *
  have c1 : ⟪q,p⟫ = ⟪p,q⟫ := real_inner_comm _ _
  have c2 : ⟪r,p⟫ = ⟪p,r⟫ := real_inner_comm _ _
  have c3 : ⟪r,q⟫ = ⟪q,r⟫ := real_inner_comm _ _
  simp only [inner_add_left, inner_add_right, inner_sub_left, inner_sub_right, inner_neg_left, inner_neg_right, real_inner_smul_left, real_inner_smul_right, c1, c2, c3] at hpq hcb hbc hT hL2 hL3 hr1 hr2 hκ hE0
  have hpr : ⟪p, r⟫ = ⟪p, q⟫ := by linarith
  simp only [hpr] at hcb hbc hT hL2 hL3 hr1 hr2 hκ hE0
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
  have key := k28h5rb_core pp (-pq) (qq - qr) (rr - qr) qr (α1 - 1) (β1 - 1) (1 - β6) (1 - γ6)
    (β6 + γ6 - β1) β6 γ6 α1 β1 ((α1 - 1) * pp + β1 * pq)
    (γ6 * qr - (1 - β6) * (qq - qr + qr)) (α1 * pq + (β1 - β6) * qq - γ6 * qr)
    (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
    (by linarith) hβ1p hu1 hu2 ht (by linarith) (by nlinarith) (by nlinarith)
    (by ring) (by ring) (by ring) (by ring) (by ring) (by ring) (by ring) (by ring)
    (by nlinarith)
  subst hg
  subst hκ
  have hE : 0 < (α1 - 1) * ((α1 - 1) * pp + β1 * pq) + β1 * ((α1 - 1) * pq + β1 * qq) := by
    linarith [hE0]
  have hEq : γ6 * ((α1 - 1) * (1 - ((α1 - 1) * ((α1 - 1) * pp + β1 * pq) + β1 * ((α1 - 1) * pq + β1 * qr)) /
        ((α1 - 1) * ((α1 - 1) * pp + β1 * pq) + β1 * ((α1 - 1) * pq + β1 * qq))) / β1) * (β1 - 1) +
      α1 * (β6 + γ6 * (((α1 - 1) * ((α1 - 1) * pp + β1 * pq) + β1 * ((α1 - 1) * pq + β1 * qr)) /
        ((α1 - 1) * ((α1 - 1) * pp + β1 * pq) + β1 * ((α1 - 1) * pq + β1 * qq))) - 1) =
      ((γ6 * (α1 - 1) * (β1 - 1) * β1 * (qq - qr) + α1 * (γ6 * ((α1 - 1) ^ 2 * pp + 2 * (α1 - 1) * β1 * pq + β1 ^ 2 * qr)
        - (1 - β6) * ((α1 - 1) ^ 2 * pp + 2 * (α1 - 1) * β1 * pq + β1 ^ 2 * qq)))
        / ((α1 - 1) * ((α1 - 1) * pp + β1 * pq) + β1 * ((α1 - 1) * pq + β1 * qq))) := by
    field_simp
    ring
  have hnum : 0 < γ6 * (α1 - 1) * (β1 - 1) * β1 * (qq - qr) + α1 * (γ6 * ((α1 - 1) ^ 2 * pp + 2 * (α1 - 1) * β1 * pq + β1 ^ 2 * qr)
        - (1 - β6) * ((α1 - 1) ^ 2 * pp + 2 * (α1 - 1) * β1 * pq + β1 ^ 2 * qq)) := by
    convert key using 1
    ring
  have hpos := div_pos hnum hE
  rw [← hEq] at hpos
  convert hpos using 1
  ring

end C2
end Type08Sp
end Minimality
