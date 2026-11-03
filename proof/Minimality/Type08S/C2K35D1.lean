module

public import Minimality.Type08S.C2K35DG1
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
theorem k28h5b_hd1 {a a' b b' c c' d : ℝ³} {α1 β1 β6 γ6 : ℝ}
    (hC : K6mCoords a a' b b' c c' d α1 β1 β6 γ6) (hM : K6sM a a' b b' c c' d)
    (hrel : K16Rel a b c d α1 β1) (h5 : K20mH5c a a' b b' c c' d α1 β1 β6 γ6) :
    ⟪b' - c, ⟪c' - a, b' - a⟫ • (c' - a) - ⟪c' - a, c' - a⟫ • (b' - a)⟫ < 0 := by
  obtain ⟨hdet, hc', hb', ha', hα1p, hβ1p, h1, hβ6p, hγ6p, h3⟩ := hC
  obtain ⟨hpq, hcb, hbc⟩ := hM
  obtain ⟨⟨⟨⟨⟨hα, hβ, hσ, hβ61, hγ61⟩, hT⟩, -, -⟩, -, -⟩, hL5, -⟩ := h5
  obtain ⟨hr1, hr2⟩ := hrel
  have ee : c' - a = (α1-1) • (a-d) + β1 • (b-d) := by rw [hc']; module
  have ff : b' - a = (α1-1) • (a-d) + β1 • (c-d) := by rw [hb']; module
  have xx : b' - c = α1 • (a-d) + (β1-1) • (c-d) := by rw [hb']; module
  have bc : b - c = (b-d) - (c-d) := by module
  have cd : c' - d = α1 • (a-d) + β1 • (b-d) := by rw [hc']; module
  have bd : b' - d = α1 • (a-d) + β1 • (c-d) := by rw [hb']; module
  have hg := k24h1c_gram (a-d) (b-d) (c-d)
  have hd2 : 0 < det3 (a-d) (b-d) (c-d) ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hdet))
  rw [bc] at hpq hcb hbc
  rw [cd] at hcb
  rw [bd] at hbc
  rw [xx, ee, ff]
  generalize a - d = p at *
  generalize b - d = q at *
  generalize c - d = r at *
  have c1 : ⟪q,p⟫ = ⟪p,q⟫ := real_inner_comm _ _
  have c2 : ⟪r,p⟫ = ⟪p,r⟫ := real_inner_comm _ _
  have c3 : ⟪r,q⟫ = ⟪q,r⟫ := real_inner_comm _ _
  simp only [inner_add_left, inner_add_right, inner_sub_left, inner_sub_right, inner_neg_left, inner_neg_right, real_inner_smul_left, real_inner_smul_right, c1, c2, c3] at hpq hcb hbc hg hr1 hr2 ⊢
  have hpr : ⟪p, r⟫ = ⟪p, q⟫ := by linarith
  simp only [hpr] at hcb hbc hg hr1 hr2 ⊢
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
  have hy : 0 < pp*(qq*rr-qr^2) - pq^2*(qq+rr-2*qr) := by nlinarith [hg, hd2]
  have key := k28h5bd_d1_gram pp pq qq qr rr (α1-1) (β1-1) (by linarith) (by linarith) hu1 hu2 hm2 ht
    (by linear_combination hr1) hy
  unfold k28h5bd_G k28h5bd_ip at key
  nlinarith [key]

end C2
end Type08Sp
end Minimality
