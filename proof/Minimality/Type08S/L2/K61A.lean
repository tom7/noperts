module

public import Minimality.Type08S.C2K46ZA

@[expose] public section

set_option maxHeartbeats 1000000

set_option autoImplicit true
set_option relaxedAutoImplicit true
open scoped RealInnerProductSpace
namespace Minimality.Type08Sp.C2

theorem k61_pq_neg {α1 β1 pq qq qr rr : ℝ} (hβ : 1 < β1) (hα : 1 < α1) (hqq : qr < qq) (hrr : qr < rr)
    (hrel : α1 * pq * (qq + rr - 2 * qr) = -(β1 - 1) * (qq * rr - qr ^ 2)) (hpd : 0 < qq * rr - qr ^ 2) :
    pq < 0 := by
  by_contra h; push_neg at h
  nlinarith [mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ α1) h) (by linarith : (0:ℝ) ≤ qq + rr - 2 * qr),
    mul_pos (by linarith : (0:ℝ) < β1 - 1) hpd]

-- k61_Av (Av < 0, Av = -α1 pp + (β6+γ6-β1) pq) : nlinarith with PD/Rel hints fails; needs the hz1 elimination, see HANDOFF.md

/-- Frame points of the K61 view `D:a'b' × P:abd`: `P = a-d`, `Q = c-d`, `R = sg•((b-d)+lam•(a-d))` (`sg = ±1`). -/
theorem k61_pts {a a' b b' c c' d R : ℝ³} {α1 β1 β6 γ6 lam sg : ℝ}
    (hC : K6mCoords a a' b b' c c' d α1 β1 β6 γ6) (hs : sg * sg = 1)
    (hR : R = sg • ((b - d) + lam • (a - d))) :
    det3 (a - d) (c - d) R ≠ 0 ∧ fpoint (a - d) (c - d) R d (0, 0, 0) = d ∧
    fpoint (a - d) (c - d) R d (1, 0, 0) = a ∧ fpoint (a - d) (c - d) R d (0, 1, 0) = c ∧
    fpoint (a - d) (c - d) R d (-lam, 0, sg) = b ∧
    fpoint (a - d) (c - d) R d (-(β6 * lam), γ6, sg * β6) = a' ∧
    fpoint (a - d) (c - d) R d (α1, β1, 0) = b' ∧
    fpoint (a - d) (c - d) R d (α1 - β1 * lam, 0, sg * β1) = c' := by
  obtain ⟨hdet, hc', hb', ha', -⟩ := hC
  have hB : b - d = sg • R - lam • (a - d) := by
    rw [hR, smul_smul, hs]; module
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have e : det3 (a - d) (c - d) R = -(sg * det3 (a - d) (b - d) (c - d)) := by
      rw [hR]
      simp only [det3_expand, PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]; ring
    rw [e]
    intro h
    have hsg : sg ≠ 0 := by intro h0; rw [h0] at hs; norm_num at hs
    exact hdet (by have := neg_eq_zero.1 h; rcases mul_eq_zero.1 this with h1 | h1; exact absurd h1 hsg; exact h1)
  · rw [k17f_fp]; module
  · rw [k17f_fp]; module
  · rw [k17f_fp]; module
  · rw [k17f_fp]
    symm
    calc b = d + (b - d) := by abel
      _ = d + (sg • R - lam • (a - d)) := by rw [hB]
      _ = _ := by module
  · rw [k17f_fp, ha', hB]; module
  · rw [k17f_fp, hb']; module
  · rw [k17f_fp, hc', hB]; module

theorem k61_pts_pos {a a' b b' c c' d R : ℝ³} {α1 β1 β6 γ6 lam : ℝ}
    (hC : K6mCoords a a' b b' c c' d α1 β1 β6 γ6)
    (hR : R = (1 : ℝ) • ((b - d) + lam • (a - d))) :
    det3 (a - d) (c - d) R ≠ 0 ∧ fpoint (a - d) (c - d) R d (0, 0, 0) = d ∧
    fpoint (a - d) (c - d) R d (1, 0, 0) = a ∧ fpoint (a - d) (c - d) R d (0, 1, 0) = c ∧
    fpoint (a - d) (c - d) R d (-lam, 0, 1) = b ∧
    fpoint (a - d) (c - d) R d (-(β6 * lam), γ6, β6) = a' ∧
    fpoint (a - d) (c - d) R d (α1, β1, 0) = b' ∧
    fpoint (a - d) (c - d) R d (α1 - β1 * lam, 0, β1) = c' := by
  have h := k61_pts (sg := 1) hC (by norm_num) hR
  simpa only [one_mul] using h

theorem k61_pts_neg {a a' b b' c c' d R : ℝ³} {α1 β1 β6 γ6 lam : ℝ}
    (hC : K6mCoords a a' b b' c c' d α1 β1 β6 γ6)
    (hR : R = (-1 : ℝ) • ((b - d) + lam • (a - d))) :
    det3 (a - d) (c - d) R ≠ 0 ∧ fpoint (a - d) (c - d) R d (0, 0, 0) = d ∧
    fpoint (a - d) (c - d) R d (1, 0, 0) = a ∧ fpoint (a - d) (c - d) R d (0, 1, 0) = c ∧
    fpoint (a - d) (c - d) R d (-lam, 0, -1) = b ∧
    fpoint (a - d) (c - d) R d (-(β6 * lam), γ6, -β6) = a' ∧
    fpoint (a - d) (c - d) R d (α1, β1, 0) = b' ∧
    fpoint (a - d) (c - d) R d (α1 - β1 * lam, 0, -β1) = c' := by
  have h := k61_pts (sg := -1) hC (by norm_num) hR
  simpa only [neg_mul, one_mul] using h
end Minimality.Type08Sp.C2
