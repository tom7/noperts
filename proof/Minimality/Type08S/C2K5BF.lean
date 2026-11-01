module

public import Minimality.Type08S.C2K5BE

@[expose] public section


/-!
# K5b / F: the relation `P` (M + overlap) from `Coll5 ∧ PersF` of `p0_kb_collpers` / `p0_n2_collpers`.
Result: `α1 ⟪a-d, b-c⟫ + (β1-1) ⟪c-d, b-c⟫ = t ⟪b-c, b-c⟫` with `-β1 ≤ t ≤ 1` (i.e. the projection of `b'` onto the
line `bc` lies at parameter `t ∈ [-β1, 1]`, `c = 0`, `b = 1`; the segment `[b', c']` overlaps `[c, b]`).
-/
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp
namespace C2

theorem k5b_inner_frame {e1 e2 e3 : ℝ³} (hF : Fr e1 e2 e3) (u v : ℝ³) :
    ⟪u, v⟫ = ⟪u, e1⟫ * ⟪v, e1⟫ + ⟪u, e2⟫ * ⟪v, e2⟫ + ⟪u, e3⟫ * ⟪v, e3⟫ := by
  have n21 : ⟪e2, e1⟫ = 0 := by rw [real_inner_comm]; exact hF.n12
  have n31 : ⟪e3, e1⟫ = 0 := by rw [real_inner_comm]; exact hF.n13
  have n32 : ⟪e3, e2⟫ = 0 := by rw [real_inner_comm]; exact hF.n23
  conv_lhs => rw [hF.expand u, hF.expand v]
  simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right, RCLike.conj_to_real,
    hF.n11, hF.n22, hF.n33, hF.n12, hF.n13, hF.n23, n21, n31, n32]
  ring

/-- Real core: persistence + collinearity give a parameter `τ ∈ [0, 1+β1]`. -/
theorem k5b_tau {L κ zf Xr zr Xg β1 s s' : ℝ} (hL : 0 < L) (hβ1 : 0 < β1)
    (hc1 : (zr - κ) * L = (zf - κ) * Xr) (hX : s * L = Xr + s' * (Xg - Xr)) (hXg : Xg - Xr = -β1 * L)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hs'0 : 0 ≤ s') (hs'1 : s' ≤ 1) :
    ∃ τ : ℝ, 0 ≤ τ ∧ τ ≤ 1 + β1 ∧ Xr = L * τ ∧ zr - κ = (zf - κ) * τ := by
  refine ⟨s + s' * β1, by positivity, by nlinarith, ?_, ?_⟩
  · rw [hXg] at hX; linarith
  · have hXr : Xr = L * (s + s' * β1) := by rw [hXg] at hX; linarith
    rw [hXr] at hc1
    have : ((zr - κ) - (zf - κ) * (s + s' * β1)) * L = 0 := by linarith
    rcases mul_eq_zero.1 this with h | h
    · linarith
    · exact absurd h hL.ne'


theorem k5b_kb_rel {a b b' c c' d : ℝ³} {α1 β1 : ℝ} (hβ1 : 0 < β1)
    (hb' : b' = d + α1 • (a - d) + β1 • (c - d)) (hc' : c' = d + α1 • (a - d) + β1 • (b - d))
    {e1 e2 e3 : ℝ³} (hF : Fr e1 e2 e3) {κ : ℝ} (hxe : b - d = κ • e3) (hce2 : ⟪c - d, e2⟫ = 0)
    (hL : 0 < ⟪c - d, e1⟫)
    (hcoll : Coll5 ⟪c - d, e1⟫ κ ⟪c - d, e3⟫ ⟪b' - d, e1⟫ ⟪b' - d, e3⟫ ⟪c' - d, e1⟫ ⟪c' - d, e3⟫)
    (hpers : PersF ⟪c - d, e1⟫ κ ⟪c - d, e3⟫ ⟪b' - d, e1⟫ ⟪b' - d, e2⟫ ⟪b' - d, e3⟫ ⟪c' - d, e1⟫
      ⟪c' - d, e2⟫ ⟪c' - d, e3⟫) :
    ∃ t : ℝ, -β1 ≤ t ∧ t ≤ 1 ∧ ⟪b' - c, b - c⟫ = t * ⟪b - c, b - c⟫ ∧ 0 < ⟪b - c, b - c⟫ := by
  obtain ⟨hq1, hq2, hq3⟩ := p0_smul_e3 hF κ
  rw [← hxe] at hq1 hq2 hq3
  obtain ⟨s, s', hs0, hs1, hs'0, hs'1, -, hX, -⟩ := hpers
  have hbc1 : ⟪b - c, e1⟫ = -⟪c - d, e1⟫ := by
    have : b - c = (b - d) - (c - d) := by abel
    rw [this, inner_sub_left, hq1]; ring
  have hbc2 : ⟪b - c, e2⟫ = 0 := by
    have : b - c = (b - d) - (c - d) := by abel
    rw [this, inner_sub_left, hq2, hce2]; ring
  have hbc3 : ⟪b - c, e3⟫ = κ - ⟪c - d, e3⟫ := by
    have : b - c = (b - d) - (c - d) := by abel
    rw [this, inner_sub_left, hq3]
  have hcb : c' - b' = β1 • (b - c) := by rw [hc', hb']; module
  have hXg : ⟪c' - d, e1⟫ - ⟪b' - d, e1⟫ = -β1 * ⟪c - d, e1⟫ := by
    have h3 : ⟪c' - b', e1⟫ = ⟪c' - d, e1⟫ - ⟪b' - d, e1⟫ := by
      rw [← inner_sub_left]; congr 1; abel
    have h2 := congrArg (fun v => ⟪v, e1⟫) hcb
    rw [inner_smul_left, hbc1, h3] at h2
    simp only [RCLike.conj_to_real] at h2
    linarith
  obtain ⟨τ, hτ0, hτ1, hXr, hzr⟩ := k5b_tau hL hβ1 hcoll.1 hX hXg hs0 hs1 hs'0 hs'1
  refine ⟨1 - τ, by linarith, by linarith, ?_, ?_⟩
  · have e1' : ⟪b' - c, e1⟫ = ⟪b' - d, e1⟫ - ⟪c - d, e1⟫ := by
      have : b' - c = (b' - d) - (c - d) := by abel
      rw [this, inner_sub_left]
    have e3' : ⟪b' - c, e3⟫ = ⟪b' - d, e3⟫ - ⟪c - d, e3⟫ := by
      have : b' - c = (b' - d) - (c - d) := by abel
      rw [this, inner_sub_left]
    rw [k5b_inner_frame hF (b' - c) (b - c), k5b_inner_frame hF (b - c) (b - c), e1', e3', hbc1, hbc2, hbc3]
    have : ⟪b' - d, e3⟫ = κ + (⟪c - d, e3⟫ - κ) * τ := by linarith
    rw [hXr, this]; ring
  · rw [k5b_inner_frame hF (b - c) (b - c), hbc1, hbc2, hbc3]; nlinarith [mul_pos hL hL, sq_nonneg (κ - ⟪c - d, e3⟫)]

theorem k5b_n2_rel {a a' b b' c c' : ℝ³} {α1 β1 : ℝ} (hβ1 : 0 < β1)
    (hb' : b' = c' - β1 • (b - c))
    {e1 e2 e3 : ℝ³} (hF : Fr e1 e2 e3) {κ : ℝ} (hxe : c - a' = κ • e3) (hbe2 : ⟪b - a', e2⟫ = 0)
    (hL : 0 < ⟪b - a', e1⟫)
    (hcoll : Coll5 ⟪b - a', e1⟫ κ ⟪b - a', e3⟫ ⟪c' - a', e1⟫ ⟪c' - a', e3⟫ ⟪b' - a', e1⟫ ⟪b' - a', e3⟫)
    (hpers : PersF ⟪b - a', e1⟫ κ ⟪b - a', e3⟫ ⟪c' - a', e1⟫ ⟪c' - a', e2⟫ ⟪c' - a', e3⟫ ⟪b' - a', e1⟫
      ⟪b' - a', e2⟫ ⟪b' - a', e3⟫) :
    ∃ t : ℝ, -β1 ≤ t ∧ t ≤ 1 ∧ ⟪b' - c, b - c⟫ = t * ⟪b - c, b - c⟫ ∧ 0 < ⟪b - c, b - c⟫ := by
  obtain ⟨hq1, hq2, hq3⟩ := p0_smul_e3 hF κ
  rw [← hxe] at hq1 hq2 hq3
  obtain ⟨s, s', hs0, hs1, hs'0, hs'1, -, hX, -⟩ := hpers
  have hbc1 : ⟪b - c, e1⟫ = ⟪b - a', e1⟫ := by
    have : b - c = (b - a') - (c - a') := by abel
    rw [this, inner_sub_left, hq1]; ring
  have hbc2 : ⟪b - c, e2⟫ = 0 := by
    have : b - c = (b - a') - (c - a') := by abel
    rw [this, inner_sub_left, hq2, hbe2]; ring
  have hbc3 : ⟪b - c, e3⟫ = ⟪b - a', e3⟫ - κ := by
    have : b - c = (b - a') - (c - a') := by abel
    rw [this, inner_sub_left, hq3]
  have hXg : ⟪b' - a', e1⟫ - ⟪c' - a', e1⟫ = -β1 * ⟪b - a', e1⟫ := by
    have h3 : ⟪b' - c', e1⟫ = ⟪b' - a', e1⟫ - ⟪c' - a', e1⟫ := by
      rw [← inner_sub_left]; congr 1; abel
    have h2 := congrArg (fun v => ⟪v, e1⟫) (show b' - c' = (-β1) • (b - c) by rw [hb']; module)
    rw [inner_smul_left, hbc1, h3] at h2
    simp only [RCLike.conj_to_real] at h2
    linarith
  obtain ⟨τ, hτ0, hτ1, hXr, hzr⟩ := k5b_tau hL hβ1 hcoll.1 hX hXg hs0 hs1 hs'0 hs'1
  have hzg : ⟪b' - a', e3⟫ - κ = (⟪b - a', e3⟫ - κ) * (τ - β1) := by
    have hXg' : ⟪b' - a', e1⟫ = ⟪b - a', e1⟫ * (τ - β1) := by rw [hXr] at hXg; linarith
    have h2 := hcoll.2
    rw [hXg'] at h2
    have : ((⟪b' - a', e3⟫ - κ) - (⟪b - a', e3⟫ - κ) * (τ - β1)) * ⟪b - a', e1⟫ = 0 := by linarith
    rcases mul_eq_zero.1 this with h | h
    · linarith
    · exact absurd h hL.ne'
  have hXg' : ⟪b' - a', e1⟫ = ⟪b - a', e1⟫ * (τ - β1) := by rw [hXr] at hXg; linarith
  refine ⟨τ - β1, by linarith, by linarith, ?_, ?_⟩
  · have e1' : ⟪b' - c, e1⟫ = ⟪b' - a', e1⟫ := by
      have : b' - c = (b' - a') - (c - a') := by abel
      rw [this, inner_sub_left, hq1]; ring
    have e3' : ⟪b' - c, e3⟫ = ⟪b' - a', e3⟫ - κ := by
      have : b' - c = (b' - a') - (c - a') := by abel
      rw [this, inner_sub_left, hq3]
    rw [k5b_inner_frame hF (b' - c) (b - c), k5b_inner_frame hF (b - c) (b - c), e1', e3', hbc1, hbc2, hbc3]
    rw [hXg', hzg]; ring
  · rw [k5b_inner_frame hF (b - c) (b - c), hbc1, hbc2, hbc3]; nlinarith [mul_pos hL hL, sq_nonneg (⟪b - a', e3⟫ - κ)]

end C2
end Type08Sp
end Minimality
