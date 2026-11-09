module

public import Minimality.Type08S.L2.K71A
public import Minimality.Type08S.LexCertA

@[expose] public section

set_option maxHeartbeats 1000000

set_option autoImplicit true
set_option relaxedAutoImplicit true
open scoped RealInnerProductSpace
namespace Minimality.Type08Sp.C2

set_option maxHeartbeats 6400000 in
theorem k71_c_fAv (pp s qq qr rr al be m : ℝ) (hs : 0 < s) (hal : 1 < al) (hbe : 1 < be) (hm : 0 < m) (hrel : al * s * (qq + rr - 2 * qr) = (be - 1) * (qq * rr - qr ^ 2)) (hD : 0 < qq * rr - qr ^ 2) (hdet : 0 < pp * (qq * rr - qr ^ 2) - s ^ 2 * (qq + rr - 2 * qr)) :
    0 < al * m * s + be * m * s + al * pp - be * s - m * s + s := by
  (refine pos_of_mul_pos_right ?_ (hD).le; linear_combination 1 * (mul_pos (mul_pos hs hm) hD) + 1 * (mul_pos (mul_pos (mul_pos hs (sub_pos.2 hal)) hm) hD) + 1 * (mul_pos (mul_pos (mul_pos hs (sub_pos.2 hbe)) hm) hD) + 1 * hdet + 1 * (mul_pos (sub_pos.2 hal) hdet) + (-s) * hrel)

set_option maxHeartbeats 6400000 in
/-- Gram data of the gWb = 0 branch (pq = pr = -s, m = β6/β1). -/
theorem k71_gram {a a' b b' c c' d : ℝ³} {α1 β1 β6 γ6 : ℝ}
    (hC : K6mCoords a a' b b' c c' d α1 β1 β6 γ6) (hM : K6sM a a' b b' c c' d)
    (hrel : K16Rel a b c d α1 β1) (hα1 : 1 < α1) (hβ1 : 1 < β1)
    (hz1 : ⟪a - a', k28l2aU0 a b c d α1 β1⟫ = 0)
    (hz2 : ⟪a', k28l2aU0 a b c d α1 β1⟫ = ⟪c, k28l2aU0 a b c d α1 β1⟫)
    (hgWb : β6 * (α1 - 1) = β1 * (γ6 - 1)) :
    ∃ pp s qq qr rr m : ℝ, pp = ⟪a - d, a - d⟫ ∧ s = -⟪a - d, b - d⟫ ∧ ⟪a - d, c - d⟫ = -s ∧
      qq = ⟪b - d, b - d⟫ ∧ qr = ⟪b - d, c - d⟫ ∧ rr = ⟪c - d, c - d⟫ ∧ β6 = β1 * m ∧ γ6 = 1 + (α1 - 1) * m ∧
      0 < s ∧ 0 < pp ∧ 0 < m ∧ qr < qq ∧ qr < rr ∧
      α1 * s * (qq + rr - 2 * qr) = (β1 - 1) * (qq * rr - qr ^ 2) ∧
      pp * ((α1 - 1) * rr + β1 * qr) = s * ((α1 + β1 - 1) * s + β1 * (rr - qr)) ∧
      0 < (α1 - 1) * rr + β1 * qr ∧ 0 < qq * rr - qr ^ 2 ∧
      0 < pp * (qq * rr - qr ^ 2) - s ^ 2 * (qq + rr - 2 * qr) ∧ s ^ 2 < pp * qq := by
  obtain ⟨hdet, hc', hb', ha', -, -, -, hβ6, hγ6, -⟩ := hC
  obtain ⟨hM1, hM2, hM3⟩ := hM
  obtain ⟨hr1, hr2⟩ := hrel
  obtain ⟨gp, gq, gr, gpq, gpr, gqr, gdet⟩ := cert_gram_pd hdet
  have hq : (b - c) = (b - d) - (c - d) := by abel
  have hM1' : ⟪a - d, (b - d) - (c - d)⟫ = 0 := by rw [← hq]; exact hM1
  have hpr : ⟪a - d, c - d⟫ = ⟪a - d, b - d⟫ := by
    rw [inner_sub_right] at hM1'; linarith
  have hM2' : 0 < β1 * (⟪b - d, b - d⟫ - ⟪b - d, c - d⟫) := by
    have e : c' - d = α1 • (a - d) + β1 • (b - d) := by rw [hc']; module
    have := hM2; rw [e, hq, inner_add_left, inner_smul_left, inner_smul_left, hM1', inner_sub_right] at this
    simp only [RCLike.conj_to_real] at this
    linarith
  have hM3' : 0 < β1 * (⟪c - d, c - d⟫ - ⟪b - d, c - d⟫) := by
    have e : b' - d = α1 • (a - d) + β1 • (c - d) := by rw [hb']; module
    have := hM3; rw [e, hq, inner_add_left, inner_smul_left, inner_smul_left, hM1', inner_sub_right] at this
    simp only [RCLike.conj_to_real] at this
    rw [real_inner_comm (b - d) (c - d)] at this
    nlinarith
  have hqx : ⟪b - d, c - d⟫ < ⟪b - d, b - d⟫ := by
    have := (pos_iff_pos_of_mul_pos hM2').1 (by linarith); linarith
  have hqy : ⟪b - d, c - d⟫ < ⟪c - d, c - d⟫ := by
    have := (pos_iff_pos_of_mul_pos hM3').1 (by linarith); linarith
  have hD1 := hr2
  have hs : 0 < -⟪a - d, b - d⟫ := by
    have := k61_pq_neg hβ1 hα1 hqx hqy hr1 hD1; linarith
  have hzc : ⟪a - c, k28l2aU0 a b c d α1 β1⟫ = 0 := by
    have : a - c = (a - a') + (a' - c) := by abel
    rw [this, inner_add_left, hz1, inner_sub_left a' c, hz2]; ring
  have hA : a - c = (1:ℝ) • (a - d) + (0:ℝ) • (b - d) + (-1:ℝ) • (c - d) := by module
  have hU : k28l2aU0 a b c d α1 β1 = ((1 - α1) * ⟪a - d, b - d⟫ - β1 * ⟪b - d, c - d⟫) • (a - d) + (0:ℝ) • (b - d) +
      (-((1 - α1) * ⟪a - d, a - d⟫ - β1 * ⟪a - d, b - d⟫)) • (c - d) := by
    unfold k28l2aU0; module
  rw [hA, hU, k71_gip] at hzc
  rw [hpr] at hzc gdet
  have hrhs : 0 < -⟪a - d, b - d⟫ * ((α1 + β1 - 1) * -⟪a - d, b - d⟫ + β1 * (⟪c - d, c - d⟫ - ⟪b - d, c - d⟫)) :=
    mul_pos hs (by nlinarith)
  have hppE : ⟪a - d, a - d⟫ * ((α1 - 1) * ⟪c - d, c - d⟫ + β1 * ⟪b - d, c - d⟫) =
      -⟪a - d, b - d⟫ * ((α1 + β1 - 1) * -⟪a - d, b - d⟫ + β1 * (⟪c - d, c - d⟫ - ⟪b - d, c - d⟫)) := by
    linear_combination (-1) * hzc
  refine ⟨⟪a - d, a - d⟫, -⟪a - d, b - d⟫, ⟪b - d, b - d⟫, ⟪b - d, c - d⟫, ⟪c - d, c - d⟫, β6 / β1, rfl, rfl,
    by linarith, rfl, rfl, rfl, ?_, ?_, hs, gp, div_pos hβ6 (by linarith), hqx, hqy, ?_, hppE, ?_, hD1, ?_, ?_⟩
  · field_simp
  · field_simp; linarith
  · linear_combination (-1) * hr1
  · exact (pos_iff_pos_of_mul_pos (hppE ▸ hrhs)).1 gp
  · nlinarith [gdet]
  · nlinarith [gpq]

/-- **k71_facts** (gWb = 0 branch): the numerics-only facts of `k63_l2_cells` that are proved here.
Proved: `fAv` (Av < 0) and `fF3`.  The rest (fL, fF1, fF2, fzA, fzB, fDP, fQ1, fQ2, fAC0, fN1) remain hypotheses
of `k63_l2_cells`, see HANDOFF.md. -/
theorem k71_facts {a a' b b' c c' d : ℝ³} {α1 β1 β6 γ6 : ℝ}
    (hC : K6mCoords a a' b b' c c' d α1 β1 β6 γ6) (hM : K6sM a a' b b' c c' d)
    (hrel : K16Rel a b c d α1 β1) (hα1 : 1 < α1) (hβ1 : 1 < β1)
    (hz1 : ⟪a - a', k28l2aU0 a b c d α1 β1⟫ = 0)
    (hz2 : ⟪a', k28l2aU0 a b c d α1 β1⟫ = ⟪c, k28l2aU0 a b c d α1 β1⟫)
    (hgWb : β6 * (α1 - 1) = β1 * (γ6 - 1)) :
    ⟪a - d, a' - b'⟫ < 0 ∧ 0 < ⟪c' - b', k61_R a a' b b' d⟫ := by
  obtain ⟨pp, s, qq, qr, rr, m, hpp_d, hs_d, hpr_d, hqq_d, hqr_d, hrr_d, hb6m, hg6m, hs, hpp, hm, hqx, hqy,
    hrel', hppE, hW, hD, hdet, hD2⟩ := k71_gram hC hM hrel hα1 hβ1 hz1 hz2 hgWb
  have hC' := hC
  obtain ⟨-, hc', hb', ha', -⟩ := hC'
  constructor
  · have core := k71_c_fAv pp s qq qr rr α1 β1 m hs hα1 hβ1 hm hrel' hD hdet
    have e : a' - b' = (-α1) • (a - d) + β6 • (b - d) + (γ6 - β1) • (c - d) := by rw [ha', hb']; module
    have e1 : a - d = (1:ℝ) • (a - d) + (0:ℝ) • (b - d) + (0:ℝ) • (c - d) := by module
    rw [e]
    nth_rewrite 1 [e1]
    have hq' : ⟪a - d, b - d⟫ = -s := by linarith
    rw [k71_gip, ← hpp_d, hpr_d, hq', hb6m, hg6m]
    nlinarith [core]
  · have e : c' - b' = β1 • ((b - d) - (c - d)) := by rw [hc', hb']; module
    have e2 : k61_R a a' b b' d = (b - d) + k61_lam a a' b b' d • (a - d) := rfl
    have h1 : ⟪b - d, b - d⟫ - ⟪b - d, c - d⟫ > 0 := by linarith
    have h0 : ⟪(b - d) - (c - d), a - d⟫ = 0 := by
      have := hM.1
      have hq : (b - c) = (b - d) - (c - d) := by abel
      rw [hq] at this; rw [real_inner_comm]; exact this
    rw [e, e2, inner_smul_left, inner_add_right, inner_smul_right, h0, inner_sub_left]
    simp only [RCLike.conj_to_real]
    rw [real_inner_comm (b - d) (c - d)]
    nlinarith
end Minimality.Type08Sp.C2
