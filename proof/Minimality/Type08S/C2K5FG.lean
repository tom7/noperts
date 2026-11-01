module

public import Minimality.Type08S.C2K5FF

@[expose] public section


set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp
namespace C2

/-- `β6 - 1` as a determinant: `det3 (a'-b) (c-d) (a-d) = (β6 - 1) Δ` (T frame, `γ6 = 1`). -/
theorem k5f_det_beta6 {a a' b c d : ℝ³} {β6 : ℝ} (ha' : a' = d + β6 • (b - d) + (1 : ℝ) • (c - d)) :
    det3 (a' - b) (c - d) (a - d) = (β6 - 1) * det3 (a - d) (b - d) (c - d) := by
  rw [ha']
  simp only [det3_expand, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring

set_option maxHeartbeats 3200000 in
/-- **Box C of K5f** (`β1 > 1`, `α4 < 1`, `β6 > 1`; view `c - d`).  With `D_c = ⟪b-d, c-d⟫`,
`ζ = ⟪c' - a, c - d⟫`: C1 (`D_c > 0`, or `D_c < 0 ∧ ζ > 0`): cycle `(c', a', b, d, a)`; C2 (`D_c < 0 ∧ ζ < 0`):
cycle `(a, c', a', c, b')`.  Leftover: `D_c = 0`, `D_c < 0 ∧ ζ = 0`. -/
theorem k5f_C_hasLexCell {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) (hT : IsT a' b c d)
    (hκ : det3 (c - b) (b' - b) (c' - b) = 0)
    (hfar : W.F.a'bc.f c' < W.F.a'bc.f a)
    (hβ : 0 < det3 (a - d) (c' - b) (c - d) * det3 (a - d) (b - d) (c - d))
    (hα : det3 (b' - a) (b - d) (c - d) * det3 (a - d) (b - d) (c - d) < 0)
    (hβ6 : 0 < det3 (a' - b) (c - d) (a - d) * det3 (a - d) (b - d) (c - d))
    (hcase : 0 < ⟪b - d, c - d⟫ ∨ (⟪b - d, c - d⟫ < 0 ∧ ⟪c' - a, c - d⟫ ≠ 0)) :
    HasLexCell (V8 a a' b b' c c' d) := by
  obtain ⟨α1, α4, β1, γ4, β6, hdet, hc', hb', ha', hα1, hβ1, hαβ, hα4, hγ4, hαγ, hβ6p, hfar'⟩ :=
    norm08w_coordsT W hT
  have hκ' := (planar_a_iff hdet hc' hb').1 hκ
  rw [det_beta1 hc'] at hβ
  rw [det_alpha4 hb'] at hα
  rw [k5f_det_beta6 ha'] at hβ6
  have hΔ2 : 0 < det3 (a - d) (b - d) (c - d) ^ 2 := by positivity
  have hβ11 : 1 < β1 := by nlinarith
  have hα41 : α4 < 1 := by nlinarith
  have hβ61 : 1 < β6 := by nlinarith
  have hγ41 : 1 < γ4 := by
    by_contra hh; push Not at hh
    nlinarith [mul_nonneg hα1.le (by linarith : 0 ≤ 1 - γ4), mul_pos hα4 (sub_pos.2 hβ11)]
  have hα1' : 1 ≤ α1 := (hfar' hfar).le
  set p := a - d with hp
  set q := b - d with hq
  set r := c - d with hr
  have hcc : c' - a = (α1 - 1) • p + β1 • q := by rw [hc', hp, hq]; module
  have hζ : ⟪c' - a, r⟫ = (α1 - 1) * ⟪p, r⟫ + β1 * ⟪q, r⟫ := by
    rw [hcc, inner_add_left, inner_smul_left, inner_smul_left]; simp
  have hqr : ⟪q, r⟫ = ⟪b - d, c - d⟫ := rfl
  have hΔ : det3 p q r ≠ 0 := hdet
  have eO : fpoint p q r d (0, 0, 0) = d := by simp [fpoint, fcomb]
  have eA : fpoint p q r d (1, 0, 0) = a := by simp only [fpoint, fcomb, hp]; module
  have eB : fpoint p q r d (0, 1, 0) = b := by simp only [fpoint, fcomb, hq]; module
  have eC : fpoint p q r d (0, 0, 1) = c := by simp only [fpoint, fcomb, hr]; module
  have eC' : fpoint p q r d (α1, β1, 0) = c' := by rw [hc']; simp only [fpoint, fcomb, hp, hq]; module
  have eB' : fpoint p q r d (α4, 0, γ4) = b' := by rw [hb']; simp only [fpoint, fcomb, hp, hr]; module
  have eA' : fpoint p q r d (0, β6, 1) = a' := by rw [ha']; simp only [fpoint, fcomb, hq, hr]; module
  have hne : r ≠ 0 := by intro h0; apply hΔ; rw [h0]; simp [det3_expand]
  refine ⟨r, hne, ?_⟩
  rcases hcase with hD | ⟨hD, hz⟩
  · refine k5f_C1_frame (V8 a a' b b' c c' d) p q r d hΔ hα1' hβ1 hα4 hα41 hγ4 hβ61
      (Or.inl (by rw [hqr]; exact hD)) ?_ ?_
    · intro i
      rcases z5_cases i with rfl | rfl | rfl | rfl | rfl
      · simp only [k5fC1Cyc, pc5_0, eC']; simp [V8]
      · simp only [k5fC1Cyc, pc5_1, eA']; simp [V8]
      · simp only [k5fC1Cyc, pc5_2, eB]; simp [V8]
      · simp only [k5fC1Cyc, pc5_3, eO]; simp [V8]
      · simp only [k5fC1Cyc, pc5_4, eA]; simp [V8]
    · intro y hy
      rw [eC', eA', eB, eO, eA, eC, eB']
      simp only [V8, Finset.mem_insert, Finset.mem_singleton] at hy
      tauto
  · rcases lt_or_gt_of_ne hz with hneg | hpos
    · refine k5f_C2_frame (V8 a a' b b' c c' d) p q r d hΔ hα1' hβ11 hβ61 hα4 hα41 hγ41
        (by rw [hqr]; exact hD) (by rw [← hζ]; exact hneg) ?_ ?_
      · intro i
        rcases z5_cases i with rfl | rfl | rfl | rfl | rfl
        · simp only [k5fC2Cyc, pc5_0, eA]; simp [V8]
        · simp only [k5fC2Cyc, pc5_1, eC']; simp [V8]
        · simp only [k5fC2Cyc, pc5_2, eA']; simp [V8]
        · simp only [k5fC2Cyc, pc5_3, eC]; simp [V8]
        · simp only [k5fC2Cyc, pc5_4, eB']; simp [V8]
      · intro y hy
        rw [eA, eC', eA', eC, eB', eO, eB]
        simp only [V8, Finset.mem_insert, Finset.mem_singleton] at hy
        tauto
    · refine k5f_C1_frame (V8 a a' b b' c c' d) p q r d hΔ hα1' hβ1 hα4 hα41 hγ4 hβ61
        (Or.inr ⟨by rw [hqr]; exact hD, by rw [← hζ]; exact hpos⟩) ?_ ?_
      · intro i
        rcases z5_cases i with rfl | rfl | rfl | rfl | rfl
        · simp only [k5fC1Cyc, pc5_0, eC']; simp [V8]
        · simp only [k5fC1Cyc, pc5_1, eA']; simp [V8]
        · simp only [k5fC1Cyc, pc5_2, eB]; simp [V8]
        · simp only [k5fC1Cyc, pc5_3, eO]; simp [V8]
        · simp only [k5fC1Cyc, pc5_4, eA]; simp [V8]
      · intro y hy
        rw [eC', eA', eB, eO, eA, eC, eB']
        simp only [V8, Finset.mem_insert, Finset.mem_singleton] at hy
        tauto

end C2
end Type08Sp
end Minimality
