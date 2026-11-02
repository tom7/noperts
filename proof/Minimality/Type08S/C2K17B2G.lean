module

public import Minimality.Type08S.C2K17B2F

@[expose] public section


set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp
namespace C2

set_option maxHeartbeats 3200000 in
theorem k17b2_p13_frame (V : Finset ℝ³) (P Q R d0 : ℝ³) (hΔ : det3 P Q R ≠ 0) {α β β6 γ6 : ℝ}
    (hα : 1 < α) (hβ : 1 < β) (hβ6 : 1 < β6) (hγ6 : 1 < γ6)
    (hmem : ∀ i, fpoint P Q R d0 (k17b2Cy13 α β β6 γ6 i) ∈ V)
    (hVall : ∀ y ∈ V, y = fpoint P Q R d0 (-α, 0, 1) ∨ y = fpoint P Q R d0 (-α / 2, 0, β) ∨
      y = fpoint P Q R d0 (β - 1 / 2, 0, 0) ∨ y = fpoint P Q R d0 (α * (β - 1 / 2), β, 0) ∨
      y = fpoint P Q R d0 (-α * γ6, β6, γ6) ∨ y = fpoint P Q R d0 (0, 0, 0) ∨ y = fpoint P Q R d0 (0, 1, 0))
    (h21 : ⟪fpoint P Q R d0 (β - 1 / 2, 0, 0), R⟫ < ⟪fpoint P Q R d0 (-α / 2, 0, β), R⟫)
    (h32 : ⟪fpoint P Q R d0 (α * (β - 1 / 2), β, 0), R⟫ < ⟪fpoint P Q R d0 (β - 1 / 2, 0, 0), R⟫)
    (h40 : ⟪fpoint P Q R d0 (-α * γ6, β6, γ6), R⟫ < ⟪fpoint P Q R d0 (-α, 0, 1), R⟫)
    (h01 : ⟪fpoint P Q R d0 (-α, 0, 1), R⟫ < ⟪fpoint P Q R d0 (-α / 2, 0, β), R⟫) :
    HasLexCellAt V R := by
  refine cyc_cell V P Q R d0 hΔ (k := 5) (by norm_num) (k17b2Cy13 α β β6 γ6)
    (k17b2Cy13_inj (by linarith) (by linarith) (by linarith) (by linarith)) hmem
    [((0 : ℝ), (0 : ℝ), (0 : ℝ)), ((0 : ℝ), (1 : ℝ), (0 : ℝ))] ?_
    (u1 := 0) (u2 := 1) (t1 := 1) (t2 := 0) (lo := 0) (hi := 1) (by norm_num) (by norm_num)
    (fun v1 v2 => 0 < v2) ?_ ?_ ?_
  · intro y hy
    rcases hVall y hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl ⟨0, rfl⟩
    · exact Or.inl ⟨1, rfl⟩
    · exact Or.inl ⟨2, rfl⟩
    · exact Or.inl ⟨3, rfl⟩
    · exact Or.inl ⟨4, rfl⟩
    · exact Or.inr ⟨_, by simp, rfl⟩
    · exact Or.inr ⟨_, by simp, rfl⟩
  · intro lam h0 h1
    simp only [mul_zero, add_zero, zero_add, mul_one]
    norm_num
  · intro v1 v2 hv2
    exact k17b2_p13_tsc hα hβ hβ6 hγ6 hv2
  · intro v1 v2 _ hL
    refine k17b2_pent_uni4 _ _ hL ?_ ?_ ?_ ?_
    · simpa only [k17b2Cy13_2, k17b2Cy13_1] using h21
    · simpa only [k17b2Cy13_3, k17b2Cy13_2] using h32
    · simpa only [k17b2Cy13_4, k17b2Cy13_0] using h40
    · simpa only [k17b2Cy13_0, k17b2Cy13_1] using h01

set_option maxHeartbeats 12800000 in
/-- **K6M2 rule 13** (view `W = b' - m(d,c)`, cell `(c, b', a, c', a')`): depth literals `b' > c > a'`, `b' > a > c'` at `W`. -/
theorem k17b2_r13 {a a' b b' c c' d : ℝ³} {α1 β1 β6 γ6 : ℝ}
    (hdet : det3 (a - d) (b - d) (c - d) ≠ 0)
    (hc' : c' = d + α1 • (a - d) + β1 • (b - d)) (hb' : b' = d + α1 • (a - d) + β1 • (c - d))
    (ha' : a' = d + β6 • (b - d) + γ6 • (c - d))
    (hα1 : 1 < α1) (hβ1 : 1 < β1) (hβ6 : 1 < β6) (hγ6 : 1 < γ6)
    (h1 : 0 < ⟪b' - c, b' - (1 / 2 : ℝ) • (d + c)⟫) (h2 : 0 < ⟪c - a', b' - (1 / 2 : ℝ) • (d + c)⟫)
    (h3 : 0 < ⟪a - c', b' - (1 / 2 : ℝ) • (d + c)⟫) (h4 : 0 < ⟪b' - a, b' - (1 / 2 : ℝ) • (d + c)⟫) :
    HasLexCell (V8 a a' b b' c c' d) := by
  obtain ⟨p, rfl⟩ : ∃ p, a = d + p := ⟨a - d, by abel⟩
  obtain ⟨q, rfl⟩ : ∃ q, b = d + q := ⟨b - d, by abel⟩
  obtain ⟨r, rfl⟩ : ∃ r, c = d + r := ⟨c - d, by abel⟩
  simp only [add_sub_cancel_left] at hdet hc' hb' ha'
  subst hc' hb' ha'
  have hα0 : 0 < α1 := by linarith
  have hμ : 0 < β1 - 1 / 2 := by linarith
  have hμ0 : 2 * β1 - 1 ≠ 0 := by intro h; linarith
  have hμ1 : -1 + β1 * 2 ≠ 0 := by intro h; linarith
  have hinv : (-1 + β1 * 2)⁻¹ * (-1 + β1 * 2) = 1 := inv_mul_cancel₀ hμ1
  set Wv : ℝ³ := (d + α1 • p + β1 • r) - (1 / 2 : ℝ) • (d + (d + r)) with hWv
  set Rv : ℝ³ := (2 / (2 * β1 - 1)) • Wv with hRv
  set P : ℝ³ := (2 / (2 * β1 - 1)) • p with hP
  have hΔ : det3 P q Rv ≠ 0 := by
    have e : det3 P q Rv = (2 / (2 * β1 - 1)) * det3 p q r := by
      simp only [hP, hRv, hWv, det3_expand, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
      field_simp; ring
    rw [e]; exact mul_ne_zero (div_pos (by norm_num) (by linarith)).ne' hdet
  have eC : fpoint P q Rv d (-α1, 0, 1) = d + r := by
    simp only [fpoint, fcomb, hP, hRv, hWv]
    match_scalars <;> field_simp <;> ring
  have eD : fpoint P q Rv d (0, 0, 0) = d := by simp [fpoint, fcomb]
  have eA : fpoint P q Rv d (β1 - 1 / 2, 0, 0) = d + p := by
    simp only [fpoint, fcomb, hP]; match_scalars <;> field_simp <;> first | ring1 | linear_combination hinv
  have eC' : fpoint P q Rv d (α1 * (β1 - 1 / 2), β1, 0) = d + α1 • p + β1 • q := by
    simp only [fpoint, fcomb, hP]; match_scalars <;> field_simp <;> first | ring1 | linear_combination hinv
  have eA' : fpoint P q Rv d (-α1 * γ6, β6, γ6) = d + β6 • q + γ6 • r := by
    simp only [fpoint, fcomb, hP, hRv, hWv]
    match_scalars <;> field_simp <;> ring
  have eB' : fpoint P q Rv d (-α1 / 2, 0, β1) = d + α1 • p + β1 • r := by
    simp only [fpoint, fcomb, hP, hRv, hWv]
    match_scalars <;> field_simp <;> first | ring1 | linear_combination hinv
  have eB : fpoint P q Rv d (0, 1, 0) = d + q := by simp only [fpoint, fcomb]; module
  have hi : ∀ x : ℝ³, ⟪x, Rv⟫ = (2 / (2 * β1 - 1)) * ⟪x, Wv⟫ := by
    intro x; rw [hRv, inner_smul_right]
  have hpos : 0 < 2 / (2 * β1 - 1) := div_pos (by norm_num) (by linarith)
  have inner_lt : ∀ X Y : ℝ³, 0 < ⟪Y - X, Wv⟫ → ⟪X, Rv⟫ < ⟪Y, Rv⟫ := by
    intro X Y h; rw [inner_sub_left] at h; rw [hi, hi]; nlinarith
  have h21 : ⟪d + p, Rv⟫ < ⟪d + α1 • p + β1 • r, Rv⟫ := inner_lt _ _ h4
  have h32 : ⟪d + α1 • p + β1 • q, Rv⟫ < ⟪d + p, Rv⟫ := inner_lt _ _ h3
  have h40 : ⟪d + β6 • q + γ6 • r, Rv⟫ < ⟪d + r, Rv⟫ := inner_lt _ _ h2
  have h01 : ⟪d + r, Rv⟫ < ⟪d + α1 • p + β1 • r, Rv⟫ := inner_lt _ _ h1
  refine ⟨Rv, ?_, ?_⟩
  · intro h0; apply hΔ; rw [h0]; simp [det3_expand]
  refine k17b2_p13_frame (V8 (d + p) (d + β6 • q + γ6 • r) (d + q) (d + α1 • p + β1 • r) (d + r) (d + α1 • p + β1 • q) d)
    P q Rv d hΔ hα1 hβ1 hβ6 hγ6 ?_ ?_ ?_ ?_ ?_ ?_
  · intro i
    rcases z5_cases i with rfl | rfl | rfl | rfl | rfl
    · simp only [k17b2Cy13_0, eC]; simp [V8]
    · simp only [k17b2Cy13_1, eB']; simp [V8]
    · simp only [k17b2Cy13_2, eA]; simp [V8]
    · simp only [k17b2Cy13_3, eC']; simp [V8]
    · simp only [k17b2Cy13_4, eA']; simp [V8]
  · intro y hy
    rw [eC, eB', eA, eC', eA', eD, eB]
    simp only [V8, Finset.mem_insert, Finset.mem_singleton] at hy
    tauto
  · rw [eA, eB']; exact h21
  · rw [eC', eA]; exact h32
  · rw [eA', eC]; exact h40
  · rw [eC, eB']; exact h01

end C2
end Type08Sp
end Minimality
