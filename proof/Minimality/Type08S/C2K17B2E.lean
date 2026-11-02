module

public import Minimality.Type08S.C2K17B2D

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

set_option maxHeartbeats 12800000 in
/-- **K6M2 rule 4** (view `d - b'`, cell `(c, d, a, c', a')`): depth literals `a' < c' < a < d`, `c < d` at `V = d - b'`. -/
theorem k17b2_r4 {a a' b b' c c' d : ℝ³} {α1 β1 β6 γ6 : ℝ}
    (hdet : det3 (a - d) (b - d) (c - d) ≠ 0)
    (hc' : c' = d + α1 • (a - d) + β1 • (b - d)) (hb' : b' = d + α1 • (a - d) + β1 • (c - d))
    (ha' : a' = d + β6 • (b - d) + γ6 • (c - d))
    (hα1 : 1 < α1) (hβ1 : 1 < β1) (hβ6 : 1 < β6) (hγ6 : 1 < γ6)
    (h1 : 0 < ⟪c' - a', d - b'⟫) (h2 : 0 < ⟪a - c', d - b'⟫) (h3 : 0 < ⟪d - a, d - b'⟫) (h4 : 0 < ⟪d - c, d - b'⟫) :
    HasLexCell (V8 a a' b b' c c' d) := by
  obtain ⟨p, rfl⟩ : ∃ p, a = d + p := ⟨a - d, by abel⟩
  obtain ⟨q, rfl⟩ : ∃ q, b = d + q := ⟨b - d, by abel⟩
  obtain ⟨r, rfl⟩ : ∃ r, c = d + r := ⟨c - d, by abel⟩
  simp only [add_sub_cancel_left] at hdet hc' hb' ha'
  subst hc' hb' ha'
  have hα0 : 0 < α1 := by linarith
  have hβ0 : 0 < β1 := by linarith
  have hβ00 : β1 ≠ 0 := hβ0.ne'
  set Vv : ℝ³ := d - (d + α1 • p + β1 • r) with hVv
  set Rv : ℝ³ := (1 / β1) • Vv with hRv
  set P : ℝ³ := (1 / β1) • p with hP
  have hΔ : det3 P q Rv ≠ 0 := by
    have e : det3 P q Rv = -(1 / β1) * det3 p q r := by
      simp only [hP, hRv, hVv, det3_expand, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
      field_simp; ring
    rw [e]; exact mul_ne_zero (by simp [hβ00]) hdet
  have eC : fpoint P q Rv d (-α1, 0, -1) = d + r := by
    simp only [fpoint, fcomb, hP, hRv, hVv]
    match_scalars <;> field_simp <;> ring
  have eD : fpoint P q Rv d (0, 0, 0) = d := by simp [fpoint, fcomb]
  have eA : fpoint P q Rv d (β1, 0, 0) = d + p := by
    simp only [fpoint, fcomb, hP]; match_scalars <;> field_simp <;> ring
  have eC' : fpoint P q Rv d (α1 * β1, β1, 0) = d + α1 • p + β1 • q := by
    simp only [fpoint, fcomb, hP]; match_scalars <;> field_simp <;> ring
  have eA' : fpoint P q Rv d (-α1 * γ6, β6, -γ6) = d + β6 • q + γ6 • r := by
    simp only [fpoint, fcomb, hP, hRv, hVv]
    match_scalars <;> field_simp <;> ring
  have eB' : fpoint P q Rv d (0, 0, -β1) = d + α1 • p + β1 • r := by
    simp only [fpoint, fcomb, hRv, hVv]
    match_scalars <;> field_simp <;> ring
  have eB : fpoint P q Rv d (0, 1, 0) = d + q := by simp only [fpoint, fcomb]; module
  have hi : ∀ x : ℝ³, ⟪x, Rv⟫ = (1 / β1) * ⟪x, Vv⟫ := by
    intro x; rw [hRv, inner_smul_right]
  have hpos : 0 < 1 / β1 := by positivity
  have inner_lt : ∀ X Y : ℝ³, 0 < ⟪Y - X, Vv⟫ → ⟪X, Rv⟫ < ⟪Y, Rv⟫ := by
    intro X Y h; rw [inner_sub_left] at h; rw [hi, hi]; nlinarith
  have h43 : ⟪d + β6 • q + γ6 • r, Rv⟫ < ⟪d + α1 • p + β1 • q, Rv⟫ := inner_lt _ _ h1
  have h32 : ⟪d + α1 • p + β1 • q, Rv⟫ < ⟪d + p, Rv⟫ := inner_lt _ _ h2
  have h21 : ⟪d + p, Rv⟫ < ⟪d, Rv⟫ := inner_lt _ _ h3
  have h01 : ⟪d + r, Rv⟫ < ⟪d, Rv⟫ := inner_lt _ _ h4
  refine ⟨Rv, ?_, ?_⟩
  · intro h0; apply hΔ; rw [h0]; simp [det3_expand]
  refine k17b2_p4_frame (V8 (d + p) (d + β6 • q + γ6 • r) (d + q) (d + α1 • p + β1 • r) (d + r) (d + α1 • p + β1 • q) d)
    P q Rv d hΔ hα1 hβ1 hβ6 hγ6 ?_ ?_ ?_ ?_ ?_ ?_
  · intro i
    rcases z5_cases i with rfl | rfl | rfl | rfl | rfl
    · simp only [k17b2Cy4_0, eC]; simp [V8]
    · simp only [k17b2Cy4_1, eD]; simp [V8]
    · simp only [k17b2Cy4_2, eA]; simp [V8]
    · simp only [k17b2Cy4_3, eC']; simp [V8]
    · simp only [k17b2Cy4_4, eA']; simp [V8]
  · intro y hy
    rw [eC, eD, eA, eC', eA', eB', eB]
    simp only [V8, Finset.mem_insert, Finset.mem_singleton] at hy
    tauto
  · rw [eA', eC']; exact h43
  · rw [eC', eA]; exact h32
  · rw [eA, eD]; exact h21
  · rw [eC, eD]; exact h01

set_option maxHeartbeats 12800000 in
/-- **K6M2 rule 5** (view `d - b'`, cell `(c, b', a, c', a')`): depth literals `b' < a < c'`, `b' < c < a' < c'` at `V = d - b'`. -/
theorem k17b2_r5 {a a' b b' c c' d : ℝ³} {α1 β1 β6 γ6 : ℝ}
    (hdet : det3 (a - d) (b - d) (c - d) ≠ 0)
    (hc' : c' = d + α1 • (a - d) + β1 • (b - d)) (hb' : b' = d + α1 • (a - d) + β1 • (c - d))
    (ha' : a' = d + β6 • (b - d) + γ6 • (c - d))
    (hα1 : 1 < α1) (hβ1 : 1 < β1) (hβ6 : 1 < β6) (hγ6 : 1 < γ6)
    (h1 : 0 < ⟪a - b', d - b'⟫) (h2 : 0 < ⟪c' - a, d - b'⟫) (h3 : 0 < ⟪c' - a', d - b'⟫) (h4 : 0 < ⟪a' - c, d - b'⟫) (h5 : 0 < ⟪c - b', d - b'⟫) :
    HasLexCell (V8 a a' b b' c c' d) := by
  obtain ⟨p, rfl⟩ : ∃ p, a = d + p := ⟨a - d, by abel⟩
  obtain ⟨q, rfl⟩ : ∃ q, b = d + q := ⟨b - d, by abel⟩
  obtain ⟨r, rfl⟩ : ∃ r, c = d + r := ⟨c - d, by abel⟩
  simp only [add_sub_cancel_left] at hdet hc' hb' ha'
  subst hc' hb' ha'
  have hα0 : 0 < α1 := by linarith
  have hβ0 : 0 < β1 := by linarith
  have hβ00 : β1 ≠ 0 := hβ0.ne'
  set Vv : ℝ³ := d - (d + α1 • p + β1 • r) with hVv
  set Rv : ℝ³ := (1 / β1) • Vv with hRv
  set P : ℝ³ := (1 / β1) • p with hP
  have hΔ : det3 P q Rv ≠ 0 := by
    have e : det3 P q Rv = -(1 / β1) * det3 p q r := by
      simp only [hP, hRv, hVv, det3_expand, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
      field_simp; ring
    rw [e]; exact mul_ne_zero (by simp [hβ00]) hdet
  have eC : fpoint P q Rv d (-α1, 0, -1) = d + r := by
    simp only [fpoint, fcomb, hP, hRv, hVv]
    match_scalars <;> field_simp <;> ring
  have eD : fpoint P q Rv d (0, 0, 0) = d := by simp [fpoint, fcomb]
  have eA : fpoint P q Rv d (β1, 0, 0) = d + p := by
    simp only [fpoint, fcomb, hP]; match_scalars <;> field_simp <;> ring
  have eC' : fpoint P q Rv d (α1 * β1, β1, 0) = d + α1 • p + β1 • q := by
    simp only [fpoint, fcomb, hP]; match_scalars <;> field_simp <;> ring
  have eA' : fpoint P q Rv d (-α1 * γ6, β6, -γ6) = d + β6 • q + γ6 • r := by
    simp only [fpoint, fcomb, hP, hRv, hVv]
    match_scalars <;> field_simp <;> ring
  have eB' : fpoint P q Rv d (0, 0, -β1) = d + α1 • p + β1 • r := by
    simp only [fpoint, fcomb, hRv, hVv]
    match_scalars <;> field_simp <;> ring
  have eB : fpoint P q Rv d (0, 1, 0) = d + q := by simp only [fpoint, fcomb]; module
  have hi : ∀ x : ℝ³, ⟪x, Rv⟫ = (1 / β1) * ⟪x, Vv⟫ := by
    intro x; rw [hRv, inner_smul_right]
  have hpos : 0 < 1 / β1 := by positivity
  have inner_lt : ∀ X Y : ℝ³, 0 < ⟪Y - X, Vv⟫ → ⟪X, Rv⟫ < ⟪Y, Rv⟫ := by
    intro X Y h; rw [inner_sub_left] at h; rw [hi, hi]; nlinarith
  have h12 : ⟪d + α1 • p + β1 • r, Rv⟫ < ⟪d + p, Rv⟫ := inner_lt _ _ h1
  have h23 : ⟪d + p, Rv⟫ < ⟪d + α1 • p + β1 • q, Rv⟫ := inner_lt _ _ h2
  have h43 : ⟪d + β6 • q + γ6 • r, Rv⟫ < ⟪d + α1 • p + β1 • q, Rv⟫ := inner_lt _ _ h3
  have h04 : ⟪d + r, Rv⟫ < ⟪d + β6 • q + γ6 • r, Rv⟫ := inner_lt _ _ h4
  have h10 : ⟪d + α1 • p + β1 • r, Rv⟫ < ⟪d + r, Rv⟫ := inner_lt _ _ h5
  refine ⟨Rv, ?_, ?_⟩
  · intro h0; apply hΔ; rw [h0]; simp [det3_expand]
  refine k17b2_p5_frame (V8 (d + p) (d + β6 • q + γ6 • r) (d + q) (d + α1 • p + β1 • r) (d + r) (d + α1 • p + β1 • q) d)
    P q Rv d hΔ hα1 hβ1 hβ6 hγ6 ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro i
    rcases z5_cases i with rfl | rfl | rfl | rfl | rfl
    · simp only [k17b2Cy5_0, eC]; simp [V8]
    · simp only [k17b2Cy5_1, eB']; simp [V8]
    · simp only [k17b2Cy5_2, eA]; simp [V8]
    · simp only [k17b2Cy5_3, eC']; simp [V8]
    · simp only [k17b2Cy5_4, eA']; simp [V8]
  · intro y hy
    rw [eC, eB', eA, eC', eA', eD, eB]
    simp only [V8, Finset.mem_insert, Finset.mem_singleton] at hy
    tauto
  · rw [eB', eA]; exact h12
  · rw [eA, eC']; exact h23
  · rw [eA', eC']; exact h43
  · rw [eC, eA']; exact h04
  · rw [eB', eC]; exact h10

end C2
end Type08Sp
end Minimality
