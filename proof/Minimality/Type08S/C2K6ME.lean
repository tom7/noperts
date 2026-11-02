module

public import Minimality.Type08S.C2K6MD

@[expose] public section


set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped RealInnerProductSpace Topology
open Finset Filter
namespace Minimality
namespace Type08Sp
namespace C2

/-- `γ6 < 1` in box B (`α1 < 1`), from `gWb ≥ 0`. -/
theorem k6m_gamma6_lt {α1 β1 β6 γ6 : ℝ} (hβ1 : 0 < β1) (hβ6 : 0 < β6) (hα11 : α1 < 1)
    (hg : β1 * (β6 + γ6 - 1) ≤ β6 * (α1 + β1 - 1)) : γ6 < 1 := by
  by_contra h; push Not at h
  nlinarith [mul_pos hβ6 hβ1, mul_pos hβ6 (sub_pos.2 hα11), mul_nonneg hβ1.le (sub_nonneg.2 h)]

set_option maxHeartbeats 1600000 in
/-- **Box B** (`α1 < 1`, view `d - b`): face `Q_ac = (d,a,b',c)`, metric-free. -/
theorem k6m_B_hasLexCell {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) {α1 β1 β6 γ6 : ℝ}
    (hdet : det3 (a - d) (b - d) (c - d) ≠ 0)
    (hc' : c' = d + α1 • (a - d) + β1 • (b - d)) (hb' : b' = d + α1 • (a - d) + β1 • (c - d))
    (ha' : a' = d + β6 • (b - d) + γ6 • (c - d))
    (hα1 : 0 < α1) (hβ1 : 0 < β1) (hs1 : 1 < α1 + β1) (hβ6 : 0 < β6) (hγ6 : 0 < γ6)
    (hα11 : α1 < 1) : HasLexCell (V8 a a' b b' c c' d) := by
  have hγ61 := k6m_gamma6_lt hβ1 hβ6 hα11 (k6m_gWb W hdet hc' hb' ha')
  set P := a - d with hP
  set Q := c - d with hQ
  set R := d - b with hR
  have hΔ : det3 P Q R ≠ 0 := by
    intro h; apply hdet
    have e : det3 (a - d) (b - d) (c - d) = det3 P Q R := by simp only [hP, hQ, hR, det3_expand, PiLp.sub_apply]; ring
    rw [e, h]
  have eO : fpoint P Q R d (0, 0, 0) = d := by simp [fpoint, fcomb]
  have eA : fpoint P Q R d (1, 0, 0) = a := by simp only [fpoint, fcomb, hP]; module
  have eC : fpoint P Q R d (0, 1, 0) = c := by simp only [fpoint, fcomb, hQ]; module
  have eB : fpoint P Q R d (0, 0, -1) = b := by simp only [fpoint, fcomb, hR]; module
  have eB' : fpoint P Q R d (α1, β1, 0) = b' := by rw [hb']; simp only [fpoint, fcomb, hP, hQ]; module
  have eC' : fpoint P Q R d (α1, 0, -β1) = c' := by rw [hc']; simp only [fpoint, fcomb, hP, hR]; module
  have eA' : fpoint P Q R d (0, γ6, -β6) = a' := by rw [ha']; simp only [fpoint, fcomb, hR, hQ]; module
  have hA : HasLexCellAt (V8 a a' b b' c c' d) R := by
    refine k6m_B_frame (V8 a a' b b' c c' d) P Q R d hΔ hα1 hα11 hβ1 hs1 hβ6 hγ6 hγ61 ?_ ?_
    · intro i
      rcases z4_cases i with rfl | rfl | rfl | rfl
      · simp only [kqCyc_0, eO]; simp [V8]
      · simp only [kqCyc_1, eA]; simp [V8]
      · simp only [kqCyc_2, eB']; simp [V8]
      · simp only [kqCyc_3, eC]; simp [V8]
    · intro y hy
      rw [eO, eA, eB', eC, eB, eC', eA']
      simp only [V8, Finset.mem_insert, Finset.mem_singleton] at hy
      tauto
  refine ⟨R, ?_, hA⟩
  intro h0; apply hΔ; rw [h0]; simp [det3_expand]

end C2
end Type08Sp
end Minimality
