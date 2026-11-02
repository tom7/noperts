module

public import Minimality.Type08S.C2K17CN

@[expose] public section


/-!
# K17C / P3O: S3.6b and S3.4 on the data.
-/
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp
namespace C2

/-- The `d - b` frame facts: `⟪P,Q⟫ = ⟪P,R⟫ = 0`, `⟪Q,R⟫ = -qr`, `⟪R,R⟫ = qq`. -/
theorem k17c_dbframe {a b c d : ℝ³} (hpr : ⟪a - d, c - d⟫ = 0) (hm0 : ⟪a - d, b - d⟫ = 0) :
    ⟪a - d, d - b⟫ = 0 ∧ ⟪c - d, d - b⟫ = -⟪b - d, c - d⟫ ∧ ⟪d - b, d - b⟫ = ⟪b - d, b - d⟫ := by
  refine ⟨?_, ?_, ?_⟩
  · have : ⟪a - d, d - b⟫ = -⟪a - d, b - d⟫ := by rw [← inner_neg_right]; congr 1; abel
    rw [this, hm0]; simp
  · have : ⟪c - d, d - b⟫ = -⟪b - d, c - d⟫ := by
      rw [real_inner_comm, ← inner_neg_left]; congr 1; abel
    exact this
  · rw [← inner_neg_neg]; congr 1 <;> abel

set_option maxHeartbeats 1600000 in
/-- **S3.6b**: `α1 > 1`, `β1 = 1`, `γ6 ≤ 1`, `ζ_b < 0`: pentagon `(c', b', c, a', b)` at `d - b`. -/
theorem k17c_s36b_hasLexCell {a a' b b' c c' d : ℝ³} {α1 β6 γ6 : ℝ}
    (hdet : det3 (a - d) (b - d) (c - d) ≠ 0)
    (hc' : c' = d + α1 • (a - d) + (1 : ℝ) • (b - d)) (hb' : b' = d + α1 • (a - d) + (1 : ℝ) • (c - d))
    (ha' : a' = d + β6 • (b - d) + γ6 • (c - d))
    (hα1 : 1 < α1) (hβ6 : 0 < β6) (hγ6 : 0 < γ6) (h3 : 1 < β6 + γ6) (hγ61 : γ6 ≤ 1)
    (hM : K6sM a a' b b' c c' d) (hm0 : ⟪a - d, b - d⟫ = 0)
    (hzb : (β6 - 1) * ⟪b - d, b - d⟫ + γ6 * ⟪b - d, c - d⟫ < 0) :
    HasLexCell (V8 a a' b b' c c' d) := by
  obtain ⟨hpr, hpp, hqq, hrr, hq1, -⟩ := k17c_gram hdet hc' hb' hM hm0
  obtain ⟨hPR, hQR, hRR⟩ := k17c_dbframe hpr hm0
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
  have eB' : fpoint P Q R d (α1, 1, 0) = b' := by rw [hb']; simp only [fpoint, fcomb, hP, hQ]; module
  have eC' : fpoint P Q R d (α1, 0, -1) = c' := by rw [hc']; simp only [fpoint, fcomb, hP, hR]; module
  have eA' : fpoint P Q R d (0, γ6, -β6) = a' := by rw [ha']; simp only [fpoint, fcomb, hR, hQ]; module
  have hA : HasLexCellAt (V8 a a' b b' c c' d) R := by
    refine k17cS36b_frame (V8 a a' b b' c c' d) P Q R d hΔ hα1 hβ6 hγ6 hγ61 h3 hpr hPR hpp ?_ ?_ ?_ ?_
    · rw [hQR, hRR]; linarith
    · rw [hQR, hRR]; linarith
    · intro i
      rcases z5_cases i with rfl | rfl | rfl | rfl | rfl
      · simp only [k17cS36bCyc, pc5_0, eC']; simp [V8]
      · simp only [k17cS36bCyc, pc5_1, eB']; simp [V8]
      · simp only [k17cS36bCyc, pc5_2, eC]; simp [V8]
      · simp only [k17cS36bCyc, pc5_3, eA']; simp [V8]
      · simp only [k17cS36bCyc, pc5_4, eB]; simp [V8]
    · intro y hy
      rw [eC', eB', eC, eA', eB, eO, eA]
      simp only [V8, Finset.mem_insert, Finset.mem_singleton] at hy
      tauto
  refine ⟨R, ?_, hA⟩
  intro h0; apply hΔ; rw [h0]; simp [det3_expand]

set_option maxHeartbeats 1600000 in
/-- **S3.4**: `α1 > 1`, `β1 = 1`, `γ6 > 1`, `ζ_b < 0`: quadrilateral `(c', b', a', b)` at `d - b`. -/
theorem k17c_s34_hasLexCell {a a' b b' c c' d : ℝ³} {α1 β6 γ6 : ℝ}
    (hdet : det3 (a - d) (b - d) (c - d) ≠ 0)
    (hc' : c' = d + α1 • (a - d) + (1 : ℝ) • (b - d)) (hb' : b' = d + α1 • (a - d) + (1 : ℝ) • (c - d))
    (ha' : a' = d + β6 • (b - d) + γ6 • (c - d))
    (hα1 : 1 < α1) (hβ6 : 0 < β6) (hγ61 : 1 < γ6)
    (hM : K6sM a a' b b' c c' d) (hm0 : ⟪a - d, b - d⟫ = 0)
    (hzb : (β6 - 1) * ⟪b - d, b - d⟫ + γ6 * ⟪b - d, c - d⟫ < 0) :
    HasLexCell (V8 a a' b b' c c' d) := by
  obtain ⟨hpr, hpp, hqq, hrr, hq1, -⟩ := k17c_gram hdet hc' hb' hM hm0
  obtain ⟨hPR, hQR, hRR⟩ := k17c_dbframe hpr hm0
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
  have eB' : fpoint P Q R d (α1, 1, 0) = b' := by rw [hb']; simp only [fpoint, fcomb, hP, hQ]; module
  have eC' : fpoint P Q R d (α1, 0, -1) = c' := by rw [hc']; simp only [fpoint, fcomb, hP, hR]; module
  have eA' : fpoint P Q R d (0, γ6, -β6) = a' := by rw [ha']; simp only [fpoint, fcomb, hR, hQ]; module
  have hA : HasLexCellAt (V8 a a' b b' c c' d) R := by
    refine k17cS34_frame (V8 a a' b b' c c' d) P Q R d hΔ hα1 hβ6 hγ61 hpr hPR hpp ?_ ?_ ?_ ?_
    · rw [hQR, hRR]; linarith
    · rw [hQR, hRR]; linarith
    · intro i
      rcases z4_cases i with rfl | rfl | rfl | rfl
      · simp only [k17cS34Cyc_0, eC']; simp [V8]
      · simp only [k17cS34Cyc_1, eB']; simp [V8]
      · simp only [k17cS34Cyc_2, eA']; simp [V8]
      · simp only [k17cS34Cyc_3, eB]; simp [V8]
    · intro y hy
      rw [eC', eB', eA', eB, eO, eA, eC]
      simp only [V8, Finset.mem_insert, Finset.mem_singleton] at hy
      tauto
  refine ⟨R, ?_, hA⟩
  intro h0; apply hΔ; rw [h0]; simp [det3_expand]

end C2
end Type08Sp
end Minimality
