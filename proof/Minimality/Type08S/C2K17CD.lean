module

public import Minimality.Type08S.C2K17CC

@[expose] public section


/-!
# K17C / P3D: Gram facts on the slice (`β1 = 1`, `⟪a-d, b-d⟫ = 0`), and the cell S3.5 on the data.
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

/-- Gram facts of the `β1 = 1` slice: `p = a - d ⟂ q = b - d, r = c - d`, `qq, rr, pp > 0`,
`qr < qq`, `qr < rr`. -/
theorem k17c_gram {a a' b b' c c' d : ℝ³} {α1 : ℝ}
    (hdet : det3 (a - d) (b - d) (c - d) ≠ 0)
    (hc' : c' = d + α1 • (a - d) + (1 : ℝ) • (b - d)) (hb' : b' = d + α1 • (a - d) + (1 : ℝ) • (c - d))
    (hM : K6sM a a' b b' c c' d) (hm0 : ⟪a - d, b - d⟫ = 0) :
    ⟪a - d, c - d⟫ = 0 ∧ 0 < ⟪a - d, a - d⟫ ∧ 0 < ⟪b - d, b - d⟫ ∧ 0 < ⟪c - d, c - d⟫ ∧
      ⟪b - d, c - d⟫ < ⟪b - d, b - d⟫ ∧ ⟪b - d, c - d⟫ < ⟪c - d, c - d⟫ := by
  obtain ⟨m1, m2, m3⟩ := hM
  have hbc : b - c = (b - d) - (c - d) := by abel
  have hpr : ⟪a - d, c - d⟫ = 0 := by
    rw [hbc, inner_sub_right] at m1; linarith
  have e1 : c' - d = α1 • (a - d) + (1 : ℝ) • (b - d) := by rw [hc']; abel
  have e2 : b' - d = α1 • (a - d) + (1 : ℝ) • (c - d) := by rw [hb']; abel
  rw [e1, hbc] at m2
  rw [e2, hbc] at m3
  have hqc := real_inner_comm (b - d) (c - d)
  generalize hp : a - d = p at *
  generalize hq : b - d = q at *
  generalize hr : c - d = r at *
  simp only [inner_add_left, inner_sub_right, real_inner_smul_left, hm0, hpr] at m2 m3
  subst hp hq hr
  refine ⟨hpr, ?_, ?_, ?_, ?_, ?_⟩
  · apply real_inner_self_pos.2; intro h0; apply hdet; rw [h0]; simp [det3_expand]
  · apply real_inner_self_pos.2; intro h0; apply hdet; rw [h0]; simp [det3_expand]
  · apply real_inner_self_pos.2; intro h0; apply hdet; rw [h0]; simp [det3_expand]
  · linarith
  · linarith

set_option maxHeartbeats 1600000 in
/-- **S3.5**: `α1 ≥ 1`, `β1 = 1`, `γ6 ≤ 1`, `⟪b-d, c-d⟫ < 0`, `⟪a-d, b-d⟫ = 0`: pentagon `(c', b', c, d, b)` at `d - b`. -/
theorem k17c_s35_hasLexCell {a a' b b' c c' d : ℝ³} {α1 β6 γ6 : ℝ}
    (hdet : det3 (a - d) (b - d) (c - d) ≠ 0)
    (hc' : c' = d + α1 • (a - d) + (1 : ℝ) • (b - d)) (hb' : b' = d + α1 • (a - d) + (1 : ℝ) • (c - d))
    (ha' : a' = d + β6 • (b - d) + γ6 • (c - d))
    (hα1 : 1 ≤ α1) (hβ6 : 0 < β6) (hγ6 : 0 < γ6) (h3 : 1 < β6 + γ6) (hγ61 : γ6 ≤ 1)
    (hM : K6sM a a' b b' c c' d) (hm0 : ⟪a - d, b - d⟫ = 0) (hqr : ⟪b - d, c - d⟫ < 0) :
    HasLexCell (V8 a a' b b' c c' d) := by
  obtain ⟨hpr, hpp, hqq, hrr, -, -⟩ := k17c_gram hdet hc' hb' hM hm0
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
  have hPQ : ⟪P, Q⟫ = 0 := hpr
  have hPR : ⟪P, R⟫ = 0 := by
    have : ⟪a - d, d - b⟫ = -⟪a - d, b - d⟫ := by rw [← inner_neg_right]; congr 1; abel
    rw [hR, this, hm0]; simp
  have hQR : 0 < ⟪Q, R⟫ := by
    have : ⟪c - d, d - b⟫ = -⟪b - d, c - d⟫ := by
      rw [real_inner_comm, ← inner_neg_left]; congr 1; abel
    rw [hQ, hR, this]; linarith
  have hRR : 0 < ⟪R, R⟫ := by
    have : ⟪d - b, d - b⟫ = ⟪b - d, b - d⟫ := by
      rw [← inner_neg_neg]; congr 1 <;> abel
    rw [hR, this]; exact hqq
  have hA : HasLexCellAt (V8 a a' b b' c c' d) R := by
    refine k17cS35_frame (V8 a a' b b' c c' d) P Q R d hΔ hα1 hβ6 hγ6 hγ61 h3 hPQ hPR hpp hQR hRR ?_ ?_
    · intro i
      rcases z5_cases i with rfl | rfl | rfl | rfl | rfl
      · simp only [k17cS35Cyc, pc5_0, eB']; simp [V8]
      · simp only [k17cS35Cyc, pc5_1, eC]; simp [V8]
      · simp only [k17cS35Cyc, pc5_2, eO]; simp [V8]
      · simp only [k17cS35Cyc, pc5_3, eB]; simp [V8]
      · simp only [k17cS35Cyc, pc5_4, eC']; simp [V8]
    · intro y hy
      rw [eB', eC, eO, eB, eC', eA, eA']
      simp only [V8, Finset.mem_insert, Finset.mem_singleton] at hy
      tauto
  refine ⟨R, ?_, hA⟩
  intro h0; apply hΔ; rw [h0]; simp [det3_expand]

end C2
end Type08Sp
end Minimality
