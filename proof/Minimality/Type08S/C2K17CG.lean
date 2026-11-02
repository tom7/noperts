module

public import Minimality.Type08S.C2K17CF

@[expose] public section


/-!
# K17C / P3G: the cell at `a - d` on the data.  `k17c_A_cell`: any tilt segment in the cone with V-shaped plateau.
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

theorem k17cMet_of {P Q R : ℝ³} {β6 γ6 v1 v2 : ℝ}
    (h : v1 * ⟪P, P⟫ + v2 * ⟪P, Q⟫ ≤ 0 ∨
      0 ≤ (β6 - 1) * (v1 * ⟪P, P⟫ + v2 * ⟪P, Q⟫) + γ6 * (v1 * ⟪Q, P⟫ + v2 * ⟪Q, Q⟫)) :
    K17cMet P Q R β6 γ6 v1 v2 := by
  unfold K17cMet
  simp only [k17c_inner_fcomb_right, zero_mul, add_zero]
  exact h

set_option maxHeartbeats 1600000 in
/-- **Cell at `a - d`** (pentagon `(b, a', b', a, d)`): `α1 ≥ 1`, `β1 = 1`, `⟪a-d, b-d⟫ = 0`, with a tilt segment
`u + lam t` (`0 < lam < 1`) in the cone and with the V-shaped plateau condition
`A ≤ 0 ∨ 0 ≤ (β6-1) A + γ6 B` (`A = v1 qq + v2 qr`, `B = v1 qr + v2 rr`). -/
theorem k17c_A_cell {a a' b b' c c' d : ℝ³} {α1 β6 γ6 : ℝ}
    (hdet : det3 (a - d) (b - d) (c - d) ≠ 0)
    (hc' : c' = d + α1 • (a - d) + (1 : ℝ) • (b - d)) (hb' : b' = d + α1 • (a - d) + (1 : ℝ) • (c - d))
    (ha' : a' = d + β6 • (b - d) + γ6 • (c - d))
    (hα1 : 1 ≤ α1) (hβ6 : 0 < β6) (hγ6 : 0 < γ6) (h3 : 1 < β6 + γ6)
    (hM : K6sM a a' b b' c c' d) (hm0 : ⟪a - d, b - d⟫ = 0)
    {u1 u2 t1 t2 : ℝ} (hut : u1 * t2 - u2 * t1 ≠ 0)
    (hC : ∀ lam : ℝ, 0 < lam → lam < 1 → K17cCone β6 γ6 (u1 + lam * t1) (u2 + lam * t2))
    (hU : ∀ lam : ℝ, 0 < lam → lam < 1 →
      (u1 + lam * t1) * ⟪b - d, b - d⟫ + (u2 + lam * t2) * ⟪b - d, c - d⟫ ≤ 0 ∨
      0 ≤ (β6 - 1) * ((u1 + lam * t1) * ⟪b - d, b - d⟫ + (u2 + lam * t2) * ⟪b - d, c - d⟫) +
        γ6 * ((u1 + lam * t1) * ⟪b - d, c - d⟫ + (u2 + lam * t2) * ⟪c - d, c - d⟫)) :
    HasLexCell (V8 a a' b b' c c' d) := by
  obtain ⟨hpr, hpp, hqq, hrr, -, -⟩ := k17c_gram hdet hc' hb' hM hm0
  set P := b - d with hP
  set Q := c - d with hQ
  set R := a - d with hR
  have hΔ : det3 P Q R ≠ 0 := by
    intro h; apply hdet
    simp only [det3_expand] at h ⊢; linarith
  have eO : fpoint P Q R d (0, 0, 0) = d := by simp [fpoint, fcomb]
  have eB : fpoint P Q R d (1, 0, 0) = b := by simp only [fpoint, fcomb, hP]; module
  have eC : fpoint P Q R d (0, 1, 0) = c := by simp only [fpoint, fcomb, hQ]; module
  have eA : fpoint P Q R d (0, 0, 1) = a := by simp only [fpoint, fcomb, hR]; module
  have eA' : fpoint P Q R d (β6, γ6, 0) = a' := by rw [ha']; simp only [fpoint, fcomb, hP, hQ]; module
  have eC' : fpoint P Q R d (1, 0, α1) = c' := by rw [hc']; simp only [fpoint, fcomb, hP, hR]; module
  have eB' : fpoint P Q R d (0, 1, α1) = b' := by rw [hb']; simp only [fpoint, fcomb, hQ, hR]; module
  have hPR : ⟪P, R⟫ = 0 := by rw [hP, hR, real_inner_comm]; exact hm0
  have hQR : ⟪Q, R⟫ = 0 := by rw [hQ, hR, real_inner_comm]; exact hpr
  have hRR : 0 < ⟪R, R⟫ := hpp
  have hA : HasLexCellAt (V8 a a' b b' c c' d) R := by
    refine k17cA_frame (V8 a a' b b' c c' d) P Q R d hΔ hα1 hβ6 hγ6 h3 hPR hQR hRR ?_ ?_ hut hC ?_
    · intro i
      rcases z5_cases i with rfl | rfl | rfl | rfl | rfl
      · simp only [k17cACyc, pc5_0, eB]; simp [V8]
      · simp only [k17cACyc, pc5_1, eA']; simp [V8]
      · simp only [k17cACyc, pc5_2, eB']; simp [V8]
      · simp only [k17cACyc, pc5_3, eA]; simp [V8]
      · simp only [k17cACyc, pc5_4, eO]; simp [V8]
    · intro y hy
      rw [eB, eA', eB', eA, eO, eC, eC']
      simp only [V8, Finset.mem_insert, Finset.mem_singleton] at hy
      tauto
    · intro lam h0 h1
      have := hU lam h0 h1
      have hcom : ⟪Q, P⟫ = ⟪P, Q⟫ := real_inner_comm P Q
      apply k17cMet_of
      rw [hcom]
      exact this
  refine ⟨R, ?_, hA⟩
  intro h0; apply hΔ; rw [h0]; simp [det3_expand]

end C2
end Type08Sp
end Minimality
