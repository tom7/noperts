module

public import Minimality.Type08S.P2RKT2

@[expose] public section

set_option relaxedAutoImplicit true
/-!
# pkR / K2 / KT3: the face cell in frame coordinates (both orientations of `det3 p q r`).
Frame `p = a - d`, `q = c - d`, `r = b - d`.  Points (coordinates in `p, q, r` over `d`):
`d = (0,0,0)`, `a = (1,0,0)`, `b' = (α,γ,0)`, `c = (0,1,0)`, `b = (0,0,1)`, `c' = (1,0,β1)`, `a' = (0,γ6,β6)`.
Tilt `v = -λ p - q`, `0 < λ < (α-1)/γ`.  Cycle `(d, a, b', c)` if `0 < Δ`, `(d, c, b', a)` if `Δ < 0`.
-/
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

theorem inner_fpoint (p q r d w : ℝ³) (t : ℝ × ℝ × ℝ) :
    ⟪fpoint p q r d t, w⟫ = ⟪d, w⟫ + t.1 * ⟪p, w⟫ + t.2.1 * ⟪q, w⟫ + t.2.2 * ⟪r, w⟫ := by
  simp only [fpoint, inner_add_left, inner_fcomb_left]; ring

/-- Non-alternation for a linear functional on the convex quadrilateral `(0, A, αA+γC, C)`. -/
theorem face_nonalt {α γ A C : ℝ} (hα : 1 < α) (hγ : 0 < γ) :
    ¬ (max A C < min 0 (α * A + γ * C)) ∧ ¬ (max 0 (α * A + γ * C) < min A C) := by
  constructor
  · intro h
    simp only [max_lt_iff, lt_min_iff] at h
    obtain ⟨⟨h1, h2⟩, h3, h4⟩ := h
    nlinarith
  · intro h
    simp only [max_lt_iff, lt_min_iff] at h
    obtain ⟨⟨h1, h2⟩, h3, h4⟩ := h
    nlinarith

/-- Lex unimodality of a 4-cycle with `w = w0 + (0, P, B, Q)`, distinct values, no alternation. -/
theorem face_lexUni {z w : ZMod 4 → ℝ} {w0 P Q B : ℝ}
    (hz : ∀ i j, z i = z j) (hw : w = quad w0 (w0 + P) (w0 + B) (w0 + Q))
    (hP : P ≠ 0) (hQ : Q ≠ 0) (hPQ : P ≠ Q) (hB : B ≠ 0) (hBP : B ≠ P) (hBQ : B ≠ Q)
    (hn1 : ¬ (max P Q < min 0 B)) (hn2 : ¬ (max 0 B < min P Q)) : LexUni z w := by
  subst hw
  apply lexUni_four z _ hz
  · intro i j hij h
    rcases z4_cases i with rfl | rfl | rfl | rfl <;> rcases z4_cases j with rfl | rfl | rfl | rfl <;>
      first
      | exact absurd rfl hij
      | (simp only [quad4_0, quad4_1, quad4_2, quad4_3] at h
         first
         | exact hP (by linarith) | exact hQ (by linarith) | exact hPQ (by linarith)
         | exact hB (by linarith) | exact hBP (by linarith) | exact hBQ (by linarith)
         | exact hP (by linarith) | exact hQ (by linarith) | exact hPQ (by linarith)
         | exact hB (by linarith) | exact hBP (by linarith) | exact hBQ (by linarith))
  · simp only [quad4_0, quad4_1, quad4_2, quad4_3]
    intro h
    apply hn1
    simp only [max_lt_iff, lt_min_iff] at h ⊢
    obtain ⟨⟨h1, h2⟩, h3, h4⟩ := h
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith
  · simp only [quad4_0, quad4_1, quad4_2, quad4_3]
    intro h
    apply hn2
    simp only [max_lt_iff, lt_min_iff] at h ⊢
    obtain ⟨⟨h1, h2⟩, h3, h4⟩ := h
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith

end Type08Sp
end Minimality
