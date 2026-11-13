module

public import Minimality.Type08S.GT_Sminus

@[expose] public section

set_option autoImplicit true

/-!
# GT, group C: Lemma 1.1 and Lemma 1.2 of sp08b (weakly beyond; `z_a > 0` and `x_a > x_2`)

Real-number form in the frame coordinates of `HFrame` (`g = (E, 0, 0)`, `h = f = (b1, b2, 0)`,
`r = (r1, r2, 0)`, weights `E`, `M` of the horizontal metric).
-/

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

/-- "r weakly beyond" (sp08b §0): `(r-g)·g, (r-g)·h, (r-h)·g, (r-h)·h ≥ 0`, weighted metric, `g = (E,0)`. -/
def WeakBeyond (E M b1 b2 r1 r2 : ℝ) : Prop :=
  0 ≤ (r1 - E) * E / E ∧ 0 ≤ (r1 - E) * b1 / E + (r2 - 0) * b2 / M ∧
  0 ≤ (r1 - b1) * E / E ∧ 0 ≤ (r1 - b1) * b1 / E + (r2 - b2) * b2 / M

/-- **Lemma 1.1 (B1′, B2′).** -/
theorem weakBeyond_B1 {E M b1 b2 r1 r2 : ℝ} (hE : 0 < E) (hM : 0 < M)
    (h : WeakBeyond E M b1 b2 r1 r2) (hne : ¬ (r1 = b1 ∧ r2 = b2)) :
    E ≤ r1 ∧ b1 ≤ r1 ∧ (r2 = b2 → b1 < r1) := by
  obtain ⟨w1, w2, w3, w4⟩ := h
  have e1 : (r1 - E) * E / E = r1 - E := by field_simp
  have e3 : (r1 - b1) * E / E = r1 - b1 := by field_simp
  rw [e1] at w1; rw [e3] at w3
  refine ⟨by linarith, by linarith, fun h2 => ?_⟩
  rcases lt_or_eq_of_le (show b1 ≤ r1 by linarith) with h | h
  · exact h
  · exact absurd ⟨h.symm, h2⟩ hne

theorem weakBeyond_B2 {E M b1 b2 r1 r2 : ℝ} (hE : 0 < E) (hM : 0 < M)
    (hb2 : 0 < b2) (h : WeakBeyond E M b1 b2 r1 r2) (hb : r2 < b2) : 0 < b1 := by
  obtain ⟨w1, w2, w3, w4⟩ := h
  have e3 : (r1 - b1) * E / E = r1 - b1 := by field_simp
  rw [e3] at w3
  have hlt : (r2 - b2) * b2 / M < 0 :=
    div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (by linarith) hb2) hM
  have : 0 < (r1 - b1) * b1 / E := by linarith
  have h5 : 0 < (r1 - b1) * b1 := by
    have := (div_pos_iff.mp this)
    rcases this with ⟨a, _⟩ | ⟨a, b⟩
    · exact a
    · linarith
  rcases lt_or_ge 0 b1 with h6 | h6
  · exact h6
  · nlinarith

end Type08Sp
end Minimality
