module

public import Minimality.Type08S.C2K1D

@[expose] public section

/-!
# C2 / K1E: `S4TRK2` (T, `γ4 = 1`, (B2) or (B3)) with `s = ⟪a' - b, a - d⟫ ≠ 0` has a lex cell

* `B' = ⟪a - d, b - d⟫ ≥ 0`: (B2) from `⟪c,ℓ⟫ ≤ ⟪c',ℓ⟫ = ⟪b',ℓ⟫`; (B3) from `¬RobKb` (⇒ `Sep` of the depths
  `(b, b', c', c)` by `robust4`) and `RobXba` (`B' < 0` puts `z_b ≤ z ≤ z_a'` for `z = z_b' = z_c'`).
* `s > 0`: `k1x1_hasLexCellAt` (cycle `(d, b, a', b', c)`); `s < 0`: `k1x2_hasLexCellAt` (cycle `(a, c', b, a', c, d)`).
-/
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp
namespace C2

theorem robKb_of_not_sep {a a' b b' c c' d : ℝ³}
    (h : ¬ Sep ⟪b, b - d⟫ ⟪b', b - d⟫ ⟪c', b - d⟫ ⟪c, b - d⟫) : RobKb a a' b b' c c' d := by
  unfold RobKb
  have e0 : (test08 1 true true).depth (pts08 a a' b b' c c' d) =
      quad ⟪b, b - d⟫ ⟪c', b - d⟫ ⟪b', b - d⟫ ⟪c, b - d⟫ := by
    funext i; rcases zmod4_cases i with rfl | rfl | rfl | rfl <;> rfl
  rw [e0]; exact robust4 h

/-- The depth sign `B' = ⟪a - d, b - d⟫ ≥ 0` on (B2) and (B3) with `γ4 = 1`, in the `T` frame. -/
theorem k1_B_nonneg {a a' b b' c c' d : ℝ³} {α1 α4 β1 β6 : ℝ}
    (hp : b - d ≠ 0)
    (hc' : c' = d + α1 • (a - d) + β1 • (b - d)) (hb' : b' = d + α4 • (a - d) + (1 : ℝ) • (c - d))
    (ha' : a' = d + β6 • (b - d) + (1 : ℝ) • (c - d)) (hα4 : 0 < α4) (hβ6 : 0 < β6)
    (h : (¬ RobKb a a' b b' c c' d ∧ N2WST a' b b' c c' d) ∨
      (¬ RobKb a a' b b' c c' d ∧ RobXba a' b b' c' d ∧ ⟪c', b - d⟫ = ⟪b', b - d⟫)) :
    0 ≤ ⟪a - d, b - d⟫ := by
  have hP : 0 < ⟪b - d, b - d⟫ := real_inner_self_pos.2 hp
  have eB' : ⟪b', b - d⟫ = ⟪d, b - d⟫ + α4 * ⟪a - d, b - d⟫ + ⟪c - d, b - d⟫ := by
    rw [hb']; simp only [inner_add_left, real_inner_smul_left]; ring
  have eC : ⟪c, b - d⟫ = ⟪d, b - d⟫ + ⟪c - d, b - d⟫ := by rw [inner_sub_left]; ring
  have eA' : ⟪a', b - d⟫ = ⟪d, b - d⟫ + β6 * ⟪b - d, b - d⟫ + ⟪c - d, b - d⟫ := by
    rw [ha']; simp only [inner_add_left, real_inner_smul_left]; ring
  have eB : ⟪b, b - d⟫ = ⟪d, b - d⟫ + ⟪b - d, b - d⟫ := by
    nth_rewrite 1 [show b = d + (b - d) by abel]; rw [inner_add_left]
  rcases h with ⟨-, h2, h3, h4, -⟩ | ⟨hK, hX, hE⟩
  · by_contra hneg
    have := mul_neg_of_pos_of_neg hα4 (not_le.1 hneg)
    linarith
  · by_contra hneg
    have hneg' := not_le.1 hneg
    have hm := mul_neg_of_pos_of_neg hα4 hneg'
    have hsep : Sep ⟪b, b - d⟫ ⟪b', b - d⟫ ⟪c', b - d⟫ ⟪c, b - d⟫ := by
      by_contra hn; exact hK (robKb_of_not_sep hn)
    apply hX
    unfold Sep at hsep ⊢
    rw [← hE]
    rw [← hE] at hsep
    rcases hsep with h | h
    · simp only [max_le_iff, le_min_iff] at h; linarith [h.1.2, h.2.2]
    · right
      simp only [max_le_iff, le_min_iff] at h ⊢
      refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith [h.1.1, h.1.2, h.2.1, h.2.2, mul_pos hβ6 hP]
end C2
end Type08Sp
end Minimality
