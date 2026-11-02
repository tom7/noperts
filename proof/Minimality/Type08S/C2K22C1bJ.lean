module

public import Minimality.Type08S.C2K22C1bF
public import Minimality.Type08S.C2K22C1bI

@[expose] public section


/-!
# K22C1b / J: `K22C1Left` closed (`k22c1b_close`)

After `k22c1b_edge` (edge-on cells), the leftover `K22C1bLeft` is closed by:
* `β1 = 1`, `qr = 0`: `q, r, p` pairwise orthogonal; the shape is the right prism along `r` over the triangle
  `(d, a, b)` (tops `c, b', a'` at heights `1, γ4, γ6`) plus the base point `c' = a + b - d` beyond the edge `a b`:
  `k20_prism3`, IsRupert;
* `β1 = 1`, `qr > 0`, `γ4 < 1`: face-on cell `F1` (`k22c1b_cellF1`);
* `β1 = 1 < γ4`, `qq ≤ γ4 qr` (so `qr > 0`), and `β1 < 1 ≤ γ4`, `⟪c-d, c-a'⟫ = 0` (so `qr = (1-γ6) rr > 0`):
  face-on cell `F2` (`k22c1b_cellF2`).
-/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.unusedVariables false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp
namespace C2

theorem k22c1b_close {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d)
    (h : K6t3LeftPc a a' b b' c c' d) (hL : K22C1Left a a' b b' c c' d) :
    HasLexCell (V8 a a' b b' c c' d) ∨ IsRupert (V8 a a' b b' c c' d) := by
  rcases k22c1b_edge W h hL with h1 | hR
  · exact Or.inl h1
  obtain ⟨hpq, hpr, β1, γ4, γ6, hdet, hc', hb', ha', hβ1, hγ4, hγ6, hγ61, hfr, hcase⟩ := hR
  have hq0 : b - d ≠ 0 := by intro h0; apply hdet; rw [h0]; simp [det3_expand]
  have hr0 : c - d ≠ 0 := by intro h0; apply hdet; rw [h0]; simp [det3_expand]
  have hqq : 0 < ⟪b - d, b - d⟫ := real_inner_self_pos.2 hq0
  have hrr : 0 < ⟪c - d, c - d⟫ := real_inner_self_pos.2 hr0
  rcases hcase with ⟨rfl, hqr, hg⟩ | ⟨hb1, hw0, hg⟩
  · rcases lt_or_eq_of_le hqr with hqr | hqr
    · rcases hg with hg | ⟨hg, hgq⟩
      · exact Or.inl (k22c1b_cellF1 hpq hpr hdet hc' hb' ha' hγ4 hg hγ6 hγ61 hqr)
      · exact Or.inl (k22c1b_cellF2 hpq hpr hdet hc' hb' ha' hβ1 le_rfl hg.le hγ6 hγ61 hqr)
    · -- the right prism along `r`
      right
      set P := a - d with hP
      set Q := b - d with hQ
      set R := c - d with hR
      have h1 : ⟪R, P⟫ = 0 := by rw [real_inner_comm]; exact hpr
      have h2 : ⟪R, Q⟫ = 0 := by rw [real_inner_comm]; exact hqr.symm
      have key := k20_prism3 d R P Q (β := 1) (γ := 1) (z0 := 1) (z1 := γ4) (z2 := γ6) h1 h2 hdet one_pos hγ4
        hγ6 (by norm_num)
      have q1 : d + P = a := by simp [P]
      have q2 : d + Q = b := by simp [Q]
      have q3 : d + ((1 : ℝ) • P + (1 : ℝ) • Q) = c' := by rw [hc']; module
      have q4 : d + (1 : ℝ) • R = c := by simp [R]
      have q5 : d + P + γ4 • R = b' := by rw [hb']; module
      have q6 : d + Q + γ6 • R = a' := by rw [ha']; module
      rw [q5, q6, q3, q4, q1, q2] at key
      convert key using 1
      ext x; simp only [V8, Finset.mem_insert, Finset.mem_singleton]; tauto
  · left
    have hqr : 0 < ⟪b - d, c - d⟫ := by
      have e : c - a' = (1 - γ6) • (c - d) - (b - d) := by rw [ha']; module
      rw [e, inner_sub_right, inner_smul_right, real_inner_comm (b - d) (c - d)] at hw0
      nlinarith [mul_pos (by linarith : (0:ℝ) < 1 - γ6) hrr]
    exact k22c1b_cellF2 hpq hpr hdet hc' hb' ha' hβ1 hb1.le hg hγ6 hγ61 hqr

end C2
end Type08Sp
end Minimality
