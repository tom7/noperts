module

public import Minimality.Type08S.P2LXcore

@[expose] public section

set_option relaxedAutoImplicit true

/-!
# Lemma LX (ii), package K: the 15 lexicographic convexity tests of the pentagon `(x', f, r, g, x)`
-/

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.unusedVariables false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

/-- The pentagon `(x', f, r, g, x)` in frame coordinates. -/
def pent (L zp zx zf Xr Yr zr Xg Yg zg : ℝ) : ZMod 5 → ℝ × ℝ × ℝ :=
  five (0, 0, zp) (L, 0, zf) (Xr, Yr, zr) (Xg, Yg, zg) (0, 0, zx)

theorem lx_cyc {σ S L zp zx zf Xr Yr zr Xg Yg zg : ℝ}
    (hL : 0 < L) (hzx : 0 < σ * (zx - zp))
    (hcr : 0 < (Xg - Xr) * (-Yr) - (Yg - Yr) * (L - Xr)) (hYr : 0 < Yr) (hYg : 0 < Yg)
    (hcg : 0 < Yg * Xr - Xg * Yr) (hs : 0 < Xg + S * Yg) (hs2 : 0 < Xr + S * Yr) :
    ∀ i j : ZMod 5, j ≠ i → j ≠ i + 1 →
      LT 1 (σ * S) (-σ) (pent L zp zx zf Xr Yr zr Xg Yg zg i) (pent L zp zx zf Xr Yr zr Xg Yg zg (i + 1))
        (pent L zp zx zf Xr Yr zr Xg Yg zg j) := by
  obtain ⟨s0, s1, s2, s3, s4⟩ := z5_add_one
  have p1 := mul_pos hL hYr
  have p2 := mul_pos hL hYg
  have q1 := mul_pos hzx hL
  have q2 := mul_pos hzx hs
  have q3 := mul_pos hzx hs2
  intro i j h1 h2
  rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
    rcases z5_cases j with rfl | rfl | rfl | rfl | rfl <;>
    first
    | exact absurd rfl h1
    | exact (h2 (by decide)).elim
    | (simp only [s0, s1, s2, s3, s4, pent, five_0, five_1, five_2, five_3, five_4, LT, ori, fo]
       first | (left; nlinarith) | (right; exact ⟨by ring, by nlinarith⟩))

end Type08Sp
end Minimality
