module

public import Minimality.Type08S.P2CR5

@[expose] public section

set_option relaxedAutoImplicit true

/-!
# P3a core, part 6: classification of the rim.
-/

set_option autoImplicit true
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

variable {e1 e2 e3 : ℝ³}

theorem inc_ne : ∀ a b c : ZMod 4, inc a b c → a ≠ b ∧ a ≠ c ∧ b ≠ c := by decide

section classify2
variable {O : ℝ³} {κ L zf Xr Yr zr Xg Yg zg κv : ℝ}

/-- The rim (labels `τ`, ZMod k') of the closing has exactly four corners. -/
theorem rim_k_eq_4 (hF : Fr e1 e2 e3) (hκv : κv ≠ 0) (hL : 0 < L) (hYr : 0 < Yr) (hYg : 0 < Yg)
    (hcr : 0 < (Xg - Xr) * (-Yr) - (Yg - Yr) * (L - Xr)) (hcg : 0 < Yg * Xr - Xg * Yr)
    {k' : ℕ} [NeZero k'] (hk3 : 3 ≤ k') (τ : ZMod k' → ZMod 4)
    (hcyc : ∀ i j : ZMod k', j ≠ i → j ≠ i + 1 → 0 < det3
      (Qg e1 e2 e3 O κ L zf Xr Yr zr Xg Yg zg (τ (i + 1)) - Qg e1 e2 e3 O κ L zf Xr Yr zr Xg Yg zg (τ i))
      (Qg e1 e2 e3 O κ L zf Xr Yr zr Xg Yg zg (τ j) - Qg e1 e2 e3 O κ L zf Xr Yr zr Xg Yg zg (τ i)) (κv • e3))
    (hleft : ∀ (i : ZMod k') (a : ZMod 4), 0 ≤ det3
      (Qg e1 e2 e3 O κ L zf Xr Yr zr Xg Yg zg (τ (i + 1)) - Qg e1 e2 e3 O κ L zf Xr Yr zr Xg Yg zg (τ i))
      (Qg e1 e2 e3 O κ L zf Xr Yr zr Xg Yg zg a - Qg e1 e2 e3 O κ L zf Xr Yr zr Xg Yg zg (τ i)) (κv • e3)) :
    k' = 4 := by
  rcases lt_or_gt_of_ne hκv with hn | hp
  · obtain ⟨H1, H2⟩ := rim_inc_neg hF hn hL hYr hYg hcr hcg τ hcyc hleft
    have hinj := inj_of_H1 hk3 τ (fun i j hi hj => by
      obtain ⟨h1, h2, h3⟩ := inc_ne _ _ _ (H1 i j hi hj)
      exact ⟨h2, h1⟩)
    have h4 := k_le_four τ hinj
    obtain rfl | rfl : k' = 3 ∨ k' = 4 := by omega
    · exact (comb3' τ H1 H2).elim
    · rfl
  · obtain ⟨H1, H2⟩ := rim_inc_pos hF hp hL hYr hYg hcr hcg τ hcyc hleft
    have hinj := inj_of_H1 hk3 τ (fun i j hi hj => by
      obtain ⟨h1, h2, h3⟩ := inc_ne _ _ _ (H1 i j hi hj)
      exact ⟨h1, h2⟩)
    have h4 := k_le_four τ hinj
    obtain rfl | rfl : k' = 3 ∨ k' = 4 := by omega
    · exact (comb3 τ H1 H2).elim
    · rfl

/-- With four corners the rim is the screen quadrilateral, in the orientation of `κv`. -/
theorem rim_orient4 (hF : Fr e1 e2 e3) (hκv : κv ≠ 0) (hL : 0 < L) (hYr : 0 < Yr) (hYg : 0 < Yg)
    (hcr : 0 < (Xg - Xr) * (-Yr) - (Yg - Yr) * (L - Xr)) (hcg : 0 < Yg * Xr - Xg * Yr)
    (τ : ZMod 4 → ZMod 4)
    (hcyc : ∀ i j : ZMod 4, j ≠ i → j ≠ i + 1 → 0 < det3
      (Qg e1 e2 e3 O κ L zf Xr Yr zr Xg Yg zg (τ (i + 1)) - Qg e1 e2 e3 O κ L zf Xr Yr zr Xg Yg zg (τ i))
      (Qg e1 e2 e3 O κ L zf Xr Yr zr Xg Yg zg (τ j) - Qg e1 e2 e3 O κ L zf Xr Yr zr Xg Yg zg (τ i)) (κv • e3))
    (hleft : ∀ (i : ZMod 4) (a : ZMod 4), 0 ≤ det3
      (Qg e1 e2 e3 O κ L zf Xr Yr zr Xg Yg zg (τ (i + 1)) - Qg e1 e2 e3 O κ L zf Xr Yr zr Xg Yg zg (τ i))
      (Qg e1 e2 e3 O κ L zf Xr Yr zr Xg Yg zg a - Qg e1 e2 e3 O κ L zf Xr Yr zr Xg Yg zg (τ i)) (κv • e3)) :
    (0 < κv → ∃ c : ZMod 4, ∀ i, τ i = c + i) ∧ (κv < 0 → ∃ c : ZMod 4, ∀ i, τ i = c - i) := by
  constructor
  · intro hp
    obtain ⟨H1, H2⟩ := rim_inc_pos hF hp hL hYr hYg hcr hcg τ hcyc hleft
    exact comb4 τ H1 H2
  · intro hn
    obtain ⟨H1, H2⟩ := rim_inc_neg hF hn hL hYr hYg hcr hcg τ hcyc hleft
    exact comb4' τ H1 H2

end classify2

end Type08Sp
end Minimality

#print axioms Minimality.Type08Sp.rim_k_eq_4
#print axioms Minimality.Type08Sp.rim_orient4
