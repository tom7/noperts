module

public import Minimality.Type08S.G6Lem

@[expose] public section

set_option autoImplicit true
set_option relaxedAutoImplicit true

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

variable {e1 e2 e3 : ℝ³}

theorem ev_pos_lin (α β γ : ℝ) (h : 0 < α ∨ (α = 0 ∧ 0 < β)) :
    ∀ᶠ s : ℝ in atTop, 0 < α * s + β + γ / s := by
  rcases h with h | ⟨rfl, hb⟩
  · filter_upwards [eventually_ge_atTop (max 1 ((|β| + |γ| + 1) / α))] with s hs
    have h1 : 1 ≤ s := le_trans (le_max_left _ _) hs
    have h2 : (|β| + |γ| + 1) / α ≤ s := le_trans (le_max_right _ _) hs
    have h3 : |β| + |γ| + 1 ≤ α * s := by
      have := (div_le_iff₀ h).1 h2
      linarith [mul_comm α s]
    have h4 : |γ / s| ≤ |γ| := by
      rw [abs_div, abs_of_pos (by linarith : 0 < s)]
      exact div_le_self (abs_nonneg _) h1
    have := neg_abs_le β
    have := neg_abs_le (γ / s)
    nlinarith [abs_nonneg γ]
  · filter_upwards [eventually_gt_atTop (max 1 (|γ| / β))] with s hs
    have h1 : 1 < s := lt_of_le_of_lt (le_max_left _ _) hs
    have h2 : |γ| / β < s := lt_of_le_of_lt (le_max_right _ _) hs
    have h3 : |γ| < s * β := by rwa [div_lt_iff₀ hb] at h2
    have h4 : |γ / s| < β := by
      rw [abs_div, abs_of_pos (by linarith : 0 < s), div_lt_iff₀ (by linarith)]
      linarith
    have := neg_abs_le (γ / s)
    nlinarith

theorem ev_of_eq {P : ℝ → ℝ} (α β γ : ℝ) (h : 0 < α ∨ (α = 0 ∧ 0 < β))
    (he : ∀ s : ℝ, 0 < s → P s = α * s + β + γ / s) : ∀ᶠ s : ℝ in atTop, 0 < P s := by
  filter_upwards [ev_pos_lin α β γ h, eventually_gt_atTop 0] with s h1 h2
  rw [he s h2]; exact h1

end Type08Sp
end Minimality
