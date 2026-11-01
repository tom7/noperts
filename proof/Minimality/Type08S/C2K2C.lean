module

public import Minimality.Type08S.C2K2B

@[expose] public section

/-!
# C2 / K2C: the items.  `P3Tpii` and `L2 ∧ γ4 = 1` have a lex cell (the 5-cycle `(a, d, b, a', b')` at `a - d`)

* `gale_coords_gen`: `gale_coords2` for `a' = d + β6 (b - d) + γ6 (c - d)` (general `γ6`, `α1`).
* `p3Tpii_hasLexCell`: `Norm08 → P3Tpii → HasLexCell (V8 …)`.  `T'`, `B' = 0`, `QacTop` off the level face give
  `D_c > 0`, `γ4 = 1`; `β1 < 1` from `κ_a > 0`, `κ_b > 0`.
* `l2K_hasLexCell`: `Norm08 → IsT → TouchT → det3 (c - b') (a - d) (b - d) = 0 → HasLexCell (V8 …)`
  (the `L2` item of `S4TR` on `γ4 = 1`: `TouchT` gives `D_c > 0` and, with `γ4 = 1`, `B' = 0`).
-/
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp
namespace C2

theorem gale_coords_gen {a a' b b' c c' d : ℝ³} (G : GaleData a a' b b' c c')
    {α1 α4 β1 γ4 β6 γ6 : ℝ} (hdet : det3 (a - d) (b - d) (c - d) ≠ 0)
    (hc' : c' = d + α1 • (a - d) + β1 • (b - d)) (hb' : b' = d + α4 • (a - d) + γ4 • (c - d))
    (ha' : a' = d + β6 • (b - d) + γ6 • (c - d)) (hs : 1 - β6 - γ6 ≠ 0) :
    ∃ μ : ℝ, galeD G.l G.m a a' = μ * (α4 - α4 * β1 - α1 + α1 * γ4) ∧
      galeD G.l G.m b b' = μ * (β6 * (α1 - 1) + β1 * (1 - γ6)) := by
  have dep : ∀ {l : ℝ³ → ℝ}, IsDep a a' b b' c c' l →
      l a = -α4 * l b' - α1 * l c' ∧ l b = -β6 * l a' - β1 * l c' ∧ l c = -γ6 * l a' - γ4 * l b' ∧
      (1 - β6 - γ6) * l a' + (1 - α4 - γ4) * l b' + (1 - α1 - β1) * l c' = 0 := by
    intro l hl
    have h0 : (l a + α4 * l b' + α1 * l c') • (a - d) + (l b + β6 * l a' + β1 * l c') • (b - d) +
        (l c + γ6 * l a' + γ4 * l b') • (c - d) = 0 := by
      have hv := hl.vsum
      have hs := hl.sum
      have e : l a • (a - d) + l a' • (a' - d) + l b • (b - d) + l b' • (b' - d) + l c • (c - d) +
          l c' • (c' - d) = 0 := by
        have : l a • (a - d) + l a' • (a' - d) + l b • (b - d) + l b' • (b' - d) + l c • (c - d) +
          l c' • (c' - d) = (l a • a + l a' • a' + l b • b + l b' • b' + l c • c + l c' • c') -
            (l a + l a' + l b + l b' + l c + l c') • d := by
          simp only [smul_sub, add_smul]; abel
        rw [this, hv, hs]; simp
      have ha'd : a' - d = β6 • (b - d) + γ6 • (c - d) := by rw [ha']; abel
      have hb'd : b' - d = α4 • (a - d) + γ4 • (c - d) := by rw [hb']; abel
      have hc'd : c' - d = α1 • (a - d) + β1 • (b - d) := by rw [hc']; abel
      rw [ha'd, hb'd, hc'd] at e
      rw [← e]
      module
    obtain ⟨h1, h2, h3⟩ := coef_zero hdet h0
    refine ⟨by linarith, by linarith, by linarith, ?_⟩
    have := hl.sum
    nlinarith [this, h1, h2, h3]
  obtain ⟨la, lb, lc, ls⟩ := dep G.hl
  obtain ⟨ma, mb, mc, ms⟩ := dep G.hm
  set Dbc := G.l b' * G.m c' - G.m b' * G.l c' with hDbc
  set Dca := G.l c' * G.m a' - G.m c' * G.l a' with hDca
  set Dab := G.l a' * G.m b' - G.m a' * G.l b' with hDab
  have e1 : Dca * (1 - β6 - γ6) = Dbc * (1 - α4 - γ4) := by
    rw [hDca, hDbc]
    linear_combination (G.l c') * ms - (G.m c') * ls
  have e2 : Dab * (1 - β6 - γ6) = Dbc * (1 - α1 - β1) := by
    rw [hDab, hDbc]
    linear_combination (-(G.l b')) * ms + (G.m b') * ls
  obtain ⟨μ, hμ⟩ : ∃ μ, μ * (1 - β6 - γ6) = Dbc := ⟨Dbc / (1 - β6 - γ6), div_mul_cancel₀ _ hs⟩
  have hca : Dca = μ * (1 - α4 - γ4) :=
    mul_right_cancel₀ hs (by linear_combination e1 - (1 - α4 - γ4) * hμ)
  have hab : Dab = μ * (1 - α1 - β1) :=
    mul_right_cancel₀ hs (by linear_combination e2 - (1 - α1 - β1) * hμ)
  refine ⟨μ, ?_, ?_⟩
  · unfold galeD
    rw [la, ma]
    linear_combination α4 * hab - α1 * hca
  · unfold galeD
    rw [lb, mb]
    linear_combination (β1) * hμ.symm - β6 * hab

end C2
end Type08Sp
end Minimality
