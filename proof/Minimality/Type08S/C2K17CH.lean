module

public import Minimality.Type08S.C2K17CG

@[expose] public section


/-!
# K17C / P3H: cell S3.3 (`γ6 > 1`, `ζ_b > 0`) at `a - d`.
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

theorem k17c_small {ζ L γ β6 : ℝ} (hζ : 0 < ζ) (hγ : 0 < γ) (hb : 0 < β6) :
    ∃ ε : ℝ, 0 < ε ∧ ε * (1 + β6) ≤ γ ∧ ε * |L| ≤ ζ := by
  refine ⟨min (γ / (1 + β6)) (ζ / (|L| + 1)), lt_min (by positivity) (by positivity), ?_, ?_⟩
  · calc min (γ / (1 + β6)) (ζ / (|L| + 1)) * (1 + β6) ≤ γ / (1 + β6) * (1 + β6) :=
          mul_le_mul_of_nonneg_right (min_le_left _ _) (by positivity)
      _ = γ := by field_simp
  · have hL := abs_nonneg L
    calc min (γ / (1 + β6)) (ζ / (|L| + 1)) * |L| ≤ ζ / (|L| + 1) * |L| :=
          mul_le_mul_of_nonneg_right (min_le_right _ _) hL
      _ ≤ ζ := by
          rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
          nlinarith

set_option maxHeartbeats 1600000 in
/-- **S3.3**: `α1 ≥ 1`, `β1 = 1`, `⟪a-d,b-d⟫ = 0`, `γ6 > 1`, `ζ_b = (β6-1) qq + γ6 qr > 0`. -/
theorem k17c_s33_hasLexCell {a a' b b' c c' d : ℝ³} {α1 β6 γ6 : ℝ}
    (hdet : det3 (a - d) (b - d) (c - d) ≠ 0)
    (hc' : c' = d + α1 • (a - d) + (1 : ℝ) • (b - d)) (hb' : b' = d + α1 • (a - d) + (1 : ℝ) • (c - d))
    (ha' : a' = d + β6 • (b - d) + γ6 • (c - d))
    (hα1 : 1 ≤ α1) (hβ6 : 0 < β6) (hγ6 : 0 < γ6) (h3 : 1 < β6 + γ6) (hγ61 : 1 < γ6)
    (hM : K6sM a a' b b' c c' d) (hm0 : ⟪a - d, b - d⟫ = 0)
    (hzb : 0 < (β6 - 1) * ⟪b - d, b - d⟫ + γ6 * ⟪b - d, c - d⟫) :
    HasLexCell (V8 a a' b b' c c' d) := by
  obtain ⟨hpr, hpp, hqq, hrr, -, -⟩ := k17c_gram hdet hc' hb' hM hm0
  obtain ⟨ε, hε, hε1, hε2⟩ := k17c_small (L := (β6 - 1) * ⟪b - d, c - d⟫ + γ6 * ⟪c - d, c - d⟫) hzb hγ6 hβ6
  have hL := le_abs_self ((β6 - 1) * ⟪b - d, c - d⟫ + γ6 * ⟪c - d, c - d⟫)
  have hLa := abs_nonneg ((β6 - 1) * ⟪b - d, c - d⟫ + γ6 * ⟪c - d, c - d⟫)
  refine k17c_A_cell hdet hc' hb' ha' hα1 hβ6 hγ6 h3 hM hm0 (u1 := 1) (u2 := 0) (t1 := 0) (t2 := -ε)
    (by simpa using hε.ne') ?_ ?_
  · intro lam h0 h1
    have p1 : 0 < lam * ε := mul_pos h0 hε
    have p2 : 0 < (1 - lam) * ε * (1 + β6) := mul_pos (mul_pos (sub_pos.2 h1) hε) (by linarith)
    refine ⟨by simp, by simp; nlinarith, by simp; nlinarith [mul_pos hβ6 p1], by simp; nlinarith⟩
  · intro lam h0 h1
    right
    have h4 : lam * ε * ((β6 - 1) * ⟪b - d, c - d⟫ + γ6 * ⟪c - d, c - d⟫) ≤
        lam * ε * |(β6 - 1) * ⟪b - d, c - d⟫ + γ6 * ⟪c - d, c - d⟫| :=
      mul_le_mul_of_nonneg_left hL (by positivity)
    have h5 : lam * ε * |(β6 - 1) * ⟪b - d, c - d⟫ + γ6 * ⟪c - d, c - d⟫| ≤
        ε * |(β6 - 1) * ⟪b - d, c - d⟫ + γ6 * ⟪c - d, c - d⟫| := by
      nlinarith [mul_nonneg (mul_nonneg (sub_pos.2 h1).le hε.le) hLa]
    nlinarith

end C2
end Type08Sp
end Minimality
