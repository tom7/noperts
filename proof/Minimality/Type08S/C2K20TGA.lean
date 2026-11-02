module

public import Minimality.Type08S.C2K20TH2
public import Minimality.Type08S.G3p
public import Minimality.OctAxis

@[expose] public section


set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp
namespace C2

/-- **Gale constraint of the tie slice**: with `α1 = γ6 = 1` the Gale brackets are `κ_a = μ E`, `κ_b = 0`,
`[b,c] = -μ β1 (α4 + γ4 - 1)`; `hκa ≥ 0`, `hU ≤ 0` and `[b,c] ≠ 0` give `E ≥ 0`, `E = α4 - α4 β1 - 1 + γ4`. -/
theorem k20t_E_nonneg {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) {α4 β1 γ4 β6 : ℝ}
    (hdet : det3 (a - d) (b - d) (c - d) ≠ 0)
    (hc' : c' = d + (1 : ℝ) • (a - d) + β1 • (b - d)) (hb' : b' = d + α4 • (a - d) + γ4 • (c - d))
    (ha' : a' = d + β6 • (b - d) + (1 : ℝ) • (c - d)) (hβ1 : 0 < β1) (hαγ : 1 < α4 + γ4) :
    0 ≤ α4 - α4 * β1 - 1 + γ4 := by
  have hνc : (1 : ℝ) - 1 - β1 ≠ 0 := by intro h; linarith
  obtain ⟨μ, hμa, -, -, hμU⟩ := gale_nf08 W.G (p := 1) (q := β1) (r := α4) (s := γ4) (t := β6) (u := 1)
    hdet hc' hb' ha' hνc
  have hbc : galeD W.G.l W.G.m b c ≠ 0 := galeD_ne_zero W.F.perm₁₂.perm₂₃ W.G.perm₁₂.perm₂₃
  have hU := W.hU
  have hκa := W.hκa
  rw [hμU] at hU hbc
  rw [hμa] at hκa
  simp only [gWU, gWa, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Matrix.head_cons] at hU hbc hκa
  have hneg : β1 * (1 - α4 - γ4) < 0 := mul_neg_of_pos_of_neg hβ1 (by linarith)
  have hμ0 : μ ≠ 0 := by
    intro h; apply hbc; rw [h]; ring
  have hμpos : 0 < μ := by
    rcases lt_or_gt_of_ne hμ0 with h | h
    · exfalso
      have : 0 < μ * (β1 * (1 - α4 - γ4)) := mul_pos_of_neg_of_neg h hneg
      nlinarith
    · exact h
  have : 0 ≤ μ * (α4 - α4 * β1 - 1 + γ4) := by nlinarith
  exact nonneg_of_mul_nonneg_right this hμpos

end C2
end Type08Sp
end Minimality
