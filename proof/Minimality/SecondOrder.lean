module

public import Minimality.FirstOrder

@[expose] public section

/-!
# Second-order lexicographic passages

Theorem T2(a), analytic half: along the Cayley curve
`R(s) = cayley ((s/2)•ω + (s²/2)•γ)` with screen offset `s•Pτ + (s²/2)•Pβ`, a vertex `v` passes a shadow edge
`⟪n, y⟫ ≤ h` if it is slack, or tight with `⟪n, screenVel ω τ v⟫ < 0`, or tight with first-order term `0` and
`⟪n, secondVel ω γ β v⟫ < 0`.  If every (vertex, edge) pair passes, `V` is Rupert (`isRupert_of_secondOrderLex`).
-/

namespace Minimality

open scoped RealInnerProductSpace Matrix Topology
open Filter

theorem cayley_apply (c x : ℝ³) :
    (cayley c).toEuclideanLin x = x + (2 * (cayleyDen c)⁻¹) •
      ((crossMatrix c).toEuclideanLin x + (crossMatrix c).toEuclideanLin ((crossMatrix c).toEuclideanLin x)) := by
  have hd := (cayleyDen_pos c).ne'
  ext i; fin_cases i <;> simp [cayley, crossMatrix, Matrix.toLpLin_apply, dotProduct,
    Fin.sum_univ_three] <;> field_simp <;> simp only [cayleyDen] <;> ring

end Minimality
