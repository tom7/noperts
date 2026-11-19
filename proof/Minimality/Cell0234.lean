module

public import Minimality.Type24Z0
public import Minimality.Cell0435
public import Minimality.RimCellClosed

@[expose] public section

set_option autoImplicit true
set_option relaxedAutoImplicit true
open scoped RealInnerProductSpace

namespace Minimality.T24.Cell0234
open Minimality Minimality.H21 Minimality.T24.SAT Minimality.RimCell

/-- Up facets of the cell 0234 (`025`, `0345`, `235` = C, D, G). -/
def U0234 : Finset (Fin 9) := {2, 3, 6}
/-- Down facets of the cell 0234. -/
def Dn0234 : Finset (Fin 9) := {0, 1, 4, 5, 7, 8}
/-- Up facets of the mirror cell 0536 (`046`, `0345`, `346` = E, D, I). -/
def U0536 : Finset (Fin 9) := {3, 4, 8}
/-- Down facets of the mirror cell 0536. -/
def Dn0536 : Finset (Fin 9) := {0, 1, 2, 5, 6, 7}

/-- Cycle of the cell 0234. -/
def c0234 : ZMod 4 → Fin 7 := ![0, 2, 3, 4]
/-- Cycle of the cell 0536. -/
def c0536 : ZMod 4 → Fin 7 := ![0, 6, 3, 5]

theorem cyc0234 : S0xCycUD s0x_S24 c0234 U0234 Dn0234 := by decide
theorem cyc0536 : S0xCycUD s0x_S24 c0536 U0536 Dn0536 := by decide

private theorem inj0234 : Function.Injective c0234 := by
  intro i j h; fin_cases i <;> fin_cases j <;> first | rfl | exact absurd h (by decide)
private theorem inj0536 : Function.Injective c0536 := by
  intro i j h; fin_cases i <;> fin_cases j <;> first | rfl | exact absurd h (by decide)

/-- **Q4 on the cell 0234**: strict point `a`, closed-cell points `g, g'`, one negative and one positive
diagonal form of the cycle `0 2 3 4`. -/
theorem isRupert_of_cell0234 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (hx : Function.Injective x)
    {a g g' : ℝ³} (ha : CellAt F U0234 Dn0234 a) (hg : CellLe F U0234 Dn0234 g)
    (hg' : CellLe F U0234 Dn0234 g')
    (hn : ∃ p ∈ diagPairs, ⟪x (c0234 p.1) - x (c0234 p.2), g⟫ < 0)
    (hp : ∃ p ∈ diagPairs, 0 < ⟪x (c0234 p.1) - x (c0234 p.2), g'⟫) :
    IsRupert (Finset.univ.image x) :=
  isRupert_of_closedCell_q4 F hx inj0234 cyc0234 ha hg hg' hn hp

/-- **Lemma CW form on 0234**: one closed-cell point `g` with `x 2 · g < x 3 · g` and `x 0 · g < x 4 · g`
(`g = g'`). -/
theorem isRupert_q4_0234_of_cevian {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (hx : Function.Injective x) {a g : ℝ³} (ha : CellAt F U0234 Dn0234 a)
    (hg : CellLe F U0234 Dn0234 g) (h3 : ⟪x 2, g⟫ < ⟪x 3, g⟫) (h4 : ⟪x 0, g⟫ < ⟪x 4, g⟫) :
    IsRupert (Finset.univ.image x) :=
  isRupert_of_cell0234 F hx ha hg hg
    ⟨(0, 3), by decide, by simp only [c0234, Matrix.cons_val, inner_sub_left]; linarith⟩
    ⟨(2, 1), by decide, by simp only [c0234, Matrix.cons_val, inner_sub_left]; linarith⟩

/-- **Q4 on the mirror cell 0536** (cycle `0 6 3 5`). -/
theorem isRupert_of_cell0536 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (hx : Function.Injective x)
    {a g g' : ℝ³} (ha : CellAt F U0536 Dn0536 a) (hg : CellLe F U0536 Dn0536 g)
    (hg' : CellLe F U0536 Dn0536 g')
    (hn : ∃ p ∈ diagPairs, ⟪x (c0536 p.1) - x (c0536 p.2), g⟫ < 0)
    (hp : ∃ p ∈ diagPairs, 0 < ⟪x (c0536 p.1) - x (c0536 p.2), g'⟫) :
    IsRupert (Finset.univ.image x) :=
  isRupert_of_closedCell_q4 F hx inj0536 cyc0536 ha hg hg' hn hp

/-- **Lemma CW form on 0536**: `x 6 · g < x 3 · g` and `x 0 · g < x 5 · g`. -/
theorem isRupert_q4_0536_of_cevian {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (hx : Function.Injective x) {a g : ℝ³} (ha : CellAt F U0536 Dn0536 a)
    (hg : CellLe F U0536 Dn0536 g) (h3 : ⟪x 6, g⟫ < ⟪x 3, g⟫) (h4 : ⟪x 0, g⟫ < ⟪x 5, g⟫) :
    IsRupert (Finset.univ.image x) :=
  isRupert_of_cell0536 F hx ha hg hg
    ⟨(0, 3), by decide, by simp only [c0536, Matrix.cons_val, inner_sub_left]; linarith⟩
    ⟨(2, 1), by decide, by simp only [c0536, Matrix.cons_val, inner_sub_left]; linarith⟩

end Minimality.T24.Cell0234
