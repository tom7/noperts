module

public import Minimality.Type08S.C2K17B2A
public import Minimality.Type08S.C2K17B2B
public import Minimality.Type08S.C2K17B2E
public import Minimality.Type08S.C2K17B2G
public import Minimality.Type08S.C2K17B2H

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

/-- K6M2 rule 1 (view `L46`) literal package. -/
def K17b2P1 (a a' b b' c c' d : ℝ³) (α1 β1 β6 γ6 : ℝ) : Prop :=
  (α1 - 1) * (β1 - 1) * (β6 + γ6 - 1) < α1 + β1 - 1 ∧
  0 < ⟪a - b', (-α1) • (a - d) - (β1 - 1) • (a' - d)⟫ ∧
  0 < ⟪a - a', (-α1) • (a - d) - (β1 - 1) • (a' - d)⟫ ∧
  0 < ⟪c' - a', (-α1) • (a - d) - (β1 - 1) • (a' - d)⟫

/-- K6M2 rule 2 (view `L03`) literal package. -/
def K17b2P2 (a a' b b' c c' d : ℝ³) (α1 β1 β6 γ6 : ℝ) : Prop :=
  α1 * β1 < (α1 - 1) * (β1 - 1) * (β6 + γ6) + γ6 * (α1 + β1 - 1) ∧
  0 < ⟪b - a', c' - a⟫ ∧ 0 < ⟪a' - b', c' - a⟫ ∧ 0 < ⟪c' - b, c' - a⟫

/-- K6M2 rule 5 (view `d - b'`, cycle `(a, b', c, a', c')`) literal package. -/
def K17b2P5 (a a' b b' c c' d : ℝ³) : Prop :=
  0 < ⟪a - b', d - b'⟫ ∧ 0 < ⟪c' - a, d - b'⟫ ∧ 0 < ⟪c' - a', d - b'⟫ ∧ 0 < ⟪a' - c, d - b'⟫ ∧ 0 < ⟪c - b', d - b'⟫

/-- K6M2 rule 4 (view `d - b'`, cycle `(a, d, c, a', c')`) literal package. -/
def K17b2P4 (a a' b b' c c' d : ℝ³) : Prop :=
  0 < ⟪c' - a', d - b'⟫ ∧ 0 < ⟪a - c', d - b'⟫ ∧ 0 < ⟪d - a, d - b'⟫ ∧ 0 < ⟪d - c, d - b'⟫

/-- K6M2 rule 13 (view `b' - m(d,c)`, cycle `(a, b', c, a', c')`) literal package. -/
def K17b2P13 (a a' b b' c c' d : ℝ³) : Prop :=
  0 < ⟪b' - c, b' - (1 / 2 : ℝ) • (d + c)⟫ ∧ 0 < ⟪c - a', b' - (1 / 2 : ℝ) • (d + c)⟫ ∧
  0 < ⟪a - c', b' - (1 / 2 : ℝ) • (d + c)⟫ ∧ 0 < ⟪b' - a, b' - (1 / 2 : ℝ) • (d + c)⟫

/-- K6M2 rule 3 (view `c' - m(d,b)`, cycle `(a, d, b, a', b')`) literal package. -/
def K17b2P3 (a a' b b' c c' d : ℝ³) : Prop :=
  0 < ⟪a - d, c' - (1 / 2 : ℝ) • (d + b)⟫ ∧ 0 < ⟪b' - a, c' - (1 / 2 : ℝ) • (d + b)⟫ ∧
  0 < ⟪a' - b', c' - (1 / 2 : ℝ) • (d + b)⟫ ∧ 0 < ⟪a' - b, c' - (1 / 2 : ℝ) • (d + b)⟫

theorem k17b2_P1w {a a' b b' c c' d : ℝ³} {α1 β1 β6 γ6 : ℝ}
    (hdet : det3 (a - d) (b - d) (c - d) ≠ 0)
    (hc' : c' = d + α1 • (a - d) + β1 • (b - d)) (hb' : b' = d + α1 • (a - d) + β1 • (c - d))
    (ha' : a' = d + β6 • (b - d) + γ6 • (c - d))
    (hα1 : 1 < α1) (hβ1 : 1 < β1) (hβ6 : 1 < β6) (hγ6 : 1 < γ6) (h : K17b2P1 a a' b b' c c' d α1 β1 β6 γ6) :
    HasLexCell (V8 a a' b b' c c' d) := by
  obtain ⟨h0, h1, h2, h3⟩ := h
  exact k17b2_r1 hdet hc' hb' ha' hα1 hβ1 hβ6 hγ6 h0 h1 h2 h3

theorem k17b2_P2w {a a' b b' c c' d : ℝ³} {α1 β1 β6 γ6 : ℝ}
    (hdet : det3 (a - d) (b - d) (c - d) ≠ 0)
    (hc' : c' = d + α1 • (a - d) + β1 • (b - d)) (hb' : b' = d + α1 • (a - d) + β1 • (c - d))
    (ha' : a' = d + β6 • (b - d) + γ6 • (c - d))
    (hα1 : 1 < α1) (hβ1 : 1 < β1) (hβ6 : 1 < β6) (hγ6 : 1 < γ6) (h : K17b2P2 a a' b b' c c' d α1 β1 β6 γ6) :
    HasLexCell (V8 a a' b b' c c' d) := by
  obtain ⟨h0, h1, h2, h3⟩ := h
  exact k17b2_r2 hdet hc' hb' ha' hα1 hβ1 hβ6 hγ6 h0 h1 h2 h3

theorem k17b2_P5w {a a' b b' c c' d : ℝ³} {α1 β1 β6 γ6 : ℝ}
    (hdet : det3 (a - d) (b - d) (c - d) ≠ 0)
    (hc' : c' = d + α1 • (a - d) + β1 • (b - d)) (hb' : b' = d + α1 • (a - d) + β1 • (c - d))
    (ha' : a' = d + β6 • (b - d) + γ6 • (c - d))
    (hα1 : 1 < α1) (hβ1 : 1 < β1) (hβ6 : 1 < β6) (hγ6 : 1 < γ6) (h : K17b2P5 a a' b b' c c' d) :
    HasLexCell (V8 a a' b b' c c' d) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  exact k17b2_r5 hdet hc' hb' ha' hα1 hβ1 hβ6 hγ6 h1 h2 h3 h4 h5

theorem k17b2_P4w {a a' b b' c c' d : ℝ³} {α1 β1 β6 γ6 : ℝ}
    (hdet : det3 (a - d) (b - d) (c - d) ≠ 0)
    (hc' : c' = d + α1 • (a - d) + β1 • (b - d)) (hb' : b' = d + α1 • (a - d) + β1 • (c - d))
    (ha' : a' = d + β6 • (b - d) + γ6 • (c - d))
    (hα1 : 1 < α1) (hβ1 : 1 < β1) (hβ6 : 1 < β6) (hγ6 : 1 < γ6) (h : K17b2P4 a a' b b' c c' d) :
    HasLexCell (V8 a a' b b' c c' d) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  exact k17b2_r4 hdet hc' hb' ha' hα1 hβ1 hβ6 hγ6 h1 h2 h3 h4

theorem k17b2_P13w {a a' b b' c c' d : ℝ³} {α1 β1 β6 γ6 : ℝ}
    (hdet : det3 (a - d) (b - d) (c - d) ≠ 0)
    (hc' : c' = d + α1 • (a - d) + β1 • (b - d)) (hb' : b' = d + α1 • (a - d) + β1 • (c - d))
    (ha' : a' = d + β6 • (b - d) + γ6 • (c - d))
    (hα1 : 1 < α1) (hβ1 : 1 < β1) (hβ6 : 1 < β6) (hγ6 : 1 < γ6) (h : K17b2P13 a a' b b' c c' d) :
    HasLexCell (V8 a a' b b' c c' d) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  exact k17b2_r13 hdet hc' hb' ha' hα1 hβ1 hβ6 hγ6 h1 h2 h3 h4

theorem k17b2_P3w {a a' b b' c c' d : ℝ³} {α1 β1 β6 γ6 : ℝ}
    (hdet : det3 (a - d) (b - d) (c - d) ≠ 0)
    (hc' : c' = d + α1 • (a - d) + β1 • (b - d)) (hb' : b' = d + α1 • (a - d) + β1 • (c - d))
    (ha' : a' = d + β6 • (b - d) + γ6 • (c - d))
    (hα1 : 1 < α1) (hβ1 : 1 < β1) (hβ6 : 1 < β6) (hγ6 : 1 < γ6) (h : K17b2P3 a a' b b' c c' d) :
    HasLexCell (V8 a a' b b' c c' d) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  exact k17b2_r3 hdet hc' hb' ha' hα1 hβ1 hβ6 hγ6 h1 h2 h3 h4

/-- Leftover of the K17B2 part of L2: `K17bL2Left` and none of the proved K6M2 rules 1, 2, 5, 4, 13, 3 fires. -/
def K17b2L2Left (a a' b b' c c' d : ℝ³) (α1 β1 β6 γ6 : ℝ) : Prop :=
  K17bL2Left a a' b b' c c' d α1 β1 β6 γ6 ∧ ¬ K17b2P1 a a' b b' c c' d α1 β1 β6 γ6 ∧
    ¬ K17b2P2 a a' b b' c c' d α1 β1 β6 γ6 ∧ ¬ K17b2P5 a a' b b' c c' d ∧ ¬ K17b2P4 a a' b b' c c' d ∧
    ¬ K17b2P13 a a' b b' c c' d ∧ ¬ K17b2P3 a a' b b' c c' d

theorem k17b2_l2 {a a' b b' c c' d : ℝ³} {α1 β1 β6 γ6 : ℝ}
    (hdet : det3 (a - d) (b - d) (c - d) ≠ 0)
    (hc' : c' = d + α1 • (a - d) + β1 • (b - d)) (hb' : b' = d + α1 • (a - d) + β1 • (c - d))
    (ha' : a' = d + β6 • (b - d) + γ6 • (c - d))
    (hα1 : 1 < α1) (hβ1 : 1 < β1) (hβ6 : 1 < β6) (hγ6 : 1 < γ6) (hσ : β1 < β6 + γ6)
    (hM : K6sM a a' b b' c c' d) (hrel : K16Rel a b c d α1 β1)
    (hL : K17bL2Left a a' b b' c c' d α1 β1 β6 γ6) :
    HasLexCell (V8 a a' b b' c c' d) ∨ K17b2L2Left a a' b b' c c' d α1 β1 β6 γ6 := by
  by_cases h1 : K17b2P1 a a' b b' c c' d α1 β1 β6 γ6
  · exact Or.inl (k17b2_P1w hdet hc' hb' ha' hα1 hβ1 hβ6 hγ6 h1)
  by_cases h2 : K17b2P2 a a' b b' c c' d α1 β1 β6 γ6
  · exact Or.inl (k17b2_P2w hdet hc' hb' ha' hα1 hβ1 hβ6 hγ6 h2)
  by_cases h5 : K17b2P5 a a' b b' c c' d
  · exact Or.inl (k17b2_P5w hdet hc' hb' ha' hα1 hβ1 hβ6 hγ6 h5)
  by_cases h4 : K17b2P4 a a' b b' c c' d
  · exact Or.inl (k17b2_P4w hdet hc' hb' ha' hα1 hβ1 hβ6 hγ6 h4)
  by_cases h13 : K17b2P13 a a' b b' c c' d
  · exact Or.inl (k17b2_P13w hdet hc' hb' ha' hα1 hβ1 hβ6 hγ6 h13)
  by_cases h3 : K17b2P3 a a' b b' c c' d
  · exact Or.inl (k17b2_P3w hdet hc' hb' ha' hα1 hβ1 hβ6 hγ6 h3)
  exact Or.inr ⟨hL, h1, h2, h5, h4, h13, h3⟩

end C2
end Type08Sp
end Minimality
