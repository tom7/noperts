module

public import Minimality.Type08S.P2FinalF

@[expose] public section

set_option relaxedAutoImplicit true
/-!
# pkP / PTDefs: definitions for package P1 (the case at `T`).  No sorry.  Compile with `leanchk PTDefs.lean -o`.
-/

set_option autoImplicit true
set_option linter.unusedVariables false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

/-! ## Definitions -/

/-- `K_b = R1` robustly unimodal at `ℓ`. -/
def RobKb (a a' b b' c c' d : ℝ³) : Prop :=
  IsRobustUnimodal ((test08 1 true true).depth (pts08 a a' b b' c c' d))

/-- The T4 weak far triple at `T` (R2T*'s exception for the T4 group at `T`; `z_c = z_w` is impossible). -/
def TouchT (b b' c c' d : ℝ³) : Prop :=
  TieT4 b b' c c' d ∧ ⟪d, b - d⟫ < ⟪c, b - d⟫ ∧ ⟪c, b - d⟫ ≤ ⟪b, b - d⟫

/-- `∠q + ∠q' > π` at `ℓ` (the sp08f §6 cells `(+,+,+)`, `(−,−,−)` exist; `a'` stays hidden in `K_2`'s slide on
`Q_ab`'s circle).  In the culJ frame at `T` this is `γ4 > 1`: `det3 (c - b') (a - d) (b - d) = 1 - γ4` and
`det3 (a - d) (c - d) (b - d) = -1` times `det3 E₁ E₂ E₃`² > 0 (map.md §1.3; `tT.cc`'s `insideQuad` test). -/
def AngBig (a b b' c d : ℝ³) : Prop :=
  0 < det3 (c - b') (a - d) (b - d) * det3 (a - d) (c - d) (b - d)

/-- Screen direction of `Q_bc`'s circle at `ℓ` (`eF` of `K_b`). -/
noncomputable def eBC (b c d : ℝ³) : ℝ³ := (c - d) - (⟪c - d, b - d⟫ / ⟪b - d, b - d⟫) • (b - d)

/-- Screen direction of `Q_ab`'s circle at `ℓ` (`eF` of `K_2`). -/
noncomputable def eAB (b c' d : ℝ³) : ℝ³ := (c' - b) - (⟪c' - b, b - d⟫ / ⟪b - d, b - d⟫) • (b - d)

/-- `X_ba' = (b, c', b', a')` robust at `ℓ` (Lemma Q form, as in `poly_rupert_off`). -/
def RobXba (a' b b' c' d : ℝ³) : Prop := ¬ Sep ⟪b, b - d⟫ ⟪b', b - d⟫ ⟪a', b - d⟫ ⟪c', b - d⟫

/-- `X_2a' = (d, c', b', a')` robust at `ℓ`. -/
def RobX2a (a' b b' c' d : ℝ³) : Prop := ¬ Sep ⟪d, b - d⟫ ⟪b', b - d⟫ ⟪a', b - d⟫ ⟪c', b - d⟫

/-- **The leftover at `T`** (codimension ≥ 4; map.md §5).  Each disjunct with its count (T counts 1). -/
def S4T' (a a' b b' c c' d : ℝ³) : Prop :=
  IsT a' b c d ∧
    (-- (L1) touching at `T` with `z_c = z_b`: three more equalities.  Codim 4.
     (TouchT b b' c c' d ∧ ⟪c, b - d⟫ = ⟪b, b - d⟫) ∨
     -- (L2) touching at `T`, `∠q + ∠q' ≤ π`, an HDN of `X_ba'`.  The level edge `[c', b']` is an HDN only if
     -- `∠q + ∠q' ≥ π`; every other HDN of `X_ba'` is one more condition.  Codim 4.
     (TouchT b b' c c' d ∧ ¬ AngBig a b b' c d ∧ ¬ NoHDNAt ({b, c', b', a'} : Finset ℝ³) (b - d)) ∨
     -- (L3) case B, `∠q + ∠q' > π`, `X_ba'` not robust (only on N2's weak far triple at `T`: two ties) and `K_2`'s
     -- HDN persists along `Q_ab`'s circle (one more: the level edge persists only with a right angle).  Codim 4.
     (¬ RobKb a a' b b' c c' d ∧ AngBig a b b' c d ∧ ¬ RobXba a' b b' c' d ∧
       ¬ NoPersistHDN (quad d c' b' c) (b - d) (eAB b c' d)) ∨
     -- (L4) case B, `∠q + ∠q' ≤ π`, an HDN of `K_2`, `X_ba'` not robust or with an HDN, `X_2a'` not robust or with
     -- an HDN persisting along `Q_bc`'s circle.  Codim 4 (map.md §5).
     (¬ RobKb a a' b b' c c' d ∧ ¬ AngBig a b b' c d ∧ ¬ NoHDNAt ({d, c', b', c} : Finset ℝ³) (b - d) ∧
       ¬ (RobXba a' b b' c' d ∧ NoHDNAt ({b, c', b', a'} : Finset ℝ³) (b - d)) ∧
       ¬ (RobX2a a' b b' c' d ∧ NoPersistHDN (quad d c' b' a') (b - d) (eBC b c d))) ∨
     -- (L5) safety valve for P1-A2 (sp08f §8 item 2 "(Q) at T"): level face of `Q_ac` and an HDN of `R1`.  Codim 4.
     (LevelQac a b c d ∧ ¬ NoHDNAt ({b, c', b', c} : Finset ℝ³) (b - d)))

end Type08Sp
end Minimality
