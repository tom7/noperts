module

public import Minimality.Type16SAT.Last16
public import Minimality.Type16SAT.FinalLast16
public import Minimality.Type16SAT.GPDead16

@[expose] public section

/-!
# Type 16: no sign vector is left

The sign vector of `C * ([0126], [0134], [1234], [2346])` (`81` possibilities) is in one of the sets closed by the type 16
branch: `Cls16Closed`, `Cls16ClosedW`, `Cls16M` (`+---`, `----`), the classes `+-+-`, `--+-`, `Cls16Dead`, `Cls16WallR`,
`Cls16WallX`, `+-0-`, `--0-`, `Cls16Z2` or `Cls16Last`.  By the trichotomy of the four products (`cls16_exhaust`).
-/

set_option autoImplicit false
set_option maxHeartbeats 0
open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21 Minimality.H29.SAT

namespace Minimality.H16.SAT

private theorem tri3 (s : ℝ) : (0 < s ∧ ¬ s < 0 ∧ s ≠ 0 ∧ 0 ≤ s) ∨ (s = 0) ∨ (s < 0 ∧ ¬ 0 < s ∧ s ≠ 0 ∧ ¬ 0 ≤ s) := by
  rcases lt_trichotomy s 0 with h | h | h
  · exact Or.inr (Or.inr ⟨h, not_lt.2 h.le, h.ne, not_le.2 h⟩)
  · exact Or.inr (Or.inl h)
  · exact Or.inl ⟨h, not_lt.2 h.le, h.ne', h.le⟩

/-- **Every type 16 sign vector is in one of the closed sets.** -/
theorem cls16_exhaust (x : Fin 7 → ℝ³) (hcl : ¬ (Cls16Closed x ∨ Cls16ClosedW x)) (hM : ¬ Cls16M x)
    (hP : ¬ ((0 < C16 x * br16 x 0 1 2 6 ∧ C16 x * br16 x 0 1 3 4 < 0 ∧ 0 < C16 x * br16 x 1 2 3 4 ∧
        C16 x * br16 x 2 3 4 6 < 0) ∨
      (C16 x * br16 x 0 1 2 6 < 0 ∧ C16 x * br16 x 0 1 3 4 < 0 ∧ 0 < C16 x * br16 x 1 2 3 4 ∧
        C16 x * br16 x 2 3 4 6 < 0)))
    (hD : ¬ Cls16Dead x)
    (hW : ¬ (Cls16WallR x ∨ Cls16WallX x ∨ (Vec16 1 (-1) 0 (-1) x ∨ Vec16 (-1) (-1) 0 (-1) x))) :
    Cls16Z2 x ∨ Cls16Last x := by
  simp only [Cls16Closed, Cls16ClosedW, Cls16M, Cls16Dead, Cls16WallR, Cls16WallX, Cls16Z2, Cls16Last, Vec16,
    SgnP] at *
  generalize C16 x * br16 x 0 1 2 6 = s1 at *
  generalize C16 x * br16 x 0 1 3 4 = s2 at *
  generalize C16 x * br16 x 1 2 3 4 = s3 at *
  generalize C16 x * br16 x 2 3 4 6 = s4 at *
  rcases tri3 s1 with ⟨a1, a2, a3, a4⟩ | a1 | ⟨a1, a2, a3, a4⟩ <;>
  rcases tri3 s2 with ⟨b1, b2, b3, b4⟩ | b1 | ⟨b1, b2, b3, b4⟩ <;>
  rcases tri3 s3 with ⟨c1, c2, c3, c4⟩ | c1 | ⟨c1, c2, c3, c4⟩ <;>
  rcases tri3 s4 with ⟨d1, d2, d3, d4⟩ | d1 | ⟨d1, d2, d3, d4⟩ <;>
  simp_all

end Minimality.H16.SAT
