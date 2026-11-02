module

public import Minimality.Type08S.C2K20TF2
public import Minimality.Type08S.C2K5DM

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

/-- Lex unimodality of cell A3 `(b', a', b, d, a)` (depths `z, z - b6 rr, z - rr, z, z`), valley-free at `a`:
`w d < w a ∨ w b' < w a`. -/
theorem k20tG_lex (zz ww : ZMod 5 → ℝ) (hinj : ∀ i j, zz i = zz j → ww i = ww j → i = j) {z rr b6 : ℝ}
    (hrr : 0 < rr) (hb6 : 0 < b6)
    (h0 : zz 0 = z) (h1 : zz 1 = z - b6 * rr) (h2 : zz 2 = z - rr) (h3 : zz 3 = z) (h4 : zz 4 = z)
    (hv : ww 3 < ww 4 ∨ ww 0 < ww 4) : LexUni zz ww := by
  obtain ⟨e0, e1, e2, e3, e4, f0, f1, f2, f3, f4⟩ := k19_z5
  have l10 : LexLt (zz 1, ww 1) (zz 0, ww 0) := Or.inl (by rw [h1, h0]; nlinarith)
  have l23 : LexLt (zz 2, ww 2) (zz 3, ww 3) := Or.inl (by rw [h2, h3]; nlinarith)
  have t34 : LexLt (zz 3, ww 3) (zz 4, ww 4) ∨ LexLt (zz 4, ww 4) (zz 3, ww 3) :=
    lexLt_total (k20t_ne5 hinj (show (3 : ZMod 5) ≠ 4 by decide))
  have t40 : LexLt (zz 4, ww 4) (zz 0, ww 0) ∨ LexLt (zz 0, ww 0) (zz 4, ww 4) :=
    lexLt_total (k20t_ne5 hinj (show (4 : ZMod 5) ≠ 0 by decide))
  have t30 : LexLt (zz 3, ww 3) (zz 0, ww 0) ∨ LexLt (zz 0, ww 0) (zz 3, ww 3) :=
    lexLt_total (k20t_ne5 hinj (show (3 : ZMod 5) ≠ 0 by decide))
  have wl : ∀ {i j : ZMod 5}, zz i = zz j → i ≠ j → ww i < ww j ∨ ww j < ww i := by
    intro i j hz hij
    rcases lexLt_total (k20t_ne5 hinj hij) with h | h
    · left; rcases h with h | ⟨-, h⟩
      · rw [hz] at h; exact absurd h (lt_irrefl _)
      · exact h
    · right; rcases h with h | ⟨-, h⟩
      · rw [hz] at h; exact absurd h (lt_irrefl _)
      · exact h
  have L : ∀ {i j : ZMod 5}, zz i = zz j → ww i < ww j → LexLt (zz i, ww i) (zz j, ww j) :=
    fun hz hw => Or.inr ⟨hz, hw⟩
  have z34 : zz 3 = zz 4 := by rw [h3, h4]
  have z40 : zz 4 = zz 0 := by rw [h4, h0]
  have w34 := wl z34 (by decide)
  have w40 := wl z40 (by decide)
  rcases w34 with h34 | h43
  · rcases w40 with h40 | h04
    · -- ww 3 < ww 4 < ww 0 : peak 0
      refine k19_lexUni_nb zz ww hinj 0 ?_ ?_ ?_
      · rw [e0]; exact L z40 h40
      · rw [f0]; exact l10
      · intro i hi
        rcases z5_cases i with rfl | rfl | rfl | rfl | rfl
        · exact absurd rfl hi
        · left; rw [e1]; exact l10
        · right; rw [f2]; exact l23
        · right; rw [f3]; exact L z34 h34
        · right; rw [f4]; exact L z40 h40
    · -- ww 0 < ww 4, ww 3 < ww 4 : peak 4
      refine k19_lexUni_nb zz ww hinj 4 ?_ ?_ ?_
      · rw [e4]; exact L z34 h34
      · rw [f4]; exact L z40.symm h04
      · intro i hi
        rcases z5_cases i with rfl | rfl | rfl | rfl | rfl
        · left; rw [e0]; exact L z40.symm h04
        · left; rw [e1]; exact l10
        · right; rw [f2]; exact l23
        · right; rw [f3]; exact L z34 h34
        · exact absurd rfl hi
  · -- ww 4 < ww 3: then valley-freeness gives ww 0 < ww 4 : peak 3
    have h04 : ww 0 < ww 4 := by
      rcases hv with h | h
      · exact absurd h (not_lt.2 h43.le)
      · exact h
    refine k19_lexUni_nb zz ww hinj 3 ?_ ?_ ?_
    · rw [e3]; exact l23
    · rw [f3]; exact L z34.symm h43
    · intro i hi
      rcases z5_cases i with rfl | rfl | rfl | rfl | rfl
      · left; rw [e0]; exact L z40.symm h04
      · left; rw [e1]; exact l10
      · right; rw [f2]; exact l23
      · exact absurd rfl hi
      · left; rw [e4]; exact L z34.symm h43

end C2
end Type08Sp
end Minimality
