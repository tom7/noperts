module

public import Minimality.LexCell

@[expose] public section

/-!
# Adjacent-tie quad lemma (`Task EE`, Carbon A61 Lemma 1.2(a))

On a 4-cycle whose adjacent corners `i`, `i + 1` tie at level 0 while the other two are not both at
that level, one of the two opposite tie-breaks at level 1 is `RobUniLex`.
-/

set_option autoImplicit false

namespace Minimality.GenPlus

open Minimality Minimality.LexCell

/-- **APPROVED (Task EE).**  On a 4-cycle whose adjacent corners `i`, `i + 1` tie at level 0 while
the other two are not both at that level, one of the two opposite tie-breaks at level 1 is
`RobUniLex`. -/
theorem robUniLex_adjTie {z : ZMod 4 → ℝ} (i : ZMod 4) (h01 : z i = z (i + 1))
    (hn : ¬ (z (i + 2) = z i ∧ z (i + 3) = z i)) :
    RobUniLex (fun j => (z j, (if j = i then 1 else if j = i + 1 then -1 else 0 : ℝ), (0 : ℝ))) ∨
      RobUniLex (fun j => (z j, (if j = i then -1 else if j = i + 1 then 1 else 0 : ℝ), (0 : ℝ))) := by
  let fPos : ZMod 4 → ℝ × ℝ × ℝ :=
    fun j => (z j, (if j = i then 1 else if j = i + 1 then -1 else 0 : ℝ), (0 : ℝ))
  let fNeg : ZMod 4 → ℝ × ℝ × ℝ :=
    fun j => (z j, (if j = i then -1 else if j = i + 1 then 1 else 0 : ℝ), (0 : ℝ))
  have h10 : i + 1 ≠ i := by
    intro h; have : (1 : ZMod 4) = 0 := by linear_combination h
    revert this; decide
  have hPos_10 : LexLt3 (fPos (i + 1)) (fPos i) := by
    refine Or.inr ⟨sub_eq_zero.mpr h01, Or.inl ?_⟩
    simp [fPos, h10]
  have hNeg_01 : LexLt3 (fNeg i) (fNeg (i + 1)) := by
    refine Or.inr ⟨sub_eq_zero.mpr h01.symm, Or.inl ?_⟩
    simp [fNeg, h10]
  have h_zmod4 : ∀ x : ZMod 4, x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 := by decide
  have hi := h_zmod4 i
  rcases lt_trichotomy (z (i + 2)) (z i) with h2lt | h2eq | h2gt
  · left
    have hPos_21 : LexLt3 (fPos (i + 2)) (fPos (i + 1)) :=
      Or.inl (sub_pos.mpr (by dsimp [fPos]; linarith))
    rcases hi with rfl | rfl | rfl | rfl
    · exact robUniLex_four_of_mixed ⟨(2, 1), by decide, hPos_21⟩ ⟨(0, 1), by decide, hPos_10⟩
    · exact robUniLex_four_of_mixed ⟨(2, 1), by decide, hPos_10⟩ ⟨(2, 3), by decide, hPos_21⟩
    · exact robUniLex_four_of_mixed ⟨(0, 3), by decide, hPos_21⟩ ⟨(2, 3), by decide, hPos_10⟩
    · exact robUniLex_four_of_mixed ⟨(0, 3), by decide, hPos_10⟩ ⟨(0, 1), by decide, hPos_21⟩
  · rcases lt_trichotomy (z (i + 3)) (z i) with h3lt | h3eq | h3gt
    · right
      have hNeg_30 : LexLt3 (fNeg (i + 3)) (fNeg i) :=
        Or.inl (sub_pos.mpr h3lt)
      rcases hi with rfl | rfl | rfl | rfl
      · exact robUniLex_four_of_mixed ⟨(0, 1), by decide, hNeg_01⟩ ⟨(0, 3), by decide, hNeg_30⟩
      · exact robUniLex_four_of_mixed ⟨(0, 1), by decide, hNeg_30⟩ ⟨(2, 1), by decide, hNeg_01⟩
      · exact robUniLex_four_of_mixed ⟨(2, 3), by decide, hNeg_01⟩ ⟨(2, 1), by decide, hNeg_30⟩
      · exact robUniLex_four_of_mixed ⟨(2, 3), by decide, hNeg_30⟩ ⟨(0, 3), by decide, hNeg_01⟩
    · exact absurd ⟨h2eq, h3eq⟩ hn
    · left
      have hPos_03 : LexLt3 (fPos i) (fPos (i + 3)) :=
        Or.inl (sub_pos.mpr h3gt)
      rcases hi with rfl | rfl | rfl | rfl
      · exact robUniLex_four_of_mixed ⟨(0, 3), by decide, hPos_03⟩ ⟨(0, 1), by decide, hPos_10⟩
      · exact robUniLex_four_of_mixed ⟨(2, 1), by decide, hPos_10⟩ ⟨(0, 1), by decide, hPos_03⟩
      · exact robUniLex_four_of_mixed ⟨(2, 1), by decide, hPos_03⟩ ⟨(2, 3), by decide, hPos_10⟩
      · exact robUniLex_four_of_mixed ⟨(0, 3), by decide, hPos_10⟩ ⟨(2, 3), by decide, hPos_03⟩
  · right
    have hNeg_12 : LexLt3 (fNeg (i + 1)) (fNeg (i + 2)) :=
      Or.inl (sub_pos.mpr (by dsimp [fNeg]; linarith))
    rcases hi with rfl | rfl | rfl | rfl
    · exact robUniLex_four_of_mixed ⟨(0, 1), by decide, hNeg_01⟩ ⟨(2, 1), by decide, hNeg_12⟩
    · exact robUniLex_four_of_mixed ⟨(2, 3), by decide, hNeg_12⟩ ⟨(2, 1), by decide, hNeg_01⟩
    · exact robUniLex_four_of_mixed ⟨(2, 3), by decide, hNeg_01⟩ ⟨(0, 3), by decide, hNeg_12⟩
    · exact robUniLex_four_of_mixed ⟨(0, 1), by decide, hNeg_12⟩ ⟨(0, 3), by decide, hNeg_01⟩

end Minimality.GenPlus
