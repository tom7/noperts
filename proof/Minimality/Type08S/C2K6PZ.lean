module

public import Minimality.Type08S.C2K6PK

@[expose] public section

/-!
# K6PZ: the ParEnd tie slices cut to M (and QN2's `α1 ≤ 1` double ties); `Resid08FinalK10 → Resid08FinalK11`

`K5ZsCE2` closes (`k6p_qce2_final`); `K5ZsCEb` leaves `K6sMKb`; `K5ZsN2` leaves `K6sMN2 ∨ K6sDN2`.
The T/T′ slices are carried over unchanged.
-/

namespace Minimality
namespace Type08Sp

open C2

/-- **The K6 leftover in one labelling.** -/
def K6Slice {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) : Prop :=
  K5ZsTT a a' b b' c c' d ∨ K5ZsPa a a' b b' c c' d ∨ K5ZsPc a a' b b' c c' d ∨
  K5ZsTouch a a' b b' c c' d ∨ K5ZsTa a a' b b' c c' d ∨ K5ZsTc a a' b b' c c' d ∨
  K6sMN2 a a' b b' c c' d ∨ K6sDN2 a a' b b' c c' d ∨ (RegT4 W.F ∧ K6sMKb a a' b b' c c' d)

theorem k6p_slice_step {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) (h : K5ZSlice W) :
    HasLexCell (V8 a a' b b' c c' d) ∨ K6Slice W := by
  rcases h with h | h | h | h | h | h | h | h | h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))
  · rcases k6p_qn2_final W h with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))
  · rcases k6p_qceb_final W h.1.1 h.1.2 h with h' | h'
    · exact Or.inl h'
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨h.1, h'⟩))))))))
  · exact Or.inl (k6p_qce2_final W h.1.1 h.1.2 h)

def K6ResidP (a a' b b' c c' d : ℝ³) : Prop :=
  ∃ W : Norm08w a a' b b' c c' d, ResP W.F d ∧ K6Slice W

def K6ResidP6 (a a' b b' c c' d : ℝ³) : Prop :=
  K6ResidP a a' b b' c c' d ∨ K6ResidP b b' a a' c c' d ∨ K6ResidP a a' c c' b b' d ∨
  K6ResidP c c' a a' b b' d ∨ K6ResidP b b' c c' a a' d ∨ K6ResidP c c' b b' a a' d

/-- **`Resid08FinalK11`**: `Resid08FinalK10` with the ParEnd slices cut to `M` (and `K6sDN2`). -/
def Resid08FinalK11 (a a' b b' c c' d : ℝ³) : Prop :=
  (PlanarTwo a a' b b' c c' ∨ PlanarGen a a' b b' c c' d) ∧ K6ResidP6 a a' b b' c c' d ∧
    ¬ HasLexCell (V8 a a' b b' c c' d)

theorem k6p_residP_step {p p' q q' r r' d : ℝ³} (h : K5ZResidP p p' q q' r r' d) :
    HasLexCell (V8 p p' q q' r r' d) ∨ K6ResidP p p' q q' r r' d := by
  obtain ⟨W, hR, hs⟩ := h
  rcases k6p_slice_step W hs with h | h
  · exact Or.inl h
  · exact Or.inr ⟨W, hR, h⟩

theorem resid08FinalK10_imp_K11 {a a' b b' c c' d : ℝ³}
    (h : Resid08FinalK10 a a' b b' c c' d) : Resid08FinalK11 a a' b b' c c' d := by
  obtain ⟨hpl, h6, hno⟩ := h
  have e := type08_set_perm a a' b b' c c' d
  refine ⟨hpl, ?_, hno⟩
  rcases h6 with h | h | h | h | h | h
  · rcases k6p_residP_step h with h | h
    · exact (hno h).elim
    · exact Or.inl h
  · rcases k6p_residP_step h with h | h
    · exact (hno (by rw [V8, ← e.2.1]; exact h)).elim
    · exact Or.inr (Or.inl h)
  · rcases k6p_residP_step h with h | h
    · exact (hno (by rw [V8, ← e.2.2.1]; exact h)).elim
    · exact Or.inr (Or.inr (Or.inl h))
  · rcases k6p_residP_step h with h | h
    · exact (hno (by rw [V8, ← e.2.2.2.1]; exact h)).elim
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · rcases k6p_residP_step h with h | h
    · exact (hno (by rw [V8, ← e.2.2.2.2.1]; exact h)).elim
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · rcases k6p_residP_step h with h | h
    · exact (hno (by rw [V8, ← e.2.2.2.2.2]; exact h)).elim
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))

end Type08Sp
end Minimality
