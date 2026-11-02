module

public import Minimality.Type08S.C2K6PZ
public import Minimality.Type08S.C2K6MQ

@[expose] public section

/-!
# K6MZ: the stratum M and DN2 cut to their leftovers; `Resid08FinalK11 → Resid08FinalK12`
-/

namespace Minimality
namespace Type08Sp

open C2

/-- **The K7 leftover in one labelling.** -/
def K7Slice {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) : Prop :=
  K5ZsTT a a' b b' c c' d ∨ K5ZsPa a a' b b' c c' d ∨ K5ZsPc a a' b b' c c' d ∨
  K5ZsTouch a a' b b' c c' d ∨ K5ZsTa a a' b b' c c' d ∨ K5ZsTc a a' b b' c c' d ∨
  K6sMLeftN2 a a' b b' c c' d ∨ K6sDN2one a a' b b' c c' d ∨ K6sMLeftKb a a' b b' c c' d

theorem k6m_slice_step {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) (h : K6Slice W) :
    HasLexCell (V8 a a' b b' c c' d) ∨ K7Slice W := by
  rcases h with h | h | h | h | h | h | h | h | ⟨hreg, h⟩
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))
  · rcases k6m_qn2 W h with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))
  · rcases k6m_dn2 W h with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))
  · rcases k6m_qceb W hreg.1 hreg.2 h with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))

def K7ResidP (a a' b b' c c' d : ℝ³) : Prop :=
  ∃ W : Norm08w a a' b b' c c' d, ResP W.F d ∧ K7Slice W

def K7ResidP6 (a a' b b' c c' d : ℝ³) : Prop :=
  K7ResidP a a' b b' c c' d ∨ K7ResidP b b' a a' c c' d ∨ K7ResidP a a' c c' b b' d ∨
  K7ResidP c c' a a' b b' d ∨ K7ResidP b b' c c' a a' d ∨ K7ResidP c c' b b' a a' d

/-- **`Resid08FinalK12`**: `Resid08FinalK11` with M cut to its box leftovers (boundaries, ties, H1, H5) and DN2 to α1 = 1. -/
def Resid08FinalK12 (a a' b b' c c' d : ℝ³) : Prop :=
  (PlanarTwo a a' b b' c c' ∨ PlanarGen a a' b b' c c' d) ∧ K7ResidP6 a a' b b' c c' d ∧
    ¬ HasLexCell (V8 a a' b b' c c' d)

theorem k6m_residP_step {p p' q q' r r' d : ℝ³} (h : K6ResidP p p' q q' r r' d) :
    HasLexCell (V8 p p' q q' r r' d) ∨ K7ResidP p p' q q' r r' d := by
  obtain ⟨W, hR, hs⟩ := h
  rcases k6m_slice_step W hs with h | h
  · exact Or.inl h
  · exact Or.inr ⟨W, hR, h⟩

theorem resid08FinalK11_imp_K12 {a a' b b' c c' d : ℝ³}
    (h : Resid08FinalK11 a a' b b' c c' d) : Resid08FinalK12 a a' b b' c c' d := by
  obtain ⟨hpl, h6, hno⟩ := h
  have e := type08_set_perm a a' b b' c c' d
  refine ⟨hpl, ?_, hno⟩
  rcases h6 with h | h | h | h | h | h
  · rcases k6m_residP_step h with h | h
    · exact (hno h).elim
    · exact Or.inl h
  · rcases k6m_residP_step h with h | h
    · exact (hno (by rw [V8, ← e.2.1]; exact h)).elim
    · exact Or.inr (Or.inl h)
  · rcases k6m_residP_step h with h | h
    · exact (hno (by rw [V8, ← e.2.2.1]; exact h)).elim
    · exact Or.inr (Or.inr (Or.inl h))
  · rcases k6m_residP_step h with h | h
    · exact (hno (by rw [V8, ← e.2.2.2.1]; exact h)).elim
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · rcases k6m_residP_step h with h | h
    · exact (hno (by rw [V8, ← e.2.2.2.2.1]; exact h)).elim
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · rcases k6m_residP_step h with h | h
    · exact (hno (by rw [V8, ← e.2.2.2.2.2]; exact h)).elim
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))

end Type08Sp
end Minimality
