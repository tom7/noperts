module

public import Minimality.Type08S.C2K6MZ
public import Minimality.Type08S.C2K6TAM
public import Minimality.Type08S.C2K6TBZ
public import Minimality.Type08S.C2K6HF

@[expose] public section

/-!
# K6TZ: the T/T′ tie slices cut to their K6T leftovers, and M's box H1 (C2K6H*); `Resid08FinalK12 → Resid08FinalK13`
-/

namespace Minimality
namespace Type08Sp

open C2

/-- **The K8 leftover in one labelling.** -/
def K8Slice {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) : Prop :=
  K6tLeftTT a a' b b' c c' d ∨ K6tLeftPa a a' b b' c c' d ∨ K6tLeftPc a a' b b' c c' d ∨
  K6tLeftTa a a' b b' c c' d ∨ K6tLeftTc a a' b b' c c' d ∨
  K6sMLeftN2' a a' b b' c c' d ∨ K6sDN2one a a' b b' c c' d ∨ K6sMLeftKb a a' b b' c c' d

theorem k6t_slice_step {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) (h : K7Slice W) :
    HasLexCell (V8 a a' b b' c c' d) ∨ K8Slice W := by
  rcases h with h | h | h | h | h | h | h | h | h
  · rcases k6t2_TT W h with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · rcases k6t2_Pa W (k5z_far1 W h.1 h.2.1) h with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inl h))
  · rcases k6t2_Pc h with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · rcases k6t1_Touch_Ta W (Or.inl h) with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · rcases k6t1_Touch_Ta W (Or.inr h) with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · rcases k6t1_Tc W h with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
  · rcases k6mh1_left h with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))

def K8ResidP (a a' b b' c c' d : ℝ³) : Prop :=
  ∃ W : Norm08w a a' b b' c c' d, ResP W.F d ∧ K8Slice W

def K8ResidP6 (a a' b b' c c' d : ℝ³) : Prop :=
  K8ResidP a a' b b' c c' d ∨ K8ResidP b b' a a' c c' d ∨ K8ResidP a a' c c' b b' d ∨
  K8ResidP c c' a a' b b' d ∨ K8ResidP b b' c c' a a' d ∨ K8ResidP c c' b b' a a' d

/-- **`Resid08FinalK13`**: `Resid08FinalK12` with the six T/T′ tie slices cut to their K6T leftovers. -/
def Resid08FinalK13 (a a' b b' c c' d : ℝ³) : Prop :=
  (PlanarTwo a a' b b' c c' ∨ PlanarGen a a' b b' c c' d) ∧ K8ResidP6 a a' b b' c c' d ∧
    ¬ HasLexCell (V8 a a' b b' c c' d)

theorem k6t_residP_step {p p' q q' r r' d : ℝ³} (h : K7ResidP p p' q q' r r' d) :
    HasLexCell (V8 p p' q q' r r' d) ∨ K8ResidP p p' q q' r r' d := by
  obtain ⟨W, hR, hs⟩ := h
  rcases k6t_slice_step W hs with h | h
  · exact Or.inl h
  · exact Or.inr ⟨W, hR, h⟩

theorem resid08FinalK12_imp_K13 {a a' b b' c c' d : ℝ³}
    (h : Resid08FinalK12 a a' b b' c c' d) : Resid08FinalK13 a a' b b' c c' d := by
  obtain ⟨hpl, h6, hno⟩ := h
  have e := type08_set_perm a a' b b' c c' d
  refine ⟨hpl, ?_, hno⟩
  rcases h6 with h | h | h | h | h | h
  · rcases k6t_residP_step h with h | h
    · exact (hno h).elim
    · exact Or.inl h
  · rcases k6t_residP_step h with h | h
    · exact (hno (by rw [V8, ← e.2.1]; exact h)).elim
    · exact Or.inr (Or.inl h)
  · rcases k6t_residP_step h with h | h
    · exact (hno (by rw [V8, ← e.2.2.1]; exact h)).elim
    · exact Or.inr (Or.inr (Or.inl h))
  · rcases k6t_residP_step h with h | h
    · exact (hno (by rw [V8, ← e.2.2.2.1]; exact h)).elim
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · rcases k6t_residP_step h with h | h
    · exact (hno (by rw [V8, ← e.2.2.2.2.1]; exact h)).elim
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · rcases k6t_residP_step h with h | h
    · exact (hno (by rw [V8, ← e.2.2.2.2.2]; exact h)).elim
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))

end Type08Sp
end Minimality
