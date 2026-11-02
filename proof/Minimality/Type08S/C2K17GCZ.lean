module

public import Minimality.Type08S.C2K17GC6
public import Minimality.Type08S.C2K17B2Y

@[expose] public section


/-!
# K17GC / Z: composition.  The Pa slice (`K17fLeftPa`) and the Pc slice (`K6t3LeftPc`) cut by bundle C.
-/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.unusedVariables false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp
open C2

/-- Pa leftover after bundle C: one extra tie. -/
def K17gcLeftPa (a a' b b' c c' d : ℝ³) : Prop :=
  K17fLeftPa a a' b b' c c' d ∧ (⟪a - d, c - d⟫ = 0 ∨ ⟪a - d, a - c'⟫ = 0)

/-- Pc leftover after bundle C. -/
def K17gcLeftPc (a a' b b' c c' d : ℝ³) : Prop :=
  K6t3LeftPc a a' b b' c c' d ∧
    (⟪a - d, a - c'⟫ = 0 ∨ (0 < ⟪a - d, a - c'⟫ ∧ ⟪c - d, c - a'⟫ = 0) ∨
      (⟪a - d, a - c'⟫ < 0 ∧ ⟪c - b', d - b⟫ = 0 ∧ ⟪c - b', c - d⟫ = 0))

theorem k17gc_Pa_step {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) (h : K17fLeftPa a a' b b' c c' d) :
    HasLexCell (V8 a a' b b' c c' d) ∨ K17gcLeftPa a a' b b' c c' d := by
  obtain ⟨hctx, hL⟩ := id h
  obtain ⟨hT', hnT, hκ, -⟩ := id hctx
  have hfar := k5z_far1 W hT' hnT
  rcases hL with ⟨h1, h2, hα⟩ | ⟨h0, hα, hβ0, hβ⟩ | ⟨hα, hβ0, hβ⟩
  · rcases k17gc_u1 W hctx h1 h2 hα with h3 | h3
    · exact Or.inl h3
    · exact Or.inr ⟨h, Or.inl h3⟩
  · rcases hβ0.eq_or_lt with he | hlt
    · rcases k17f_s17 W hT' hκ hfar h0 hα he.symm with h3 | h3
      · exact Or.inl h3
      · exact Or.inr ⟨h, Or.inl h3⟩
    · rcases hβ with he | hpq
      · exact absurd he (ne_of_gt hlt)
      · exact Or.inl (k17gc_u2 W hctx h0 hα hlt hpq)
  · rcases hβ0.eq_or_lt with he | hlt
    · rcases k17gc_s15 W hctx hα he.symm with h3 | h3
      · exact Or.inl h3
      · exact Or.inr ⟨h, Or.inr h3⟩
    · rcases hβ with he | h0
      · exact absurd he (ne_of_gt hlt)
      · rcases k17gc_u3 W hctx hα hlt h0 with h3 | h3
        · exact Or.inl h3
        · exact Or.inr ⟨h, Or.inr h3⟩

theorem k17gc_Pc_step {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) (h : K6t3LeftPc a a' b b' c c' d) :
    HasLexCell (V8 a a' b b' c c' d) ∨ K17gcLeftPc a a' b b' c c' d := by
  rcases k17gc_s16 W h with h1 | h1
  · exact Or.inl h1
  · exact Or.inr ⟨h, h1⟩

def K17GSlice {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) : Prop :=
  K6t3LeftTT a a' b b' c c' d ∨ K17gcLeftPa a a' b b' c c' d ∨ K17gcLeftPc a a' b b' c c' d ∨
  K17fLeftTa14 a a' b b' c c' d ∨ K17fLeftTc' a a' b b' c c' d ∨
  K17B2LeftMN2 W ∨ K6sDN2one a a' b b' c c' d ∨ K17LeftMKb W

theorem k17g_slice_step {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) (h : K17B2Slice W) :
    HasLexCell (V8 a a' b b' c c' d) ∨ K17GSlice W := by
  rcases h with h | h | h | h | h | h | h | h
  · exact Or.inr (Or.inl h)
  · rcases k17gc_Pa_step W h with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inl h))
  · rcases k17gc_Pc_step W h with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))

def K17GResidP (a a' b b' c c' d : ℝ³) : Prop :=
  ∃ W : Norm08w a a' b b' c c' d, ResP W.F d ∧ K17GSlice W

def K17GResidP6 (a a' b b' c c' d : ℝ³) : Prop :=
  K17GResidP a a' b b' c c' d ∨ K17GResidP b b' a a' c c' d ∨ K17GResidP a a' c c' b b' d ∨
  K17GResidP c c' a a' b b' d ∨ K17GResidP b b' c c' a a' d ∨ K17GResidP c c' b b' a a' d

/-- **`Resid08FinalK17G`**: `Resid08FinalK17B2` with the Pa and Pc slices cut by bundle C. -/
def Resid08FinalK17G (a a' b b' c c' d : ℝ³) : Prop :=
  (PlanarTwo a a' b b' c c' ∨ PlanarGen a a' b b' c c' d) ∧ K17GResidP6 a a' b b' c c' d ∧
    ¬ HasLexCell (V8 a a' b b' c c' d)

theorem k17g_residP_step {p p' q q' r r' d : ℝ³} (h : K17B2ResidP p p' q q' r r' d) :
    HasLexCell (V8 p p' q q' r r' d) ∨ K17GResidP p p' q q' r r' d := by
  obtain ⟨W, hR, hs⟩ := h
  rcases k17g_slice_step W hs with h | h
  · exact Or.inl h
  · exact Or.inr ⟨W, hR, h⟩

theorem resid08FinalK17B2_imp_K17G {a a' b b' c c' d : ℝ³}
    (h : Resid08FinalK17B2 a a' b b' c c' d) : Resid08FinalK17G a a' b b' c c' d := by
  obtain ⟨hpl, h6, hno⟩ := h
  have e := type08_set_perm a a' b b' c c' d
  refine ⟨hpl, ?_, hno⟩
  rcases h6 with h | h | h | h | h | h
  · rcases k17g_residP_step h with h | h
    · exact (hno h).elim
    · exact Or.inl h
  · rcases k17g_residP_step h with h | h
    · exact (hno (by rw [V8, ← e.2.1]; exact h)).elim
    · exact Or.inr (Or.inl h)
  · rcases k17g_residP_step h with h | h
    · exact (hno (by rw [V8, ← e.2.2.1]; exact h)).elim
    · exact Or.inr (Or.inr (Or.inl h))
  · rcases k17g_residP_step h with h | h
    · exact (hno (by rw [V8, ← e.2.2.2.1]; exact h)).elim
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · rcases k17g_residP_step h with h | h
    · exact (hno (by rw [V8, ← e.2.2.2.2.1]; exact h)).elim
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · rcases k17g_residP_step h with h | h
    · exact (hno (by rw [V8, ← e.2.2.2.2.2]; exact h)).elim
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))

end Type08Sp
end Minimality
