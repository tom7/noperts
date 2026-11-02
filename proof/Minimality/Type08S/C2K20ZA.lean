module

public import Minimality.Type08S.C2K19ZA
public import Minimality.Type08S.C2K20E
public import Minimality.Type08S.C2K18E

@[expose] public section

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp
open C2

/-- Pa after K20: the S1.5 corner (4th K19 tie) is closed by Rupert. -/
def K20LeftPa (a a' b b' c c' d : ℝ³) : Prop :=
  K17fLeftPa a a' b b' c c' d ∧
  ((⟪a - d, c - d⟫ = 0 ∧ det3 (b' - a) (b - d) (c - d) = 0 ∧ det3 (a - d) (c' - b) (c - d) = 0) ∨
   (⟪a - d, c - d⟫ = 0 ∧ det3 (b' - a) (b - d) (c - d) * det3 (a - d) (b - d) (c - d) < 0 ∧
     (det3 (a - d) (c' - b) (c - d) = 0 ∨ det3 (c' - a') (b' - a') (a - d) = 0)) ∨
   (⟪a - d, c - d⟫ = 0 ∧ det3 (b' - a) (b - d) (c - d) * det3 (a - d) (b - d) (c - d) < 0 ∧
     det3 (a - d) (c' - b) (c - d) * det3 (a - d) (b - d) (c - d) = 0 ∧
     (⟪a' - b, a' - c⟫ = 0 ∨ (⟪a' - b, a' - c⟫ < 0 ∧ ⟪a' - b, b - d⟫ = 0))))

/-- Ta after K20: B11 as before; A41 with the S1.3 tie (S1.4 closed by Rupert). -/
def K20LeftTa (a a' b b' c c' d : ℝ³) : Prop :=
  K17hTaB11 a a' b b' c c' d ∨ (K17hTaA41 a a' b b' c c' d ∧ ⟪a - d, a - c'⟫ = 0)

theorem k20z_Pa_step {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d)
    (hNR : ¬ IsRupert (V8 a a' b b' c c' d)) (h : K19LeftPa a a' b b' c c' d) :
    HasLexCell (V8 a a' b b' c c' d) ∨ K20LeftPa a a' b b' c c' d := by
  obtain ⟨h, h1 | h1 | h1 | ⟨h0, hα, hβ⟩⟩ := h
  · exact Or.inr ⟨h, Or.inl h1⟩
  · exact Or.inr ⟨h, Or.inr (Or.inl h1)⟩
  · exact Or.inr ⟨h, Or.inr (Or.inr h1)⟩
  · rcases k18_s15_tie W h.1 hα hβ h0 with h3 | ⟨hpq, hpr⟩
    · exact Or.inl h3
    · exact (hNR (k20_s15_corner W h.1 hα hβ hpq hpr)).elim

theorem k20z_Ta_step {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d)
    (hNR : ¬ IsRupert (V8 a a' b b' c c' d)) (h : K19LeftTa a a' b b' c c' d) :
    HasLexCell (V8 a a' b b' c c' d) ∨ K20LeftTa a a' b b' c c' d := by
  rcases h with hB | ⟨hA, hl | hl⟩
  · exact Or.inr (Or.inl hB)
  · obtain ⟨hctx, hA', hqr, h0⟩ := id hA
    have hT : IsT a' b c d := hctx.elim (fun h => h.1) (fun h => h.1)
    have hT' : ¬ IsT' a b c' d := hctx.elim (fun h => h.2.1) (fun h => h.2.1)
    obtain ⟨-, -, -, -, -, hdet, -⟩ := norm08w_coordsT W hT
    have hz : ⟪d - b, a - b'⟫ = 0 := k17h_zeta_of_qr W hT hA'.2.2.2.1 hqr
    have hβ6 : det3 (a' - b) (c - d) (a - d) = 0 :=
      (mul_eq_zero.1 hl).resolve_right hdet
    exact (hNR (k20_s14 W hT' hA' hz hβ6 h0)).elim
  · exact Or.inr (Or.inr ⟨hA, hl⟩)

def K20Slice {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) : Prop :=
  K6t3LeftTT a a' b b' c c' d ∨ K20LeftPa a a' b b' c c' d ∨ K19LeftPc a a' b b' c c' d ∨
  K20LeftTa a a' b b' c c' d ∨ K17hLeftTc a a' b b' c c' d ∨
  K17B2LeftMN2 W ∨ K17LeftMKb W

theorem k20_slice_step {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d)
    (hNR : ¬ IsRupert (V8 a a' b b' c c' d)) (h : K19Slice W) :
    HasLexCell (V8 a a' b b' c c' d) ∨ K20Slice W := by
  rcases h with h | h | h | h | h | h | h
  · exact Or.inr (Or.inl h)
  · rcases k20z_Pa_step W hNR h with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · rcases k20z_Ta_step W hNR h with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))

def K20ResidP (a a' b b' c c' d : ℝ³) : Prop :=
  ∃ W : Norm08w a a' b b' c c' d, ResP W.F d ∧ K20Slice W

def K20ResidP6 (a a' b b' c c' d : ℝ³) : Prop :=
  K20ResidP a a' b b' c c' d ∨ K20ResidP b b' a a' c c' d ∨ K20ResidP a a' c c' b b' d ∨
  K20ResidP c c' a a' b b' d ∨ K20ResidP b b' c c' a a' d ∨ K20ResidP c c' b b' a a' d

/-- **`Resid08FinalK20`**: `Resid08FinalK19` with the S1.5 corner and S1.4 tie closed by Rupert. -/
def Resid08FinalK20 (a a' b b' c c' d : ℝ³) : Prop :=
  (PlanarTwo a a' b b' c c' ∨ PlanarGen a a' b b' c c' d) ∧ K20ResidP6 a a' b b' c c' d ∧
    ¬ HasLexCell (V8 a a' b b' c c' d)

theorem k20_residP_step {p p' q q' r r' d : ℝ³}
    (hNR : ¬ IsRupert (V8 p p' q q' r r' d)) (h : K19ResidP p p' q q' r r' d) :
    HasLexCell (V8 p p' q q' r r' d) ∨ K20ResidP p p' q q' r r' d := by
  obtain ⟨W, hR, hs⟩ := h
  rcases k20_slice_step W hNR hs with h | h
  · exact Or.inl h
  · exact Or.inr ⟨W, hR, h⟩

theorem resid08FinalK19_imp_K20 {a a' b b' c c' d : ℝ³}
    (hNR : ¬ IsRupert (V8 a a' b b' c c' d)) (h : Resid08FinalK19 a a' b b' c c' d) :
    Resid08FinalK20 a a' b b' c c' d := by
  obtain ⟨hpl, h6, hno⟩ := h
  have e := type08_set_perm a a' b b' c c' d
  refine ⟨hpl, ?_, hno⟩
  rcases h6 with h | h | h | h | h | h
  · rcases k20_residP_step hNR h with h | h
    · exact (hno h).elim
    · exact Or.inl h
  · rcases k20_residP_step (fun hR => hNR (by rw [V8, ← e.2.1]; exact hR)) h with h | h
    · exact (hno (by rw [V8, ← e.2.1]; exact h)).elim
    · exact Or.inr (Or.inl h)
  · rcases k20_residP_step (fun hR => hNR (by rw [V8, ← e.2.2.1]; exact hR)) h with h | h
    · exact (hno (by rw [V8, ← e.2.2.1]; exact h)).elim
    · exact Or.inr (Or.inr (Or.inl h))
  · rcases k20_residP_step (fun hR => hNR (by rw [V8, ← e.2.2.2.1]; exact hR)) h with h | h
    · exact (hno (by rw [V8, ← e.2.2.2.1]; exact h)).elim
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · rcases k20_residP_step (fun hR => hNR (by rw [V8, ← e.2.2.2.2.1]; exact hR)) h with h | h
    · exact (hno (by rw [V8, ← e.2.2.2.2.1]; exact h)).elim
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · rcases k20_residP_step (fun hR => hNR (by rw [V8, ← e.2.2.2.2.2]; exact hR)) h with h | h
    · exact (hno (by rw [V8, ← e.2.2.2.2.2]; exact h)).elim
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))

end Type08Sp
end Minimality
