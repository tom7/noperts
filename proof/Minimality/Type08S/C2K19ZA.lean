module

public import Minimality.Type08S.C2K17AZ
public import Minimality.Type08S.C2K19G

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

/-- Pa after K19: `K17fLeftPa` and one of the four remaining ties. -/
def K19LeftPa (a a' b b' c c' d : ℝ³) : Prop :=
  K17fLeftPa a a' b b' c c' d ∧
  ((⟪a - d, c - d⟫ = 0 ∧ det3 (b' - a) (b - d) (c - d) = 0 ∧ det3 (a - d) (c' - b) (c - d) = 0) ∨
   (⟪a - d, c - d⟫ = 0 ∧ det3 (b' - a) (b - d) (c - d) * det3 (a - d) (b - d) (c - d) < 0 ∧
     (det3 (a - d) (c' - b) (c - d) = 0 ∨ det3 (c' - a') (b' - a') (a - d) = 0)) ∨
   (⟪a - d, c - d⟫ = 0 ∧ det3 (b' - a) (b - d) (c - d) * det3 (a - d) (b - d) (c - d) < 0 ∧
     det3 (a - d) (c' - b) (c - d) * det3 (a - d) (b - d) (c - d) = 0 ∧
     (⟪a' - b, a' - c⟫ = 0 ∨ (⟪a' - b, a' - c⟫ < 0 ∧ ⟪a' - b, b - d⟫ = 0))) ∨
   (⟪a - d, a - c'⟫ = 0 ∧ det3 (b' - a) (b - d) (c - d) = 0 ∧
     det3 (a - d) (c' - b) (c - d) * det3 (a - d) (b - d) (c - d) = 0))

/-- Pc after K19. -/
def K19LeftPc (a a' b b' c c' d : ℝ³) : Prop :=
  K6t3LeftPc a a' b b' c c' d ∧
    ((⟪a - d, a - c'⟫ = 0 ∧ (⟪b - d, c - d⟫ = 0 ∨ ⟪b' - c, d - b⟫ = 0 ∨ ⟪b' - c', d - b⟫ = 0)) ∨
     (0 < ⟪a - d, a - c'⟫ ∧ ⟪c - d, c - a'⟫ = 0 ∧ ⟪b' - c, d - b⟫ = 0) ∨
     (⟪a - d, a - c'⟫ < 0 ∧ ⟪c - b', d - b⟫ = 0 ∧ ⟪c - b', c - d⟫ = 0))

/-- Ta after K19: B11 as before; A41 (`qr = 0`, `⟪a-b',a-c'⟫ = 0`) with `β6 = 1` (S1.4) or the S1.3 tie. -/
def K19LeftTa (a a' b b' c c' d : ℝ³) : Prop :=
  K17hTaB11 a a' b b' c c' d ∨
  (K17hTaA41 a a' b b' c c' d ∧
    (det3 (a' - b) (c - d) (a - d) * det3 (a - d) (b - d) (c - d) = 0 ∨ ⟪a - d, a - c'⟫ = 0))

theorem k19z_Pa_step {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d)
    (h : K17gcLeftPa a a' b b' c c' d) :
    HasLexCell (V8 a a' b b' c c' d) ∨ K19LeftPa a a' b b' c c' d := by
  obtain ⟨h, -⟩ := h
  obtain ⟨hctx, hL⟩ := id h
  obtain ⟨hT', hnT, hκ, -⟩ := id hctx
  have hfar := k5z_far1 W hT' hnT
  obtain ⟨-, -, -, -, -, hdet, -⟩ := norm08w_coordsTp W hT'
  rcases hL with ⟨h1, h2, hα⟩ | ⟨h0, hα, hβ0, hβ⟩ | ⟨hα, hβ0, hβ⟩
  · rcases k17gc_u1 W hctx h1 h2 hα with h3 | hpr
    · exact Or.inl h3
    · rcases hα.eq_or_lt with he | hlt
      · have hα0 : det3 (b' - a) (b - d) (c - d) = 0 :=
          (mul_eq_zero.1 he).resolve_right hdet
        rcases k19_u1_eq W hctx h1 h2 hα0 hpr with h4 | h4
        · exact Or.inl h4
        · exact Or.inr ⟨h, Or.inl ⟨hpr, hα0, h4⟩⟩
      · rcases k19_u1_lt W hctx h1 h2 hlt hpr with h4 | h4 | h4
        · exact Or.inl h4
        · exact Or.inr ⟨h, Or.inr (Or.inl ⟨hpr, hlt, Or.inl h4⟩)⟩
        · exact Or.inr ⟨h, Or.inr (Or.inl ⟨hpr, hlt, Or.inr h4⟩)⟩
  · rcases hβ0.eq_or_lt with he | hlt
    · rcases k17f_s17 W hT' hκ hfar h0 hα he.symm with h3 | hpr
      · exact Or.inl h3
      · rcases k19_s17_tie W hT' hκ hfar h0 hα he.symm hpr with h4 | h4
        · exact Or.inl h4
        · exact Or.inr ⟨h, Or.inr (Or.inr (Or.inl ⟨hpr, hα, he.symm, h4⟩))⟩
    · rcases hβ with he | hpq
      · exact absurd he (ne_of_gt hlt)
      · exact Or.inl (k17gc_u2 W hctx h0 hα hlt hpq)
  · rcases hβ0.eq_or_lt with he | hlt
    · rcases k17gc_s15 W hctx hα he.symm with h3 | hZ
      · exact Or.inl h3
      · exact Or.inr ⟨h, Or.inr (Or.inr (Or.inr ⟨hZ, hα, he.symm⟩))⟩
    · rcases hβ with he | h0
      · exact absurd he (ne_of_gt hlt)
      · rcases k17gc_u3 W hctx hα hlt h0 with h3 | hZ
        · exact Or.inl h3
        · exact Or.inl (k19_u3_closed W hctx hα hlt h0 hZ)

theorem k19z_Pc_step {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d)
    (h : K17gcLeftPc a a' b b' c c' d) :
    HasLexCell (V8 a a' b b' c c' d) ∨ K19LeftPc a a' b b' c c' d := by
  obtain ⟨h, hL⟩ := h
  rcases hL with hZ | ⟨hp, hw⟩ | ⟨hn, h1, h2⟩
  · rcases k19_s16_pq0 W h hZ with h3 | h3 | h3 | h3
    · exact Or.inl h3
    · exact Or.inr ⟨h, Or.inl ⟨hZ, Or.inl h3⟩⟩
    · exact Or.inr ⟨h, Or.inl ⟨hZ, Or.inr (Or.inl h3)⟩⟩
    · exact Or.inr ⟨h, Or.inl ⟨hZ, Or.inr (Or.inr h3)⟩⟩
  · rcases k19_s16w W h hp hw with h3 | h3
    · exact Or.inl h3
    · exact Or.inr ⟨h, Or.inr (Or.inl ⟨hp, hw, h3⟩)⟩
  · exact Or.inr ⟨h, Or.inr (Or.inr ⟨hn, h1, h2⟩)⟩

theorem k19z_Ta_step {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d)
    (h : K17hLeftTa a a' b b' c c' d) :
    HasLexCell (V8 a a' b b' c c' d) ∨ K19LeftTa a a' b b' c c' d := by
  rcases h with hB | hA
  · exact Or.inr (Or.inl hB)
  · obtain ⟨hctx, hA', hqr, hl⟩ := id hA
    have hT : IsT a' b c d := hctx.elim (fun h => h.1) (fun h => h.1)
    have hT' : ¬ IsT' a b c' d := hctx.elim (fun h => h.2.1) (fun h => h.2.1)
    obtain ⟨-, -, -, -, -, hdet, -⟩ := norm08w_coordsT W hT
    have hz : ⟪d - b, a - b'⟫ = 0 := k17h_zeta_of_qr W hT hA'.2.2.2.1 hqr
    have hb6 := hA'.2.2.2.2
    rcases hb6.eq_or_lt with he | hlt
    · exact Or.inr (Or.inr ⟨hA, Or.inl he.symm⟩)
    · rcases k19_s13_tie W hT' hA' hz hlt hl with h1 | h1
      · exact Or.inl h1
      · exact Or.inr (Or.inr ⟨hA, Or.inr h1⟩)

def K19Slice {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) : Prop :=
  K6t3LeftTT a a' b b' c c' d ∨ K19LeftPa a a' b b' c c' d ∨ K19LeftPc a a' b b' c c' d ∨
  K19LeftTa a a' b b' c c' d ∨ K17hLeftTc a a' b b' c c' d ∨
  K17B2LeftMN2 W ∨ K17LeftMKb W

theorem k19_slice_step {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) (h : K17ISlice W) :
    HasLexCell (V8 a a' b b' c c' d) ∨ K19Slice W := by
  rcases h with h | h | h | h | h | h | h
  · exact Or.inr (Or.inl h)
  · rcases k19z_Pa_step W h with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inl h))
  · rcases k19z_Pc_step W h with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · rcases k19z_Ta_step W h with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))

def K19ResidP (a a' b b' c c' d : ℝ³) : Prop :=
  ∃ W : Norm08w a a' b b' c c' d, ResP W.F d ∧ K19Slice W

def K19ResidP6 (a a' b b' c c' d : ℝ³) : Prop :=
  K19ResidP a a' b b' c c' d ∨ K19ResidP b b' a a' c c' d ∨ K19ResidP a a' c c' b b' d ∨
  K19ResidP c c' a a' b b' d ∨ K19ResidP b b' c c' a a' d ∨ K19ResidP c c' b b' a a' d

/-- **`Resid08FinalK19`**: `Resid08FinalK17I` with the K19 ties applied to the Pa, Pc and Ta slices. -/
def Resid08FinalK19 (a a' b b' c c' d : ℝ³) : Prop :=
  (PlanarTwo a a' b b' c c' ∨ PlanarGen a a' b b' c c' d) ∧ K19ResidP6 a a' b b' c c' d ∧
    ¬ HasLexCell (V8 a a' b b' c c' d)

theorem k19_residP_step {p p' q q' r r' d : ℝ³} (h : K17IResidP p p' q q' r r' d) :
    HasLexCell (V8 p p' q q' r r' d) ∨ K19ResidP p p' q q' r r' d := by
  obtain ⟨W, hR, hs⟩ := h
  rcases k19_slice_step W hs with h | h
  · exact Or.inl h
  · exact Or.inr ⟨W, hR, h⟩

theorem resid08FinalK17I_imp_K19 {a a' b b' c c' d : ℝ³}
    (h : Resid08FinalK17I a a' b b' c c' d) : Resid08FinalK19 a a' b b' c c' d := by
  obtain ⟨hpl, h6, hno⟩ := h
  have e := type08_set_perm a a' b b' c c' d
  refine ⟨hpl, ?_, hno⟩
  rcases h6 with h | h | h | h | h | h
  · rcases k19_residP_step h with h | h
    · exact (hno h).elim
    · exact Or.inl h
  · rcases k19_residP_step h with h | h
    · exact (hno (by rw [V8, ← e.2.1]; exact h)).elim
    · exact Or.inr (Or.inl h)
  · rcases k19_residP_step h with h | h
    · exact (hno (by rw [V8, ← e.2.2.1]; exact h)).elim
    · exact Or.inr (Or.inr (Or.inl h))
  · rcases k19_residP_step h with h | h
    · exact (hno (by rw [V8, ← e.2.2.2.1]; exact h)).elim
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · rcases k19_residP_step h with h | h
    · exact (hno (by rw [V8, ← e.2.2.2.2.1]; exact h)).elim
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · rcases k19_residP_step h with h | h
    · exact (hno (by rw [V8, ← e.2.2.2.2.2]; exact h)).elim
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))

end Type08Sp
end Minimality
