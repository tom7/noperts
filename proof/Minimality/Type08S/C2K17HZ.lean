module

public import Minimality.Type08S.C2K17GCZ
public import Minimality.Type08S.C2K17GD5D
public import Minimality.Type08S.C2K17GD4C
public import Minimality.Type08S.C2K17GD3C
public import Minimality.Type08S.C2K17GD2F
public import Minimality.Type08S.C2K17GD1
public import Minimality.Type08S.C2K17GB12
public import Minimality.Type08S.C2K18B
public import Minimality.Type08S.C2K18C
public import Minimality.Type08S.C2K18D

@[expose] public section

/-!
# K17H / Z: composition.  The Ta and Tc tie slices cut by bundles A, B, D and K18.
-/
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
open C2

/-- Tc, `K6tTcA41`: `qr = ⟪b-d,c-d⟫ = 0 ∧ pr = ⟪a-d,c-d⟫ = 0` stays open. -/
def K17hTcA41 (a a' b b' c c' d : ℝ³) : Prop :=
  K5ZsTc a a' b b' c c' d ∧ K6tTcA41 a a' b b' c c' d ∧ ⟪b - d, c - d⟫ = 0 ∧ ⟪a - d, c - d⟫ = 0

/-- Tc, Zdb(i) (`ζ(c',c) = 0`): the `β1 = 1` corner `ζ_{c'-b}(d,b) = 0 ∧ pq = 0` stays open. -/
def K17hTcZ1 (a a' b b' c c' d : ℝ³) : Prop :=
  K17fZdbTc a a' b b' c c' d ∧ ⟪c' - c, a - b'⟫ = 0 ∧ ⟪d - b, c' - b⟫ = 0 ∧ ⟪a - d, b - d⟫ = 0

def K17hLeftTc (a a' b b' c c' d : ℝ³) : Prop :=
  K17hTcA41 a a' b b' c c' d ∨ K17hTcZ1 a a' b b' c c' d

/-- Ta, `K6t4B11`: `pr = ⟪a-d,c-d⟫ = 0` stays open. -/
def K17hTaB11 (a a' b b' c c' d : ℝ³) : Prop :=
  (K5ZsTouch a a' b b' c c' d ∨ K5ZsTa a a' b b' c c' d) ∧ K6t4B11 a a' b b' c c' d ∧ ⟪a - d, c - d⟫ = 0

/-- Ta, `K6tTaA41`: `qr = 0` (so `ζ(d,b) = 0`) and `⟪a-b',a-c'⟫ = 0` stay open. -/
def K17hTaA41 (a a' b b' c c' d : ℝ³) : Prop :=
  (K5ZsTouch a a' b b' c c' d ∨ K5ZsTa a a' b b' c c' d) ∧ K6tTaA41 a a' b b' c c' d ∧
    ⟪b - d, c - d⟫ = 0 ∧ ⟪a - b', a - c'⟫ = 0

def K17hLeftTa (a a' b b' c c' d : ℝ³) : Prop :=
  K17hTaB11 a a' b b' c c' d ∨ K17hTaA41 a a' b b' c c' d

theorem k17h_zeta_of_qr {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) (hT : IsT a' b c d)
    (h : det3 (b' - a) (b - d) (c - d) = 0) (hqr : ⟪b - d, c - d⟫ = 0) : ⟪d - b, a - b'⟫ = 0 := by
  obtain ⟨α1, α4, β1, γ4, β6, hdet, hc', hb', ha', -⟩ := norm08w_coordsT W hT
  rw [det_alpha4 hb'] at h
  have hα41 : α4 = 1 := by
    rcases mul_eq_zero.1 h with h | h
    · linarith
    · exact absurd h hdet
  have e1 : a - b' = (-γ4) • (c - d) := by rw [hb', hα41]; module
  have e2 : d - b = -(b - d) := by abel
  rw [e1, e2, inner_neg_left, inner_smul_right, hqr]; simp

theorem k17h_Tc_step {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) (h : K17fLeftTc' a a' b b' c c' d) :
    HasLexCell (V8 a a' b b' c c' d) ∨ K17hLeftTc a a' b b' c c' d := by
  obtain ⟨hctx, hL⟩ := id h
  have hT := hctx.1
  have hT' := hctx.2.1
  have hfar := k5z_far2 W hT hT'
  have hκb := k5z_kb_pos W hT hT'
  rcases hL with hA | hZ
  · rcases k17gd_tca41 W hA hfar hκb with h1 | ⟨h1, h2⟩
    · exact Or.inl h1
    · exact Or.inr (Or.inl ⟨hctx, hA, h1, h2⟩)
  · rcases hZ.2.2.2 with hz1 | hZ2
    · rcases k18_s11_tc W hZ hz1 with h1 | ⟨h1, h2⟩
      · exact Or.inl h1
      · exact Or.inr (Or.inr ⟨hZ, hz1, h1, h2⟩)
    · exact Or.inl (k18_s12_tc W hZ hZ2)

set_option maxHeartbeats 3200000 in
theorem k17h_Ta_step {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) (h : K17fLeftTa14 a a' b b' c c' d) :
    HasLexCell (V8 a a' b b' c c' d) ∨ K17hLeftTa a a' b b' c c' d := by
  obtain ⟨hctx, hL⟩ := id h
  have hT : IsT a' b c d := hctx.elim (fun h => h.1) (fun h => h.1)
  have hT' : ¬ IsT' a b c' d := hctx.elim (fun h => h.2.1) (fun h => h.2.1)
  have hfar := k5z_far2 W hT hT'
  obtain ⟨-, -, -, -, -, hdet, -⟩ := norm08w_coordsT W hT
  rcases hL with hB | hZ | hC | hA | hE
  · rcases k17gd_b11 W hB hfar with h1 | h1
    · exact Or.inl h1
    · exact Or.inr (Or.inl ⟨hctx, hB, h1⟩)
  · have hZ' : K6t4Zdb0 a a' b b' c c' d := hZ.2.2.2.2
    rcases hZ'.2 with hz1 | hZ2
    · exact Or.inl (k18_s11_ta W hZ hz1)
    · exact Or.inl (k18_s12_ta W hZ hZ2)
  · rcases k17gd_taC W hC hfar with h1 | h1
    · exact Or.inl h1
    · exact Or.inl (k18_s18 W hT' hC h1)
  · rcases k17gd_taA41 W hA hfar with h1 | hqr
    · exact Or.inl h1
    · have hz : ⟪d - b, a - b'⟫ = 0 := k17h_zeta_of_qr W hT hA.2.2.2.1 hqr
      rcases lt_trichotomy ⟪a - b', a - c'⟫ 0 with hl | hl | hl
      · -- lit < 0: S1.3b (beta6 > 1) or S1.4b (beta6 = 1)
        have hb6 := hA.2.2.2.2
        by_cases h6 : det3 (a' - b) (c - d) (a - d) = 0
        · rcases k17gb_s14b W hT' hA hz h6 with h1 | h1
          · exact Or.inl h1
          · exact absurd h1 (not_le.2 hl)
        · have h6' : 0 < det3 (a' - b) (c - d) (a - d) * det3 (a - d) (b - d) (c - d) :=
            lt_of_le_of_ne hb6 (fun e => h6 ((mul_eq_zero.1 e.symm).resolve_right hdet))
          rcases k17gb_s13b W hT' hA hz h6' with h1 | h1
          · exact Or.inl h1
          · exact absurd h1 (not_le.2 hl)
      · exact Or.inr (Or.inr ⟨hctx, hA, hqr, hl⟩)
      · exact Or.inl (k17ga_s13a W hT' hA hz hl)
  · rcases k17gd_taE W hE hfar with h1 | h1
    · exact Or.inl h1
    · exact Or.inl (k17gb_s19 W hT' hE h1)

def K17HSlice {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) : Prop :=
  K6t3LeftTT a a' b b' c c' d ∨ K17gcLeftPa a a' b b' c c' d ∨ K17gcLeftPc a a' b b' c c' d ∨
  K17hLeftTa a a' b b' c c' d ∨ K17hLeftTc a a' b b' c c' d ∨
  K17B2LeftMN2 W ∨ K6sDN2one a a' b b' c c' d ∨ K17LeftMKb W

theorem k17h_slice_step {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) (h : K17GSlice W) :
    HasLexCell (V8 a a' b b' c c' d) ∨ K17HSlice W := by
  rcases h with h | h | h | h | h | h | h | h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · rcases k17h_Ta_step W h with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · rcases k17h_Tc_step W h with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))

def K17HResidP (a a' b b' c c' d : ℝ³) : Prop :=
  ∃ W : Norm08w a a' b b' c c' d, ResP W.F d ∧ K17HSlice W

def K17HResidP6 (a a' b b' c c' d : ℝ³) : Prop :=
  K17HResidP a a' b b' c c' d ∨ K17HResidP b b' a a' c c' d ∨ K17HResidP a a' c c' b b' d ∨
  K17HResidP c c' a a' b b' d ∨ K17HResidP b b' c c' a a' d ∨ K17HResidP c c' b b' a a' d

/-- **`Resid08FinalK17H`**: `Resid08FinalK17G` with the Ta and Tc slices cut by bundles A, B, D and K18. -/
def Resid08FinalK17H (a a' b b' c c' d : ℝ³) : Prop :=
  (PlanarTwo a a' b b' c c' ∨ PlanarGen a a' b b' c c' d) ∧ K17HResidP6 a a' b b' c c' d ∧
    ¬ HasLexCell (V8 a a' b b' c c' d)

theorem k17h_residP_step {p p' q q' r r' d : ℝ³} (h : K17GResidP p p' q q' r r' d) :
    HasLexCell (V8 p p' q q' r r' d) ∨ K17HResidP p p' q q' r r' d := by
  obtain ⟨W, hR, hs⟩ := h
  rcases k17h_slice_step W hs with h | h
  · exact Or.inl h
  · exact Or.inr ⟨W, hR, h⟩

theorem resid08FinalK17G_imp_K17H {a a' b b' c c' d : ℝ³}
    (h : Resid08FinalK17G a a' b b' c c' d) : Resid08FinalK17H a a' b b' c c' d := by
  obtain ⟨hpl, h6, hno⟩ := h
  have e := type08_set_perm a a' b b' c c' d
  refine ⟨hpl, ?_, hno⟩
  rcases h6 with h | h | h | h | h | h
  · rcases k17h_residP_step h with h | h
    · exact (hno h).elim
    · exact Or.inl h
  · rcases k17h_residP_step h with h | h
    · exact (hno (by rw [V8, ← e.2.1]; exact h)).elim
    · exact Or.inr (Or.inl h)
  · rcases k17h_residP_step h with h | h
    · exact (hno (by rw [V8, ← e.2.2.1]; exact h)).elim
    · exact Or.inr (Or.inr (Or.inl h))
  · rcases k17h_residP_step h with h | h
    · exact (hno (by rw [V8, ← e.2.2.2.1]; exact h)).elim
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · rcases k17h_residP_step h with h | h
    · exact (hno (by rw [V8, ← e.2.2.2.2.1]; exact h)).elim
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · rcases k17h_residP_step h with h | h
    · exact (hno (by rw [V8, ← e.2.2.2.2.2]; exact h)).elim
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))

end Type08Sp
end Minimality
