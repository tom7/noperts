module

public import Minimality.R012W

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped RealInnerProductSpace Topology
open Filter Finset
open Minimality Minimality.H21 Minimality.FaceChord Minimality.T24.SAT Minimality.RimFromSigns
open Minimality.T24.Q45 Minimality.T24.R012

namespace Minimality.T24.R012
variable {x : Fin 7 → ℝ³}

/-- Root of the 0345 facet (`N3`) on the 012 chord line `u0 t = (x0 - x1) + t (x2 - x1)`. -/
noncomputable def t3_f0345 (F : S0xFac 9 s0x_S24 x) : ℝ :=
  - ⟪F.N 3, x 0 - x 1⟫ / ⟪F.N 3, x 2 - x 1⟫

theorem rf0345_inner_N3 (F : S0xFac 9 s0x_S24 x) (t : ℝ) :
    ⟪F.N 3, u0 x t⟫ = ⟪F.N 3, x 0 - x 1⟫ + t * ⟪F.N 3, x 2 - x 1⟫ := by
  simp only [u0, inner_add_right, real_inner_smul_right]

/-- For `0 < t3`: `N3` vanishes at `u0 t3` and decreases strictly along the chord line. -/
theorem rf0345_t3 (F : S0xFac 9 s0x_S24 x) (h : 0 < t3_f0345 F) :
    ⟪F.N 3, u0 x (t3_f0345 F)⟫ = 0 ∧ ⟪F.N 3, x 2 - x 1⟫ < 0 := by
  have ha : 0 < ⟪F.N 3, x 0 - x 1⟫ := by
    have h0 := inner_N3_u0 F 0
    rw [rf0345_inner_N3] at h0
    have := lambda3_pos F
    unfold lambda3 at this
    linarith
  have hs : ⟪F.N 3, x 2 - x 1⟫ < 0 := by
    by_contra hn
    push Not at hn
    have : t3_f0345 F ≤ 0 := by
      unfold t3_f0345
      rcases hn.eq_or_lt with h0 | h0
      · rw [← h0]; simp
      · exact (div_neg_of_neg_of_pos (by linarith) h0).le
    linarith
  refine ⟨?_, hs⟩
  rw [rf0345_inner_N3]; unfold t3_f0345
  have := hs.ne
  field_simp; ring

/-- Lo side: rim `(0,4,3,2)` at `u0 (t3 - ε)`. Uses `0 < t3`, `N4 < 0`, `N8 < 0`, `N7 < 0`, `0 < N6` at `t3`
and the base inequality "not `{0,3}`-high". (`N2 > 0`, `N5 < 0`, `N3 > 0` are automatic.) -/
theorem q012_f0345_lo (F : S0xFac 9 s0x_S24 x)
    (ht : 0 < t3_f0345 F)
    (hN4 : ⟪F.N 4, u0 x (t3_f0345 F)⟫ < 0)
    (hN7 : ⟪F.N 7, u0 x (t3_f0345 F)⟫ < 0)
    (hN6 : 0 < ⟪F.N 6, u0 x (t3_f0345 F)⟫)
    (hN8 : ⟪F.N 8, u0 x (t3_f0345 F)⟫ < 0)
    (hbase : min ⟪x 0, u0 x (t3_f0345 F)⟫ ⟪x 3, u0 x (t3_f0345 F)⟫ <
      max ⟪x 4, u0 x (t3_f0345 F)⟫ ⟪x 2, u0 x (t3_f0345 F)⟫)
    (hfar : F.f 0 (x 4) ≠ F.f 0 (x 3))
    (hoff4 : F.f 0 (x 4) < F.f 0 (x 3) → Off012 F 4)
    (hoff3 : F.f 0 (x 3) < F.f 0 (x 4) → Off012 F 3)
    (hgen : Gen4 (quad (x 0) (x 4) (x 3) (x 2)) (u0 x (t3_f0345 F)) (x 2 - x 1)) :
    FaceChordView F 0 := by
  obtain ⟨hz, hs⟩ := rf0345_t3 F ht
  refine leaf_core012 F (t3_f0345 F) (-1) (Or.inr rfl) ht 4 3 5 6 4 3 8 3 7 6 (by decide)
    (Or.inr (Or.inr (Or.inr rfl))) ?_ (Or.inr ⟨kap2 F, hbase⟩) hgen (hw_of_ne F 4 3 hfar hoff4 hoff3)
  filter_upwards [ev_neg_u0 (F.N 4) _ (-1) (Or.inl hN4),
    ev_pos_u0 (F.N 3) _ (-1) (Or.inr ⟨hz, by linarith⟩),
    ev_neg_u0 (F.N 8) _ (-1) (Or.inl hN8), ev_pos_u0 (F.N 6) _ (-1) (Or.inl hN6),
    ev_neg_u0 (F.N 7) _ (-1) (Or.inl hN7)] with ε h4 h3 h8 h6 h7
  exact ⟨⟨h4, h3⟩, ⟨h8, h3⟩, ⟨h7, h6⟩⟩

/-- Hi side: rim `(0,5,3,2)` at `u0 (t3 + ε)`. Uses `0 < t3`, `N7 < 0`, `0 < N6` at `t3` and the base
inequality "not `{5,2}`-high". (`N4`, `N8` are not needed: vertex 4 is hidden by the facets 3, 6, 7.) -/
theorem q012_f0345_hi (F : S0xFac 9 s0x_S24 x)
    (ht : 0 < t3_f0345 F)
    (hN7 : ⟪F.N 7, u0 x (t3_f0345 F)⟫ < 0)
    (hN6 : 0 < ⟪F.N 6, u0 x (t3_f0345 F)⟫)
    (hbase : min ⟪x 5, u0 x (t3_f0345 F)⟫ ⟪x 2, u0 x (t3_f0345 F)⟫ <
      max ⟪x 0, u0 x (t3_f0345 F)⟫ ⟪x 3, u0 x (t3_f0345 F)⟫)
    (hfar : F.f 0 (x 5) ≠ F.f 0 (x 3))
    (hoff5 : F.f 0 (x 5) < F.f 0 (x 3) → Off012 F 5)
    (hoff3 : F.f 0 (x 3) < F.f 0 (x 5) → Off012 F 3)
    (hgen : Gen4 (quad (x 0) (x 5) (x 3) (x 2)) (u0 x (t3_f0345 F)) (x 2 - x 1)) :
    FaceChordView F 0 := by
  obtain ⟨hz, hs⟩ := rf0345_t3 F ht
  have hN2 : 0 < ⟪F.N 2, u0 x (t3_f0345 F)⟫ := by
    rw [inner_N2_u0]; exact mul_pos (lambda2_pos F) (by linarith)
  refine leaf_core012 F (t3_f0345 F) 1 (Or.inl rfl) ht 5 3 4 6 3 2 3 6 7 6 (by decide)
    (Or.inr (Or.inr (Or.inr rfl))) ?_ (Or.inl ⟨kap3 F, hbase⟩) hgen (hw_of_ne F 5 3 hfar hoff5 hoff3)
  filter_upwards [ev_neg_u0 (F.N 3) _ 1 (Or.inr ⟨hz, by linarith⟩), ev_pos_u0 (F.N 2) _ 1 (Or.inl hN2),
    ev_pos_u0 (F.N 6) _ 1 (Or.inl hN6), ev_neg_u0 (F.N 7) _ 1 (Or.inl hN7)] with ε h3 h2 h6 h7
  exact ⟨⟨h3, h2⟩, ⟨h3, h6⟩, ⟨h7, h6⟩⟩

/-- **Leaf `q012_f0345`** (cross-facet flip at the root `t3` of facet 0345 on the 012 circle).
`Case_f0345` is `ht ∧ hN4 ∧ hN7 ∧ hN6 ∧ hN8`; excluded loci: the triple tie `z0 = z2 = z3` at `u0 t3`
(`htie`), the far-vertex ties and foot-off-chord conditions of both rims, and the depth/direction
genericity of both 4-rims. -/
theorem q012_f0345 (F : S0xFac 9 s0x_S24 x)
    (ht : 0 < t3_f0345 F)
    (hN4 : ⟪F.N 4, u0 x (t3_f0345 F)⟫ < 0)
    (hN7 : ⟪F.N 7, u0 x (t3_f0345 F)⟫ < 0)
    (hN6 : 0 < ⟪F.N 6, u0 x (t3_f0345 F)⟫)
    (hN8 : ⟪F.N 8, u0 x (t3_f0345 F)⟫ < 0)
    (htie : ¬ (⟪x 0, u0 x (t3_f0345 F)⟫ = ⟪x 2, u0 x (t3_f0345 F)⟫ ∧
      ⟪x 2, u0 x (t3_f0345 F)⟫ = ⟪x 3, u0 x (t3_f0345 F)⟫))
    (hfar43 : F.f 0 (x 4) ≠ F.f 0 (x 3))
    (hoff4 : F.f 0 (x 4) < F.f 0 (x 3) → Off012 F 4)
    (hoff3 : F.f 0 (x 3) < F.f 0 (x 4) → Off012 F 3)
    (hgenLo : Gen4 (quad (x 0) (x 4) (x 3) (x 2)) (u0 x (t3_f0345 F)) (x 2 - x 1))
    (hfar53 : F.f 0 (x 5) ≠ F.f 0 (x 3))
    (hoff5 : F.f 0 (x 5) < F.f 0 (x 3) → Off012 F 5)
    (hoff3' : F.f 0 (x 3) < F.f 0 (x 5) → Off012 F 3)
    (hgenHi : Gen4 (quad (x 0) (x 5) (x 3) (x 2)) (u0 x (t3_f0345 F)) (x 2 - x 1)) :
    FaceChordView F 0 := by
  by_cases hlo : min ⟪x 0, u0 x (t3_f0345 F)⟫ ⟪x 3, u0 x (t3_f0345 F)⟫ <
      max ⟪x 4, u0 x (t3_f0345 F)⟫ ⟪x 2, u0 x (t3_f0345 F)⟫
  · exact q012_f0345_lo F ht hN4 hN7 hN6 hN8 hlo hfar43 hoff4 hoff3 hgenLo
  · by_cases hhi : min ⟪x 5, u0 x (t3_f0345 F)⟫ ⟪x 2, u0 x (t3_f0345 F)⟫ <
        max ⟪x 0, u0 x (t3_f0345 F)⟫ ⟪x 3, u0 x (t3_f0345 F)⟫
    · exact q012_f0345_hi F ht hN7 hN6 hhi hfar53 hoff5 hoff3' hgenHi
    · exfalso
      apply htie
      push Not at hlo hhi
      have a2 : ⟪x 2, u0 x (t3_f0345 F)⟫ ≤ ⟪x 0, u0 x (t3_f0345 F)⟫ :=
        le_trans (le_max_right _ _) (le_trans hlo (min_le_left _ _))
      have a3 : ⟪x 2, u0 x (t3_f0345 F)⟫ ≤ ⟪x 3, u0 x (t3_f0345 F)⟫ :=
        le_trans (le_max_right _ _) (le_trans hlo (min_le_right _ _))
      have b2 : ⟪x 0, u0 x (t3_f0345 F)⟫ ≤ ⟪x 2, u0 x (t3_f0345 F)⟫ :=
        le_trans (le_max_left _ _) (le_trans hhi (min_le_right _ _))
      have b3 : ⟪x 3, u0 x (t3_f0345 F)⟫ ≤ ⟪x 2, u0 x (t3_f0345 F)⟫ :=
        le_trans (le_max_right _ _) (le_trans hhi (min_le_right _ _))
      exact ⟨le_antisymm b2 a2, le_antisymm a3 b3⟩

end Minimality.T24.R012
