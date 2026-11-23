module

public import Minimality.Type24SVCCellsLex5
public import Minimality.Type24SVCCellsTB_c01
public import Minimality.Type24TBLeaf_c01
public import Minimality.Type24SVCCellsTB_c03
public import Minimality.Type24TBLeaf_c03
public import Minimality.Type24SVCCellsTB_c12
public import Minimality.Type24TBLeaf_c12
public import Minimality.Type24SVCCellsTB_c14
public import Minimality.Type24TBLeaf_c14

@[expose] public section

/-!
# The four tie-free SVC cells (Task TB24B)

`cell_*_tb` are the cells `cell_*_lex` of `Type24SVCCellsLex_*` without the tie hypotheses
(`⟪x 2, w⟫ ≠ ⟪x 3, w⟫`, `⟪x 4, w⟫ ≠ ⟪x 5, w⟫` and their analogues): the per-rim tie-break rule
`svc_local_tb` constructs the tilt per weak order.
-/

set_option autoImplicit false

open scoped RealInnerProductSpace
open Minimality Minimality.H21 Minimality.SVCC Minimality.SVCC.Cells Minimality.SVCC.CellsLex Minimality.T24.SAT Minimality.SVC

namespace Minimality.SVCC.CellsTB

theorem cell_012_0345_zpmzppmpp_tb {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (w : ℝ³)
    (h0 : ⟪F.N 0, w⟫ = 0)
    (h1 : 0 < ⟪F.N 1, w⟫)
    (h2 : ⟪F.N 2, w⟫ < 0)
    (h3 : ⟪F.N 3, w⟫ = 0)
    (h4 : 0 < ⟪F.N 4, w⟫)
    (h5 : 0 < ⟪F.N 5, w⟫)
    (h6 : ⟪F.N 6, w⟫ < 0)
    (h7 : 0 < ⟪F.N 7, w⟫)
    (h8 : 0 < ⟪F.N 8, w⟫) :
    Gen.LexAny F := by
  have hT : ∀ ρ ∈ c01_R, ∀ t, t ∈ ρ.U ∨ t ∈ ρ.Dn → t ∈ ({0, 1, 2, 3, 4, 5, 6, 7, 8} : Finset (Fin 9)) := by decide
  have hsw : ∀ ρ ∈ c01_R, ∀ t, t ∈ ρ.U ∨ t ∈ ρ.Dn → SignType.sign ⟪F.N t, w⟫ = c01_sw t := by
    intro ρ hρ t ht
    have ht' := hT ρ hρ t ht
    clear ht hρ
    fin_cases t <;> simp at ht'
    · exact sign_eq_zero_iff.mpr h0
    · exact sign_pos h1
    · exact sign_neg h2
    · exact sign_eq_zero_iff.mpr h3
    · exact sign_pos h4
    · exact sign_pos h5
    · exact sign_neg h6
    · exact sign_pos h7
    · exact sign_pos h8
  have hR1 := hR_two F c01_sw c01_R 0 3 0 3 1 (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  have hR := hR_lex_of_hR F w c01_sw c01_R 1 0 h1.ne' h0 (by decide) hR1 rfl
  have hPinj : Function.Injective (fun i => x (c01_P i)) :=
    (EdgeViewLink.inj_of_fac24 F).comp (by decide : Function.Injective c01_P)
  have ht0 : ⟪F.N 1, w⟫ ≠ 0 := h1.ne'
  have hw0 : w ≠ 0 := fun h => ht0 (by rw [h, inner_zero_right])
  exact SVC.svc_local_tb F c01_P w c01_sw c01_R (by decide) hsw hR [] (fun _ h => by simp at h)
    c01_D (c01_dep F) hPinj c01_vacs (c01_hvac F hw0 h3 h0) c01_certs
    (c01_hreal F w h0 h3 ht0) c01_tbCheck

theorem cell_016_0345_pzpzmpppm_tb {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (w : ℝ³)
    (h0 : 0 < ⟪F.N 0, w⟫)
    (h1 : ⟪F.N 1, w⟫ = 0)
    (h2 : 0 < ⟪F.N 2, w⟫)
    (h3 : ⟪F.N 3, w⟫ = 0)
    (h4 : ⟪F.N 4, w⟫ < 0)
    (h5 : 0 < ⟪F.N 5, w⟫)
    (h6 : 0 < ⟪F.N 6, w⟫)
    (h7 : 0 < ⟪F.N 7, w⟫)
    (h8 : ⟪F.N 8, w⟫ < 0) :
    Gen.LexAny F := by
  have hT : ∀ ρ ∈ c03_R, ∀ t, t ∈ ρ.U ∨ t ∈ ρ.Dn → t ∈ ({0, 1, 2, 3, 4, 5, 6, 7, 8} : Finset (Fin 9)) := by decide
  have hsw : ∀ ρ ∈ c03_R, ∀ t, t ∈ ρ.U ∨ t ∈ ρ.Dn → SignType.sign ⟪F.N t, w⟫ = c03_sw t := by
    intro ρ hρ t ht
    have ht' := hT ρ hρ t ht
    clear ht hρ
    fin_cases t <;> simp at ht'
    · exact sign_pos h0
    · exact sign_eq_zero_iff.mpr h1
    · exact sign_pos h2
    · exact sign_eq_zero_iff.mpr h3
    · exact sign_neg h4
    · exact sign_pos h5
    · exact sign_pos h6
    · exact sign_pos h7
    · exact sign_neg h8
  have hR1 := hR_two F c03_sw c03_R 1 3 0 3 1 (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  have hR := hR_lex_of_hR F w c03_sw c03_R 0 1 h0.ne' h1 (by decide) hR1 rfl
  have hPinj : Function.Injective (fun i => x (c03_P i)) :=
    (EdgeViewLink.inj_of_fac24 F).comp (by decide : Function.Injective c03_P)
  have ht0 : ⟪F.N 0, w⟫ ≠ 0 := h0.ne'
  have hw0 : w ≠ 0 := fun h => ht0 (by rw [h, inner_zero_right])
  exact SVC.svc_local_tb F c03_P w c03_sw c03_R (by decide) hsw hR [] (fun _ h => by simp at h)
    c03_D (c03_dep F) hPinj c03_vacs (c03_hvac F hw0 h3 h1) c03_certs
    (c03_hreal F w h1 h3 ht0) c03_tbCheck

theorem cell_0345_236_ppmzppmzp_tb {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (w : ℝ³)
    (h0 : 0 < ⟪F.N 0, w⟫)
    (h2 : ⟪F.N 2, w⟫ < 0)
    (h3 : ⟪F.N 3, w⟫ = 0)
    (h4 : 0 < ⟪F.N 4, w⟫)
    (h5 : 0 < ⟪F.N 5, w⟫)
    (h6 : ⟪F.N 6, w⟫ < 0)
    (h7 : ⟪F.N 7, w⟫ = 0)
    (h8 : 0 < ⟪F.N 8, w⟫) :
    Gen.LexAny F := by
  have hT : ∀ ρ ∈ c12_R, ∀ t, t ∈ ρ.U ∨ t ∈ ρ.Dn → t ∈ ({0, 2, 3, 4, 5, 6, 7, 8} : Finset (Fin 9)) := by decide
  have hsw : ∀ ρ ∈ c12_R, ∀ t, t ∈ ρ.U ∨ t ∈ ρ.Dn → SignType.sign ⟪F.N t, w⟫ = c12_sw t := by
    intro ρ hρ t ht
    have ht' := hT ρ hρ t ht
    clear ht hρ
    fin_cases t <;> simp at ht'
    · exact sign_pos h0
    · exact sign_neg h2
    · exact sign_eq_zero_iff.mpr h3
    · exact sign_pos h4
    · exact sign_pos h5
    · exact sign_neg h6
    · exact sign_eq_zero_iff.mpr h7
    · exact sign_pos h8
  have hR1 := hR_two F c12_sw c12_R 3 7 3 2 0 (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  have hR := hR_lex_of_hR F w c12_sw c12_R 0 3 h0.ne' h3 (by decide) hR1 rfl
  have hPinj : Function.Injective (fun i => x (c12_P i)) :=
    (EdgeViewLink.inj_of_fac24 F).comp (by decide : Function.Injective c12_P)
  have ht0 : ⟪F.N 0, w⟫ ≠ 0 := h0.ne'
  have hw0 : w ≠ 0 := fun h => ht0 (by rw [h, inner_zero_right])
  exact SVC.svc_local_tb F c12_P w c12_sw c12_R (by decide) hsw hR [] (fun _ h => by simp at h)
    c12_D (c12_dep F) hPinj c12_vacs (c12_hvac F hw0 h3 h7) c12_certs
    (c12_hreal F w h3 h7 ht0) c12_tbCheck

theorem cell_0345_236_pppzmppzm_tb {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (w : ℝ³)
    (h1 : 0 < ⟪F.N 1, w⟫)
    (h2 : 0 < ⟪F.N 2, w⟫)
    (h3 : ⟪F.N 3, w⟫ = 0)
    (h4 : ⟪F.N 4, w⟫ < 0)
    (h5 : 0 < ⟪F.N 5, w⟫)
    (h6 : 0 < ⟪F.N 6, w⟫)
    (h7 : ⟪F.N 7, w⟫ = 0)
    (h8 : ⟪F.N 8, w⟫ < 0) :
    Gen.LexAny F := by
  have hT : ∀ ρ ∈ c14_R, ∀ t, t ∈ ρ.U ∨ t ∈ ρ.Dn → t ∈ ({1, 2, 3, 4, 5, 6, 7, 8} : Finset (Fin 9)) := by decide
  have hsw : ∀ ρ ∈ c14_R, ∀ t, t ∈ ρ.U ∨ t ∈ ρ.Dn → SignType.sign ⟪F.N t, w⟫ = c14_sw t := by
    intro ρ hρ t ht
    have ht' := hT ρ hρ t ht
    clear ht hρ
    fin_cases t <;> simp at ht'
    · exact sign_pos h1
    · exact sign_pos h2
    · exact sign_eq_zero_iff.mpr h3
    · exact sign_neg h4
    · exact sign_pos h5
    · exact sign_pos h6
    · exact sign_eq_zero_iff.mpr h7
    · exact sign_neg h8
  have hR1 := hR_two F c14_sw c14_R 3 7 3 2 0 (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  have hR := hR_lex_of_hR F w c14_sw c14_R 1 3 h1.ne' h3 (by decide) hR1 rfl
  have hPinj : Function.Injective (fun i => x (c14_P i)) :=
    (EdgeViewLink.inj_of_fac24 F).comp (by decide : Function.Injective c14_P)
  have ht0 : ⟪F.N 1, w⟫ ≠ 0 := h1.ne'
  have hw0 : w ≠ 0 := fun h => ht0 (by rw [h, inner_zero_right])
  exact SVC.svc_local_tb F c14_P w c14_sw c14_R (by decide) hsw hR [] (fun _ h => by simp at h)
    c14_D (c14_dep F) hPinj c14_vacs (c14_hvac F hw0 h3 h7) c14_certs
    (c14_hreal F w h3 h7 ht0) c14_tbCheck

end Minimality.SVCC.CellsTB
