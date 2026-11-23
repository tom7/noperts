module

public import Minimality.Type24SVCCellsLex5

@[expose] public section

set_option autoImplicit false

open scoped RealInnerProductSpace
open Minimality Minimality.H21 Minimality.SVCC Minimality.SVCC.Cells Minimality.T24.SAT

namespace Minimality.SVCC.CellsLex

theorem c16_checkW :
    SVC.checkW s0x_S24 c16_P c16_sw [] c16_D c16_R (allPairs 6) = true := by
  decide +kernel

theorem cell_046_235_pppmzpzpp_lex {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (w : ℝ³)
    (h1 : 0 < ⟪F.N 1, w⟫)
    (h2 : 0 < ⟪F.N 2, w⟫)
    (h3 : ⟪F.N 3, w⟫ < 0)
    (h4 : ⟪F.N 4, w⟫ = 0)
    (h6 : ⟪F.N 6, w⟫ = 0)
    (h7 : 0 < ⟪F.N 7, w⟫)
    (h8 : 0 < ⟪F.N 8, w⟫)
    (hD : ⟪F.N 4, F.N 4⟫ * ⟪F.N 6, F.N 6⟫ - ⟪F.N 4, F.N 6⟫ ^ 2 ≠ 0) :
    Gen.LexAny F := by
  have hT : ∀ ρ ∈ c16_R, ∀ t, t ∈ ρ.U ∨ t ∈ ρ.Dn → t ∈ ({1, 2, 3, 4, 6, 7, 8} : Finset (Fin 9)) := by decide
  have hsw : ∀ ρ ∈ c16_R, ∀ t, t ∈ ρ.U ∨ t ∈ ρ.Dn → SignType.sign ⟪F.N t, w⟫ = c16_sw t := by
    intro ρ hρ t ht
    have ht' := hT ρ hρ t ht
    clear ht hρ
    fin_cases t <;> simp at ht'
    · exact sign_pos h1
    · exact sign_pos h2
    · exact sign_neg h3
    · exact sign_eq_zero_iff.mpr h4
    · exact sign_eq_zero_iff.mpr h6
    · exact sign_pos h7
    · exact sign_pos h8
  have hR1 := hR_gram F c16_sw c16_R 4 6 hD (by decide)
  have hR := hR_lex_of_hR F w c16_sw c16_R 1 4 h1.ne' h4 (by decide) hR1 rfl
  have hPinj : Function.Injective (fun i => x (c16_P i)) :=
    (EdgeViewLink.inj_of_fac24 F).comp (by decide : Function.Injective c16_P)
  exact SVC.svc_local_lex F c16_P w c16_sw c16_R (by decide) hsw hR [] (fun _ h => by simp at h)
    c16_D (c16_dep F) hPinj (allPairs 6) (fun i j hij _ => mem_allPairs hij) c16_checkW

end Minimality.SVCC.CellsLex
