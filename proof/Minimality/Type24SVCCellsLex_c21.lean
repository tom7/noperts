module

public import Minimality.Type24SVCCellsLex5

@[expose] public section

set_option autoImplicit false

open scoped RealInnerProductSpace
open Minimality Minimality.H21 Minimality.SVCC Minimality.SVCC.Cells Minimality.T24.SAT

namespace Minimality.SVCC.CellsLex

theorem c21_checkW :
    SVC.checkW s0x_S24 c21_P c21_sw [] c21_D c21_R (allPairs 6) = true := by
  decide +kernel

theorem cell_235_346_pppmppzpz_lex {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (w : ℝ³)
    (h2 : 0 < ⟪F.N 2, w⟫)
    (h3 : ⟪F.N 3, w⟫ < 0)
    (h4 : 0 < ⟪F.N 4, w⟫)
    (h6 : ⟪F.N 6, w⟫ = 0)
    (h7 : 0 < ⟪F.N 7, w⟫)
    (h8 : ⟪F.N 8, w⟫ = 0) :
    Gen.LexAny F := by
  have hT : ∀ ρ ∈ c21_R, ∀ t, t ∈ ρ.U ∨ t ∈ ρ.Dn → t ∈ ({2, 3, 4, 6, 7, 8} : Finset (Fin 9)) := by decide
  have hsw : ∀ ρ ∈ c21_R, ∀ t, t ∈ ρ.U ∨ t ∈ ρ.Dn → SignType.sign ⟪F.N t, w⟫ = c21_sw t := by
    intro ρ hρ t ht
    have ht' := hT ρ hρ t ht
    clear ht hρ
    fin_cases t <;> simp at ht'
    · exact sign_pos h2
    · exact sign_neg h3
    · exact sign_pos h4
    · exact sign_eq_zero_iff.mpr h6
    · exact sign_pos h7
    · exact sign_eq_zero_iff.mpr h8
  have hR1 := hR_two F c21_sw c21_R 6 8 3 4 2 (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  have hR := hR_lex_of_hR F w c21_sw c21_R 2 6 h2.ne' h6 (by decide) hR1 rfl
  have hPinj : Function.Injective (fun i => x (c21_P i)) :=
    (EdgeViewLink.inj_of_fac24 F).comp (by decide : Function.Injective c21_P)
  exact SVC.svc_local_lex F c21_P w c21_sw c21_R (by decide) hsw hR [] (fun _ h => by simp at h)
    c21_D (c21_dep F) hPinj (allPairs 6) (fun i j hij _ => mem_allPairs hij) c21_checkW

end Minimality.SVCC.CellsLex
