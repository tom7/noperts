module

public import Minimality.Type24SVCCellsLex5

@[expose] public section

set_option autoImplicit false

open scoped RealInnerProductSpace
open Minimality Minimality.H21 Minimality.SVCC Minimality.SVCC.Cells Minimality.T24.SAT

namespace Minimality.SVCC.CellsLex

theorem c10_checkW :
    SVC.checkW s0x_S24 c10_P c10_sw [] c10_D c10_R (allPairs 6) = true := by
  decide +kernel

theorem cell_025_346_ppzmppppz_lex {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (w : ℝ³)
    (h0 : 0 < ⟪F.N 0, w⟫)
    (h2 : ⟪F.N 2, w⟫ = 0)
    (h3 : ⟪F.N 3, w⟫ < 0)
    (h4 : 0 < ⟪F.N 4, w⟫)
    (h6 : 0 < ⟪F.N 6, w⟫)
    (h7 : 0 < ⟪F.N 7, w⟫)
    (h8 : ⟪F.N 8, w⟫ = 0)
    (hD : ⟪F.N 2, F.N 2⟫ * ⟪F.N 8, F.N 8⟫ - ⟪F.N 2, F.N 8⟫ ^ 2 ≠ 0) :
    Gen.LexAny F := by
  have hT : ∀ ρ ∈ c10_R, ∀ t, t ∈ ρ.U ∨ t ∈ ρ.Dn → t ∈ ({0, 2, 3, 4, 6, 7, 8} : Finset (Fin 9)) := by decide
  have hsw : ∀ ρ ∈ c10_R, ∀ t, t ∈ ρ.U ∨ t ∈ ρ.Dn → SignType.sign ⟪F.N t, w⟫ = c10_sw t := by
    intro ρ hρ t ht
    have ht' := hT ρ hρ t ht
    clear ht hρ
    fin_cases t <;> simp at ht'
    · exact sign_pos h0
    · exact sign_eq_zero_iff.mpr h2
    · exact sign_neg h3
    · exact sign_pos h4
    · exact sign_pos h6
    · exact sign_pos h7
    · exact sign_eq_zero_iff.mpr h8
  have hR1 := hR_gram F c10_sw c10_R 2 8 hD (by decide)
  have hR := hR_lex_of_hR F w c10_sw c10_R 0 2 h0.ne' h2 (by decide) hR1 rfl
  have hPinj : Function.Injective (fun i => x (c10_P i)) :=
    (EdgeViewLink.inj_of_fac24 F).comp (by decide : Function.Injective c10_P)
  exact SVC.svc_local_lex F c10_P w c10_sw c10_R (by decide) hsw hR [] (fun _ h => by simp at h)
    c10_D (c10_dep F) hPinj (allPairs 6) (fun i j hij _ => mem_allPairs hij) c10_checkW

end Minimality.SVCC.CellsLex
