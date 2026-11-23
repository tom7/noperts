module

public import Minimality.Type24SVCCellsLex5

@[expose] public section

set_option autoImplicit false

open scoped RealInnerProductSpace
open Minimality Minimality.H21 Minimality.SVCC Minimality.SVCC.Cells Minimality.T24.SAT

namespace Minimality.SVCC.CellsLex

theorem c06_checkW :
    SVC.checkW s0x_S24 c06_P c06_sw [] c06_D c06_R (allPairs 6) = true := by
  decide +kernel

theorem cell_025_046_ppzmzpppp_lex {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (w : ℝ³)
    (h0 : 0 < ⟪F.N 0, w⟫)
    (h1 : 0 < ⟪F.N 1, w⟫)
    (h2 : ⟪F.N 2, w⟫ = 0)
    (h3 : ⟪F.N 3, w⟫ < 0)
    (h4 : ⟪F.N 4, w⟫ = 0)
    (h6 : 0 < ⟪F.N 6, w⟫)
    (h8 : 0 < ⟪F.N 8, w⟫) :
    Gen.LexAny F := by
  have hT : ∀ ρ ∈ c06_R, ∀ t, t ∈ ρ.U ∨ t ∈ ρ.Dn → t ∈ ({0, 1, 2, 3, 4, 6, 8} : Finset (Fin 9)) := by decide
  have hsw : ∀ ρ ∈ c06_R, ∀ t, t ∈ ρ.U ∨ t ∈ ρ.Dn → SignType.sign ⟪F.N t, w⟫ = c06_sw t := by
    intro ρ hρ t ht
    have ht' := hT ρ hρ t ht
    clear ht hρ
    fin_cases t <;> simp at ht'
    · exact sign_pos h0
    · exact sign_pos h1
    · exact sign_eq_zero_iff.mpr h2
    · exact sign_neg h3
    · exact sign_eq_zero_iff.mpr h4
    · exact sign_pos h6
    · exact sign_pos h8
  have hR1 := hR_two F c06_sw c06_R 2 4 0 4 2 (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  have hR := hR_lex_of_hR F w c06_sw c06_R 0 2 h0.ne' h2 (by decide) hR1 rfl
  have hPinj : Function.Injective (fun i => x (c06_P i)) :=
    (EdgeViewLink.inj_of_fac24 F).comp (by decide : Function.Injective c06_P)
  exact SVC.svc_local_lex F c06_P w c06_sw c06_R (by decide) hsw hR [] (fun _ h => by simp at h)
    c06_D (c06_dep F) hPinj (allPairs 6) (fun i j hij _ => mem_allPairs hij) c06_checkW

end Minimality.SVCC.CellsLex
