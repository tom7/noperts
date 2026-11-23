module

public import Minimality.Type24SVCCellsLex5

@[expose] public section

set_option autoImplicit false

open scoped RealInnerProductSpace
open Minimality Minimality.H21 Minimality.SVCC Minimality.SVCC.Cells Minimality.T24.SAT

namespace Minimality.SVCC.CellsLex

def c12_T : List (Fin 6 × Fin 6) :=
  [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 3), (1, 4), (1, 5), (2, 3),
   (2, 4), (2, 5), (3, 5), (4, 5)]

theorem c12_checkW :
    SVC.checkW s0x_S24 c12_P c12_sw [] c12_D c12_R c12_T = true := by
  decide +kernel

theorem cell_0345_236_ppmzppmzp_lex {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (w : ℝ³)
    (h0 : 0 < ⟪F.N 0, w⟫)
    (h2 : ⟪F.N 2, w⟫ < 0)
    (h3 : ⟪F.N 3, w⟫ = 0)
    (h4 : 0 < ⟪F.N 4, w⟫)
    (h5 : 0 < ⟪F.N 5, w⟫)
    (h6 : ⟪F.N 6, w⟫ < 0)
    (h7 : ⟪F.N 7, w⟫ = 0)
    (h8 : 0 < ⟪F.N 8, w⟫)
    (h23 : ⟪x 2, w⟫ ≠ ⟪x 3, w⟫)
    (h45 : ⟪x 4, w⟫ ≠ ⟪x 5, w⟫) :
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
  refine SVC.svc_local_lex F c12_P w c12_sw c12_R (by decide) hsw hR [] (fun _ h => by simp at h)
    c12_D (c12_dep F) hPinj c12_T (fun i j hij heq => ?_) c12_checkW
  by_contra hnot
  have hbad := (by decide : ∀ i j : Fin 6, i ≠ j → ¬ ((i, j) ∈ c12_T ∨ (j, i) ∈ c12_T) →
    (i, j) = (1, 2) ∨ (i, j) = (2, 1) ∨ (i, j) = (3, 4) ∨ (i, j) = (4, 3)) i j hij hnot
  rcases hbad with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact h23 heq
  · exact h23 heq.symm
  · exact h45 heq
  · exact h45 heq.symm

end Minimality.SVCC.CellsLex
