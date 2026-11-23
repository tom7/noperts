module

public import Minimality.Type24SVCCellsLex5

@[expose] public section

set_option autoImplicit false

open scoped RealInnerProductSpace
open Minimality Minimality.H21 Minimality.SVCC Minimality.SVCC.Cells Minimality.T24.SAT

namespace Minimality.SVCC.CellsLex

def c14_T : List (Fin 6 × Fin 6) :=
  [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 2), (1, 3), (1, 4), (1, 5),
   (2, 3), (2, 4), (3, 5), (4, 5)]

theorem c14_checkW :
    SVC.checkW s0x_S24 c14_P c14_sw [] c14_D c14_R c14_T = true := by
  decide +kernel

theorem cell_0345_236_pppzmppzm_lex {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (w : ℝ³)
    (h1 : 0 < ⟪F.N 1, w⟫)
    (h2 : 0 < ⟪F.N 2, w⟫)
    (h3 : ⟪F.N 3, w⟫ = 0)
    (h4 : ⟪F.N 4, w⟫ < 0)
    (h5 : 0 < ⟪F.N 5, w⟫)
    (h6 : 0 < ⟪F.N 6, w⟫)
    (h7 : ⟪F.N 7, w⟫ = 0)
    (h8 : ⟪F.N 8, w⟫ < 0)
    (h36 : ⟪x 3, w⟫ ≠ ⟪x 6, w⟫)
    (h45 : ⟪x 4, w⟫ ≠ ⟪x 5, w⟫) :
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
  refine SVC.svc_local_lex F c14_P w c14_sw c14_R (by decide) hsw hR [] (fun _ h => by simp at h)
    c14_D (c14_dep F) hPinj c14_T (fun i j hij heq => ?_) c14_checkW
  by_contra hnot
  have hbad := (by decide : ∀ i j : Fin 6, i ≠ j → ¬ ((i, j) ∈ c14_T ∨ (j, i) ∈ c14_T) →
    (i, j) = (2, 5) ∨ (i, j) = (5, 2) ∨ (i, j) = (3, 4) ∨ (i, j) = (4, 3)) i j hij hnot
  rcases hbad with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact h36 heq
  · exact h36 heq.symm
  · exact h45 heq
  · exact h45 heq.symm

end Minimality.SVCC.CellsLex
