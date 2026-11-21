module

public import Minimality.FaceCircleClosed
public import Minimality.Type24SAT.K24.ParR2
public import Minimality.FaceChordFac
public import Minimality.LexCell

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped RealInnerProductSpace
open Finset

namespace Minimality.T24.RCell

open Minimality Minimality.H21 Minimality.H24.SAT Minimality.T24.SAT Minimality.FaceChord Minimality.LexCell





/-- Existence of a `FaceChordView` on any of the nine facets of Type 24. -/
def AnyFaceChord {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) : Prop :=
  ∃ t : Fin 9, FaceChordView F t

/-- Any `FaceChordView` on any of the nine facets of Type 24 yields `IsRupert`. -/
theorem anyFaceChord_isRupert {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (h : AnyFaceChord F) :
    IsRupert (univ.image x) := by
  rcases h with ⟨t, ht⟩
  exact isRupert_of_faceChordView F ht

/-- Generic lexicographic closed-cell leaf on Type 24 (`k ≥ 4`). -/
def LexAny {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) : Prop :=
  ∃ (k : ℕ) (_ : NeZero k) (c : ZMod k → Fin 7) (U Dn : Finset (Fin 9)) (b d1 d2 : ℝ³),
    4 ≤ k ∧ Function.Injective c ∧ S0xCycUD s0x_S24 c U Dn ∧
    (∀ t ∈ U, LexPos3 ⟪F.N t, b⟫ ⟪F.N t, d1⟫ ⟪F.N t, d2⟫) ∧
    (∀ t ∈ Dn, LexPos3 (-⟪F.N t, b⟫) (-⟪F.N t, d1⟫) (-⟪F.N t, d2⟫)) ∧
    RobUniLex (fun i => (⟪x (c i), b⟫, ⟪x (c i), d1⟫, ⟪x (c i), d2⟫))

/-- Every generic lexicographic closed-cell leaf on Type 24 (`k ≥ 4`) yields `IsRupert`. -/
theorem lexAny_isRupert {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (h : LexAny F) :
    IsRupert (univ.image x) := by
  rcases h with ⟨k, _, c, U, Dn, b, d1, d2, hk, hc, hcyc, hU, hD, hR⟩
  exact Minimality.LexCell.isRupert_of_lexCell hk F (inj_of_fac F) hc hcyc b d1 d2 hU hD hR



end Minimality.T24.RCell
