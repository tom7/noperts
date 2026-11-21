module

public import Minimality.FaceCircleClosed
public import Minimality.Type24SAT.K24.ParR2
public import Minimality.FaceChordFac
public import Minimality.LexCell
public import Minimality.SplitLeaf

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

private theorem s24_sep :
    ∀ i j : Fin 7, j ≠ i → ∃ t : Fin 9, i ∈ s0x_S24 t ∧ j ∉ s0x_S24 t := by decide

/-- Generic tope split-pair view (facings lex at `(u, v)` via `S0xFacOK`, split rows strict
at `u` via `Minimality.Split.SplitRows`) on Type 24 (`k ≥ 3`). -/
def SplitAny24 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) : Prop :=
  ∃ (k : ℕ) (_ : NeZero k) (c : ZMod k → Fin 7) (pat : Fin 9 → Bool) (u v : ℝ³)
    (a cc : ZMod k) (σ : ℝ),
    3 ≤ k ∧ Function.Injective c ∧ S0xCycOK s0x_S24 c pat ∧ S0xFacOK F pat u v ∧
    cc ≠ a ∧ cc ≠ a + 1 ∧ Minimality.Split.SplitRows (fun i => x (c i)) u a cc σ

/-- Every generic tope split-pair view on Type 24 (`k ≥ 3`) yields `IsRupert`. -/
theorem splitAny24_isRupert {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (h : SplitAny24 F) :
    IsRupert (univ.image x) := by
  rcases h with ⟨k, hne, c, pat, u, v, a, cc, σ, hk, hc, hcyc, hfac, hca, hca1, hrows⟩
  have := hne
  exact Minimality.Split.split_tope_rupert F (inj_of_fac F) (Minimality.Split.noBetween_of_fac F s24_sep)
    v hc hk hcyc hfac a cc σ hca hca1 hrows

end Minimality.T24.RCell
