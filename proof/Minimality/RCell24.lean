module

public import Minimality.FaceCircleClosed
public import Minimality.Type24SAT.K24.ParR2
public import Minimality.FaceChordFac

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped RealInnerProductSpace
open Finset

namespace Minimality.T24.RCell

open Minimality Minimality.H21 Minimality.H24.SAT Minimality.T24.SAT Minimality.FaceChord

/-- Generic closed-cell tope leaf on Type 24 (`k ≥ 4`).
Note: `k = 3` has no closed-cell version in the toolbox because `RobUni` is vacuously true
for `k ≤ 3` (every 3-cycle). -/
def ToCC {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) : Prop :=
  ∃ (k : ℕ) (_ : NeZero k) (c : ZMod k → Fin 7) (U Dn : Finset (Fin 9)) (a u₀ : ℝ³),
    4 ≤ k ∧ Function.Injective c ∧ S0xCycUD s0x_S24 c U Dn ∧
    CellAt F U Dn a ∧ CellLe F U Dn u₀ ∧ RobUni (fun i => ⟪x (c i), u₀⟫)

/-- Generic closed-cell view on any of the nine facet circles (`k ≥ 4`).
Note: `k = 3` has no closed-cell version in the toolbox because `RobUni` is vacuously true
for `k ≤ 3` (every 3-cycle). -/
def CircCC {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) : Prop :=
  ∃ (f : Fin 9) (k : ℕ) (_ : NeZero k) (c : ZMod k → Fin 7) (U Dn : Finset (Fin 9)) (u₀ : ℝ³),
    4 ≤ k ∧ Function.Injective c ∧ S0xCycUD s0x_S24 c U Dn ∧
    ((f ∈ U ∧ f ∉ Dn) ∨ (f ∈ Dn ∧ f ∉ U)) ∧ F.N f ≠ 0 ∧
    ⟪F.N f, u₀⟫ = 0 ∧ (∀ t ∈ U, t ≠ f → 0 < ⟪F.N t, u₀⟫) ∧
    (∀ t ∈ Dn, t ≠ f → ⟪F.N t, u₀⟫ < 0) ∧ RobUni (fun i => ⟪x (c i), u₀⟫)

/-- Every generic closed-cell tope leaf on Type 24 (`k ≥ 4`) yields `IsRupert`. -/
theorem toCC_isRupert {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (h : ToCC F) :
    IsRupert (univ.image x) := by
  rcases h with ⟨k, _, c, U, Dn, a, u₀, hk, hc, hcyc, ha, hu₀, hR⟩
  exact isRupert_of_closedCell hk F (inj_of_fac F) hc hcyc ha hu₀ hR

/-- Every generic closed-cell facet-circle view on Type 24 (`k ≥ 4`) yields `IsRupert`. -/
theorem circCC_isRupert {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (h : CircCC F) :
    IsRupert (univ.image x) := by
  rcases h with ⟨f, k, _, c, U, Dn, u₀, hk, hc, hcyc, hf, hNf, hf0, hU, hD, hR⟩
  exact isRupert_faceCircleClosed hk F (inj_of_fac F) hc hcyc hf hNf hf0 hU hD hR

/-- Existence of a `FaceChordView` on any of the nine facets of Type 24. -/
def AnyFaceChord {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) : Prop :=
  ∃ t : Fin 9, FaceChordView F t

/-- Any `FaceChordView` on any of the nine facets of Type 24 yields `IsRupert`. -/
theorem anyFaceChord_isRupert {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (h : AnyFaceChord F) :
    IsRupert (univ.image x) := by
  rcases h with ⟨t, ht⟩
  exact isRupert_of_faceChordView F ht

end Minimality.T24.RCell
