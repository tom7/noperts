module

public import Minimality.Type24SAT.Geo.Top
public import Minimality.GenericLeaves

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped RealInnerProductSpace
open Finset

namespace Minimality.T24.RCell

open Minimality Minimality.H21 Minimality.H24.SAT Minimality.T24.SAT

/-- Existence of a `FaceChordView` on any of the nine facets of Type 24. -/
abbrev AnyFaceChord {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) : Prop :=
  Gen.AnyFaceChord F

/-- Any `FaceChordView` on any of the nine facets of Type 24 yields `IsRupert`. -/
theorem anyFaceChord_isRupert {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (h : AnyFaceChord F) :
    IsRupert (univ.image x) :=
  Gen.anyFaceChord_isRupert F h

/-- Generic lexicographic closed-cell leaf on Type 24 (`k ≥ 4`). -/
abbrev LexAny {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) : Prop :=
  Gen.LexAny F

/-- Every generic lexicographic closed-cell leaf on Type 24 (`k ≥ 4`) yields `IsRupert`. -/
theorem lexAny_isRupert {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (h : LexAny F) :
    IsRupert (univ.image x) :=
  Gen.lexAny_isRupert F (inj_of_fac F) h

private theorem s24_sep :
    ∀ i j : Fin 7, j ≠ i → ∃ t : Fin 9, i ∈ s0x_S24 t ∧ j ∉ s0x_S24 t := by decide

/-- Generic tope split-pair view (facings lex at `(u, v)` via `S0xFacOK`, split rows strict
at `u` via `Minimality.Split.SplitRows`) on Type 24 (`k ≥ 3`). -/
abbrev SplitAny24 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) : Prop :=
  Gen.SplitAny F

/-- Every generic tope split-pair view on Type 24 (`k ≥ 3`) yields `IsRupert`. -/
theorem splitAny24_isRupert {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (h : SplitAny24 F) :
    IsRupert (univ.image x) :=
  Gen.splitAny_isRupert F (inj_of_fac F) s24_sep h

end Minimality.T24.RCell
