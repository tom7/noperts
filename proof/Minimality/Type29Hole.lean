module

public import Minimality.GenericLeaves
public import Minimality.Type29Faces
public import Minimality.Type29GA
public import Minimality.Type29KSAT.K1CornerOB

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.Gen Minimality.H21 Minimality.H29K1 Minimality.H29S

namespace Minimality.H29

/-!
# Type 29: Single Named Open Hole (`Hole29`)

Isolates the open Type-29 case (class `K1` on `OB6` off `Z`, under `H29GenResid N.facets`) as a
named predicate `Hole29 x N` in `Minimality.lean`, also negating the generic `S0xFac` Rupert
leaves (`AnyFaceChord29`, `LexAny29`, `SplitAny29`).
-/

/-- Generic `FaceChordView` on any of the nine facets of Type 29. -/
abbrev AnyFaceChord29 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S29 x) : Prop :=
  AnyFaceChord F

/-- Generic lexicographic closed-cell leaf on Type 29. -/
abbrev LexAny29 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S29 x) : Prop :=
  LexAny F

/-- Generic tope split-pair view on Type 29. -/
abbrev SplitAny29 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S29 x) : Prop :=
  SplitAny F

private theorem s29_sep :
    ∀ i j : Fin 7, j ≠ i → ∃ t : Fin 9, i ∈ s0x_S29 t ∧ j ∉ s0x_S29 t := by decide

/-- Type-29 class K1 (`a2 < 0 < b0, V < 0` or `0 < a2, b0 < 0 < V`). -/
def K1_29 {x : Fin 7 → ℝ³} (N : NF29 x) : Prop :=
  (N.a2 < 0 ∧ 0 < N.b0 ∧ N.V < 0) ∨ (0 < N.a2 ∧ N.b0 < 0 ∧ 0 < N.V)

/-- Type-29 corner stratum `Z` (vertex 6 trirectangular). -/
def Z29 (x : Fin 7 → ℝ³) : Prop :=
  ⟪x 3 - x 6, x 4 - x 6⟫ = 0 ∧ ⟪x 3 - x 6, x 5 - x 6⟫ = 0 ∧ ⟪x 4 - x 6, x 5 - x 6⟫ = 0

/-- The single named Type-29 open hole proposition for `Minimality.lean`. -/
def Hole29 (x : Fin 7 → ℝ³) (N : NF29 x) : Prop :=
  K1_29 N ∧ ¬ Z29 x ∧ OB6 x ∧ H29GenResid N.facets ∧
    ¬ AnyFaceChord29 (s0x_fac29 N.facets) ∧
    ¬ LexAny29 (s0x_fac29 N.facets) ∧
    ¬ SplitAny29 (s0x_fac29 N.facets)

/-- Main Type-29 reduction: either `x` is Rupert or `Hole29 x N` holds. -/
theorem type29_rupert_or_hole {x : Fin 7 → ℝ³} (N : NF29 x)
    (hK1 : K1_29 N) (hZ : ¬ Z29 x) (hOB : OB6 x) :
    IsRupert (univ.image x) ∨ Hole29 x N := by
  by_cases hres : H29GenResid N.facets
  · by_cases hAfc : AnyFaceChord29 (s0x_fac29 N.facets)
    · exact Or.inl (anyFaceChord_isRupert _ hAfc)
    · by_cases hLex : LexAny29 (s0x_fac29 N.facets)
      · exact Or.inl (lexAny_isRupert _ N.inj hLex)
      · by_cases hSp : SplitAny29 (s0x_fac29 N.facets)
        · exact Or.inl (splitAny_isRupert _ N.inj s29_sep hSp)
        · exact Or.inr ⟨hK1, hZ, hOB, hres, hAfc, hLex, hSp⟩
  · exact Or.inl (h29g_rule_isRupert N.facets hres)

end Minimality.H29
