module

public import Minimality.SilS0XC
public import Minimality.Type29Faces

@[expose] public section


/-!
# S0X-D: demonstration, a type-29 edge-view leaf through the type-free interface

Facets of type 29 (Lean order) `A..I = 012 015 023 035 124 1456 234 346 356` as an `S0xFac`.
Leaf `s05:1235[BvDv]` (SIL/packages.md §2.4): view `x 5 - x 0`; `B = 015`, `D = 035` edge-on and
tilted down; `A−, C−` (through 0), `F+, I+` (through 5) forced; literals `E+ G+ H+`; cycle `1 2 3 5`
(edges 12 E/A, 23 G/C, 35 I/D, 51 F/B); depths `RobUni` (or `Uni`, via `s0x_robUni_of_uni`).
-/

set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace H21

/-- Facet vertex sets of type 29, `A..I = 0..8`. -/
def s0x_S29 : Fin 9 → Finset (Fin 7) :=
  ![{0, 1, 2}, {0, 1, 5}, {0, 2, 3}, {0, 3, 5}, {1, 2, 4}, {1, 4, 5, 6}, {2, 3, 4}, {3, 4, 6},
    {3, 5, 6}]

/-- The nine facets of `Facets29` as a type-free facet family. -/
noncomputable def s0x_fac29 {x : Fin 7 → ℝ³} (T : Facets29 x) : S0xFac 9 s0x_S29 x where
  f := ![T.f012.f, T.f015.f, T.f023.f, T.f035.f, T.f124.f, T.f1456.f, T.f234.f, T.f346.f,
    T.f356.f]
  N := ![T.f012.N, T.f015.N, T.f023.N, T.f035.N, T.f124.N, T.f1456.N, T.f234.N, T.f346.N,
    T.f356.N]
  hN t := by
    fin_cases t
    exacts [T.f012.hN, T.f015.hN, T.f023.hN, T.f035.hN, T.f124.hN, T.f1456.hN, T.f234.hN,
      T.f346.hN, T.f356.hN]
  zero t := by
    fin_cases t
    exacts [T.f012.zero, T.f015.zero, T.f023.zero, T.f035.zero, T.f124.zero, T.f1456.zero,
      T.f234.zero, T.f346.zero, T.f356.zero]
  neg t := by
    fin_cases t
    exacts [T.f012.neg, T.f015.neg, T.f023.neg, T.f035.neg, T.f124.neg, T.f1456.neg,
      T.f234.neg, T.f346.neg, T.f356.neg]

/-- The leaf `s05:1235[BvDv]`. -/
def s0x_L29s05 : S0xSeg 7 9 4 where
  i := 0
  j := 5
  pat := ![false, false, false, false, true, true, true, true, true]
  c := ![1, 2, 3, 5]

theorem s0x_L29s05_good : s0x_L29s05.Good s0x_S29 := by decide

variable {x : Fin 7 → ℝ³}

/-- **Type 29, edge view s05** (B, D edge-on): literals `E+ G+ H+` and robust unimodal depths along
`1 2 3 5` give `IsRupert`. -/
theorem s0x_29_s05 (T : Facets29 x) (hE : 0 < T.f124.f (x 5) - T.f124.f (x 0))
    (hG : 0 < T.f234.f (x 5) - T.f234.f (x 0)) (hH : 0 < T.f346.f (x 5) - T.f346.f (x 0))
    (hU : RobUni (fun a : ZMod 4 => ⟪x (s0x_L29s05.c a), x 5 - x 0⟫)) :
    IsRupert (univ.image x) := by
  refine s0x_seg_rupert (s0x_fac29 T) T.inj s0x_L29s05 s0x_L29s05_good ⟨?_, hU⟩
  intro t h0 h5
  fin_cases t
  all_goals first
    | exact absurd h0 (by decide)
    | exact absurd h5 (by decide)
    | exact ⟨fun _ => hE, fun h => absurd h (by decide)⟩
    | exact ⟨fun _ => hG, fun h => absurd h (by decide)⟩
    | exact ⟨fun _ => hH, fun h => absurd h (by decide)⟩

end H21
end Minimality

