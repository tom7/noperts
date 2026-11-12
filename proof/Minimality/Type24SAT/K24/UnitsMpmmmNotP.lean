module

public import Minimality.Type24SAT.K24.CasesSplit

@[expose] public section

/-!
# Type 24, class mpmmm: the class units (the five bracket signs) and their truth
-/

set_option autoImplicit false
open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21

namespace Minimality.H24K.SAT
open Minimality.H29.SAT Minimality.H24.SAT Minimality.H24T.SAT
open Minimality.T24.SAT (s0x_S24)

variable {x : Fin 7 → ℝ³}

open V W in
/-- The bracket literals of class mpmmm: `[1234]- [1245]+ [1356]- [1456]- [2456]-`. -/
def unitsMpmmmNotP : List LitW :=
  [(true, base (ng (br 1 2 3 4))), (true, base (br 1 2 4 5)), (true, base (ng (br 1 3 5 6))), (true, base (ng (br 1 4 5 6))), (true, base (ng (br 2 4 5 6)))]

/-- The bracket literals of mpmmm hold for the five bracket signs. -/
theorem unitsMpmmmNotP_true (F : S0xFac 9 s0x_S24 x)
    (h0 : det3 (x 2 - x 1) (x 3 - x 1) (x 4 - x 1) < 0)
    (h1 : 0 < det3 (x 2 - x 1) (x 4 - x 1) (x 5 - x 1))
    (h2 : det3 (x 3 - x 1) (x 5 - x 1) (x 6 - x 1) < 0)
    (h3 : det3 (x 4 - x 1) (x 5 - x 1) (x 6 - x 1) < 0)
    (h4 : det3 (x 4 - x 2) (x 5 - x 2) (x 6 - x 2) < 0) :
    ∀ l ∈ unitsMpmmmNotP, evalW (rhoW (geoF F)) l = true := by
  have e1 : (geoF F).x 1 = x 1 := geoF_x F 1
  have e2 : (geoF F).x 2 = x 2 := geoF_x F 2
  have e3 : (geoF F).x 3 = x 3 := geoF_x F 3
  have e4 : (geoF F).x 4 = x 4 := geoF_x F 4
  have e5 : (geoF F).x 5 = x 5 := geoF_x F 5
  have e6 : (geoF F).x 6 = x 6 := geoF_x F 6
  intro l hl
  simp only [unitsMpmmmNotP, List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl | rfl | rfl | rfl
  · show evalL (rho (geoF F)) (true, V.ng (V.br 1 2 3 4)) = true
    simp [evalL, H24.SAT.rho, H24.SAT.Geo.atom, e1, e2, e3, e4, h0]
  · show evalL (rho (geoF F)) (true, V.br 1 2 4 5) = true
    simp [evalL, H24.SAT.rho, H24.SAT.Geo.atom, e1, e2, e4, e5, h1]
  · show evalL (rho (geoF F)) (true, V.ng (V.br 1 3 5 6)) = true
    simp [evalL, H24.SAT.rho, H24.SAT.Geo.atom, e1, e3, e5, e6, h2]
  · show evalL (rho (geoF F)) (true, V.ng (V.br 1 4 5 6)) = true
    simp [evalL, H24.SAT.rho, H24.SAT.Geo.atom, e1, e4, e5, e6, h3]
  · show evalL (rho (geoF F)) (true, V.ng (V.br 2 4 5 6)) = true
    simp [evalL, H24.SAT.rho, H24.SAT.Geo.atom, e2, e4, e5, e6, h4]

end Minimality.H24K.SAT
