module

public import Minimality.Type29TSAT.TTop

@[expose] public section

/-!
# L29T, T11: the dispatcher with a class clause (`rowK`) and the top theorem `caseK_of_unsat`

The dispatcher `rowW` of the tree (`Type29TSAT/TDec`) handles family 26 rows with a single literal of the class unit list `U`.
A core with a class *clause* (K2 off `Z1`: "not all three of KF1456, KF1546, B:34 vanish") has one family 26 row with
several literals.  `rowKc U C fam p cl` is `rowWc U fam p cl`, or a family 26 row whose literals include all of the
class clause `C` (`coversW cl C`).  Soundness needs `HoldsW (rhoW (geoF F)) C`.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21

namespace Minimality.H29K.SAT
open Minimality.H29.SAT Minimality.H29T.SAT

variable {x : Fin 7 → ℝ³}

/-- The check of a decoded row: the tree's `rowWc`, or a family 26 row containing the class clause `C`. -/
def rowKc (U C : List LitW) (fam : Nat) (p : List Nat) (cl : List LitW) : Bool :=
  rowWc U fam p cl || (fam == 26 && coversW cl C)

/-- The check of a packed row. -/
def rowK (U C : List LitW) (chunks : List (List W)) (n : Nat) : Bool :=
  rowKc U C (decRow n).1 (decRow n).2.1 ((decRow n).2.2.map (litOfCW chunks))

/-- A checked row holds under `rhoW` of every non-Rupert type 29 shape, given the class literals `U` and the class
clause `C`. -/
theorem rowKc_holds (U C : List LitW) (F : S0xFac 9 s0x_S29 x) (hx : Function.Injective x)
    (hNR : ¬ IsRupert (univ.image x)) (hG : GeoOK (geoF F)) (hU : ∀ l ∈ U, evalW (rhoW (geoF F)) l = true)
    (hC : HoldsW (rhoW (geoF F)) C)
    {fam : Nat} {p : List Nat} {cl : List LitW} (h : rowKc U C fam p cl = true) : HoldsW (rhoW (geoF F)) cl := by
  unfold rowKc at h
  rcases Bool.or_eq_true _ _ |>.mp h with h1 | h2
  · exact rowWc_holds U F hx hNR hG hU h1
  · simp only [Bool.and_eq_true] at h2
    exact HoldsW.of_covers (rhoW_proper _) h2.2 hC

/-- **Top theorem for a tie-file core with a class clause.**  If the numbered clauses are unsatisfiable and every row passes
its check, every type 29 shape of the chirality `0 < [0123]` that satisfies the class literals `U` and the class clause `C`
is Rupert. -/
theorem caseK_of_unsat (chunks : List (List W)) (rows : List (List Nat)) (U C : List LitW)
    (hA : CoreUnsat rows) (hall : ∀ ch ∈ rows, ∀ n ∈ ch, rowK U C chunks n = true)
    (F : S0xFac 9 s0x_S29 x) (hchir : 0 < det3 (x 1 - x 0) (x 2 - x 0) (x 3 - x 0))
    (hU : ∀ l ∈ U, evalW (rhoW (geoF F)) l = true) (hC : HoldsW (rhoW (geoF F)) C) :
    IsRupert (univ.image x) := by
  by_contra hNR
  have hG := geoOK_of F hchir
  refine hA (fun i => evalW (rhoW (geoF F)) (nmOfW chunks i)) ?_
  intro ch hch n hn
  exact code_of_holdsW chunks _ n
    (rowKc_holds U C F (inj_of_fac F) hNR hG hU hC (hall ch hch n hn))

end Minimality.H29K.SAT
