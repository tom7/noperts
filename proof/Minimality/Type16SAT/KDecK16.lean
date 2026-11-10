module

public import Minimality.Type16SAT.KDec16

@[expose] public section

/-!
# Type 16: the dispatcher with a class clause (`rowSK`) and the top theorem `caseSK_of_unsat`

The dispatcher `rowSc` of `KDec16` accepts a family 26 row only as a single literal of the class unit list `U`.  A core
with a class *clause* (a case hypothesis: "one of these atoms is nonzero") has one family 26 row with several literals.
`rowSKc U C fam p cl` is `rowSc U fam p cl`, or a family 26 row whose literals include all of the class clause `C`
(`coversW cl C`).  Soundness needs `HoldsW (rhoW (geoF F)) C`.  Same construction as the type 29 `rowKc`.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21

namespace Minimality.H16K.SAT
open Minimality.H29.SAT Minimality.H16.SAT Minimality.H16T.SAT

variable {x : Fin 7 → ℝ³}

/-- The check of a decoded row: the dispatcher `rowSc`, or a family 26 row containing the class clause `C`. -/
def rowSKc (U C : List LitW) (fam : Nat) (p : List Nat) (cl : List LitW) : Bool :=
  rowSc U fam p cl || (fam == 26 && coversW cl C)

/-- The check of a packed row. -/
def rowSK (U C : List LitW) (chunks : List (List W)) (n : Nat) : Bool :=
  rowSKc U C (decRow n).1 (decRow n).2.1 ((decRow n).2.2.map (litOfCW chunks))

/-- A checked row holds under `rhoW` of every non-Rupert type 16 shape, given the class literals `U` and the class
clause `C`. -/
theorem rowSKc_holds (U C : List LitW) (F : S0xFac 8 V2.fIdx x) (hx : Function.Injective x)
    (hNR : ¬ IsRupert (univ.image x)) (hG : GeoOK (geoF F)) (hU : ∀ l ∈ U, evalW (rhoW (geoF F)) l = true)
    (hC : HoldsW (rhoW (geoF F)) C)
    {fam : Nat} {p : List Nat} {cl : List LitW} (h : rowSKc U C fam p cl = true) : HoldsW (rhoW (geoF F)) cl := by
  unfold rowSKc at h
  rcases Bool.or_eq_true _ _ |>.mp h with h1 | h2
  · exact rowSc_holds U F hx hNR hG hU h1
  · simp only [Bool.and_eq_true] at h2
    exact HoldsW.of_covers (rhoW_proper _) h2.2 hC

/-- **Top theorem for a type 16 core with a class clause.**  If the numbered clauses are unsatisfiable and every packed
row passes `rowSK`, every type 16 shape of the chirality `0 < [3056]` whose real data satisfy the class literals `U` and
the class clause `C` is Rupert. -/
theorem caseSK_of_unsat (chunks : List (List W)) (rows : List (List Nat)) (U C : List LitW)
    (hA : Minimality.H16.SAT.CoreUnsat rows) (hall : ∀ ch ∈ rows, ∀ n ∈ ch, rowSK U C chunks n = true)
    (F : S0xFac 8 V2.fIdx x) (hchir : 0 < det3 (x 0 - x 3) (x 5 - x 3) (x 6 - x 3))
    (hU : ∀ l ∈ U, evalW (rhoW (geoF F)) l = true) (hC : HoldsW (rhoW (geoF F)) C) : IsRupert (univ.image x) := by
  by_contra hNR
  have hG := geoOK_of F hchir
  refine hA (fun i => evalW (rhoW (geoF F)) (nmOfW chunks i)) ?_
  intro ch hch n hn
  exact code_of_holdsW chunks _ n
    (rowSKc_holds U C F (inj_of_fac F) hNR hG hU hC (hall ch hch n hn))

end Minimality.H16K.SAT
