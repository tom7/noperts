module

public import Minimality.Type24SAT.Tie.KDec

@[expose] public section

/-!
# Type 24: the dispatcher with several class clauses (`rowKs`) and the top theorem `caseKs_of_unsat`

`Tie/KDec` has one class clause `C` (`rowK`).  The cores of the parallelogram split cases need several class clauses (the
facet-parallelism exclusions and the acute-angle clause), so `rowKs U Cs` accepts a family 26 row that contains one of
the clauses of `Cs` (as `Type29KSAT/NfZB` does for type 29).
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21

open Minimality.T24.SAT (s0x_S24)

namespace Minimality.H24K.SAT
open Minimality.H24.SAT Minimality.H29.SAT Minimality.H24T.SAT

variable {x : Fin 7 → ℝ³}

/-- The check of a decoded row: the tree's `rowWc`, or a family 26 row containing one of the class clauses `Cs`. -/
def rowKsc (U : List LitW) (Cs : List (List LitW)) (fam : Nat) (p : List Nat) (cl : List LitW) : Bool :=
  rowWc U fam p cl || (fam == 26 && Cs.any fun C => coversW cl C)

/-- The check of a packed row. -/
def rowKs (U : List LitW) (Cs : List (List LitW)) (chunks : List (List W)) (n : Nat) : Bool :=
  rowKsc U Cs (decRow n).1 (decRow n).2.1 ((decRow n).2.2.map (litOfCW chunks))

/-- A checked row holds under `rhoW` of every non-Rupert type 24 shape, given the class literals `U` and clauses `Cs`. -/
theorem rowKsc_holds (U : List LitW) (Cs : List (List LitW)) (F : S0xFac 9 s0x_S24 x) (hx : Function.Injective x)
    (hNR : ¬ IsRupert (univ.image x)) (hG : GeoOK (geoF F)) (hU : ∀ l ∈ U, evalW (rhoW (geoF F)) l = true)
    (hC : ∀ C ∈ Cs, HoldsW (rhoW (geoF F)) C)
    {fam : Nat} {p : List Nat} {cl : List LitW} (h : rowKsc U Cs fam p cl = true) : HoldsW (rhoW (geoF F)) cl := by
  unfold rowKsc at h
  rcases Bool.or_eq_true _ _ |>.mp h with h1 | h2
  · exact rowWc_holds U F hx hNR hG hU h1
  · simp only [Bool.and_eq_true, List.any_eq_true] at h2
    obtain ⟨-, C, hC', hc⟩ := h2
    exact HoldsW.of_covers (rhoW_proper _) hc (hC C hC')

/-- **Top theorem for a tie-file core with several class clauses.**  If the numbered clauses are unsatisfiable and every row
passes its check, every type 24 shape of the chirality `Bq 0 1 2 6 < 0` that satisfies the class literals `U` and all class
clauses `Cs` is Rupert. -/
theorem caseKs_of_unsat (chunks : List (List W)) (rows : List (List Nat)) (U : List LitW) (Cs : List (List LitW))
    (hA : CoreUnsat rows) (hall : ∀ ch ∈ rows, ∀ n ∈ ch, rowKs U Cs chunks n = true)
    (F : S0xFac 9 s0x_S24 x) (hchir : det3 (x 1 - x 0) (x 2 - x 0) (x 6 - x 0) < 0)
    (hU : ∀ l ∈ U, evalW (rhoW (geoF F)) l = true) (hC : ∀ C ∈ Cs, HoldsW (rhoW (geoF F)) C) :
    IsRupert (univ.image x) := by
  by_contra hNR
  have hG := geoOK_of F hchir
  refine hA (fun i => evalW (rhoW (geoF F)) (nmOfW chunks i)) ?_
  intro ch hch n hn
  exact code_of_holdsW chunks _ n
    (rowKsc_holds U Cs F (inj_of_fac F) hNR hG hU hC (hall ch hch n hn))

end Minimality.H24K.SAT
