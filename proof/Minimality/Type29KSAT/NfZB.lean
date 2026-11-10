module

public import Minimality.Type29KSAT.KDec

@[expose] public section

/-!
# Type 29, class K2a on `Z1`, case B: the residue hypotheses and a dispatcher with several class clauses

Case B on `Z1` is "`x1 - x4` is orthogonal to the plane of the facet `B = 015`", here in the form of the two inner
products of case A vanishing (`CaseB`).  The Slide leaf closes case B when the deep vertices `0, 2, 3` lie strictly on
one side of the end planes of the edge `15`; the residue left over is `CaseBRes`: some deep vertex overhangs the end `1`
and some deep vertex overhangs the end `5`.

The core of case B uses two class clauses (the residue clauses), so the dispatcher `rowK` of `KDec` (one class clause)
is generalized to a list of class clauses: `rowKs U Cs` accepts a family 26 row containing one of the clauses of `Cs`
(`caseKs_of_unsat` is `caseK_of_unsat` for it).
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

/-- **Case B**: the edge direction `x1 - x4` is orthogonal to both `x0 - x1` and `x0 - x5`. -/
def CaseB (y : Fin 7 → ℝ³) : Prop := ⟪y 1 - y 4, y 0 - y 1⟫ = 0 ∧ ⟪y 1 - y 4, y 0 - y 5⟫ = 0

/-- **The residue of the Slide leaf** (overhang at both ends of the edge `15`): some deep vertex `p ∈ {0, 2, 3}` has
`<x p - x1, x5 - x1> ≤ 0`, and some deep vertex `q ∈ {0, 2, 3}` has `<x q - x5, x1 - x5> ≤ 0`. -/
def CaseBRes (y : Fin 7 → ℝ³) : Prop :=
  (∃ p ∈ ({0, 2, 3} : Finset (Fin 7)), ⟪y p - y 1, y 5 - y 1⟫ ≤ 0) ∧
    (∃ q ∈ ({0, 2, 3} : Finset (Fin 7)), ⟪y q - y 5, y 1 - y 5⟫ ≤ 0)

/-- The check of a decoded row: the tree's `rowWc`, or a family 26 row containing one of the class clauses `Cs`. -/
def rowKsc (U : List LitW) (Cs : List (List LitW)) (fam : Nat) (p : List Nat) (cl : List LitW) : Bool :=
  rowWc U fam p cl || (fam == 26 && Cs.any fun C => coversW cl C)

/-- The check of a packed row. -/
def rowKs (U : List LitW) (Cs : List (List LitW)) (chunks : List (List W)) (n : Nat) : Bool :=
  rowKsc U Cs (decRow n).1 (decRow n).2.1 ((decRow n).2.2.map (litOfCW chunks))

/-- A checked row holds under `rhoW` of every non-Rupert type 29 shape, given the class literals `U` and the class
clauses `Cs`. -/
theorem rowKsc_holds (U : List LitW) (Cs : List (List LitW)) (F : S0xFac 9 s0x_S29 x) (hx : Function.Injective x)
    (hNR : ¬ IsRupert (univ.image x)) (hG : GeoOK (geoF F)) (hU : ∀ l ∈ U, evalW (rhoW (geoF F)) l = true)
    (hC : ∀ C ∈ Cs, HoldsW (rhoW (geoF F)) C)
    {fam : Nat} {p : List Nat} {cl : List LitW} (h : rowKsc U Cs fam p cl = true) : HoldsW (rhoW (geoF F)) cl := by
  unfold rowKsc at h
  rcases Bool.or_eq_true _ _ |>.mp h with h1 | h2
  · exact rowWc_holds U F hx hNR hG hU h1
  · simp only [Bool.and_eq_true, List.any_eq_true] at h2
    obtain ⟨-, C, hC', hc⟩ := h2
    exact HoldsW.of_covers (rhoW_proper _) hc (hC C hC')

/-- **Top theorem for a tie-file core with several class clauses.**  If the numbered clauses are unsatisfiable and every
row passes its check, every type 29 shape of the chirality `0 < [0123]` that satisfies the class literals `U` and all
class clauses `Cs` is Rupert. -/
theorem caseKs_of_unsat (chunks : List (List W)) (rows : List (List Nat)) (U : List LitW) (Cs : List (List LitW))
    (hA : CoreUnsat rows) (hall : ∀ ch ∈ rows, ∀ n ∈ ch, rowKs U Cs chunks n = true)
    (F : S0xFac 9 s0x_S29 x) (hchir : 0 < det3 (x 1 - x 0) (x 2 - x 0) (x 3 - x 0))
    (hU : ∀ l ∈ U, evalW (rhoW (geoF F)) l = true) (hC : ∀ C ∈ Cs, HoldsW (rhoW (geoF F)) C) :
    IsRupert (univ.image x) := by
  by_contra hNR
  have hG := geoOK_of F hchir
  refine hA (fun i => evalW (rhoW (geoF F)) (nmOfW chunks i)) ?_
  intro ch hch n hn
  exact code_of_holdsW chunks _ n
    (rowKsc_holds U Cs F (inj_of_fac F) hNR hG hU hC (hall ch hch n hn))

end Minimality.H29K.SAT
