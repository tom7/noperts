module

public import Minimality.Type16SAT.KDecX16
public import Minimality.Type16SAT.TabY

@[expose] public section

/-!
# Type 16: the dispatcher with two class clauses and both lists of extra triple routes (`rowSK2X`, `caseSK2X_of_unsat`)

`rowSK2Xc U C C2` is `rowSKc U C` (`KDecK16`), or a family 13 row over the table `tab3Y` (`row4OKY`: triple keys of
`triRoutes`, `triRoutesX` or `triRoutesY`), or a family 26 row containing the second class clause `C2`.  For the cores whose
case is "some entry of `Z` is nonzero and some entry of the `sigma16` image of `Z` is nonzero" (`Cls16ZZ`).
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

/-- The `row4` row over the table with both extensions. -/
def row4OKY (p : List Nat) (cl : List Lit) : Bool :=
  let e := prm p 0; let f0 := prm p 1; let f1 := prm p 2; let f2 := prm p 3; let f3 := prm p 4
  decide (e < 36 ∧ f0 < 21 ∧ f1 < 21 ∧ f2 < 21 ∧ f3 < 21) &&
  hasKeyY f1 f2 f3 && hasKeyY f0 f2 f3 && hasKeyY f0 f1 f3 && hasKeyY f0 f1 f2 && anyCov cl (row4 tab3Y e f0 f1 f2 f3)

/-- The `row4` rows over the table with both extensions are true. -/
theorem row4OKY_sound {g : Geo} (hG : GeoOK g) {p : List Nat} {cl : List Lit}
    (h : row4OKY p cl = true) : Holds (rho g) cl := by
  unfold row4OKY at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨-, h0, h1, h2, h3⟩, k1⟩, k2⟩, k3⟩, k4⟩, hcov⟩ := h
  exact anyCov_holds (rho_proper g) hcov
    (row4_sound (entOK_tab3Y hG.hF hG.hO) _ _ _ _ _ (fun h' => hG.hv _ h') (fun f hf => vv_lt g hf) h0 h1 h2 h3
      k1 k2 k3 k4)

/-- The check of a decoded row: `rowSKc` with the first clause `C`, a family 13 row over `tab3Y`, or a family 26 row
containing `C2`. -/
def rowSK2Xc (U C C2 : List LitW) (fam : Nat) (p : List Nat) (cl : List LitW) : Bool :=
  rowSKc U C fam p cl || (fam == 13 && (row4OKY p (cl.map unliftL) && cl.all isBaseW)) || (fam == 26 && coversW cl C2)

/-- The check of a packed row. -/
def rowSK2X (U C C2 : List LitW) (chunks : List (List W)) (n : Nat) : Bool :=
  rowSK2Xc U C C2 (decRow n).1 (decRow n).2.1 ((decRow n).2.2.map (litOfCW chunks))

/-- A checked row holds under `rhoW` of every non-Rupert type 16 shape. -/
theorem rowSK2Xc_holds (U C C2 : List LitW) (F : S0xFac 8 V2.fIdx x) (hx : Function.Injective x)
    (hNR : ¬ IsRupert (univ.image x)) (hG : GeoOK (geoF F)) (hU : ∀ l ∈ U, evalW (rhoW (geoF F)) l = true)
    (hC : HoldsW (rhoW (geoF F)) C) (hC2 : HoldsW (rhoW (geoF F)) C2)
    {fam : Nat} {p : List Nat} {cl : List LitW} (h : rowSK2Xc U C C2 fam p cl = true) :
    HoldsW (rhoW (geoF F)) cl := by
  unfold rowSK2Xc at h
  rcases Bool.or_eq_true _ _ |>.mp h with h1 | h2
  · rcases Bool.or_eq_true _ _ |>.mp h1 with h1 | h3
    · exact rowSKc_holds U C F hx hNR hG hU hC h1
    · simp only [Bool.and_eq_true] at h3
      exact holdsW_of_base _ h3.2.2 (row4OKY_sound hG h3.2.1)
  · simp only [Bool.and_eq_true] at h2
    exact HoldsW.of_covers (rhoW_proper _) h2.2 hC2

/-- **Top theorem for a type 16 core with two class clauses and the extra triple routes.** -/
theorem caseSK2X_of_unsat (chunks : List (List W)) (rows : List (List Nat)) (U C C2 : List LitW)
    (hA : Minimality.H16.SAT.CoreUnsat rows) (hall : ∀ ch ∈ rows, ∀ n ∈ ch, rowSK2X U C C2 chunks n = true)
    (F : S0xFac 8 V2.fIdx x) (hchir : 0 < det3 (x 0 - x 3) (x 5 - x 3) (x 6 - x 3))
    (hU : ∀ l ∈ U, evalW (rhoW (geoF F)) l = true) (hC : HoldsW (rhoW (geoF F)) C)
    (hC2 : HoldsW (rhoW (geoF F)) C2) : IsRupert (univ.image x) := by
  by_contra hNR
  have hG := geoOK_of F hchir
  refine hA (fun i => evalW (rhoW (geoF F)) (nmOfW chunks i)) ?_
  intro ch hch n hn
  exact code_of_holdsW chunks _ n
    (rowSK2Xc_holds U C C2 F (inj_of_fac F) hNR hG hU hC hC2 (hall ch hch n hn))

end Minimality.H16K.SAT
