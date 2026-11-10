module

public import Minimality.Type16SAT.KDecK16
public import Minimality.Type16SAT.TabX

@[expose] public section

/-!
# Type 16: the dispatcher with a class clause and the extra triple routes (`rowSKX`, `caseSKX_of_unsat`)

`row4OKX` is the family 13 check `row4OK` over the extended table `tab3X` (`TabX.lean`).  `rowSKXc` is `rowSKc` (`KDecK16`), or a
family 13 row passing `row4OKX`.  The soundness proof is that of `row4OK_sound` with `entOK_tab3X`.
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

/-- The `row4` row over the extended table. -/
def row4OKX (p : List Nat) (cl : List Lit) : Bool :=
  let e := prm p 0; let f0 := prm p 1; let f1 := prm p 2; let f2 := prm p 3; let f3 := prm p 4
  decide (e < 36 ∧ f0 < 21 ∧ f1 < 21 ∧ f2 < 21 ∧ f3 < 21) &&
  hasKeyX f1 f2 f3 && hasKeyX f0 f2 f3 && hasKeyX f0 f1 f3 && hasKeyX f0 f1 f2 && anyCov cl (row4 tab3X e f0 f1 f2 f3)

/-- The `row4` rows over the extended table are true. -/
theorem row4OKX_sound {g : Geo} (hG : GeoOK g) {p : List Nat} {cl : List Lit}
    (h : row4OKX p cl = true) : Holds (rho g) cl := by
  unfold row4OKX at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨-, h0, h1, h2, h3⟩, k1⟩, k2⟩, k3⟩, k4⟩, hcov⟩ := h
  exact anyCov_holds (rho_proper g) hcov
    (row4_sound (entOK_tab3X hG.hF hG.hO) _ _ _ _ _ (fun h' => hG.hv _ h') (fun f hf => vv_lt g hf) h0 h1 h2 h3
      k1 k2 k3 k4)

/-- The check of a decoded row: `rowSKc`, or a family 13 row over the extended table. -/
def rowSKXc (U C : List LitW) (fam : Nat) (p : List Nat) (cl : List LitW) : Bool :=
  rowSKc U C fam p cl || (fam == 13 && (row4OKX p (cl.map unliftL) && cl.all isBaseW))

/-- The check of a packed row. -/
def rowSKX (U C : List LitW) (chunks : List (List W)) (n : Nat) : Bool :=
  rowSKXc U C (decRow n).1 (decRow n).2.1 ((decRow n).2.2.map (litOfCW chunks))

/-- A checked row holds under `rhoW` of every non-Rupert type 16 shape. -/
theorem rowSKXc_holds (U C : List LitW) (F : S0xFac 8 V2.fIdx x) (hx : Function.Injective x)
    (hNR : ¬ IsRupert (univ.image x)) (hG : GeoOK (geoF F)) (hU : ∀ l ∈ U, evalW (rhoW (geoF F)) l = true)
    (hC : HoldsW (rhoW (geoF F)) C)
    {fam : Nat} {p : List Nat} {cl : List LitW} (h : rowSKXc U C fam p cl = true) : HoldsW (rhoW (geoF F)) cl := by
  unfold rowSKXc at h
  rcases Bool.or_eq_true _ _ |>.mp h with h1 | h2
  · exact rowSKc_holds U C F hx hNR hG hU hC h1
  · simp only [Bool.and_eq_true] at h2
    exact holdsW_of_base _ h2.2.2 (row4OKX_sound hG h2.2.1)

/-- **Top theorem for a type 16 core with a class clause and the extra triple routes.** -/
theorem caseSKX_of_unsat (chunks : List (List W)) (rows : List (List Nat)) (U C : List LitW)
    (hA : Minimality.H16.SAT.CoreUnsat rows) (hall : ∀ ch ∈ rows, ∀ n ∈ ch, rowSKX U C chunks n = true)
    (F : S0xFac 8 V2.fIdx x) (hchir : 0 < det3 (x 0 - x 3) (x 5 - x 3) (x 6 - x 3))
    (hU : ∀ l ∈ U, evalW (rhoW (geoF F)) l = true) (hC : HoldsW (rhoW (geoF F)) C) : IsRupert (univ.image x) := by
  by_contra hNR
  have hG := geoOK_of F hchir
  refine hA (fun i => evalW (rhoW (geoF F)) (nmOfW chunks i)) ?_
  intro ch hch n hn
  exact code_of_holdsW chunks _ n
    (rowSKXc_holds U C F (inj_of_fac F) hNR hG hU hC (hall ch hch n hn))

/-- A clause that holds the positive literals of an atom and of its negation holds when the atom is nonzero (`g.atom a ≠ 0`). -/
theorem holdsW_atom_ne {g : Geo} {a : V} (h : rho g a = decide (0 < g.atom a)) {cl : List LitW}
    (h1 : ((true, W.base a) : LitW) ∈ cl) (h2 : ((true, W.base (V.ng a)) : LitW) ∈ cl) (hne : g.atom a ≠ 0) :
    HoldsW (rhoW g) cl := by
  rcases lt_or_gt_of_ne hne with hl | hl
  · refine ⟨_, h2, ?_⟩
    show evalL (rho g) (true, V.ng a) = true
    simp [evalL, rho, hl]
  · refine ⟨_, h1, ?_⟩
    show evalL (rho g) (true, a) = true
    simp [evalL, h, hl]

end Minimality.H16K.SAT
