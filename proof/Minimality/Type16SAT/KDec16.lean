module

public import Minimality.Type16SAT.TTop

@[expose] public section

/-!
# J6: the row dispatcher `rowS` of a type 16 core (the split families included) and `caseS_of_unsat`

`rowSc U fam p cl` is the check of a decoded row (family, the eight parameters, the clause over `W`): the dispatcher `rowWc`
of `TDec` (menu families 8, 11 to 16, 20, 21, 17, 19, 22, quad relations 24, class units 26, tie families 23, 30 to 36, 38, 39),
or one of the split families of `SSplit`:

* 40 (split rule; tag `40 kind key side pp sfv`, here `p = [kind, key, side, pp, 0, aux]`; `aux` is the parameter of the
  sibling rule row the tag does not carry: the mask of the sibling `17 e pp mask ..` for kind 0, the zero facet `zs` of the
  sibling `23 t f sd pp mask zs ..` for kind 1, stored `999` for none, as `toI`): kind 0 `split0OK key pp aux`,
  kind 1 `split1OK (key / 32) (key % 32) side pp (zs1Of aux)`;
* 41 (certificate; tag `41 sfv kind key side a cc sig : cyc`, `p = [0, kind, key, side, a, cc, sig]`, `sig` stored `+1000` if
  negative; the cycle is read off the clause's `sf` literal): `certOK kind view f side a cc sg cyc` with `view = key`,
  `f = 0` (kind 0) or `view = key / 32`, `f = key % 32` (kind 1) and `sg = 1` iff `sig = +1`;
* 42 and 43 (`Q` zero sums, `p = [key, e1, e2]`): `chk42`, `chk43`;
* 44 (`p = [kind, key, e1, e2]`): `chk44`.

The class units are the family 26 rows of `rowWc` (a single literal of the list `U`); the type 16 cores have no class clause.
`rowSc_holds`: a checked row holds under `rhoW (geoF F)` of every non-Rupert type 16 shape with `GeoOK`.
`caseS_of_unsat`: the top theorem.
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

/-- The cycle of the flag `sf kind view f sd _` of a family 41 row (its literal there is negative: `-sf`). -/
def sfCycOf (cl : List LitW) (kind view f sd : Nat) : List Nat :=
  (cl.findSome? fun l => match l with
    | (_, .sf k' v' f' sd' c) => if k' == kind && v' == view && f' == f && sd' == sd then some c else none
    | _ => none).getD []

/-- The check of a split family row (40 to 44). -/
def rowSplit (fam : Nat) (p : List Nat) (cl : List LitW) : Bool :=
  (fam == 40 && (if p.getD 0 0 == 0 then split0OK (p.getD 1 0) (p.getD 3 0) (p.getD 5 0) cl
      else split1OK (p.getD 1 0 / 32) (p.getD 1 0 % 32) (p.getD 2 0) (p.getD 3 0) (zs1Of (p.getD 5 0)) cl)) ||
  (fam == 41 &&
    (let kind := p.getD 1 0
     let view := if kind == 0 then p.getD 2 0 else p.getD 2 0 / 32
     let f := if kind == 0 then 0 else p.getD 2 0 % 32
     certOK kind view f (p.getD 3 0) (p.getD 4 0) (p.getD 5 0) (if toI (p.getD 6 0) == 1 then 1 else 0)
       (sfCycOf cl kind view f (p.getD 3 0)) cl)) ||
  (fam == 42 && chk42 (p.getD 0 0) (p.getD 1 0) (p.getD 2 0) cl) ||
  (fam == 43 && chk43 (p.getD 0 0) (p.getD 1 0) (p.getD 2 0) cl) ||
  (fam == 44 && chk44 (p.getD 0 0) (p.getD 1 0) (p.getD 2 0) (p.getD 3 0) cl)

/-- **The check of a decoded row**: the tree-shaped dispatcher `rowWc`, or a split family row. -/
def rowSc (U : List LitW) (fam : Nat) (p : List Nat) (cl : List LitW) : Bool :=
  rowWc U fam p cl || rowSplit fam p cl

/-- The check of a packed row. -/
def rowS (U : List LitW) (chunks : List (List W)) (n : Nat) : Bool :=
  rowSc U (decRow n).1 (decRow n).2.1 ((decRow n).2.2.map (litOfCW chunks))

/-- A checked split row holds under `rhoW` of every non-Rupert type 16 shape with `GeoOK`. -/
theorem rowSplit_holds (F : S0xFac 8 V2.fIdx x) (hx : Function.Injective x)
    (hNR : ¬ IsRupert (univ.image x)) (hG : GeoOK (geoF F))
    {fam : Nat} {p : List Nat} {cl : List LitW} (h : rowSplit fam p cl = true) : HoldsW (rhoW (geoF F)) cl := by
  unfold rowSplit at h
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h
  rcases h with (((⟨-, h0⟩ | ⟨-, h1⟩) | ⟨-, h2⟩) | ⟨-, h3⟩) | ⟨-, h4⟩
  · by_cases hk : p.getD 0 0 = 0
    · rw [if_pos (by simpa using hk)] at h0
      exact split0OK_sound F hx hNR hG h0
    · rw [if_neg (by simpa using hk)] at h0
      exact split1OK_sound F hx hNR hG h0
  · exact certOK_sound hG h1
  · exact chk42_sound hG h2
  · exact chk43_sound hG h3
  · exact chk44_sound _ h4

/-- **A checked row holds** under `rhoW` of every non-Rupert type 16 shape, given the class literals `U`. -/
theorem rowSc_holds (U : List LitW) (F : S0xFac 8 V2.fIdx x) (hx : Function.Injective x)
    (hNR : ¬ IsRupert (univ.image x)) (hG : GeoOK (geoF F)) (hU : ∀ l ∈ U, evalW (rhoW (geoF F)) l = true)
    {fam : Nat} {p : List Nat} {cl : List LitW} (h : rowSc U fam p cl = true) : HoldsW (rhoW (geoF F)) cl := by
  unfold rowSc at h
  rcases Bool.or_eq_true _ _ |>.mp h with h1 | h2
  · exact rowWc_holds U F hx hNR hG hU h1
  · exact rowSplit_holds F hx hNR hG h2

/-- **Top theorem for a type 16 core.**  If the numbered clauses are unsatisfiable and every packed row passes `rowS`
(names `chunks : List (List W)`, class literals `U`), every type 16 shape of the chirality `0 < [3056]` whose real data
satisfy the class literals `U` is Rupert. -/
theorem caseS_of_unsat (chunks : List (List W)) (rows : List (List Nat)) (U : List LitW)
    (hA : Minimality.H16.SAT.CoreUnsat rows) (hall : ∀ ch ∈ rows, ∀ n ∈ ch, rowS U chunks n = true)
    (F : S0xFac 8 V2.fIdx x) (hchir : 0 < det3 (x 0 - x 3) (x 5 - x 3) (x 6 - x 3))
    (hU : ∀ l ∈ U, evalW (rhoW (geoF F)) l = true) : IsRupert (univ.image x) := by
  by_contra hNR
  have hG := geoOK_of F hchir
  refine hA (fun i => evalW (rhoW (geoF F)) (nmOfW chunks i)) ?_
  intro ch hch n hn
  exact code_of_holdsW chunks _ n
    (rowSc_holds U F (inj_of_fac F) hNR hG hU (hall ch hch n hn))

end Minimality.H16K.SAT
