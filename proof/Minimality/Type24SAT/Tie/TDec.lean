module

public import Minimality.Type24SAT.Tie.TLink
public import Minimality.Type24SAT.Tie.TRule
public import Minimality.Type24SAT.Geo.Top

@[expose] public section

/-!
# L24T, T7: decoding of the packed rows over `W` and the row dispatcher `rowW`

The rows of a tie-file core are packed as in Type29SAT/Dec (`decRow`: family + 1, parameters, literal codes); the
variable names are `W` terms (`nmOfW`, `litOfCW`).  `rowWc U fam p cl` is the check of a decoded row (family, the
eight parameters, the clause over `W`):

* menu families 8, 11 to 16, 20, 21, rules 17, witnesses 19, `T(L,L)` 22, quad relations 24 (T8 moved the old 23 to 24):
  all literals must be `base`, then the clause is un-lifted (`unliftL`) and checked by the existing `rowOK3`, `ruleOK`,
  `witOK`, `tllOK`, `krelOK`;
* 20 with a `wgate` literal: the three defining rows of the gate (`wgateOK`);
* 26: a single literal of the class list `U` (over `W`);
* tie families 23 (rule, `tieOK`), 30 to 36, 38, 39 to the checkers of T3 to T6.  Negative parameters are stored `+1000`
  (`toI`); the `lineS` data `(view, k)` of families 32 (kind 1) and 35 (kind 2) is `p8 = 2 view + (1 if k < 0)`;
  family 39 reads the cycle off the clause's `tfail` literal (`tfailVarOf`; `tfailOf` of TRule is for the positive literal of rule rows).
* no split families (the type 24 cores have SPLIT = 0).

`rowWc_holds`: a checked row holds under `rhoW (geoF F)` of every non-Rupert type 24 shape with `GeoOK`.
-/

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open scoped RealInnerProductSpace
open Finset

open Minimality.T24.SAT (s0x_S24)

namespace Minimality.H24T.SAT
open Minimality Minimality.H21 Minimality.H24.SAT Minimality.H29.SAT

/-- The literal of variable number `i` (`i = 0` is the constant true) from name chunks of 200. -/
def nmOfW (chunks : List (List W)) (i : Nat) : LitW :=
  match i with
  | 0 => ltrueW
  | j + 1 => (true, lget (lget chunks (j / 200) []) (j % 200) (W.base V.tru))

/-- The literal of a code `2 i + (1 if negative)`. -/
def litOfCW (chunks : List (List W)) (c : Nat) : LitW :=
  if c % 2 == 0 then nmOfW chunks (c / 2) else (nmOfW chunks (c / 2)).neg

/-- The literal is over a `base` variable. -/
def isBaseW : LitW → Bool
  | (_, .base _) => true
  | _ => false

/-- Un-lift a `base` literal (junk on others). -/
def unliftL : LitW → Lit
  | (s, .base v) => (s, v)
  | (s, _) => (s, V.tru)

theorem liftCl_unlift : ∀ {cl : List LitW}, cl.all isBaseW = true → liftCl (cl.map unliftL) = cl
  | [], _ => rfl
  | (s, w) :: cl, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    have ih := liftCl_unlift h.2
    cases w <;> simp [isBaseW] at h <;> simp only [liftCl, List.map_cons, unliftL, liftL] at ih ⊢ <;> rw [ih]

theorem holdsW_of_base (g : Geo) {cl : List LitW} (hb : cl.all isBaseW = true)
    (h : Holds (rho g) (cl.map unliftL)) : HoldsW (rhoW g) cl := by
  rw [← liftCl_unlift hb]
  exact (holdsW_rho_lift g _).2 h

/-! ### Gate rows of a `wgate` variable -/

/-- The three defining clauses of `wgate sa a sb b`. -/
def wgateRows (sa : Bool) (a : W) (sb : Bool) (b : W) : List (List LitW) :=
  [[(false, W.wgate sa a sb b), (sa, a)], [(false, W.wgate sa a sb b), (sb, b)],
   [(true, W.wgate sa a sb b), (!sa, a), (!sb, b)]]

/-- The clause contains a `wgate` literal and covers one of its three defining clauses. -/
def wgateOK (cl : List LitW) : Bool :=
  cl.any fun l => match l.2 with
    | .wgate sa a sb b => (wgateRows sa a sb b).any fun s => coversW cl s
    | _ => false

theorem wgateOK_sound (g : Geo) {cl : List LitW} (h : wgateOK cl = true) : HoldsW (rhoW g) cl := by
  unfold wgateOK at h
  obtain ⟨⟨s, w⟩, -, hl⟩ := List.any_eq_true.mp h
  cases w with
  | wgate sa a sb b =>
    obtain ⟨s', hs', hc⟩ := List.any_eq_true.mp hl
    obtain ⟨h1, h2, h3⟩ := wgate_rowsW sa a sb b (rhoW_wgate g sa a sb b)
    simp only [wgateRows, List.mem_cons, List.not_mem_nil, or_false] at hs'
    rcases hs' with rfl | rfl | rfl
    · exact HoldsW.of_covers (rhoW_proper g) hc h1
    · exact HoldsW.of_covers (rhoW_proper g) hc h2
    · exact HoldsW.of_covers (rhoW_proper g) hc h3
  | _ => simp at hl

/-! ### The dispatcher -/

/-- A stored parameter: `n >= 500` stands for `n - 1000`. -/
def toI (n : Nat) : Int := if 500 ≤ n then (n : Int) - 1000 else n

/-- The `view` of the packed `lineS` datum `p8 = 2 view + (1 if k < 0)`. -/
def lsView (p8 : Nat) : Nat := p8 / 2
/-- The sign `k` of the packed `lineS` datum. -/
def lsK (p8 : Nat) : Int := if p8 % 2 = 1 then -1 else 1

/-- The zero facet of a tie rule shifted by one (`0` for none: stored `999`). -/
def zs1Of (n : Nat) : Nat := if 500 ≤ n then 0 else n + 1

/-- The cycle of the `tfail t f sd c` variable of a family 39 row (its literal there is negative: `-tfail`). -/
def tfailVarOf (cl : List LitW) (t f sd : Nat) : List Nat :=
  (cl.findSome? fun l => match l with
    | (_, .tfail t' f' sd' c) => if t' == t && f' == f && sd' == sd then some c else none
    | _ => none).getD []

/-- The cycle of the flag `sf kind view f sd _` of a family 41 row (its literal there is negative: `-sf`). -/
def sfCycOf (cl : List LitW) (kind view f sd : Nat) : List Nat :=
  (cl.findSome? fun l => match l with
    | (_, .sf k' v' f' sd' c) => if k' == kind && v' == view && f' == f && sd' == sd then some c else none
    | _ => none).getD []

/-- **The check of a decoded row** (family, the eight parameters, the clause over `W`); `U` is the class unit list. -/
def rowWc (U : List LitW) (fam : Nat) (p : List Nat) (cl : List LitW) : Bool :=
  (rowOK3 fam p (cl.map unliftL) && cl.all isBaseW) ||
  ((fam == 17 && (ruleOK p (cl.map unliftL) && cl.all isBaseW)) ||
  ((fam == 19 && (witOK p (cl.map unliftL) && cl.all isBaseW)) ||
  ((fam == 22 && (tllOK p (cl.map unliftL) && cl.all isBaseW)) ||
  ((fam == 24 && (krelOK p (cl.map unliftL) && cl.all isBaseW)) ||
  ((fam == 20 && wgateOK cl) ||
  ((fam == 26 && (cl.length == 1 && cl.all fun l => U.contains l)) ||
  ((fam == 23 && tieOK (p.getD 0 0) (p.getD 1 0) (p.getD 2 0) (p.getD 3 0) (zs1Of (p.getD 5 0)) cl) ||
  ((fam == 30 && (linkChk (p.getD 0 0) (p.getD 1 0) (p.getD 2 0) (p.getD 3 0) (p.getD 4 0) (toI (p.getD 5 0)) &&
      (linkRows (p.getD 0 0) (p.getD 1 0) (p.getD 2 0) (p.getD 3 0) (p.getD 4 0) (toI (p.getD 5 0))).any fun s => coversW cl s)) ||
  ((fam == 31 && (plkChk (p.getD 0 0) (p.getD 1 0) (p.getD 2 0) (p.getD 3 0) (p.getD 4 0) &&
      (plkRows (p.getD 0 0) (p.getD 1 0) (p.getD 2 0) (p.getD 3 0) (p.getD 4 0)).any fun s => coversW cl s)) ||
  ((fam == 32 && (cramChk (p.getD 0 0) (p.getD 1 0) (p.getD 2 0) (lsView (p.getD 7 0)) (lsK (p.getD 7 0))
        (p.getD 3 0) (p.getD 4 0) (p.getD 5 0) &&
      (cramRows (p.getD 0 0) (p.getD 1 0) (p.getD 2 0) (lsView (p.getD 7 0)) (lsK (p.getD 7 0))
        (p.getD 3 0) (p.getD 4 0) (p.getD 5 0)).any fun s => coversW cl s)) ||
  ((fam == 33 && (prowChk (p.getD 0 0) (p.getD 1 0) (p.getD 2 0) (p.getD 3 0) (p.getD 4 0) &&
      (prowRows (p.getD 0 0) (p.getD 1 0) (p.getD 2 0) (p.getD 3 0) (p.getD 4 0)).any fun s => coversW cl s)) ||
  ((fam == 34 && chk34 (p.getD 0 0) (p.getD 1 0) (p.getD 2 0) (p.getD 3 0) (p.getD 4 0) (p.getD 5 0) cl) ||
  ((fam == 35 && chk35 (p.getD 0 0) (p.getD 1 0) (p.getD 2 0) (p.getD 3 0) (p.getD 4 0) (toI (p.getD 5 0))
      (toI (p.getD 6 0)) (if p.getD 0 0 == 2 then lsView (p.getD 7 0) else 0) (if p.getD 0 0 == 2 then lsK (p.getD 7 0) else 0) cl) ||
  ((fam == 36 && chk36 (p.getD 0 0) (p.getD 1 0) (p.getD 2 0) (p.getD 3 0) (p.getD 4 0) (p.getD 5 0) cl) ||
  ((fam == 38 && chk38 (p.getD 1 0) (p.getD 2 0) (p.getD 3 0) (p.getD 4 0) (p.getD 5 0) (p.getD 6 0) (p.getD 7 0) cl) ||
  (fam == 39 && chk39 (p.getD 1 0) (p.getD 2 0) (p.getD 3 0) (tfailVarOf cl (p.getD 1 0) (p.getD 2 0) (p.getD 3 0)) cl)
  )))))))))))))))

/-- The check of a packed row. -/
def rowW (U : List LitW) (chunks : List (List W)) (n : Nat) : Bool :=
  rowWc U (decRow n).1 (decRow n).2.1 ((decRow n).2.2.map (litOfCW chunks))

variable {x : Fin 7 → ℝ³}

/-- **A checked row holds** under `rhoW` of every non-Rupert type 24 shape, given the class literals `U`. -/
theorem rowWc_holds (U : List LitW) (F : S0xFac 9 s0x_S24 x) (hx : Function.Injective x)
    (hNR : ¬ IsRupert (univ.image x)) (hG : GeoOK (geoF F)) (hU : ∀ l ∈ U, evalW (rhoW (geoF F)) l = true)
    {fam : Nat} {p : List Nat} {cl : List LitW} (h : rowWc U fam p cl = true) : HoldsW (rhoW (geoF F)) cl := by
  unfold rowWc at h
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h
  rcases h with ⟨h1, hb⟩ | ⟨-, h2, hb⟩ | ⟨-, h3, hb⟩ | ⟨-, h4, hb⟩ | ⟨-, h5, hb⟩ | ⟨-, h6⟩ | ⟨-, h7, h7'⟩ | ⟨-, h8⟩ |
    ⟨-, h9, h9'⟩ | ⟨-, h10, h10'⟩ | ⟨-, h11, h11'⟩ | ⟨-, h12, h12'⟩ | ⟨-, h13⟩ | ⟨-, h14⟩ | ⟨-, h15⟩ | ⟨-, h16⟩ | ⟨-, h17⟩
  · exact holdsW_of_base _ hb (rowOK3_sound hG h1)
  · exact holdsW_of_base _ hb (ruleOK_sound F hx hNR hG h2)
  · exact holdsW_of_base _ hb (witOK_sound F hG h3)
  · exact holdsW_of_base _ hb (tllOK_sound hG h4)
  · exact holdsW_of_base _ hb (krelOK_sound hG h5)
  · exact wgateOK_sound _ h6
  · obtain ⟨l, hl⟩ : ∃ l, l ∈ cl := by
      have : 0 < cl.length := by omega
      exact ⟨_, List.getElem_mem this⟩
    have hu := List.all_eq_true.mp h7' l hl
    exact ⟨l, hl, hU l (by simpa using hu)⟩
  · exact tieOK_sound F hx hNR hG h8
  · exact link_cover hG h9 (by simpa using h9')
  · exact plk_cover h10 (by simpa using h10')
  · exact cram_cover hG h11 (by simpa using h11')
  · exact prow_cover h12 (by simpa using h12')
  · exact fam34_sound hG h13
  · exact fam35_sound hG h14
  · exact fam36_rhoW F hG h15
  · exact fam38_sound hG h16
  · exact fam39_sound hG h17

end Minimality.H24T.SAT
