module

public import Minimality.Type24SAT.Geo.Tabs

@[expose] public section

/-!
# L3, part 13: the row check of the families that are not rules or witnesses

`rowOK3 fam p cl` says the clause `cl` (a list of literals) is an instance of the schema of its family.
`rowOK3_sound` : under `GeoOK` (the facet facts, the orientation, nonzero edge views) every clause that
passes is true of the real assignment `rho g`.  Families: 8 cramer, 11 texcl, 12 row3, 13 row4, 14 line,
15 y, 16 failbig, 20 gate, 21 sign exclusion.  Equality of variables is by `eqV` (constructor by constructor).
-/

set_option autoImplicit false
open scoped RealInnerProductSpace
open Classical

open Minimality.H29.SAT

namespace Minimality.H24.SAT

/-! ### Fast equality -/

/-- Equality of lists of naturals. -/
def eqNL : List Nat → List Nat → Bool
  | [], [] => true
  | a :: as, b :: bs => (a == b) && eqNL as bs
  | _, _ => false

/-- The list equality is equality. -/
theorem eqNL_iff : ∀ (a b : List Nat), eqNL a b = true ↔ a = b
  | [], [] => by simp [eqNL]
  | [], _ :: _ => by simp [eqNL]
  | _ :: _, [] => by simp [eqNL]
  | a :: as, b :: bs => by simp [eqNL, eqNL_iff as bs]

/-- Fast equality of variables. -/
def eqV : V → V → Bool
  | .tru, .tru => true
  | .br a b c d, .br a' b' c' d' => (a == a') && (b == b') && (c == c') && (d == d')
  | .lv a b c p q, .lv a' b' c' p' q' => (a == a') && (b == b') && (c == c') && (p == p') && (q == q')
  | .mv e f g, .mv e' f' g' => (e == e') && (f == f') && (g == g')
  | .fv t p q, .fv t' p' q' => (t == t') && (p == p') && (q == q')
  | .nv r s t, .nv r' s' t' => (r == r') && (s == s') && (t == t')
  | .kv t e f, .kv t' e' f' => (t == t') && (e == e') && (f == f')
  | .ng a, .ng a' => eqV a a'
  | .gate sa a sb b, .gate sa' a' sb' b' => (sa == sa') && eqV a a' && (sb == sb') && eqV b b'
  | .tp e f, .tp e' f' => (e == e') && (f == f')
  | .tq e f, .tq e' f' => (e == e') && (f == f')
  | .tpv e m s, .tpv e' m' s' => (e == e') && (m == m') && (s == s')
  | .yv e p1 p2 q1 q2, .yv e' p1' p2' q1' q2' =>
    (e == e') && (p1 == p1') && (p2 == p2') && (q1 == q1') && (q2 == q2')
  | .fail e c, .fail e' c' => (e == e') && eqNL c c'
  | .ltl e d ep p q, .ltl e' d' ep' p' q' => (e == e') && (d == d') && (ep == ep') && (p == p') && (q == q')
  | .yl e d ep c p1 p2 q1 q2, .yl e' d' ep' c' p1' p2' q1' q2' =>
    (e == e') && (d == d') && (ep == ep') && eqNL c c' && (p1 == p1') && (p2 == p2') && (q1 == q1') && (q2 == q2')
  | .faill e d ep c, .faill e' d' ep' c' => (e == e') && (d == d') && (ep == ep') && eqNL c c'
  | _, _ => false

/-- `eqV` is equality of variables. -/
theorem eqV_iff : ∀ (a b : V), eqV a b = true ↔ a = b := by
  intro a
  induction a with
  | tru => intro b; cases b <;> simp [eqV]
  | br a b c d => intro w; cases w <;> simp [eqV, and_assoc]
  | lv a b c p q => intro w; cases w <;> simp [eqV, and_assoc]
  | mv e f g => intro w; cases w <;> simp [eqV, and_assoc]
  | fv t p q => intro w; cases w <;> simp [eqV, and_assoc]
  | nv r s t => intro w; cases w <;> simp [eqV, and_assoc]
  | kv t e f => intro w; cases w <;> simp [eqV, and_assoc]
  | ng a iha => intro w; cases w <;> simp [eqV, iha]
  | gate sa a sb b iha ihb => intro w; cases w <;> simp [eqV, iha, ihb, and_assoc]
  | tp e f => intro w; cases w <;> simp [eqV]
  | tq e f => intro w; cases w <;> simp [eqV]
  | tpv e m s => intro w; cases w <;> simp [eqV, and_assoc]
  | yv e p1 p2 q1 q2 => intro w; cases w <;> simp [eqV, and_assoc]
  | fail e c => intro w; cases w <;> simp [eqV, eqNL_iff]
  | ltl e d ep p q => intro w; cases w <;> simp [eqV, and_assoc]
  | yl e d ep c p1 p2 q1 q2 => intro w; cases w <;> simp [eqV, eqNL_iff, and_assoc]
  | faill e d ep c => intro w; cases w <;> simp [eqV, eqNL_iff, and_assoc]

/-- Fast equality of literals. -/
def eqL (a b : Lit) : Bool := (a.1 == b.1) && eqV a.2 b.2

/-- `eqL` is equality. -/
theorem eqL_iff (a b : Lit) : eqL a b = true ↔ a = b := by
  obtain ⟨s, v⟩ := a; obtain ⟨s', v'⟩ := b
  simp [eqL, eqV_iff]

/-- `covers` with fast equality. -/
def coversF (cl s : List Lit) : Bool := s.all fun l => eqL l lfalse || cl.any (eqL l)

/-- `coversF` is `covers`. -/
theorem coversF_eq (cl s : List Lit) : coversF cl s = covers cl s := by
  rw [Bool.eq_iff_iff]
  simp [coversF, covers, List.all_eq_true, List.any_eq_true, eqL_iff]

/-- Some clause of the list is covered. -/
def anyCov (cl : List Lit) (S : List (List Lit)) : Bool := S.any (coversF cl)

/-- If every clause of `S` holds, a clause covering one of them holds. -/
theorem anyCov_holds {ρ : V → Bool} (hP : Proper ρ) {cl : List Lit} {S : List (List Lit)}
    (h : anyCov cl S = true) (hS : ∀ s ∈ S, Holds ρ s) : Holds ρ cl := by
  obtain ⟨s, hs, hc⟩ := List.any_eq_true.mp h
  rw [coversF_eq] at hc
  exact Holds.of_covers hP hc (hS s hs)

/-! ### What the rows need from the real data -/

/-- Parameter `i` of a row (0 if absent). -/
def prm (p : List Nat) (i : Nat) : Nat := p.getD i 0

/-- The facts about the real data that the rows use. -/
structure GeoOK (g : Geo) : Prop where
  hF : FacOK g
  hO : OriOK g
  hv : ∀ e, e < 21 → g.vv e ≠ 0

/-- The view of the pair `a < b < 7` is the difference `x a - x b`. -/
theorem vv_EI (g : Geo) {a b : Nat} (hab : a < b) (hb : b < 7) : g.vv (EI a b) = g.x a - g.x b := by
  have key : ∀ a < 7, ∀ b < 7, a < b → EI a b < 21 ∧ EA (EI a b) = a ∧ EB (EI a b) = b := by
    decide +kernel
  obtain ⟨h1, h2, h3⟩ := key a (by omega) b hb hab
  simp only [Geo.vv, h1, ite_true, Geo.dv, h2, h3]

/-- Views below 21 are the differences. -/
theorem vv_lt (g : Geo) {e : Nat} (h : e < 21) : g.vv e = g.dv e := by simp [Geo.vv, h]

/-- The ends of an edge are points of the shape. -/
theorem EAB_lt : ∀ e < 21, EA e < 7 ∧ EB e < 7 := by decide +kernel

/-- Table of the tables: `tab3` keys. -/
abbrev EOK (g : Geo) : Prop :=
  EntOK tab3 g (fun a b c => hasKey3 triRoutes a b c = true) (fun a b c => hasKey3 nlRoutes a b c = true)
    (fun _t p q => p < 7 ∧ q < 7)

/-- The tables tell the truth for a shape with `GeoOK`. -/
theorem GeoOK.eok {g : Geo} (h : GeoOK g) : EOK g := entOK_tab3 h.hF h.hO

/-! ### The schemas, with their side conditions -/

/-- Cramer row: sorted facets, points, keys. -/
def cramerOK (p : List Nat) (cl : List Lit) : Bool :=
  let a := prm p 0; let b := prm p 1; let c := prm p 2; let d := prm p 3; let q1 := prm p 4; let q2 := prm p 5
  decide (a < b ∧ b < c ∧ c < d ∧ d < 9 ∧ q1 < 7 ∧ q2 < 7) &&
  hasKey3 nlRoutes b c d && hasKey3 nlRoutes a c d && hasKey3 nlRoutes a b d && hasKey3 nlRoutes a b c &&
  anyCov cl (cramer tab3 a b c d q1 q2)

/-- The `row3` row. -/
def row3OK (p : List Nat) (cl : List Lit) : Bool :=
  decide (prm p 0 < 43 ∧ prm p 1 < 7 ∧ prm p 2 < 7 ∧ prm p 3 < 7 ∧ prm p 1 ≠ prm p 2 ∧
    prm p 2 ≠ prm p 3 ∧ prm p 3 ≠ prm p 1) &&
  anyCov cl (row3 (prm p 0) (prm p 1) (prm p 2) (prm p 3))

/-- The `row4` row: five numbers, four triples of the table. -/
def row4OK (p : List Nat) (cl : List Lit) : Bool :=
  let e := prm p 0; let f0 := prm p 1; let f1 := prm p 2; let f2 := prm p 3; let f3 := prm p 4
  decide (e < 43 ∧ f0 < 21 ∧ f1 < 21 ∧ f2 < 21 ∧ f3 < 21) &&
  hasKey3 triRoutes f1 f2 f3 && hasKey3 triRoutes f0 f2 f3 && hasKey3 triRoutes f0 f1 f3 &&
  hasKey3 triRoutes f0 f1 f2 && anyCov cl (row4 tab3 e f0 f1 f2 f3)

/-- Line view `L` by its two facets. -/
def lineOf (L : Nat) : Nat × Nat := lines.getD (L - 21) (0, 0)

/-- The kappa sign claimed by a line row is the sign of the constant `Aconst` of its facet. -/
def kapChk (p : List Nat) : Bool :=
  let ab := lineOf (prm p 1)
  let a := if prm p 2 = 0 then ab.1 else ab.2
  let c := Aconst a (prm p 3) (prm p 4)
  let σ : Int := if prm p 2 = 0 then 1 else -1
  decide (σ * c ≠ 0) && (decide (0 < σ * c) == (prm p 5 == 1))

/-- Side conditions of a line row (`r` the view, `L` the line view, the edges `e1, e2` of the facet). -/
def lineSide (r L side e1 e2 : Nat) : Bool :=
  let ab := lineOf L
  let a := if side = 0 then ab.1 else ab.2
  decide (r < 43 ∧ 21 ≤ L ∧ L < 43 ∧ side < 2 ∧ e1 < 21 ∧ e2 < 21 ∧ a < 9) &&
  inF a (EA e1) && inF a (EB e1) && inF a (EA e2) && inF a (EB e2)

/-- The line row (parameters `r L side e1 e2 kap`). -/
def lineOK (p : List Nat) (cl : List Lit) : Bool :=
  lineSide (prm p 0) (prm p 1) (prm p 2) (prm p 3) (prm p 4) && kapChk p &&
  anyCov cl (lineS tab3 (prm p 0) (prm p 1)
    (if prm p 2 = 0 then (lineOf (prm p 1)).2 else (lineOf (prm p 1)).1)
    (prm p 3) (prm p 4) (prm p 5 == 1))

/-- A shape entry (an atom with a positive and a negative variable). -/
def isAtom : V → Bool
  | .br .. | .lv .. | .mv .. | .fv .. | .nv .. | .kv .. => true
  | _ => false

/-- Sign exclusion row: `not v, not (ng v)` for an atom `v`. -/
def signOK (cl : List Lit) : Bool :=
  cl.any fun l => isAtom l.2 && coversF cl [(false, l.2), (false, V.ng l.2)]

/-- `T` exclusion row. -/
def texclOK (cl : List Lit) : Bool :=
  cl.any fun l => match l.2 with
    | .tp e f => coversF cl [(false, V.tp e f), (false, V.tq e f)]
    | _ => false

/-- The clauses of a `y` row: `y` implies each of its four weak inequalities. -/
def yS (e p1 p2 q1 q2 : Nat) : List (List Lit) :=
  [p1, p2].flatMap fun p => [q1, q2].map fun q =>
    [(false, V.yv e p1 p2 q1 q2), (ordS e p q).2.neg]

/-- A `y` row. -/
def yOK (cl : List Lit) : Bool :=
  cl.any fun l => match l with
    | (false, .yv e p1 p2 q1 q2) =>
      decide (e < 43 ∧ p1 < 7 ∧ p2 < 7 ∧ q1 < 7 ∧ q2 < 7 ∧ p1 ≠ q1 ∧ p1 ≠ q2 ∧ p2 ≠ q1 ∧ p2 ≠ q2) &&
      anyCov cl (yS e p1 p2 q1 q2)
    | _ => false

/-- The clause of a failure row. -/
def failS (e : Nat) (c : List Nat) : List Lit :=
  (false, V.fail e c) :: (alts c).map fun t => (true, V.yv e t.1 t.2.1 t.2.2.1 t.2.2.2)

/-- A failure row. -/
def failOK (cl : List Lit) : Bool :=
  cl.any fun l => match l with
    | (false, .fail e c) => coversF cl (failS e c)
    | _ => false

/-- A gate row: some literal names a gate whose operands give the gate by `andL`, and the clause covers one of the
three clauses of `y = a and b`. -/
def gateOK (cl : List Lit) : Bool :=
  cl.any fun l => match l.2 with
    | .gate sa a sb b =>
      eqL (andL (sa, a) (sb, b)) (true, V.gate sa a sb b) &&
      anyCov cl [[Lit.neg (true, V.gate sa a sb b), (sa, a)], [Lit.neg (true, V.gate sa a sb b), (sb, b)],
        [(true, V.gate sa a sb b), Lit.neg (sa, a), Lit.neg (sb, b)]]
    | _ => false

/-- The check of the families that are not rules or witnesses. -/
def rowOK3 (fam : Nat) (p : List Nat) (cl : List Lit) : Bool :=
  match fam with
  | 8 => cramerOK p cl
  | 11 => texclOK cl
  | 12 => row3OK p cl
  | 13 => row4OK p cl
  | 14 => lineOK p cl
  | 15 => yOK cl
  | 16 => failOK cl
  | 20 => gateOK cl
  | 21 => signOK cl
  | _ => false

end Minimality.H24.SAT
