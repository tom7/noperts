module

public import Minimality.Type21SAT.RowSound

@[expose] public section

/-!
# L3, part 24: the lex definition rows of core B (families 23, 24, 27)

`ltl` (lex less-than of two depths), `yl` (the four pairs of an alternation are not lex less-than) and `faill`
(the lex failure of a cycle), checked as the families 15 and 16 are.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
open scoped RealInnerProductSpace
open Classical

namespace Minimality.H21.SAT

/-- The two clauses of an `ltl` row. -/
def ltlS (e d ep p q : Nat) : List (List Lit) :=
  [[(ordS e p q).2.neg, (true, V.ltl e d ep p q)],
   [(ordS e p q).1, (ordS e p q).2, (ordE d ep p q).2.neg, (true, V.ltl e d ep p q)]]

/-- An `ltl` row (family 23): the clause covers one of the two clauses of the definition. -/
def ltlOK (cl : List Lit) : Bool :=
  cl.any fun l => match l with
    | (true, .ltl e d ep p q) =>
      decide (e < 36 ∧ d < 21 ∧ p < 7 ∧ q < 7 ∧ p ≠ q) && anyCov cl (ltlS e d ep p q)
    | _ => false

/-- The clauses of a `yl` row. -/
def ylS (e d ep : Nat) (c : List Nat) (p1 p2 q1 q2 : Nat) : List (List Lit) :=
  [p1, p2].flatMap fun p => [q1, q2].map fun q =>
    [(false, V.yl e d ep c p1 p2 q1 q2), (false, V.ltl e d ep p q)]

/-- A `yl` row (family 24). -/
def ylOK (cl : List Lit) : Bool :=
  cl.any fun l => match l with
    | (false, .yl e d ep c p1 p2 q1 q2) => anyCov cl (ylS e d ep c p1 p2 q1 q2)
    | _ => false

/-- The clause of a `faill` row. -/
def faillS (e d ep : Nat) (c : List Nat) : List Lit :=
  (false, V.faill e d ep c) :: (alts c).map fun t => (true, V.yl e d ep c t.1 t.2.1 t.2.2.1 t.2.2.2)

/-- A `faill` row (family 27). -/
def faillOK (cl : List Lit) : Bool :=
  cl.any fun l => match l with
    | (false, .faill e d ep c) => coversF cl (faillS e d ep c)
    | _ => false

/-- The check of the lex definition families. -/
def lexDefOK (fam : Nat) (cl : List Lit) : Bool :=
  match fam with
  | 23 => ltlOK cl
  | 24 => ylOK cl
  | 27 => faillOK cl
  | _ => false

/-- **Lex definition rows that pass the check are true of the real data.** -/
theorem lexDefOK_sound (g : Geo) (hG : GeoOK g) {fam : Nat} {cl : List Lit}
    (h : lexDefOK fam cl = true) : Holds (rho g) cl := by
  unfold lexDefOK at h
  match fam, h with
  | 23, h =>
    obtain ⟨l, -, hl⟩ := List.any_eq_true.mp h
    obtain ⟨s, v⟩ := l
    cases s <;> cases v <;> simp only [Bool.false_eq_true] at hl
    rename_i e d ep p q
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hl
    obtain ⟨⟨he, hd, hp, hq, hpq⟩, hcov⟩ := hl
    refine anyCov_holds (rho_proper g) hcov ?_
    have := ltl_rows g e d ep p q (fun h' => hG.hv _ h') (fun h' => hG.hv _ h')
      (fun a b hab hb => vv_EI g hab hb) hp hq hpq
    intro s hs
    simp only [ltlS, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact this.1
    · exact this.2
  | 24, h =>
    obtain ⟨l, -, hl⟩ := List.any_eq_true.mp h
    obtain ⟨s, v⟩ := l
    cases s <;> cases v <;> simp only [Bool.false_eq_true] at hl
    rename_i e d ep c p1 p2 q1 q2
    refine anyCov_holds (rho_proper g) hl ?_
    intro s hs
    simp only [ylS, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false, List.mem_map] at hs
    obtain ⟨a, ha, b, hb, rfl⟩ := hs
    exact yl_rows g e d ep c p1 p2 q1 q2 a b ⟨by simpa using ha, by simpa using hb⟩
  | 27, h =>
    obtain ⟨l, -, hl⟩ := List.any_eq_true.mp h
    obtain ⟨s, v⟩ := l
    cases s <;> cases v <;> simp only [Bool.false_eq_true] at hl
    rename_i e d ep c
    rw [coversF_eq] at hl
    exact Holds.of_covers (rho_proper g) hl (faill_rows g e d ep c)
  | n + 28, h => simp at h
  | 0, h => simp at h
  | 1, h => simp at h
  | 2, h => simp at h
  | 3, h => simp at h
  | 4, h => simp at h
  | 5, h => simp at h
  | 6, h => simp at h
  | 7, h => simp at h
  | 8, h => simp at h
  | 9, h => simp at h
  | 10, h => simp at h
  | 11, h => simp at h
  | 12, h => simp at h
  | 13, h => simp at h
  | 14, h => simp at h
  | 15, h => simp at h
  | 16, h => simp at h
  | 17, h => simp at h
  | 18, h => simp at h
  | 19, h => simp at h
  | 20, h => simp at h
  | 21, h => simp at h
  | 22, h => simp at h
  | 25, h => simp at h
  | 26, h => simp at h

end Minimality.H21.SAT
