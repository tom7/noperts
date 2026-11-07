module

public import Minimality.OctaTools

@[expose] public section

/-!
# L3, part 1: variables, literals, the three valued product, the relation lemma

Three valued from the start (L/DESIGN.md section 12, ST/core/CORE.md section 4).  A shape entry (atom) `v`
has two Boolean variables: `v` (`atom > 0`) and `ng v` (`atom < 0`), so it may vanish.  A product
of three valued signs is built from `gate` (the AND of two literals), as the encoder does
(`andL`, `orL`, `mul3` of ST/core/gc.cc).  There are no `prod` and `mux` variables.
-/

set_option autoImplicit false
open scoped RealInnerProductSpace

namespace Minimality.H29.SAT

/-- A CNF variable, by meaning.  `br lv mv fv nv kv` are the shape entries (`> 0`); `ng v` is `atom v < 0`;
`gate sa a sb b` is the AND of two literals; `tp e f`, `tq e f` the signs `> 0`, `< 0` of an inner product of
two views; `tpv e mask sig` the tope variable; `yv`, `fail` as in the two valued bridge. -/
inductive V where
  | tru
  | br (a b c d : Nat)
  | lv (a b c p q : Nat)
  | mv (e f g : Nat)
  | fv (t p q : Nat)
  | nv (r s t : Nat)
  | kv (t e f : Nat)
  | ng (a : V)
  | gate (sa : Bool) (a : V) (sb : Bool) (b : V)
  | tp (e f : Nat)
  | tq (e f : Nat)
  | tpv (e mask sig : Nat)
  | yv (e p1 p2 q1 q2 : Nat)
  | fail (e : Nat) (c : List Nat)
  /-- lex less-than of the depths of `p`, `q`: `z e p q < 0`, or `= 0` and `eps * z d p q < 0` (tag 23); `ep = 1` is `eps = +1` -/
  | ltl (e d ep p q : Nat)
  /-- the four pairs of an alternation are not lex less-than, for the cycle `c` (tag 24) -/
  | yl (e d ep : Nat) (c : List Nat) (p1 p2 q1 q2 : Nat)
  /-- the lex failure of the cycle `c` (tag 27) -/
  | faill (e d ep : Nat) (c : List Nat)
  deriving DecidableEq, Repr

/-- An injective code of a variable as a list of numbers (prefix-free), used only to order gate operands. -/
def V.key : V → List Nat
  | .tru => [0]
  | .br a b c d => [1, a, b, c, d]
  | .lv a b c p q => [2, a, b, c, p, q]
  | .mv e f g => [3, e, f, g]
  | .fv t p q => [4, t, p, q]
  | .nv r s t => [5, r, s, t]
  | .kv t e f => [6, t, e, f]
  | .ng a => 7 :: a.key
  | .gate sa a sb b => [8, sa.toNat, (a.key).length] ++ a.key ++ [sb.toNat] ++ b.key
  | .tp e f => [9, e, f]
  | .tq e f => [10, e, f]
  | .tpv e m s => [11, e, m, s]
  | .yv e p1 p2 q1 q2 => [12, e, p1, p2, q1, q2]
  | .fail e c => [13, e, c.length] ++ c
  | .ltl e d ep p q => [14, e, d, ep, p, q]
  | .yl e d ep c p1 p2 q1 q2 => [15, e, d, ep, c.length] ++ c ++ [p1, p2, q1, q2]
  | .faill e d ep c => [16, e, d, ep, c.length] ++ c

/-- Lexicographic comparison of two codes (structural, so that the kernel can evaluate it). -/
def cmpKey : List Nat → List Nat → Ordering
  | [], [] => .eq
  | [], _ :: _ => .lt
  | _ :: _, [] => .gt
  | x :: xs, y :: ys => if x < y then .lt else if y < x then .gt else cmpKey xs ys

/-- A literal: sign (`true` = positive) and variable. -/
abbrev Lit := Bool × V

/-- The true literal. -/
def ltrue : Lit := (true, V.tru)
/-- The false literal. -/
def lfalse : Lit := (false, V.tru)
/-- Negation of a literal. -/
def Lit.neg (l : Lit) : Lit := (!l.1, l.2)

/-- Value of a literal under an assignment. -/
def evalL (ρ : V → Bool) (l : Lit) : Bool := l.1 == ρ l.2

/-- An assignment is proper if the constant variable is true. -/
def Proper (ρ : V → Bool) : Prop := ρ V.tru = true

/-- A clause holds if one of its literals is true. -/
def Holds (ρ : V → Bool) (c : List Lit) : Prop := ∃ l ∈ c, evalL ρ l = true

/-- The value of a negated literal. -/
theorem evalL_neg (ρ : V → Bool) (l : Lit) : evalL ρ l.neg = !evalL ρ l := by
  obtain ⟨s, v⟩ := l
  cases s <;> cases ρ v <;> simp [evalL, Lit.neg]

/-- An assignment respects `gate`: the variable is the AND of its two literals. -/
def GateOK (ρ : V → Bool) : Prop :=
  ∀ sa a sb b, ρ (V.gate sa a sb b) = (evalL ρ (sa, a) && evalL ρ (sb, b))

/-- Order on signs: false before true. -/
def cmpB : Bool → Bool → Ordering
  | false, false => .eq
  | false, true => .lt
  | true, false => .gt
  | true, true => .eq

/-- AND of two literals, as the encoder forms it (constants fold; `a` and `not a` give false;
the gate operands are put in a fixed order). -/
def andL (a b : Lit) : Lit :=
  if a = lfalse ∨ b = lfalse then lfalse
  else if a = ltrue then b
  else if b = ltrue then a
  else if a = b then a
  else if a = b.neg then lfalse
  else if (cmpKey a.2.key b.2.key).then (cmpB a.1 b.1) = Ordering.gt then (true, V.gate b.1 b.2 a.1 a.2)
  else (true, V.gate a.1 a.2 b.1 b.2)

/-- `andL` is the AND of the values. -/
theorem evalL_andL {ρ : V → Bool} (hP : Proper ρ) (hG : GateOK ρ) (a b : Lit) :
    evalL ρ (andL a b) = (evalL ρ a && evalL ρ b) := by
  have e : ρ V.tru = true := hP
  have hf : evalL ρ lfalse = false := by simp [lfalse, evalL, e]
  have ht : evalL ρ ltrue = true := by simp [ltrue, evalL, e]
  unfold andL
  by_cases h1 : a = lfalse ∨ b = lfalse
  · rw [if_pos h1]
    rcases h1 with rfl | rfl <;> simp [hf]
  · rw [if_neg h1]
    by_cases h2 : a = ltrue
    · rw [if_pos h2]; subst h2; simp [ht]
    · rw [if_neg h2]
      by_cases h3 : b = ltrue
      · rw [if_pos h3]; subst h3; simp [ht]
      · rw [if_neg h3]
        by_cases h4 : a = b
        · rw [if_pos h4]; subst h4; simp
        · rw [if_neg h4]
          by_cases h5 : a = b.neg
          · rw [if_pos h5]; rw [h5, evalL_neg, hf]; cases evalL ρ b <;> simp
          · rw [if_neg h5]
            split_ifs
            · have := hG b.1 b.2 a.1 a.2
              simp only [evalL] at this ⊢
              rw [this]; simp [Bool.and_comm]
            · have := hG a.1 a.2 b.1 b.2
              simp only [evalL] at this ⊢
              rw [this]; cases (a.1 == ρ a.2 && b.1 == ρ b.2) <;> rfl

/-- OR of two literals. -/
def orL (a b : Lit) : Lit := (andL a.neg b.neg).neg

/-- `orL` is the OR of the values. -/
theorem evalL_orL {ρ : V → Bool} (hP : Proper ρ) (hG : GateOK ρ) (a b : Lit) :
    evalL ρ (orL a b) = (evalL ρ a || evalL ρ b) := by
  unfold orL
  rw [evalL_neg, evalL_andL hP hG, evalL_neg, evalL_neg]
  cases evalL ρ a <;> cases evalL ρ b <;> rfl

/-- A three valued sign: literals for `> 0` and for `< 0`. -/
abbrev S3 := Lit × Lit

/-- `Sg3 ρ t r`: the two literals of `t` say exactly whether `r` is positive, and negative. -/
def Sg3 (ρ : V → Bool) (t : S3) (r : ℝ) : Prop :=
  (evalL ρ t.1 = true ↔ 0 < r) ∧ (evalL ρ t.2 = true ↔ r < 0)

/-- Negation of a three valued sign. -/
def negS (t : S3) : S3 := (t.2, t.1)

/-- Negating swaps the two literals. -/
theorem Sg3.neg {ρ : V → Bool} {t : S3} {r : ℝ} (h : Sg3 ρ t r) : Sg3 ρ (negS t) (-r) :=
  ⟨by simpa [negS] using h.2, by simpa [negS] using h.1⟩

/-- Zero as a three valued sign. -/
def zeroS : S3 := (lfalse, lfalse)

/-- The three valued sign of an atom `v` (a shape entry): `v` is `> 0`, `ng v` is `< 0`. -/
def atomS (v : V) : S3 := ((true, v), (true, V.ng v))

/-- **An atom has the three valued sign of its real, nonzero or not.**  The only hypothesis is the
meaning of the two variables (`ρ v = decide (0 < r)`, `ρ (ng v) = decide (r < 0)`). -/
theorem Sg3_atom {ρ : V → Bool} {v : V} {r : ℝ} (h1 : ρ v = decide (0 < r))
    (h2 : ρ (V.ng v) = decide (r < 0)) : Sg3 ρ (atomS v) r := by
  simp [Sg3, atomS, evalL, h1, h2]

/-- The sign of a nonzero integer constant (or zero) as a three valued sign. -/
def cS (c : Int) : S3 := if 0 < c then (ltrue, lfalse) else if c < 0 then (lfalse, ltrue) else zeroS

/-- A constant has the sign of its value. -/
theorem Sg3_cS {ρ : V → Bool} (hP : Proper ρ) (c : Int) {r : ℝ}
    (hr : (0 < c → 0 < r) ∧ (c < 0 → r < 0) ∧ (c = 0 → r = 0)) : Sg3 ρ (cS c) r := by
  have e : ρ V.tru = true := hP
  unfold cS
  rcases lt_trichotomy c 0 with h | h | h
  · have := hr.2.1 h
    simp [h, not_lt.mpr h.le, Sg3, ltrue, lfalse, evalL, e, this, not_lt.mpr this.le]
  · have := hr.2.2 h
    subst h
    simp [Sg3, zeroS, lfalse, evalL, e, this]
  · have := hr.1 h
    simp [h, not_lt.mpr h.le, Sg3, ltrue, lfalse, evalL, e, this, not_lt.mpr this.le]

/-- Zero is the sign of 0. -/
theorem Sg3_zero {ρ : V → Bool} (hP : Proper ρ) : Sg3 ρ zeroS 0 := by
  have e : ρ V.tru = true := hP
  simp [Sg3, zeroS, lfalse, evalL, e]

/-- **The three valued product** (`mul3` of the encoder), from gates. -/
def mul3 (a b : S3) : S3 :=
  (orL (andL a.1 b.1) (andL a.2 b.2), orL (andL a.1 b.2) (andL a.2 b.1))

/-- **The product of two three valued signs.**  No nonzero hypothesis on either factor. -/
theorem Sg3.mul3 {ρ : V → Bool} (hP : Proper ρ) (hG : GateOK ρ) {a b : S3} {r s : ℝ}
    (ha : Sg3 ρ a r) (hb : Sg3 ρ b s) : Sg3 ρ (SAT.mul3 a b) (r * s) := by
  obtain ⟨a1, a2⟩ := ha
  obtain ⟨b1, b2⟩ := hb
  simp only [Sg3, SAT.mul3, evalL_orL hP hG, evalL_andL hP hG, Bool.or_eq_true,
    Bool.and_eq_true, a1, a2, b1, b2]
  rcases lt_trichotomy r 0 with hr | hr | hr <;> rcases lt_trichotomy s 0 with hs | hs | hs
  · have := mul_pos_of_neg_of_neg hr hs
    simp [hr, hs, this, not_lt.mpr hr.le, not_lt.mpr hs.le, not_lt.mpr this.le]
  · subst hs; simp [hr, not_lt.mpr hr.le]
  · have := mul_neg_of_neg_of_pos hr hs
    simp [hr, hs, this, not_lt.mpr hr.le, not_lt.mpr hs.le, not_lt.mpr this.le]
  · subst hr; simp
  · subst hr; simp
  · subst hr; simp
  · have := mul_neg_of_pos_of_neg hr hs
    simp [hr, hs, this, not_lt.mpr hr.le, not_lt.mpr hs.le, not_lt.mpr this.le]
  · subst hs; simp [hr, not_lt.mpr hr.le]
  · have := mul_pos hr hs
    simp [hr, hs, this, not_lt.mpr hr.le, not_lt.mpr hs.le, not_lt.mpr this.le]

/-- A positive multiple of a real has its three valued sign. -/
theorem Sg3.scale {ρ : V → Bool} {t : S3} {r c : ℝ} (hc : 0 < c) (h : Sg3 ρ t r) :
    Sg3 ρ t (c * r) := by
  refine ⟨h.1.trans ?_, h.2.trans ?_⟩
  · exact (mul_pos_iff_of_pos_left hc).symm
  · constructor
    · intro h'; exact mul_neg_of_pos_of_neg hc h'
    · intro h'; by_contra h''; nlinarith [mul_nonneg hc.le (not_lt.mp h'')]

/-- Clauses of "these four three valued terms add to 0": a positive term needs a negative one, and
a negative term a positive one.  Each relation of the encoder (`zsum`), is a sub-collection of
these, with zero terms as `zeroS`. -/
def z4 (a b c d : S3) : List (List Lit) :=
  [[a.1.neg, b.2, c.2, d.2], [b.1.neg, a.2, c.2, d.2], [c.1.neg, a.2, b.2, d.2],
   [d.1.neg, a.2, b.2, c.2], [a.2.neg, b.1, c.1, d.1], [b.2.neg, a.1, c.1, d.1],
   [c.2.neg, a.1, b.1, d.1], [d.2.neg, a.1, b.1, c.1]]

/-- **The relation lemma**: reals with these signs that add to 0 satisfy every clause of `z4`. -/
theorem z4_sound {ρ : V → Bool} {a b c d : S3} {ra rb rc rd : ℝ} (ha : Sg3 ρ a ra)
    (hb : Sg3 ρ b rb) (hc : Sg3 ρ c rc) (hd : Sg3 ρ d rd) (hs : ra + rb + rc + rd = 0) :
    ∀ cl ∈ z4 a b c d, Holds ρ cl := by
  have key : ∀ (t u v w : S3) (rt ru rv rw : ℝ), Sg3 ρ t rt → Sg3 ρ u ru → Sg3 ρ v rv →
      Sg3 ρ w rw → rt + ru + rv + rw = 0 →
      Holds ρ [t.1.neg, u.2, v.2, w.2] ∧ Holds ρ [t.2.neg, u.1, v.1, w.1] := by
    intro t u v w rt ru rv rw ht hu hv hw h
    have byc : ∀ {p q r s : Lit}, ¬ Holds ρ [p, q, r, s] →
        evalL ρ p = false ∧ evalL ρ q = false ∧ evalL ρ r = false ∧ evalL ρ s = false := by
      intro p q r s hn
      refine ⟨?_, ?_, ?_, ?_⟩ <;> (rw [← Bool.not_eq_true]; intro e; exact hn ⟨_, by simp, e⟩)
    constructor
    · by_contra hn
      obtain ⟨e1, e2, e3, e4⟩ := byc hn
      rw [evalL_neg, Bool.not_eq_false'] at e1
      have p1 := ht.1.mp e1
      have p2 : 0 ≤ ru := not_lt.mp fun h' => by simpa [e2] using hu.2.mpr h'
      have p3 : 0 ≤ rv := not_lt.mp fun h' => by simpa [e3] using hv.2.mpr h'
      have p4 : 0 ≤ rw := not_lt.mp fun h' => by simpa [e4] using hw.2.mpr h'
      linarith
    · by_contra hn
      obtain ⟨e1, e2, e3, e4⟩ := byc hn
      rw [evalL_neg, Bool.not_eq_false'] at e1
      have p1 := ht.2.mp e1
      have p2 : ru ≤ 0 := not_lt.mp fun h' => by simpa [e2] using hu.1.mpr h'
      have p3 : rv ≤ 0 := not_lt.mp fun h' => by simpa [e3] using hv.1.mpr h'
      have p4 : rw ≤ 0 := not_lt.mp fun h' => by simpa [e4] using hw.1.mpr h'
      linarith
  intro cl hcl
  simp only [z4, List.mem_cons, List.not_mem_nil, or_false] at hcl
  rcases hcl with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact (key a b c d _ _ _ _ ha hb hc hd hs).1
  · exact (key b a c d _ _ _ _ hb ha hc hd (by linarith)).1
  · exact (key c a b d _ _ _ _ hc ha hb hd (by linarith)).1
  · exact (key d a b c _ _ _ _ hd ha hb hc (by linarith)).1
  · exact (key a b c d _ _ _ _ ha hb hc hd hs).2
  · exact (key b a c d _ _ _ _ hb ha hc hd (by linarith)).2
  · exact (key c a b d _ _ _ _ hc ha hb hd (by linarith)).2
  · exact (key d a b c _ _ _ _ hd ha hb hc (by linarith)).2

/-- `cl` contains every literal of `s` other than the false constant, so `s` implies `cl`. -/
def covers (cl s : List Lit) : Bool := s.all fun l => l == lfalse || cl.contains l

/-- A clause covering a true clause is true. -/
theorem Holds.of_covers {ρ : V → Bool} (hP : Proper ρ) {cl s : List Lit}
    (hc : covers cl s = true) (h : Holds ρ s) : Holds ρ cl := by
  obtain ⟨l, hl, he⟩ := h
  have := List.all_eq_true.mp hc l hl
  rcases Bool.or_eq_true _ _ |>.mp this with h1 | h1
  · have : l = lfalse := by simpa using h1
    subst this
    have e : ρ V.tru = true := hP
    simp [lfalse, evalL, e] at he
  · exact ⟨l, by simpa using h1, he⟩

end Minimality.H29.SAT
