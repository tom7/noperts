module

public import Minimality.Type24SAT.Geo.Sem

@[expose] public section

/-!
# L24T, T1: the variable type `W`, literals, evaluation, gates, the lift from `V`

`W` wraps the menu variable type `V` of Type29SAT (constructor `base`) and adds the variables of the tie
layer `rh`, `ka`, `z0`, `ty`, `tfail`, and `wgate` (an AND gate with an operand that is not
`base`).  Everything of Core.lean is repeated over `W` (`LitW`, `evalW`, `HoldsW`, `andW`, `orW`, `mul3W`,
`z4W`, `coversW`, with soundness), and `liftL`, `liftS`, `liftCl` embed the menu objects, so that a menu
row is un-lifted by `holdsW_lift` and checked with the existing code.

Gates: `gateW sa a sb b` is `base (V.gate ..)` when both operands are `base`, else `wgate`.  `GateOKW` says
`rho (gateW ..)` is the AND of the two literals, so `ρ ∘ W.base` is a `GateOK` assignment for `V`.
-/

set_option autoImplicit false
open scoped RealInnerProductSpace

namespace Minimality.H24T.SAT
open Minimality.H24.SAT Minimality.H29.SAT

/-- A CNF variable of the tie file.  `rh t f q pos`: sign of `RH(t,f,q)` (`pos`: the "> 0" Boolean, else "< 0");
`ka t f s pos` likewise for `KA(t,f,s)`; `z0 t f` is the guard `D_f // N_t`; `ty t f sd p1 p2 q1 q2` the
alternation gate of a tie rule (`sd = 1` for side `+`); `tfail t f sd c` the failure of the cycle `c`;
`wgate sa a sb b` an AND gate with a non-`base` operand.
Split additions: `qv kind key e1 e2 pos` is the sign of `Q = det3 D_e1 D_e2 v` (kind 0: line view, `key` = the
view number e in 21..42, `v = vv e = N_A x N_B` for `lines[e - 21] = (A,B)`; kind 1: tie view, `key = 32 t + f`, `v = wf t f`); `pos` as for `rh`.
`sf kind view f sd cyc` is the split flag: no split certificate `(a, cc, sigma)` exists for the cycle `cyc` (kind 0: at
the menu view `view`; kind 1: at the tie view `(t, f, sd) = (view, f, sd)`). -/
inductive W where
  | base (v : V)
  | rh (t f q : Nat) (pos : Bool)
  | ka (t f s : Nat) (pos : Bool)
  | z0 (t f : Nat)
  | ty (t f sd p1 p2 q1 q2 : Nat)
  | tfail (t f sd : Nat) (c : List Nat)
  | wgate (sa : Bool) (a : W) (sb : Bool) (b : W)
  | qv (kind key e1 e2 : Nat) (pos : Bool)
  | sf (kind view f sd : Nat) (cyc : List Nat)
  deriving DecidableEq

/-- Injective code, used only to order gate operands.  `base v` is `0 :: v.key`, so that the order of two
`base` operands is the order of `V.key`; the new tags are `>= 100`. -/
def W.key : W → List Nat
  | .base v => 0 :: v.key
  | .rh t f q p => [100, t, f, q, p.toNat]
  | .ka t f s p => [101, t, f, s, p.toNat]
  | .z0 t f => [102, t, f]
  | .ty t f sd p1 p2 q1 q2 => [103, t, f, sd, p1, p2, q1, q2]
  | .tfail t f sd c => [104, t, f, sd, c.length] ++ c
  | .wgate sa a sb b => [105, sa.toNat, (a.key).length] ++ a.key ++ [sb.toNat] ++ b.key
  | .qv k key e1 e2 p => [106, k, key, e1, e2, p.toNat]
  | .sf k v f sd c => [107, k, v, f, sd, c.length] ++ c

/-- A literal over `W`. -/
abbrev LitW := Bool × W

/-- The true literal. -/
def ltrueW : LitW := (true, W.base V.tru)
/-- The false literal. -/
def lfalseW : LitW := (false, W.base V.tru)
/-- Negation. -/
def LitW.neg (l : LitW) : LitW := (!l.1, l.2)

/-- Value of a literal. -/
def evalW (ρ : W → Bool) (l : LitW) : Bool := l.1 == ρ l.2
/-- The constant is true. -/
def ProperW (ρ : W → Bool) : Prop := ρ (W.base V.tru) = true
/-- A clause holds if one literal is true. -/
def HoldsW (ρ : W → Bool) (c : List LitW) : Prop := ∃ l ∈ c, evalW ρ l = true

theorem evalW_neg (ρ : W → Bool) (l : LitW) : evalW ρ l.neg = !evalW ρ l := by
  obtain ⟨s, v⟩ := l
  cases s <;> cases ρ v <;> simp [evalW, LitW.neg]

/-- AND gate over `W`: `base (V.gate ..)` for two `base` operands, else `wgate`. -/
def gateW (sa : Bool) (a : W) (sb : Bool) (b : W) : W :=
  match a, b with
  | .base a', .base b' => .base (V.gate sa a' sb b')
  | _, _ => .wgate sa a sb b

/-- An assignment respects the gates. -/
def GateOKW (ρ : W → Bool) : Prop :=
  ∀ sa a sb b, ρ (gateW sa a sb b) = (evalW ρ (sa, a) && evalW ρ (sb, b))

/-- AND of two literals, as the encoder forms it (same folding as `andL`, operands ordered by `W.key`). -/
def andW (a b : LitW) : LitW :=
  if a = lfalseW ∨ b = lfalseW then lfalseW
  else if a = ltrueW then b
  else if b = ltrueW then a
  else if a = b then a
  else if a = b.neg then lfalseW
  else if (cmpKey a.2.key b.2.key).then (cmpB a.1 b.1) = Ordering.gt then (true, gateW b.1 b.2 a.1 a.2)
  else (true, gateW a.1 a.2 b.1 b.2)

theorem evalW_andW {ρ : W → Bool} (hP : ProperW ρ) (hG : GateOKW ρ) (a b : LitW) :
    evalW ρ (andW a b) = (evalW ρ a && evalW ρ b) := by
  have e : ρ (W.base V.tru) = true := hP
  have hf : evalW ρ lfalseW = false := by simp [lfalseW, evalW, e]
  have ht : evalW ρ ltrueW = true := by simp [ltrueW, evalW, e]
  unfold andW
  by_cases h1 : a = lfalseW ∨ b = lfalseW
  · rw [ite_eq_left h1]
    rcases h1 with rfl | rfl <;> simp [hf]
  · rw [ite_eq_right h1]
    by_cases h2 : a = ltrueW
    · rw [ite_eq_left h2]; subst h2; simp [ht]
    · rw [ite_eq_right h2]
      by_cases h3 : b = ltrueW
      · rw [ite_eq_left h3]; subst h3; simp [ht]
      · rw [ite_eq_right h3]
        by_cases h4 : a = b
        · rw [ite_eq_left h4]; subst h4; simp
        · rw [ite_eq_right h4]
          by_cases h5 : a = b.neg
          · rw [ite_eq_left h5]; rw [h5, evalW_neg, hf]; cases evalW ρ b <;> simp
          · rw [ite_eq_right h5]
            split_ifs
            · have := hG b.1 b.2 a.1 a.2
              simp only [evalW] at this ⊢
              rw [this]; simp [Bool.and_comm]
            · have := hG a.1 a.2 b.1 b.2
              simp only [evalW] at this ⊢
              rw [this]; cases (a.1 == ρ a.2 && b.1 == ρ b.2) <;> rfl

/-- OR of two literals. -/
def orW (a b : LitW) : LitW := (andW a.neg b.neg).neg

theorem evalW_orW {ρ : W → Bool} (hP : ProperW ρ) (hG : GateOKW ρ) (a b : LitW) :
    evalW ρ (orW a b) = (evalW ρ a || evalW ρ b) := by
  unfold orW
  rw [evalW_neg, evalW_andW hP hG, evalW_neg, evalW_neg]
  cases evalW ρ a <;> cases evalW ρ b <;> rfl

/-- A three valued sign over `W`: literals for `> 0` and `< 0`. -/
abbrev S3W := LitW × LitW

/-- The two literals of `t` say exactly whether `r` is positive, and negative. -/
def SgW (ρ : W → Bool) (t : S3W) (r : ℝ) : Prop :=
  (evalW ρ t.1 = true ↔ 0 < r) ∧ (evalW ρ t.2 = true ↔ r < 0)

def negSW (t : S3W) : S3W := (t.2, t.1)

theorem SgW.neg {ρ : W → Bool} {t : S3W} {r : ℝ} (h : SgW ρ t r) : SgW ρ (negSW t) (-r) :=
  ⟨by simpa [negSW] using h.2, by simpa [negSW] using h.1⟩

def zeroSW : S3W := (lfalseW, lfalseW)

theorem SgW_zero {ρ : W → Bool} (hP : ProperW ρ) : SgW ρ zeroSW 0 := by
  have e : ρ (W.base V.tru) = true := hP
  simp [SgW, zeroSW, lfalseW, evalW, e]

/-- Zero as the sign of a real that vanishes. -/
theorem SgW_zero_of {ρ : W → Bool} (hP : ProperW ρ) {r : ℝ} (h : r = 0) : SgW ρ zeroSW r := by
  subst h; exact SgW_zero hP

/-- The sign of a nonzero integer constant (or zero). -/
def cSW (c : Int) : S3W := if 0 < c then (ltrueW, lfalseW) else if c < 0 then (lfalseW, ltrueW) else zeroSW

/-- The three valued product, from gates. -/
def mul3W (a b : S3W) : S3W :=
  (orW (andW a.1 b.1) (andW a.2 b.2), orW (andW a.1 b.2) (andW a.2 b.1))

theorem SgW.mul3 {ρ : W → Bool} (hP : ProperW ρ) (hG : GateOKW ρ) {a b : S3W} {r s : ℝ}
    (ha : SgW ρ a r) (hb : SgW ρ b s) : SgW ρ (mul3W a b) (r * s) := by
  obtain ⟨a1, a2⟩ := ha
  obtain ⟨b1, b2⟩ := hb
  simp only [SgW, mul3W, evalW_orW hP hG, evalW_andW hP hG, Bool.or_eq_true,
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
theorem SgW.scale {ρ : W → Bool} {t : S3W} {r c : ℝ} (hc : 0 < c) (h : SgW ρ t r) :
    SgW ρ t (c * r) := by
  refine ⟨h.1.trans ?_, h.2.trans ?_⟩
  · exact (mul_pos_iff_of_pos_left hc).symm
  · constructor
    · intro h'; exact mul_neg_of_pos_of_neg hc h'
    · intro h'; by_contra h''; nlinarith [mul_nonneg hc.le (not_lt.mp h'')]

/-- The clauses of "these four three valued terms add to 0". -/
def z4W (a b c d : S3W) : List (List LitW) :=
  [[a.1.neg, b.2, c.2, d.2], [b.1.neg, a.2, c.2, d.2], [c.1.neg, a.2, b.2, d.2],
   [d.1.neg, a.2, b.2, c.2], [a.2.neg, b.1, c.1, d.1], [b.2.neg, a.1, c.1, d.1],
   [c.2.neg, a.1, b.1, d.1], [d.2.neg, a.1, b.1, c.1]]

/-- **The relation lemma over `W`.** -/
theorem z4W_sound {ρ : W → Bool} {a b c d : S3W} {ra rb rc rd : ℝ} (ha : SgW ρ a ra)
    (hb : SgW ρ b rb) (hc : SgW ρ c rc) (hd : SgW ρ d rd) (hs : ra + rb + rc + rd = 0) :
    ∀ cl ∈ z4W a b c d, HoldsW ρ cl := by
  have key : ∀ (t u v w : S3W) (rt ru rv rw : ℝ), SgW ρ t rt → SgW ρ u ru → SgW ρ v rv →
      SgW ρ w rw → rt + ru + rv + rw = 0 →
      HoldsW ρ [t.1.neg, u.2, v.2, w.2] ∧ HoldsW ρ [t.2.neg, u.1, v.1, w.1] := by
    intro t u v w rt ru rv rw ht hu hv hw h
    have byc : ∀ {p q r s : LitW}, ¬ HoldsW ρ [p, q, r, s] →
        evalW ρ p = false ∧ evalW ρ q = false ∧ evalW ρ r = false ∧ evalW ρ s = false := by
      intro p q r s hn
      refine ⟨?_, ?_, ?_, ?_⟩ <;> (rw [← Bool.not_eq_true]; intro e; exact hn ⟨_, by simp, e⟩)
    constructor
    · by_contra hn
      obtain ⟨e1, e2, e3, e4⟩ := byc hn
      rw [evalW_neg, Bool.not_eq_false'] at e1
      have p1 := ht.1.mp e1
      have p2 : 0 ≤ ru := not_lt.mp fun h' => by simpa [e2] using hu.2.mpr h'
      have p3 : 0 ≤ rv := not_lt.mp fun h' => by simpa [e3] using hv.2.mpr h'
      have p4 : 0 ≤ rw := not_lt.mp fun h' => by simpa [e4] using hw.2.mpr h'
      linarith
    · by_contra hn
      obtain ⟨e1, e2, e3, e4⟩ := byc hn
      rw [evalW_neg, Bool.not_eq_false'] at e1
      have p1 := ht.2.mp e1
      have p2 : ru ≤ 0 := not_lt.mp fun h' => by simpa [e2] using hu.1.mpr h'
      have p3 : rv ≤ 0 := not_lt.mp fun h' => by simpa [e3] using hv.1.mpr h'
      have p4 : rw ≤ 0 := not_lt.mp fun h' => by simpa [e4] using hw.1.mpr h'
      linarith
  intro cl hcl
  simp only [z4W, List.mem_cons, List.not_mem_nil, or_false] at hcl
  rcases hcl with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact (key a b c d _ _ _ _ ha hb hc hd hs).1
  · exact (key b a c d _ _ _ _ hb ha hc hd (by linarith)).1
  · exact (key c a b d _ _ _ _ hc ha hb hd (by linarith)).1
  · exact (key d a b c _ _ _ _ hd ha hb hc (by linarith)).1
  · exact (key a b c d _ _ _ _ ha hb hc hd hs).2
  · exact (key b a c d _ _ _ _ hb ha hc hd (by linarith)).2
  · exact (key c a b d _ _ _ _ hc ha hb hd (by linarith)).2
  · exact (key d a b c _ _ _ _ hd ha hb hc (by linarith)).2

/-- `cl` contains every literal of `s` other than the false constant. -/
def coversW (cl s : List LitW) : Bool := s.all fun l => l == lfalseW || cl.contains l

theorem HoldsW.of_covers {ρ : W → Bool} (hP : ProperW ρ) {cl s : List LitW}
    (hc : coversW cl s = true) (h : HoldsW ρ s) : HoldsW ρ cl := by
  obtain ⟨l, hl, he⟩ := h
  have := List.all_eq_true.mp hc l hl
  rcases Bool.or_eq_true _ _ |>.mp this with h1 | h1
  · have : l = lfalseW := by simpa using h1
    subst this
    have e : ρ (W.base V.tru) = true := hP
    simp [lfalseW, evalW, e] at he
  · exact ⟨l, by simpa using h1, he⟩

/-- The three clauses of "the literal `y` is the AND of `a` and `b`". -/
theorem and_rowsW {ρ : W → Bool} (y a b : LitW) (h : evalW ρ y = (evalW ρ a && evalW ρ b)) :
    HoldsW ρ [y.neg, a] ∧ HoldsW ρ [y.neg, b] ∧ HoldsW ρ [y, a.neg, b.neg] := by
  have n1 := evalW_neg ρ y
  have n2 := evalW_neg ρ a
  have n3 := evalW_neg ρ b
  unfold HoldsW
  cases ha : evalW ρ a <;> cases hb : evalW ρ b <;> simp [h, n1, n2, n3, ha, hb]

/-- Family 20 over `W`: the three clauses of `y = andW a b`. -/
theorem gate_rowsW {ρ : W → Bool} (hP : ProperW ρ) (hG : GateOKW ρ) (a b : LitW) :
    HoldsW ρ [(andW a b).neg, a] ∧ HoldsW ρ [(andW a b).neg, b] ∧
    HoldsW ρ [andW a b, a.neg, b.neg] :=
  and_rowsW _ a b (evalW_andW hP hG a b)

/-- The defining rows of a `wgate` variable itself, from the equation `ρ (wgate ..) = AND`. -/
theorem wgate_rowsW {ρ : W → Bool} (sa : Bool) (a : W) (sb : Bool) (b : W)
    (hw : ρ (W.wgate sa a sb b) = (evalW ρ (sa, a) && evalW ρ (sb, b))) :
    HoldsW ρ [(false, W.wgate sa a sb b), (sa, a)] ∧ HoldsW ρ [(false, W.wgate sa a sb b), (sb, b)] ∧
    HoldsW ρ [(true, W.wgate sa a sb b), (!sa, a), (!sb, b)] :=
  and_rowsW (ρ := ρ) (true, W.wgate sa a sb b) (sa, a) (sb, b) (by simpa [evalW] using hw)

/-! ### The lift from `V` -/

/-- Embed a menu literal. -/
def liftL (l : Lit) : LitW := (l.1, W.base l.2)
/-- Embed a menu three valued sign. -/
def liftS (t : S3) : S3W := (liftL t.1, liftL t.2)
/-- Embed a menu clause. -/
def liftCl (c : List Lit) : List LitW := c.map liftL

theorem liftL_inj {a b : Lit} : liftL a = liftL b ↔ a = b := by
  obtain ⟨a1, a2⟩ := a; obtain ⟨b1, b2⟩ := b
  simp [liftL]

theorem liftL_neg (l : Lit) : liftL l.neg = (liftL l).neg := rfl

theorem liftL_true : liftL ltrue = ltrueW := rfl
theorem liftL_false : liftL lfalse = lfalseW := rfl

/-- **`evalW_lift`**: a lifted literal has the value of the menu literal under `ρ ∘ base`. -/
theorem evalW_lift (ρ : W → Bool) (l : Lit) : evalW ρ (liftL l) = evalL (fun v => ρ (W.base v)) l := rfl

/-- **`holds_lift`**: a lifted clause holds under `ρ` iff the menu clause holds under `ρ ∘ base`. -/
theorem holds_lift (ρ : W → Bool) (c : List Lit) :
    HoldsW ρ (liftCl c) ↔ Holds (fun v => ρ (W.base v)) c := by
  unfold HoldsW Holds liftCl
  constructor
  · rintro ⟨l, hl, he⟩
    obtain ⟨l', hl', rfl⟩ := List.mem_map.mp hl
    exact ⟨l', hl', he⟩
  · rintro ⟨l, hl, he⟩
    exact ⟨liftL l, List.mem_map.mpr ⟨l, hl, rfl⟩, he⟩

theorem proper_base {ρ : W → Bool} (h : ProperW ρ) : Proper (fun v => ρ (W.base v)) := h

theorem gateOK_base {ρ : W → Bool} (h : GateOKW ρ) : GateOK (fun v => ρ (W.base v)) :=
  fun sa a sb b => h sa (W.base a) sb (W.base b)

theorem sgW_lift (ρ : W → Bool) (t : S3) (r : ℝ) :
    SgW ρ (liftS t) r ↔ Sg3 (fun v => ρ (W.base v)) t r := Iff.rfl

theorem liftS_neg (t : S3) : liftS (negS t) = negSW (liftS t) := rfl
theorem liftS_zero : liftS zeroS = zeroSW := rfl
theorem liftS_atom (v : V) : liftS (atomS v) = ((true, W.base v), (true, W.base (V.ng v))) := rfl

theorem cmpKey_zero_cons (x y : List Nat) : cmpKey (0 :: x) (0 :: y) = cmpKey x y := by
  simp [cmpKey]

theorem andW_lift (a b : Lit) : andW (liftL a) (liftL b) = liftL (andL a b) := by
  unfold andW andL
  have hk : (liftL a).2.key = 0 :: a.2.key := rfl
  have hk' : (liftL b).2.key = 0 :: b.2.key := rfl
  have l1 : (liftL a).1 = a.1 := rfl
  have l2 : (liftL b).1 = b.1 := rfl
  simp only [← liftL_true, ← liftL_false, liftL_inj, ← liftL_neg, hk, hk', cmpKey_zero_cons, l1, l2]
  split_ifs <;> first | rfl | simp [liftL, gateW]

theorem orW_lift (a b : Lit) : orW (liftL a) (liftL b) = liftL (orL a b) := by
  unfold orW orL
  rw [← liftL_neg, ← liftL_neg, andW_lift]; rfl

theorem mul3W_lift (a b : S3) : mul3W (liftS a) (liftS b) = liftS (mul3 a b) := by
  unfold mul3W mul3 liftS
  simp only [andW_lift, orW_lift]

theorem z4W_lift (a b c d : S3) : z4W (liftS a) (liftS b) (liftS c) (liftS d) = (z4 a b c d).map liftCl := rfl

theorem liftL_injective : Function.Injective liftL := fun _ _ h => liftL_inj.mp h

theorem coversW_lift (cl s : List Lit) : coversW (liftCl cl) (liftCl s) = covers cl s := by
  unfold coversW covers
  have h1 : ∀ l, (liftL l == lfalseW) = (l == lfalse) := by
    intro l; rw [← liftL_false, Bool.eq_iff_iff]; simp [liftL_inj]
  have h2 : ∀ l, (cl.map liftL).contains (liftL l) = cl.contains l := by
    intro l; simp [ List.mem_map_of_injective liftL_injective]
  unfold liftCl
  rw [List.all_map]
  congr 1
  funext l
  simp only [Function.comp, h1, h2]

end Minimality.H24T.SAT
