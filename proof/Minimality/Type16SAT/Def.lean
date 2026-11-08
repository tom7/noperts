module

public import Minimality.Type16SAT.Sem

@[expose] public section

/-!
# L3, part 3: the definitional rows (gates, sign and T exclusions, y, failbig)

Each is true by unfolding `rho`; no geometry.  Families 20 (gate), 21 (sign exclusion of an atom),
11 (exclusion of `tp`/`tq`), 15 (y), 16 (failbig).
-/

set_option autoImplicit false
open scoped RealInnerProductSpace
open Classical

open Minimality.H29.SAT

namespace Minimality.H16.SAT

/-- Family 20: the three clauses of `y = a and b`, with `y = andL a b`.  Each holds. -/
theorem gate_rows (g : Geo) (a b : Lit) :
    Holds (rho g) [(andL a b).neg, a] ∧ Holds (rho g) [(andL a b).neg, b] ∧
    Holds (rho g) [andL a b, a.neg, b.neg] := by
  have e := evalL_andL (rho_proper g) (rho_gateOK g) a b
  have n1 := evalL_neg (rho g) (andL a b)
  have n2 := evalL_neg (rho g) a
  have n3 := evalL_neg (rho g) b
  unfold Holds
  cases ha : evalL (rho g) a <;> cases hb : evalL (rho g) b <;> simp [e, n1, n2, n3, ha, hb]

/-- Family 21: an atom is not both positive and negative. -/
theorem sign_excl (g : Geo) (v : V) (hv : rho g v = decide (0 < g.atom v)) :
    Holds (rho g) [(false, v), (false, V.ng v)] := by
  by_cases h : 0 < g.atom v
  · refine ⟨(false, V.ng v), by simp, ?_⟩
    have : ¬ g.atom v < 0 := not_lt.mpr h.le
    simp [evalL, rho, this]
  · refine ⟨(false, v), by simp, ?_⟩
    simp [evalL, hv, h]

/-- Family 11: `tp e f` and `tq e f` are not both true. -/
theorem texcl (g : Geo) (e f : Nat) : Holds (rho g) [(false, V.tp e f), (false, V.tq e f)] := by
  by_cases h : 0 < ⟪g.vv e, g.vv f⟫
  · refine ⟨(false, V.tq e f), by simp, ?_⟩
    have : ¬ ⟪g.vv e, g.vv f⟫ < 0 := not_lt.mpr h.le
    simp [evalL, rho, this]
  · refine ⟨(false, V.tp e f), by simp, ?_⟩
    simp [evalL, rho, h]

/-- Family 15: `y` implies each of the four weak inequalities `geL`; `geL e a b` is the negation of the
`< 0` literal of `ordS e a b`. -/
theorem y_rows (g : Geo) (e p1 p2 q1 q2 : Nat) (hv : e < 21 → g.vv e ≠ 0)
    (hd : ∀ a b, a < b → b < 7 → g.vv (EI a b) = g.x a - g.x b)
    (h1 : p1 < 7) (h2 : p2 < 7) (h3 : q1 < 7) (h4 : q2 < 7)
    (n1 : p1 ≠ q1) (n2 : p1 ≠ q2) (n3 : p2 ≠ q1) (n4 : p2 ≠ q2) :
    ∀ (a b : Nat), ((a = p1 ∧ b = q1) ∨ (a = p1 ∧ b = q2) ∨ (a = p2 ∧ b = q1) ∨ (a = p2 ∧ b = q2)) →
      Holds (rho g) [(false, V.yv e p1 p2 q1 q2), (ordS e a b).2.neg] := by
  intro a b hab
  have key : ∀ a b, a ≠ b → a < 7 → b < 7 → (0 ≤ g.z e a b ∨ ¬ (0 ≤ g.z e a b)) →
      (0 ≤ g.z e a b → evalL (rho g) (ordS e a b).2.neg = true) := by
    intro a b hne ha hb _ hz
    have s := Sg3_ordS g e a b hv hne ha hb hd
    rw [evalL_neg]
    have : evalL (rho g) (ordS e a b).2 = false := by
      rw [← Bool.not_eq_true]; intro c; exact absurd (s.2.mp c) (not_lt.mpr hz)
    simp [this]
  by_cases hy : rho g (V.yv e p1 p2 q1 q2) = true
  · have hy' : g.yB e p1 p2 q1 q2 = true := hy
    simp only [Geo.yB, decide_eq_true_eq] at hy'
    obtain ⟨y1, y2, y3, y4⟩ := hy'
    refine ⟨(ordS e a b).2.neg, by simp, ?_⟩
    rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact key _ _ n1 h1 h3 (Or.inl y1) y1
    · exact key _ _ n2 h1 h4 (Or.inl y2) y2
    · exact key _ _ n3 h2 h3 (Or.inl y3) y3
    · exact key _ _ n4 h2 h4 (Or.inl y4) y4
  · refine ⟨(false, V.yv e p1 p2 q1 q2), by simp, ?_⟩
    simp only [evalL, Bool.not_eq_true] at hy ⊢
    simp [hy]

/-- Family 16: `fail e c` implies one of its `y` variables (the clause `-v, y1, ..., yn`). -/
theorem failbig (g : Geo) (e : Nat) (c : List Nat) :
    Holds (rho g) ((false, V.fail e c) ::
      (alts c).map fun t => (true, V.yv e t.1 t.2.1 t.2.2.1 t.2.2.2)) := by
  by_cases h : rho g (V.fail e c) = true
  · have h' : ((alts c).any fun t => g.yB e t.1 t.2.1 t.2.2.1 t.2.2.2) = true := h
    obtain ⟨t, ht, hy⟩ := List.any_eq_true.mp h'
    exact ⟨(true, V.yv e t.1 t.2.1 t.2.2.1 t.2.2.2), List.mem_cons_of_mem _ (List.mem_map.mpr ⟨t, ht, rfl⟩),
      by simp [evalL, rho, hy]⟩
  · refine ⟨(false, V.fail e c), by simp, ?_⟩
    simp only [Bool.not_eq_true] at h
    simp [evalL, h]

/-! ### The lex families (23, 24, 27), used by the lex rules of core B -/

/-- Three valued sign of `eps * (depth of p minus depth of q)` at view `d`. -/
def ordE (d ep p q : Nat) : S3 := if ep = 1 then ordS d p q else negS (ordS d p q)

/-- `ordE` tells the truth. -/
theorem Sg3_ordE (g : Geo) (d ep p q : Nat) (hv : d < 21 → g.vv d ≠ 0) (hab : p ≠ q) (hp : p < 7) (hq : q < 7)
    (hd : ∀ a b, a < b → b < 7 → g.vv (EI a b) = g.x a - g.x b) :
    Sg3 (rho g) (ordE d ep p q) (epR ep * g.z d p q) := by
  have s := Sg3_ordS g d p q hv hab hp hq hd
  unfold ordE epR
  by_cases h : ep = 1
  · simp only [h, if_true, one_mul]; exact s
  · simp only [h, if_false]
    have := s.neg
    simpa using this

/-- Family 23: the two clauses that force `ltl` when the depth of `p` is lex less than that of `q`. -/
theorem ltl_rows (g : Geo) (e d ep p q : Nat) (hv : e < 21 → g.vv e ≠ 0) (hvd : d < 21 → g.vv d ≠ 0)
    (hd : ∀ a b, a < b → b < 7 → g.vv (EI a b) = g.x a - g.x b)
    (hp : p < 7) (hq : q < 7) (hpq : p ≠ q) :
    Holds (rho g) [(ordS e p q).2.neg, (true, V.ltl e d ep p q)] ∧
    Holds (rho g) [(ordS e p q).1, (ordS e p q).2, (ordE d ep p q).2.neg, (true, V.ltl e d ep p q)] := by
  have sa := Sg3_ordS g e p q hv hpq hp hq hd
  have sb := Sg3_ordE g d ep p q hvd hpq hp hq hd
  have hl : ∀ h : g.lexLt e d ep p q, evalL (rho g) (true, V.ltl e d ep p q) = true := fun h => by
    simp [evalL, rho, h]
  constructor
  · by_cases h : g.z e p q < 0
    · exact ⟨_, by simp, hl (Or.inl h)⟩
    · refine ⟨(ordS e p q).2.neg, by simp, ?_⟩
      rw [evalL_neg]
      have : evalL (rho g) (ordS e p q).2 = false := by
        rw [← Bool.not_eq_true]; intro c; exact h (sa.2.mp c)
      simp [this]
  · by_cases h1 : 0 < g.z e p q
    · exact ⟨(ordS e p q).1, by simp, sa.1.mpr h1⟩
    · by_cases h2 : g.z e p q < 0
      · exact ⟨_, by simp, hl (Or.inl h2)⟩
      · have h0 : g.z e p q = 0 := le_antisymm (not_lt.mp h1) (not_lt.mp h2)
        by_cases h3 : epR ep * g.z d p q < 0
        · exact ⟨_, by simp, hl (Or.inr ⟨h0, h3⟩)⟩
        · refine ⟨(ordE d ep p q).2.neg, by simp, ?_⟩
          rw [evalL_neg]
          have : evalL (rho g) (ordE d ep p q).2 = false := by
            rw [← Bool.not_eq_true]; intro c; exact h3 (sb.2.mp c)
          simp [this]

/-- Family 24: `yl` implies that none of its four pairs is lex less-than. -/
theorem yl_rows (g : Geo) (e d ep : Nat) (c : List Nat) (p1 p2 q1 q2 p q : Nat)
    (h : (p = p1 ∨ p = p2) ∧ (q = q1 ∨ q = q2)) :
    Holds (rho g) [(false, V.yl e d ep c p1 p2 q1 q2), (false, V.ltl e d ep p q)] := by
  by_cases hy : rho g (V.yl e d ep c p1 p2 q1 q2) = true
  · have hy' : g.yL e d ep p1 p2 q1 q2 = true := hy
    simp only [Geo.yL, decide_eq_true_eq] at hy'
    obtain ⟨y1, y2, y3, y4⟩ := hy'
    refine ⟨(false, V.ltl e d ep p q), by simp, ?_⟩
    have : ¬ g.lexLt e d ep p q := by
      obtain ⟨hp, hq⟩ := h
      rcases hp with rfl | rfl <;> rcases hq with rfl | rfl <;> assumption
    simp [evalL, rho, this]
  · refine ⟨(false, V.yl e d ep c p1 p2 q1 q2), by simp, ?_⟩
    simp only [evalL, Bool.not_eq_true] at hy ⊢
    simp [hy]

/-- Family 27: `faill` implies one of its `yl` variables. -/
theorem faill_rows (g : Geo) (e d ep : Nat) (c : List Nat) :
    Holds (rho g) ((false, V.faill e d ep c) ::
      (alts c).map fun t => (true, V.yl e d ep c t.1 t.2.1 t.2.2.1 t.2.2.2)) := by
  by_cases h : rho g (V.faill e d ep c) = true
  · have h' : ((alts c).any fun t => g.yL e d ep t.1 t.2.1 t.2.2.1 t.2.2.2) = true := h
    obtain ⟨t, ht, hy⟩ := List.any_eq_true.mp h'
    exact ⟨(true, V.yl e d ep c t.1 t.2.1 t.2.2.1 t.2.2.2), List.mem_cons_of_mem _ (List.mem_map.mpr ⟨t, ht, rfl⟩),
      by simp [evalL, rho, hy]⟩
  · refine ⟨(false, V.faill e d ep c), by simp, ?_⟩
    simp only [Bool.not_eq_true] at h
    simp [evalL, h]

end Minimality.H16.SAT
