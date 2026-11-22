module

public import Minimality.M4eType24
public import Minimality.M4dType24
public import Minimality.M4cType24
public import Minimality.M4bType24
public import Minimality.M4Sym24
public import Minimality.GenQuad
public import Minimality.Type24SAT.K24.CornerOB1

@[expose] public section

/-!
# Type 24: A17 off-OB1 lemmas, part 1 (A17-REFEREE section 5: S1-S3)

`e16_gbc` (Lemma E16-Gbc: nC > 0, gbc > 0, not LexAny => gac > 0; 4-rim 1 0 5 2 or 5-rim 1 0 5 3 2 with the
exact chord `chord_e16`), `e12_gbc` (its sym24 twin: nB > 0 => gab > 0), `gac_pos_famA` (Family A: a5 > 1 >= a4,
not OB1, not LexAny => gac > 0); helpers `robUniLex_five_lin`, `robUniLex_five_chord`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped RealInnerProductSpace
open Finset Filter

namespace Minimality.T24.A17

open Minimality Minimality.H21 Minimality.H24.SAT Minimality.T24.SAT Minimality.T24.RCell
  Minimality.LexCell Minimality.Split Minimality.T24.M4 Minimality.T24.A7 Minimality.T24.A8
  Minimality.T24.Sym

/-! ### Lex helpers: `RobUniLex` of a 5-cycle from a chord inequality -/

/-- Lex order on depth triples as a linear order. -/
def iota3 (p : ℝ × ℝ × ℝ) : ℝ ×ₗ ℝ ×ₗ ℝ := toLex (p.1, toLex p.2)

theorem lexLt3_iff (p q : ℝ × ℝ × ℝ) : LexLt3 p q ↔ iota3 p < iota3 q := by
  obtain ⟨p1, p2, p3⟩ := p
  obtain ⟨q1, q2, q3⟩ := q
  simp only [LexLt3, LexPos3, iota3, Prod.Lex.toLex_lt_toLex, sub_pos]
  constructor
  · rintro (h | ⟨h, h' | ⟨h', h''⟩⟩)
    · exact Or.inl h
    · exact Or.inr ⟨(sub_eq_zero.mp h).symm, Or.inl (by linarith)⟩
    · exact Or.inr ⟨(sub_eq_zero.mp h).symm, Or.inr ⟨(sub_eq_zero.mp h').symm, by linarith⟩⟩
  · rintro (h | ⟨h, h' | ⟨h', h''⟩⟩)
    · exact Or.inl h
    · exact Or.inr ⟨by linarith, Or.inl (by linarith)⟩
    · exact Or.inr ⟨by linarith, Or.inr ⟨by linarith, by linarith⟩⟩

theorem iota3_le_fst {p q : ℝ × ℝ × ℝ} (h : iota3 p ≤ iota3 q) : p.1 ≤ q.1 := by
  simp only [iota3] at h
  rcases lt_or_eq_of_le h with h | h
  · rw [Prod.Lex.toLex_lt_toLex] at h
    rcases h with h | ⟨h, _⟩
    · exact h.le
    · exact h.le
  · have := congrArg (fun w => (ofLex w).1) h
    simp at this
    exact this.le

set_option maxHeartbeats 1600000 in
theorem robUniLex_five_lin {α : Type*} [LinearOrder α] (z : ZMod 5 → α)
    (h10 : z 1 < z 0) (h04 : z 0 < z 4)
    (hdiag : ¬ (max (z 1) (z 3) ≤ min (z 4) (z 2))) :
    ∀ (B : ZMod 5) (b c d : ℕ), 0 < b → b < c → c < d → d < 5 →
      z B < z (B + b) ∨ z (B + c) < z (B + b) ∨ z B < z (B + d) ∨ z (B + c) < z (B + d) := by
  intro B b c d hb hbc hcd hd
  have hB : B = 0 ∨ B = 1 ∨ B = 2 ∨ B = 3 ∨ B = 4 := by revert B; decide
  have hbcd : (b = 1 ∧ c = 2 ∧ d = 3) ∨ (b = 1 ∧ c = 2 ∧ d = 4) ∨
      (b = 1 ∧ c = 3 ∧ d = 4) ∨ (b = 2 ∧ c = 3 ∧ d = 4) := by omega
  have hcases : z 2 < z 1 ∨ z 4 < z 3 ∨ z 2 < z 3 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨h1, h2, h3⟩ := hcon
    apply hdiag
    exact max_le (le_min (by order) h1) (le_min h2 h3)
  rcases hcases with h21 | h43 | h23
  all_goals rcases hB with rfl | rfl | rfl | rfl | rfl <;>
    rcases hbcd with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
    simp only [Nat.cast_one, Nat.cast_ofNat,
      show (0 : ZMod 5) + 1 = 1 from rfl, show (0 : ZMod 5) + 2 = 2 from rfl,
      show (0 : ZMod 5) + 3 = 3 from rfl, show (0 : ZMod 5) + 4 = 4 from rfl,
      show (1 : ZMod 5) + 1 = 2 from rfl, show (1 : ZMod 5) + 2 = 3 from rfl,
      show (1 : ZMod 5) + 3 = 4 from rfl, show (1 : ZMod 5) + 4 = 0 from rfl,
      show (2 : ZMod 5) + 1 = 3 from rfl, show (2 : ZMod 5) + 2 = 4 from rfl,
      show (2 : ZMod 5) + 3 = 0 from rfl, show (2 : ZMod 5) + 4 = 1 from rfl,
      show (3 : ZMod 5) + 1 = 4 from rfl, show (3 : ZMod 5) + 2 = 0 from rfl,
      show (3 : ZMod 5) + 3 = 1 from rfl, show (3 : ZMod 5) + 4 = 2 from rfl,
      show (4 : ZMod 5) + 1 = 0 from rfl, show (4 : ZMod 5) + 2 = 1 from rfl,
      show (4 : ZMod 5) + 3 = 2 from rfl, show (4 : ZMod 5) + 4 = 3 from rfl]
  all_goals first
    | (left; order)
    | (right; left; order)
    | (right; right; left; order)
    | (right; right; right; order)

/-- 5-cycle of lex depth triples: `z 0 < z 1` lexicographically at positions `(1, 0)`, `(0, 4)`, and a
first-level chord inequality. -/
theorem robUniLex_five_chord (z : ZMod 5 → ℝ × ℝ × ℝ)
    (h10 : LexLt3 (z 1) (z 0)) (h04 : LexLt3 (z 0) (z 4))
    (hd : min (z 4).1 (z 2).1 < max (z 1).1 (z 3).1) : RobUniLex z := by
  intro B b c d hb hbc hcd hd'
  have key := robUniLex_five_lin (fun i => iota3 (z i)) ((lexLt3_iff _ _).mp h10)
    ((lexLt3_iff _ _).mp h04) (by
      intro hle
      have h1 := iota3_le_fst (le_trans (le_max_left _ _) (le_trans hle (min_le_left _ _)))
      have h2 := iota3_le_fst (le_trans (le_max_left _ _) (le_trans hle (min_le_right _ _)))
      have h3 := iota3_le_fst (le_trans (le_max_right _ _) (le_trans hle (min_le_left _ _)))
      have h4 := iota3_le_fst (le_trans (le_max_right _ _) (le_trans hle (min_le_right _ _)))
      have : max (z 1).1 (z 3).1 ≤ min (z 4).1 (z 2).1 :=
        max_le (le_min h1 h2) (le_min h3 h4)
      exact absurd hd (not_lt.mpr this)) B b c d hb hbc hcd hd'
  simpa only [lexLt3_iff] using key


theorem lexPos3_of_two {a b c : ℝ} (h : 0 < a ∨ (a = 0 ∧ 0 < b)) : LexPos3 a b c := by
  rcases h with h | ⟨h, h'⟩
  · exact Or.inl h
  · exact Or.inr ⟨h, Or.inl h'⟩

/-! ### S1: Lemma E16-Gbc -/

set_option maxHeartbeats 1600000 in
/-- **Chord `0-3` in front of `2-5` at `e_c`** (Lemma E16-Gbc, 5-rim case).  If `235` faces down (weakly)
at `e_c` and `0345` faces up there, then `(1-l) y0 + l y3 = (1-m) y2 + m y5 + s e_c` with `l, m ∈ [0,1]`,
`s > 0`; the coefficients are the Cramer solution `l = ω5 c5 / Δ`, `m = (a3 + b3 - 1) / Δ`,
`Δ = a5 b3 - (a3 - 1)(b5 - 1) = ω5 c5 + Y`, `Y = a5 (b3 - 1) - a3 (b5 - 1) ≥ 0`. -/
theorem chord_e16 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (hC : CbarIn x)
    (hnc : F.f 3 (x 1) < F.f 3 (x 6)) (h6 : F.f 6 (x 6) ≤ F.f 6 (x 1)) :
    ∃ l m s : ℝ, 0 ≤ l ∧ l ≤ 1 ∧ 0 ≤ m ∧ m ≤ 1 ∧ 0 < s ∧
      (1 - l) • (x 0 - x 1) + l • (x 3 - x 1) =
        (1 - m) • (x 2 - x 1) + m • (x 5 - x 1) + s • (x 6 - x 1) := by
  have T := type24OfFac F
  have hom3 : 0 < omega3 x := hC.1
  have hom5 : 0 < omega5 x := hC.2.2.1
  have ha3 : 0 < oblX0 x 3 := T.X0_pos (v := 3) (by decide)
  have ha5 : 0 < oblX0 x 5 := T.X0_pos (v := 5) (by decide)
  have hb3 : 0 < oblX2 x 3 := T.X2_pos (v := 3) (by decide)
  have hb5 : 0 < oblX2 x 5 := T.X2_pos (v := 5) (by decide)
  have hc3 : 0 < oblX6 x 3 := T.X6_pos (v := 3) (by decide)
  have hc5 : 0 < oblX6 x 5 := T.X6_pos (v := 5) (by decide)
  have e3 : oblX2 x 3 + oblX6 x 3 - omega3 x * oblX0 x 3 = 1 := by linarith [eq3 F]
  have e5 : oblX0 x 5 + oblX2 x 5 - 1 = omega5 x * oblX6 x 5 := by linarith [eq5 F]
  have hN : ∀ (t : Fin 9) (v : Fin 7), ⟪F.N t, x v - x 1⟫ = F.f t (x v) - F.f t (x 1) :=
    fun t v => (F.hN t (x v) (x 1)).symm
  have f2_1 : F.f 2 (x 1) < 0 := F.neg 2 1 (by decide)
  have f2_0 : F.f 2 (x 0) = 0 := F.zero 2 0 (by decide)
  have f2_2 : F.f 2 (x 2) = 0 := F.zero 2 2 (by decide)
  have f2_5 : F.f 2 (x 5) = 0 := F.zero 2 5 (by decide)
  have f2_3 : F.f 2 (x 3) < 0 := F.neg 2 3 (by decide)
  have f7_1 : F.f 7 (x 1) < 0 := F.neg 7 1 (by decide)
  have f7_2 : F.f 7 (x 2) = 0 := F.zero 7 2 (by decide)
  have f7_3 : F.f 7 (x 3) = 0 := F.zero 7 3 (by decide)
  have f7_6 : F.f 7 (x 6) = 0 := F.zero 7 6 (by decide)
  have f7_5 : F.f 7 (x 5) < 0 := F.neg 7 5 (by decide)
  have f6_1 : F.f 6 (x 1) < 0 := F.neg 6 1 (by decide)
  have f6_0 : F.f 6 (x 0) < 0 := F.neg 6 0 (by decide)
  have f6_2 : F.f 6 (x 2) = 0 := F.zero 6 2 (by decide)
  have f6_3 : F.f 6 (x 3) = 0 := F.zero 6 3 (by decide)
  have f6_5 : F.f 6 (x 5) = 0 := F.zero 6 5 (by decide)
  have f3_0 : F.f 3 (x 0) = 0 := F.zero 3 0 (by decide)
  have f3_3 : F.f 3 (x 3) = 0 := F.zero 3 3 (by decide)
  have f3_5 : F.f 3 (x 5) = 0 := F.zero 3 5 (by decide)
  have f3_2 : F.f 3 (x 2) < 0 := F.neg 3 2 (by decide)
  have f5_1 : F.f 5 (x 1) = 0 := F.zero 5 1 (by decide)
  have f5_2 : F.f 5 (x 2) = 0 := F.zero 5 2 (by decide)
  have f5_6 : F.f 5 (x 6) = 0 := F.zero 5 6 (by decide)
  have f5_0 : F.f 5 (x 0) < 0 := F.neg 5 0 (by decide)
  have f5_3 : F.f 5 (x 3) < 0 := F.neg 5 3 (by decide)
  have f5_5 : F.f 5 (x 5) < 0 := F.neg 5 5 (by decide)
  -- facing of `025` at `e_c`
  have hn2eq : F.f 2 (x 6) - F.f 2 (x 1) = F.f 2 (x 1) * omega5 x := by
    have ev := fac_eval F 2 5
    rw [f2_5, f2_0, f2_2] at ev
    have h : oblX6 x 5 * (F.f 2 (x 6) - F.f 2 (x 1) - F.f 2 (x 1) * omega5 x) = 0 := by
      linear_combination -ev + F.f 2 (x 1) * e5
    have := (mul_eq_zero.mp h).resolve_left hc5.ne'
    linarith
  have hn2 : F.f 2 (x 6) - F.f 2 (x 1) < 0 := by
    rw [hn2eq]; exact mul_neg_of_neg_of_pos f2_1 hom5
  -- `q1 > 0` from `025` at vertex 3
  have hq1 : 0 < oblX6 x 3 * (1 + omega5 x) - oblX0 x 3 * (1 + omega3 x) := by
    have ev := fac_eval F 2 3
    rw [f2_0, f2_2] at ev
    have h : F.f 2 (x 3) = F.f 2 (x 1) * (oblX6 x 3 * (1 + omega5 x) - oblX0 x 3 * (1 + omega3 x)) := by
      linear_combination ev
        + oblX6 x 3 * hn2eq + F.f 2 (x 1) * (-1) * e3
    by_contra hcon
    push Not at hcon
    have : 0 ≤ F.f 2 (x 1) * (oblX6 x 3 * (1 + omega5 x) - oblX0 x 3 * (1 + omega3 x)) :=
      mul_nonneg_of_nonpos_of_nonpos f2_1.le hcon
    linarith
  -- `q2 > 0` from `236` at vertex 5
  have hq2 : 0 < oblX0 x 5 * (1 + omega3 x) - oblX6 x 5 * (1 + omega5 x) := by
    have ev3 := fac_eval F 7 3
    rw [f7_3, f7_2, f7_6] at ev3
    have hP : F.f 7 (x 0) - F.f 7 (x 1) = F.f 7 (x 1) * omega3 x := by
      have h : oblX0 x 3 * (F.f 7 (x 0) - F.f 7 (x 1) - F.f 7 (x 1) * omega3 x) = 0 := by
        linear_combination -ev3 + F.f 7 (x 1) * e3
      have := (mul_eq_zero.mp h).resolve_left ha3.ne'
      linarith
    have ev5 := fac_eval F 7 5
    rw [f7_2, f7_6] at ev5
    have h : F.f 7 (x 5) = F.f 7 (x 1) * (oblX0 x 5 * (1 + omega3 x) - oblX6 x 5 * (1 + omega5 x)) := by
      linear_combination ev5 + oblX0 x 5 * hP - F.f 7 (x 1) * e5
    by_contra hcon
    push Not at hcon
    have : 0 ≤ F.f 7 (x 1) * (oblX0 x 5 * (1 + omega3 x) - oblX6 x 5 * (1 + omega5 x)) :=
      mul_nonneg_of_nonpos_of_nonpos f7_1.le hcon
    linarith
  -- `ν = c3 a5 - a3 c5 > 0`
  have hν : 0 < oblX6 x 3 * oblX0 x 5 - oblX0 x 3 * oblX6 x 5 := by
    have h1 := mul_lt_mul'' (sub_pos.mp hq1) (sub_pos.mp hq2) (by positivity) (by positivity)
    have hpos : 0 < (oblX6 x 3 * oblX0 x 5 - oblX0 x 3 * oblX6 x 5) * ((1 + omega3 x) * (1 + omega5 x)) := by
      nlinarith
    exact (mul_pos_iff_of_pos_right (by positivity)).mp hpos
  -- `Y ≥ 0` from `235`: `f6(x1) * Y = n6 * ν`
  have hY : 0 ≤ oblX0 x 5 * (oblX2 x 3 - 1) - oblX0 x 3 * (oblX2 x 5 - 1) := by
    have ev3 := fac_eval F 6 3
    have ev5 := fac_eval F 6 5
    rw [f6_3, f6_2] at ev3
    rw [f6_5, f6_2] at ev5
    have hid : F.f 6 (x 1) * (oblX0 x 5 * (oblX2 x 3 - 1) - oblX0 x 3 * (oblX2 x 5 - 1)) =
        (F.f 6 (x 6) - F.f 6 (x 1)) * (oblX6 x 3 * oblX0 x 5 - oblX0 x 3 * oblX6 x 5) := by
      linear_combination oblX0 x 5 * ev3 - oblX0 x 3 * ev5
    by_contra hcon
    push Not at hcon
    have h1 : F.f 6 (x 1) * (oblX0 x 5 * (oblX2 x 3 - 1) - oblX0 x 3 * (oblX2 x 5 - 1)) > 0 :=
      mul_pos_of_neg_of_neg f6_1 hcon
    have h2 : (F.f 6 (x 6) - F.f 6 (x 1)) * (oblX6 x 3 * oblX0 x 5 - oblX0 x 3 * oblX6 x 5) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith) hν.le
    linarith
  -- the Cramer solution
  obtain ⟨Δ, hΔdef⟩ : ∃ Δ : ℝ, Δ = oblX0 x 5 * oblX2 x 3 - (oblX0 x 3 - 1) * (oblX2 x 5 - 1) := ⟨_, rfl⟩
  have hΔ : 0 < Δ := by
    have h5 : 0 < oblX0 x 5 + oblX2 x 5 - 1 := by rw [e5]; positivity
    have hsplit : Δ = (oblX0 x 5 + oblX2 x 5 - 1) +
        (oblX0 x 5 * (oblX2 x 3 - 1) - oblX0 x 3 * (oblX2 x 5 - 1)) := by rw [hΔdef]; ring
    linarith
  obtain ⟨l, hl⟩ : ∃ l : ℝ, l = (oblX0 x 5 + oblX2 x 5 - 1) / Δ := ⟨_, rfl⟩
  obtain ⟨m, hm⟩ : ∃ m : ℝ, m = (oblX0 x 3 + oblX2 x 3 - 1) / Δ := ⟨_, rfl⟩
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s = l * oblX6 x 3 - m * oblX6 x 5 := ⟨_, rfl⟩
  have hea : (1 - l) + l * oblX0 x 3 - m * oblX0 x 5 = 0 := by
    rw [hl, hm]; field_simp; rw [hΔdef]; ring
  have heb : l * oblX2 x 3 - (1 - m) - m * oblX2 x 5 = 0 := by
    rw [hl, hm]; field_simp; rw [hΔdef]; ring
  have hvec : (1 - l) • (x 0 - x 1) + l • (x 3 - x 1) =
      (1 - m) • (x 2 - x 1) + m • (x 5 - x 1) + s • (x 6 - x 1) := by
    have hrep3 : x 3 - x 1 = oblX0 x 3 • (x 0 - x 1) + oblX2 x 3 • (x 2 - x 1) +
        oblX6 x 3 • (x 6 - x 1) := by rw [T.rep 3]; abel
    have hrep5 : x 5 - x 1 = oblX0 x 5 • (x 0 - x 1) + oblX2 x 5 • (x 2 - x 1) +
        oblX6 x 5 • (x 6 - x 1) := by rw [T.rep 5]; abel
    rw [hrep3, hrep5]
    linear_combination (norm := module) hea • (x 0 - x 1) + heb • (x 2 - x 1) - hs • (x 6 - x 1)
  have hid : ∀ t : Fin 9, (1 - l) * (F.f t (x 0) - F.f t (x 1)) + l * (F.f t (x 3) - F.f t (x 1)) =
      (1 - m) * (F.f t (x 2) - F.f t (x 1)) + m * (F.f t (x 5) - F.f t (x 1)) +
        s * (F.f t (x 6) - F.f t (x 1)) := by
    intro t
    have hi := congrArg (fun v => ⟪F.N t, v⟫) hvec
    simp only [inner_add_right, inner_smul_right, hN] at hi
    exact hi
  have E2 : l * F.f 2 (x 3) = s * (F.f 2 (x 6) - F.f 2 (x 1)) := by
    have := hid 2
    rw [f2_0, f2_2, f2_5] at this
    linear_combination this
  have E6 : (1 - l) * F.f 6 (x 0) = s * (F.f 6 (x 6) - F.f 6 (x 1)) := by
    have := hid 6
    rw [f6_2, f6_3, f6_5] at this
    linear_combination this
  have E3 : (1 - m) * F.f 3 (x 2) + s * (F.f 3 (x 6) - F.f 3 (x 1)) = 0 := by
    have := hid 3
    rw [f3_0, f3_3, f3_5] at this
    linear_combination -this
  have E5 : m * F.f 5 (x 5) = (1 - l) * F.f 5 (x 0) + l * F.f 5 (x 3) := by
    have := hid 5
    rw [f5_1, f5_2, f5_6] at this
    linear_combination -this
  have hn6 : F.f 6 (x 6) - F.f 6 (x 1) ≤ 0 := by linarith
  have hspos : 0 < s := by
    by_contra hs0
    push Not at hs0
    have h1 : 0 ≤ s * (F.f 2 (x 6) - F.f 2 (x 1)) := mul_nonneg_of_nonpos_of_nonpos hs0 hn2.le
    have h2 : 0 ≤ s * (F.f 6 (x 6) - F.f 6 (x 1)) := mul_nonneg_of_nonpos_of_nonpos hs0 hn6
    have hl0 : l ≤ 0 := by
      by_contra h
      push Not at h
      have := mul_neg_of_pos_of_neg h f2_3
      linarith
    have : (1 - l) * F.f 6 (x 0) < 0 := mul_neg_of_pos_of_neg (by linarith) f6_0
    linarith
  have hl0 : 0 < l := by
    by_contra h
    push Not at h
    have h1 : 0 ≤ l * F.f 2 (x 3) := mul_nonneg_of_nonpos_of_nonpos h f2_3.le
    have h2 : s * (F.f 2 (x 6) - F.f 2 (x 1)) < 0 := mul_neg_of_pos_of_neg hspos hn2
    linarith
  have hl1 : l ≤ 1 := by
    by_contra h
    push Not at h
    have h1 : 0 < (1 - l) * F.f 6 (x 0) := mul_pos_of_neg_of_neg (by linarith) f6_0
    have h2 : s * (F.f 6 (x 6) - F.f 6 (x 1)) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hspos.le hn6
    linarith
  have hm1 : m < 1 := by
    by_contra h
    push Not at h
    have h1 : 0 ≤ (1 - m) * F.f 3 (x 2) := mul_nonneg_of_nonpos_of_nonpos (by linarith) f3_2.le
    have h2 : 0 < s * (F.f 3 (x 6) - F.f 3 (x 1)) := mul_pos hspos (by linarith)
    linarith
  have hm0 : 0 ≤ m := by
    by_contra h
    push Not at h
    have h1 : 0 < m * F.f 5 (x 5) := mul_pos_of_neg_of_neg h (F.neg 5 5 (by decide))
    have h2 : (1 - l) * F.f 5 (x 0) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by linarith) f5_0.le
    have h3 : l * F.f 5 (x 3) < 0 := mul_neg_of_pos_of_neg hl0 f5_3
    linarith
  exact ⟨l, m, s, hl0.le, hl1, hm0, hm1.le, hspos, hvec⟩


set_option maxHeartbeats 3200000 in
/-- **Lemma E16-Gbc.** `nC > 0` (facet `0345` faces up at `e_c`), `G_bc > 0` and no lex leaf give
`G_ac > 0`. -/
theorem e16_gbc {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (hC : CbarIn x)
    (hnc : F.f 3 (x 1) < F.f 3 (x 6)) (hbc : 0 < ⟪x 2 - x 1, x 6 - x 1⟫)
    (hU : ¬ LexAny F) : 0 < ⟪x 0 - x 1, x 6 - x 1⟫ := by
  by_contra hgac
  push Not at hgac
  have T := type24OfFac F
  have hom3 : 0 < omega3 x := hC.1
  have hom5 : 0 < omega5 x := hC.2.2.1
  have ha3 : 0 < oblX0 x 3 := T.X0_pos (v := 3) (by decide)
  have ha5 : 0 < oblX0 x 5 := T.X0_pos (v := 5) (by decide)
  have hb3 : 0 < oblX2 x 3 := T.X2_pos (v := 3) (by decide)
  have hb5 : 0 < oblX2 x 5 := T.X2_pos (v := 5) (by decide)
  have hc3 : 0 < oblX6 x 3 := T.X6_pos (v := 3) (by decide)
  have hc5 : 0 < oblX6 x 5 := T.X6_pos (v := 5) (by decide)
  have e3 : oblX2 x 3 + oblX6 x 3 - omega3 x * oblX0 x 3 = 1 := by linarith [eq3 F]
  have e5 : oblX0 x 5 + oblX2 x 5 - 1 = omega5 x * oblX6 x 5 := by linarith [eq5 F]
  have hN : ∀ (t : Fin 9) (v : Fin 7), ⟪F.N t, x v - x 1⟫ = F.f t (x v) - F.f t (x 1) :=
    fun t v => (F.hN t (x v) (x 1)).symm
  have hx6 : x 6 - x 1 ≠ 0 := sub_ne_zero.mpr fun h => absurd (T.inj h) (by decide)
  have hx0 : x 0 - x 1 ≠ 0 := sub_ne_zero.mpr fun h => absurd (T.inj h) (by decide)
  have hA : 0 < ⟪x 0 - x 1, x 0 - x 1⟫ := real_inner_self_pos.mpr hx0
  have hCC : 0 < ⟪x 6 - x 1, x 6 - x 1⟫ := real_inner_self_pos.mpr hx6
  -- facet data
  have f0_6 : F.f 0 (x 6) < 0 := F.neg 0 6 (by decide)
  have f0_1 : F.f 0 (x 1) = 0 := F.zero 0 1 (by decide)
  have f1_6 : F.f 1 (x 6) = 0 := F.zero 1 6 (by decide)
  have f1_1 : F.f 1 (x 1) = 0 := F.zero 1 1 (by decide)
  have f1_0 : F.f 1 (x 0) = 0 := F.zero 1 0 (by decide)
  have f1_2 : F.f 1 (x 2) < 0 := F.neg 1 2 (by decide)
  have f2_1 : F.f 2 (x 1) < 0 := F.neg 2 1 (by decide)
  have f2_0 : F.f 2 (x 0) = 0 := F.zero 2 0 (by decide)
  have f2_2 : F.f 2 (x 2) = 0 := F.zero 2 2 (by decide)
  have f2_5 : F.f 2 (x 5) = 0 := F.zero 2 5 (by decide)
  have f2_3 : F.f 2 (x 3) < 0 := F.neg 2 3 (by decide)
  have f3_1 := F.neg 3 1 (by decide)
  have f4_1 : F.f 4 (x 1) < 0 := F.neg 4 1 (by decide)
  have f4_6 : F.f 4 (x 6) = 0 := F.zero 4 6 (by decide)
  have f5_1 : F.f 5 (x 1) = 0 := F.zero 5 1 (by decide)
  have f5_2 : F.f 5 (x 2) = 0 := F.zero 5 2 (by decide)
  have f5_6 : F.f 5 (x 6) = 0 := F.zero 5 6 (by decide)
  have f5_0 : F.f 5 (x 0) < 0 := F.neg 5 0 (by decide)
  have f6_2 : F.f 6 (x 2) = 0 := F.zero 6 2 (by decide)
  have f6_1 : F.f 6 (x 1) < 0 := F.neg 6 1 (by decide)
  have f6_0 : F.f 6 (x 0) < 0 := F.neg 6 0 (by decide)
  have f7_1 : F.f 7 (x 1) < 0 := F.neg 7 1 (by decide)
  have f7_6 : F.f 7 (x 6) = 0 := F.zero 7 6 (by decide)
  have f8_1 : F.f 8 (x 1) < 0 := F.neg 8 1 (by decide)
  have f8_6 : F.f 8 (x 6) = 0 := F.zero 8 6 (by decide)
  -- the facing of 025 at `e_c`
  have hn2eq : F.f 2 (x 6) - F.f 2 (x 1) = F.f 2 (x 1) * omega5 x := by
    have ev := fac_eval F 2 5
    rw [f2_5, f2_0, f2_2] at ev
    have h : oblX6 x 5 * (F.f 2 (x 6) - F.f 2 (x 1) - F.f 2 (x 1) * omega5 x) = 0 := by
      linear_combination -ev + F.f 2 (x 1) * e5
    exact sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_left hc5.ne') |> fun h => by linarith
  have hn2 : F.f 2 (x 6) - F.f 2 (x 1) < 0 := by
    rw [hn2eq]; exact mul_neg_of_neg_of_pos f2_1 hom5
  -- choose the tilt parameter
  obtain ⟨η, hη0, hηA, hηtie⟩ : ∃ η : ℝ, 0 < η ∧
      η * |⟪x 0 - x 1, x 2 - x 1⟫| < ⟪x 0 - x 1, x 0 - x 1⟫ ∧
      (F.f 6 (x 6) = F.f 6 (x 1) →
        -(F.f 6 (x 0) - F.f 6 (x 1)) - η * (F.f 6 (x 2) - F.f 6 (x 1)) ≠ 0) := by
    obtain ⟨g, hg⟩ : ∃ g, g = |⟪x 0 - x 1, x 2 - x 1⟫| := ⟨_, rfl⟩
    obtain ⟨A, hAd⟩ : ∃ A, A = ⟪x 0 - x 1, x 0 - x 1⟫ := ⟨_, rfl⟩
    rw [← hg, ← hAd]
    rw [← hAd] at hA
    have hg0 : 0 ≤ g := by rw [hg]; exact abs_nonneg _
    have hη1 : 0 < A / (g + 1) / 2 := by positivity
    have hη1A : A / (g + 1) / 2 * g < A := by
      have : A / (g + 1) / 2 * g = A * g / (2 * (g + 1)) := by field_simp
      rw [this, div_lt_iff₀ (by positivity)]; nlinarith
    have hφ : 0 < F.f 6 (x 2) - F.f 6 (x 1) := by linarith
    by_cases h : -(F.f 6 (x 0) - F.f 6 (x 1)) - A / (g + 1) / 2 * (F.f 6 (x 2) - F.f 6 (x 1)) = 0
    · refine ⟨A / (g + 1) / 2 / 2, by positivity, ?_, fun _ => ?_⟩
      · nlinarith
      · intro hh
        nlinarith [mul_pos hη1 hφ]
    · exact ⟨_, hη1, hη1A, fun _ => h⟩
  obtain ⟨d1, hd1⟩ : ∃ d1 : ℝ³, d1 = -(x 0 - x 1) - η • (x 2 - x 1) := ⟨_, rfl⟩
  have hNd : ∀ t : Fin 9, ⟪F.N t, d1⟫ =
      -(F.f t (x 0) - F.f t (x 1)) - η * (F.f t (x 2) - F.f t (x 1)) := by
    intro t
    rw [hd1, inner_sub_right, inner_neg_right, inner_smul_right, hN, hN]
  have hz0d : ⟪x 0 - x 1, d1⟫ = -⟪x 0 - x 1, x 0 - x 1⟫ - η * ⟪x 0 - x 1, x 2 - x 1⟫ := by
    rw [hd1, inner_sub_right, inner_neg_right, inner_smul_right]
  have hl1 : 0 < ⟪x 0 - x 1, x 0 - x 1⟫ + η * ⟪x 0 - x 1, x 2 - x 1⟫ := by
    have := mul_le_mul_of_nonneg_left (neg_abs_le ⟪x 0 - x 1, x 2 - x 1⟫) hη0.le
    nlinarith
  have hsh : ∀ (v : Fin 7) (w : ℝ³), ⟪x v, w⟫ = ⟪x v - x 1, w⟫ + ⟪x 1, w⟫ := fun v w => by
    rw [inner_sub_left]; ring
  -- depth comparisons at `(e_c, d1, 0)`
  have hlex01 : LexLt3 (⟪x 0, x 6 - x 1⟫, ⟪x 0, d1⟫, ⟪x 0, (0 : ℝ³)⟫)
      (⟪x 1, x 6 - x 1⟫, ⟪x 1, d1⟫, ⟪x 1, (0 : ℝ³)⟫) := by
    simp only [LexLt3]
    apply lexPos3_of_two
    rw [hsh 0 (x 6 - x 1), hsh 0 d1]
    rcases lt_or_eq_of_le hgac with h | h
    · left; linarith
    · right; refine ⟨by linarith, by linarith⟩
  have hlex12 : LexLt3 (⟪x 1, x 6 - x 1⟫, ⟪x 1, d1⟫, ⟪x 1, (0 : ℝ³)⟫)
      (⟪x 2, x 6 - x 1⟫, ⟪x 2, d1⟫, ⟪x 2, (0 : ℝ³)⟫) := by
    simp only [LexLt3]
    apply lexPos3_of_two
    left
    rw [hsh 2 (x 6 - x 1)]
    linarith
  -- facings at `e_c`
  have hn0 : ⟪F.N 0, x 6 - x 1⟫ < 0 := by rw [hN, f0_1]; linarith
  have hn1 : ⟪F.N 1, x 6 - x 1⟫ = 0 := by rw [hN, f1_6, f1_1]; ring
  have hn2 : ⟪F.N 2, x 6 - x 1⟫ < 0 := by rw [hN]; linarith
  have hn3 : 0 < ⟪F.N 3, x 6 - x 1⟫ := by rw [hN]; linarith
  have hn4 : 0 < ⟪F.N 4, x 6 - x 1⟫ := by rw [hN, f4_6]; linarith
  have hn5 : ⟪F.N 5, x 6 - x 1⟫ = 0 := by rw [hN, f5_6, f5_1]; ring
  have hn7 : 0 < ⟪F.N 7, x 6 - x 1⟫ := by rw [hN, f7_6]; linarith
  have hn8 : 0 < ⟪F.N 8, x 6 - x 1⟫ := by rw [hN, f8_6]; linarith
  have hd1' : 0 < ⟪F.N 1, d1⟫ := by
    rw [hNd, f1_0, f1_1]; nlinarith [mul_pos hη0 (neg_pos.mpr f1_2)]
  have hd5' : 0 < ⟪F.N 5, d1⟫ := by rw [hNd, f5_1, f5_2]; linarith
  have hinj4 : ∀ (i j : ZMod 4), (![1, 0, 5, 2] : ZMod 4 → Fin 7) i = (![1, 0, 5, 2] : ZMod 4 → Fin 7) j → i = j := by
    intro i j h; fin_cases i <;> fin_cases j <;> first | rfl | exact absurd h (by decide)
  have hinj5 : ∀ (i j : ZMod 5), (![1, 0, 5, 3, 2] : ZMod 5 → Fin 7) i = (![1, 0, 5, 3, 2] : ZMod 5 → Fin 7) j → i = j := by
    intro i j h; fin_cases i <;> fin_cases j <;> first | rfl | exact absurd h (by decide)
  -- Case `235` up: rim `![1, 0, 5, 2]`
  have h4 : LexPos3 ⟪F.N 6, x 6 - x 1⟫ ⟪F.N 6, d1⟫ ⟪F.N 6, (0 : ℝ³)⟫ → False := by
    intro h6
    apply hU
    refine ⟨4, inferInstance, (![1, 0, 5, 2] : ZMod 4 → Fin 7), {1, 3, 4, 5, 6, 7, 8}, {0, 2},
      x 6 - x 1, d1, 0, by decide, hinj4, (by unfold S0xCycUD; decide), ?_, ?_, ?_⟩
    · intro t ht
      simp only [Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact Or.inr ⟨hn1, Or.inl hd1'⟩
      · exact Or.inl hn3
      · exact Or.inl hn4
      · exact Or.inr ⟨hn5, Or.inl hd5'⟩
      · exact h6
      · exact Or.inl hn7
      · exact Or.inl hn8
    · intro t ht
      simp only [Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl
      · exact Or.inl (by linarith)
      · exact Or.inl (by linarith)
    · exact robUniLex_four_of_mixed ⟨((0 : ZMod 4), (3 : ZMod 4)), by decide, Or.inl (by
          dsimp only [Matrix.cons_val]; rw [hsh 2, hsh 1]; simp only [sub_self, inner_zero_left]; linarith)⟩
        ⟨((0 : ZMod 4), (1 : ZMod 4)), by decide, hlex01⟩
  -- Case `235` down: rim `![1, 0, 5, 3, 2]`
  have h5 : LexPos3 (-⟪F.N 6, x 6 - x 1⟫) (-⟪F.N 6, d1⟫) (-⟪F.N 6, (0 : ℝ³)⟫) → False := by
    intro h6
    have h6le : F.f 6 (x 6) ≤ F.f 6 (x 1) := by
      rcases h6 with h | ⟨h, _⟩
      · rw [hN] at h; linarith
      · rw [hN] at h; linarith
    obtain ⟨l, m, s, hl0, hl1', hm0, hm1, hs0, hvec⟩ := chord_e16 F hC hnc h6le
    have hchord : min ⟪x 2, x 6 - x 1⟫ ⟪x 5, x 6 - x 1⟫ < max ⟪x 0, x 6 - x 1⟫ ⟪x 3, x 6 - x 1⟫ := by
      have hi := congrArg (fun v => ⟪v, x 6 - x 1⟫) hvec
      simp only [inner_add_left, inner_smul_left, conj_trivial] at hi
      have e0 := hsh 0 (x 6 - x 1)
      have e2 := hsh 2 (x 6 - x 1)
      have e3' := hsh 3 (x 6 - x 1)
      have e5' := hsh 5 (x 6 - x 1)
      have hmax0 := le_max_left ⟪x 0, x 6 - x 1⟫ ⟪x 3, x 6 - x 1⟫
      have hmax3 := le_max_right ⟪x 0, x 6 - x 1⟫ ⟪x 3, x 6 - x 1⟫
      have hmin2 := min_le_left ⟪x 2, x 6 - x 1⟫ ⟪x 5, x 6 - x 1⟫
      have hmin5 := min_le_right ⟪x 2, x 6 - x 1⟫ ⟪x 5, x 6 - x 1⟫
      have h1 := mul_le_mul_of_nonneg_left hmax0 (sub_nonneg.mpr hl1')
      have h2 := mul_le_mul_of_nonneg_left hmax3 hl0
      have h3 := mul_le_mul_of_nonneg_left hmin2 (sub_nonneg.mpr hm1)
      have h4' := mul_le_mul_of_nonneg_left hmin5 hm0
      have := mul_pos hs0 hCC
      nlinarith
    apply hU
    refine ⟨5, inferInstance, (![1, 0, 5, 3, 2] : ZMod 5 → Fin 7), {1, 3, 4, 5, 7, 8}, {0, 2, 6},
      x 6 - x 1, d1, 0, by decide, hinj5, (by unfold S0xCycUD; decide), ?_, ?_, ?_⟩
    · intro t ht
      simp only [Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl | rfl | rfl | rfl | rfl
      · exact Or.inr ⟨hn1, Or.inl hd1'⟩
      · exact Or.inl hn3
      · exact Or.inl hn4
      · exact Or.inr ⟨hn5, Or.inl hd5'⟩
      · exact Or.inl hn7
      · exact Or.inl hn8
    · intro t ht
      simp only [Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl | rfl
      · exact Or.inl (by linarith)
      · exact Or.inl (by linarith)
      · exact h6
    · exact robUniLex_five_chord _ hlex01 hlex12 hchord
  -- the facet `235` at `(e_c, d1)`
  rcases lt_trichotomy (F.f 6 (x 6)) (F.f 6 (x 1)) with hlt | heq | hgt
  · exact h5 (Or.inl (by rw [hN]; linarith))
  · have hg := hηtie heq
    rw [← hNd 6] at hg
    have h0 : ⟪F.N 6, x 6 - x 1⟫ = 0 := by rw [hN, heq]; ring
    rcases lt_or_gt_of_ne hg with hlt | hgt
    · exact h5 (Or.inr ⟨by rw [h0]; ring, Or.inl (by linarith)⟩)
    · exact h4 (Or.inr ⟨h0, Or.inl hgt⟩)
  · exact h4 (Or.inl (by rw [hN]; linarith))


/-- **Lemma E12-Gbc** (the `Sym24` twin of `e16_gbc`): `nB > 0`, `G_bc > 0` and no lex leaf give
`G_ab > 0`. -/
theorem e12_gbc {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (hC : CbarIn x)
    (hnb : F.f 3 (x 1) < F.f 3 (x 2)) (hbc : 0 < ⟪x 2 - x 1, x 6 - x 1⟫)
    (hU : ¬ LexAny F) : 0 < ⟪x 0 - x 1, x 2 - x 1⟫ := by
  have h := e16_gbc (sym24 F) ((cbarIn_comp_pi24 x).2 hC)
    (by simpa [sym24_f_apply] using hnb)
    (by simpa [Function.comp_apply, real_inner_comm] using hbc)
    (fun h => hU (lexAny_sym F h))
  simpa [Function.comp_apply] using h


/-- **Corollary OffOB1-FamilyA.**  On Family A (`a5 > 1`, `a4 ≤ 1`; this includes `a4 = 1`), off `OB1` and
without a lex leaf, `G_ac > 0`. -/
theorem gac_pos_famA {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (hC : CbarIn x)
    (ha5 : 1 < oblX0 x 5) (ha4 : oblX0 x 4 ≤ 1) (hO : ¬ Minimality.H24K.SAT.OB1 x)
    (hU : ¬ LexAny F) : 0 < ⟪x 0 - x 1, x 6 - x 1⟫ := by
  have T := type24OfFac F
  have hb4 : 0 < oblX2 x 4 := T.X2_pos (v := 4) (by decide)
  have hb5 : 0 < oblX2 x 5 := T.X2_pos (v := 5) (by decide)
  have hc4 : 0 < oblX6 x 4 := T.X6_pos (v := 4) (by decide)
  have hc5 : 0 < oblX6 x 5 := T.X6_pos (v := 5) (by decide)
  have hnC : 0 < nC x := by
    dsimp [nC]; nlinarith [mul_nonneg hb5.le (sub_nonneg.mpr ha4), mul_pos hb4 (sub_pos.mpr ha5)]
  have hnB : nB x < 0 := by
    dsimp [nB]; nlinarith [mul_nonneg hc5.le (sub_nonneg.mpr ha4), mul_pos hc4 (sub_pos.mpr ha5)]
  have hnc : F.f 3 (x 1) < F.f 3 (x 6) := (nC_pos_iff F).mp hnC
  have hnb : F.f 3 (x 2) ≤ F.f 3 (x 1) := not_lt.mp (fun h => absurd ((nB_pos_iff F).mpr h) (not_lt.mpr hnB.le))
  by_cases hbc : ⟪x 2 - x 1, x 6 - x 1⟫ ≤ 0
  · have hw := w26_bound F hC hbc (by linarith) hU
    by_contra hac
    push Not at hac
    apply hO
    refine ⟨?_, hac, hbc⟩
    have : ⟪x 0 - x 1, x 2 - x 6⟫ = ⟪x 0 - x 1, x 2 - x 1⟫ - ⟪x 0 - x 1, x 6 - x 1⟫ := by
      rw [← inner_sub_right]; congr 1; abel
    linarith
  · exact e16_gbc F hC hnc (not_le.mp hbc) hU

end Minimality.T24.A17
