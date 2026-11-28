module

public import Minimality.Type24OffOB1DW4
public import Minimality.M4fType24

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21 Minimality.FaceChord Minimality.T24.SAT Minimality.T24.Stmt Minimality.T24.Q45
  Minimality.T24.Reg Minimality.T24.A19

/-!
# Type 24 off `OB1`: the K0 rim from the plane identity (job OSPEC27)

nopert229 notes/OPENSPECIAL-STRATEGY.md section 2o.  On `kJ = 0` (`x 2, x 4, x 5, x 6` coplanar) with the frame signs
`a4 b5 - a5 b4 > 0`, `a5 c4 - a4 c5 > 0` of the open statement, `x 6` is an affine combination

  `x 6 = ν x 2 + λ x 4 + μ x 5`,  `ν, λ > 0 > μ`,  `ν + λ + μ = 1`   (`k0Aff_of`; `λ = a5 / D`, `μ = -a4 / D`,
  `ν = (a4 b5 - a5 b4) / D`, `D = a5 c4 - a4 c5`, and `ν + λ + μ = 1` is `kJ_obl`),

so for every linear depth `z` (also lexicographic): if `z4 < z5`, then `6` is below `4`, or `6` below `2`, or `5`
below `2` (`lex_conv`: `6` above `2` and `4` with `5` not below `2` would make `4` above `5`).  That is exactly what
the K0 rims need once `4 < 3 < 5` holds at level 1 of the K0 view `(x 0 - x 4, x 0 - x 5, N3)`
(`robUniLex_five_k0R`, `robUniLex_four_of_mixed`), so

  **`k0RU_of_aff`**: plane identity, angle `0 4 3` acute and `⟪x 5 - x 3, x 0 - x 4⟫ > 0` give `K0RU F t` (both rims,
  every `t`); for `t ≤ 1` the second letter is `k0_z35`, so `K0RU` follows from the acute angle alone
  (`k0ViewOK_of_acute`).

The mirror (`π24`) is the same lemma for `π24 x` (`k0Aff_sym`).  Residue: `K0Res` (on `kJ = 0` and off the wall of each
view with its `236` condition: an obtuse or right angle `0 4 3`, or `t > 1` with `3` not below `5`; mirror `0 5 3`),
`Q45ResWR3` (= `Q45ResWR2U` and `K0Res` at its decomposition), **`OpenSpecialR3`** (equivalent to `OpenSpecialR2U`,
`openSpecialR3_iff_R2U`) and its chains.
-/

namespace Minimality.T24.OSpec

variable {x : Fin 7 → ℝ³}

section K0Aff
open Minimality.LexCell

/-! ### Lexicographic cone algebra -/

/-- Weakly lex-nonnegative triple. -/
def LexNN3 (a b c : ℝ) : Prop := LexPos3 a b c ∨ (a = 0 ∧ b = 0 ∧ c = 0)

theorem lexNN3_congr {a b c a' b' c' : ℝ} (ha : a = a') (hb : b = b') (hc : c = c') (h : LexNN3 a b c) :
    LexNN3 a' b' c' := by
  subst ha hb hc; exact h

theorem lexPos3_congr {a b c a' b' c' : ℝ} (ha : a = a') (hb : b = b') (hc : c = c') (h : LexPos3 a b c) :
    LexPos3 a' b' c' := by
  subst ha hb hc; exact h

theorem lexPos3_add_nn {a b c a' b' c' : ℝ} (h : LexPos3 a b c) (h' : LexNN3 a' b' c') :
    LexPos3 (a + a') (b + b') (c + c') := by
  rcases h' with h' | ⟨rfl, rfl, rfl⟩
  · rcases h with h | ⟨rfl, h | ⟨rfl, h⟩⟩ <;> rcases h' with h' | ⟨rfl, h' | ⟨rfl, h'⟩⟩
    all_goals first
      | exact Or.inl (by linarith)
      | exact Or.inr ⟨by ring, Or.inl (by linarith)⟩
      | exact Or.inr ⟨by ring, Or.inr ⟨by ring, by linarith⟩⟩
  · simpa using h

theorem lexNN3_add {a b c a' b' c' : ℝ} (h : LexNN3 a b c) (h' : LexNN3 a' b' c') :
    LexNN3 (a + a') (b + b') (c + c') := by
  rcases h with h | ⟨rfl, rfl, rfl⟩
  · exact Or.inl (lexPos3_add_nn h h')
  · simpa using h'

theorem lexPos3_mul {k a b c : ℝ} (hk : 0 < k) (h : LexPos3 a b c) : LexPos3 (k * a) (k * b) (k * c) := by
  rcases h with h | ⟨rfl, h | ⟨rfl, h⟩⟩
  · exact Or.inl (mul_pos hk h)
  · exact Or.inr ⟨by ring, Or.inl (mul_pos hk h)⟩
  · exact Or.inr ⟨by ring, Or.inr ⟨by ring, mul_pos hk h⟩⟩

theorem lexNN3_mul {k a b c : ℝ} (hk : 0 < k) (h : LexNN3 a b c) : LexNN3 (k * a) (k * b) (k * c) := by
  rcases h with h | ⟨rfl, rfl, rfl⟩
  · exact Or.inl (lexPos3_mul hk h)
  · exact Or.inr ⟨by ring, by ring, by ring⟩

theorem lexNN3_of_not {a b c : ℝ} (h : ¬ LexPos3 a b c) : LexNN3 (-a) (-b) (-c) := by
  simp only [LexPos3, not_or, not_and, not_lt] at h
  obtain ⟨ha, h2⟩ := h
  rcases ha.lt_or_eq with ha | rfl
  · exact Or.inl (Or.inl (by linarith))
  · obtain ⟨hb, h3⟩ := h2 rfl
    rcases hb.lt_or_eq with hb | rfl
    · exact Or.inl (Or.inr ⟨by ring, Or.inl (by linarith)⟩)
    · rcases (h3 rfl).lt_or_eq with hc | rfl
      · exact Or.inl (Or.inr ⟨by ring, Or.inr ⟨by ring, by linarith⟩⟩)
      · exact Or.inr ⟨by ring, by ring, by ring⟩

theorem not_lexPos3_of_nn {a b c : ℝ} (h : LexNN3 (-a) (-b) (-c)) : ¬ LexPos3 a b c := by
  intro hp
  rcases h with h | ⟨h1, h2, h3⟩
  · rcases hp with hp | ⟨rfl, hp | ⟨rfl, hp⟩⟩ <;> rcases h with h | ⟨h1, h | ⟨h2, h⟩⟩ <;> linarith
  · rcases hp with hp | ⟨_, hp | ⟨_, hp⟩⟩ <;> linarith

/-- **The plane identity in lex form**: with `r = ν p + λ q + μ w` componentwise (`ν, λ > 0 > μ`, `ν + λ + μ = 1`) and
`q < w`, one of `r < q`, `r < p`, `w < p` holds (strict lex comparisons of the triples). -/
theorem lex_conv {p1 p2 p3 q1 q2 q3 w1 w2 w3 r1 r2 r3 nu la mu : ℝ} (hnu : 0 < nu) (hla : 0 < la)
    (hmu : mu < 0) (hs : nu + la + mu = 1) (e1 : r1 = nu * p1 + la * q1 + mu * w1)
    (e2 : r2 = nu * p2 + la * q2 + mu * w2) (e3 : r3 = nu * p3 + la * q3 + mu * w3)
    (hqw : LexPos3 (w1 - q1) (w2 - q2) (w3 - q3)) :
    LexPos3 (q1 - r1) (q2 - r2) (q3 - r3) ∨ LexPos3 (p1 - r1) (p2 - r2) (p3 - r3) ∨
      LexPos3 (p1 - w1) (p2 - w2) (p3 - w3) := by
  by_contra hc
  simp only [not_or] at hc
  obtain ⟨hrq, hrp, hwp⟩ := hc
  -- `r ≥ p`, `w ≥ p`
  have Nrp := lexNN3_of_not hrp
  have Nwp := lexNN3_of_not hwp
  have hm : 0 < -mu := by linarith
  -- `λ (q - p) = (r - p) + (-μ) (w - p) ≥ 0`
  have Nqp : LexNN3 (la * (q1 - p1)) (la * (q2 - p2)) (la * (q3 - p3)) :=
    lexNN3_congr (by linear_combination e1 + p1 * hs) (by linear_combination e2 + p2 * hs)
      (by linear_combination e3 + p3 * hs) (lexNN3_add Nrp (lexNN3_mul hm Nwp))
  -- `λ (q - r) = ν λ (q - p) + (-μ) λ (w - q) > 0`
  have P : LexPos3 (la * (q1 - r1)) (la * (q2 - r2)) (la * (q3 - r3)) :=
    lexPos3_congr (by linear_combination la * e1 + la * q1 * hs) (by linear_combination la * e2 + la * q2 * hs)
      (by linear_combination la * e3 + la * q3 * hs)
      (lexPos3_add_nn (lexPos3_mul (mul_pos hm hla) hqw) (lexNN3_mul hnu Nqp))
  apply hrq
  rcases P with P | ⟨P1, P | ⟨P2, P⟩⟩
  · exact Or.inl (pos_of_mul_pos_right P hla.le)
  · exact Or.inr ⟨(mul_eq_zero.mp P1).resolve_left hla.ne', Or.inl (pos_of_mul_pos_right P hla.le)⟩
  · exact Or.inr ⟨(mul_eq_zero.mp P1).resolve_left hla.ne', Or.inr ⟨(mul_eq_zero.mp P2).resolve_left hla.ne',
      pos_of_mul_pos_right P hla.le⟩⟩

/-! ### The rims -/

/-- A 5-cycle (linear order) with `z3 < z2 < z1` and (`z1 < z0` or `z4 < z0` or `z4 < z3`) is robustly unimodal. -/
theorem five_k0R_lin {α : Type*} [LinearOrder α] (z : ZMod 5 → α) (h21 : z 2 < z 1) (h32 : z 3 < z 2)
    (h : z 1 < z 0 ∨ z 4 < z 0 ∨ z 4 < z 3) : Minimality.GenRev.RobUniO z := by
  intro B b c d hb hbc hcd hd
  have hB : B = 0 ∨ B = 1 ∨ B = 2 ∨ B = 3 ∨ B = 4 := by revert B; decide
  have hbcd : (b = 1 ∧ c = 2 ∧ d = 3) ∨ (b = 1 ∧ c = 2 ∧ d = 4) ∨
      (b = 1 ∧ c = 3 ∧ d = 4) ∨ (b = 2 ∧ c = 3 ∧ d = 4) := by omega
  rcases hB with rfl | rfl | rfl | rfl | rfl <;>
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
  all_goals (rintro ⟨q1, q2, q3, q4⟩; rcases h with h | h | h <;> order)

/-- **A 5-cycle with `z3 < z2 < z1` and (`z1 < z0` or `z4 < z0` or `z4 < z3`) is `RobUniLex`.** -/
theorem robUniLex_five_k0R (z : ZMod 5 → ℝ × ℝ × ℝ) (h21 : LexLt3 (z 2) (z 1)) (h32 : LexLt3 (z 3) (z 2))
    (h : LexLt3 (z 1) (z 0) ∨ LexLt3 (z 4) (z 0) ∨ LexLt3 (z 4) (z 3)) : RobUniLex z :=
  (Minimality.GenRev.robUniLex_iff_O z).2 (five_k0R_lin _ (lexLt3_toLex_dw h21) (lexLt3_toLex_dw h32)
    (h.imp lexLt3_toLex_dw (Or.imp lexLt3_toLex_dw lexLt3_toLex_dw)))

/-- Lex transitivity. -/
theorem lexLt3_trans' {p q r : ℝ × ℝ × ℝ} (h1 : LexLt3 p q) (h2 : LexLt3 q r) : LexLt3 p r :=
  (Minimality.T24.A15.lexLt3_iff _ _).2
    (lt_trans ((Minimality.T24.A15.lexLt3_iff _ _).1 h1) ((Minimality.T24.A15.lexLt3_iff _ _).1 h2))

/-! ### The plane identity on `kJ = 0` -/

/-- `x 6` is an affine combination of `x 2, x 4, x 5` with coefficient signs `+, +, -`. -/
def K0Aff (x : Fin 7 → ℝ³) : Prop :=
  ∃ nu la mu : ℝ, 0 < nu ∧ 0 < la ∧ mu < 0 ∧ nu + la + mu = 1 ∧ x 6 = nu • x 2 + la • x 4 + mu • x 5

/-- **The plane identity on `kJ = 0`** from the frame signs `a4 b5 - a5 b4 > 0`, `a5 c4 - a4 c5 > 0` (`a4, a5 > 0`). -/
theorem k0Aff_of (F : S0xFac 9 s0x_S24 x) (hkJ : det3 (x 5 - x 6) (x 2 - x 6) (x 4 - x 6) = 0)
    (h4 : 0 < oblX0 x 4) (h5 : 0 < oblX0 x 5) (b3 : 0 < oblX0 x 4 * oblX2 x 5 - oblX0 x 5 * oblX2 x 4)
    (b4 : 0 < oblX0 x 5 * oblX6 x 4 - oblX0 x 4 * oblX6 x 5) : K0Aff x := by
  have T := M4.type24OfFac F
  have hk := kJ_obl F hkJ
  set a4 := oblX0 x 4; set a5 := oblX0 x 5; set p4 := oblX2 x 4; set p5 := oblX2 x 5
  set c4 := oblX6 x 4; set c5 := oblX6 x 5
  set D := a5 * c4 - a4 * c5 with hDdef
  have hD : D ≠ 0 := b4.ne'
  have num : a4 * p5 - a5 * p4 + a5 - a4 = D := by rw [hDdef]; linear_combination -hk
  have s1 : (a4 * p5 - a5 * p4) / D + a5 / D + -a4 / D = 1 := by
    rw [show (a4 * p5 - a5 * p4) / D + a5 / D + -a4 / D = (a4 * p5 - a5 * p4 + a5 - a4) / D by ring, num,
      div_self hD]
  refine ⟨(a4 * p5 - a5 * p4) / D, a5 / D, -a4 / D, div_pos b3 b4, div_pos h5 b4,
    div_neg_of_neg_of_pos (by linarith) b4, s1, ?_⟩
  · have key : ((a4 * p5 - a5 * p4) / D) • x 2 + (a5 / D) • x 4 + (-a4 / D) • x 5 =
        ((a4 * p5 - a5 * p4) / D + a5 / D + -a4 / D) • x 1 + (a5 / D * a4 + -a4 / D * a5) • (x 0 - x 1) +
        ((a4 * p5 - a5 * p4) / D + a5 / D * p4 + -a4 / D * p5) • (x 2 - x 1) +
        (a5 / D * c4 + -a4 / D * c5) • (x 6 - x 1) := by
      rw [T.rep 4, T.rep 5]; module
    have s2 : a5 / D * a4 + -a4 / D * a5 = 0 := by ring
    have s3 : (a4 * p5 - a5 * p4) / D + a5 / D * p4 + -a4 / D * p5 = 0 := by field_simp; ring
    have s4 : a5 / D * c4 + -a4 / D * c5 = 1 := by
      rw [show a5 / D * c4 + -a4 / D * c5 = (a5 * c4 - a4 * c5) / D by ring, ← hDdef, div_self hD]
    rw [key, s1, s2, s3, s4]; module

/-- **The plane identity of the mirror**: `K0Aff x → K0Aff (x ∘ π24)` (`x 2 = (1/ν) x 6 - (μ/ν) x 5 - (λ/ν) x 4`). -/
theorem k0Aff_sym (h : K0Aff x) : K0Aff (x ∘ Sym.pi24) := by
  obtain ⟨nu, la, mu, hnu, hla, hmu, hs, e⟩ := h
  refine ⟨1 / nu, -mu / nu, -la / nu, by positivity, div_pos (by linarith) hnu, div_neg_of_neg_of_pos (by linarith) hnu,
    ?_, ?_⟩
  · field_simp; linarith
  · simp only [Function.comp_apply, Sym.pi24_2, Sym.pi24_4, Sym.pi24_5, Sym.pi24_6]
    rw [e]
    have hn : nu ≠ 0 := hnu.ne'
    rw [smul_add, smul_add, smul_smul, smul_smul, smul_smul]
    field_simp
    module

/-! ### The K0 rims -/

/-- **The K0 rims from the plane identity**: with `K0Aff x`, the angle `0 4 3` acute and `3` below `5` at level 1
(`⟪x 5 - x 3, x 0 - x 4⟫ > 0`), both K0 rims are `RobUniLex` (so `K0RU F t` for every `t`). -/
theorem k0RU_of_aff (F : S0xFac 9 s0x_S24 x) (hA : K0Aff x) (h43 : 0 < ⟪x 0 - x 4, x 3 - x 4⟫)
    (h35 : 0 < ⟪x 5 - x 3, x 0 - x 4⟫) (t : ℝ) : K0RU F t := by
  obtain ⟨nu, la, mu, hnu, hla, hmu, hs, e⟩ := hA
  set u := x 0 - x 4
  set w := x 0 - x 5
  set n := F.N 3
  have L43 : LexLt3 (⟪x 4, u⟫, ⟪x 4, w⟫, ⟪x 4, n⟫) (⟪x 3, u⟫, ⟪x 3, w⟫, ⟪x 3, n⟫) := by
    refine Or.inl ?_
    have : ⟪x 3, u⟫ - ⟪x 4, u⟫ = ⟪u, x 3 - x 4⟫ := by rw [← inner_sub_left, real_inner_comm]
    show 0 < ⟪x 3, u⟫ - ⟪x 4, u⟫
    rw [this]; exact h43
  have L35 : LexLt3 (⟪x 3, u⟫, ⟪x 3, w⟫, ⟪x 3, n⟫) (⟪x 5, u⟫, ⟪x 5, w⟫, ⟪x 5, n⟫) := by
    refine Or.inl ?_
    have : ⟪x 5, u⟫ - ⟪x 3, u⟫ = ⟪x 5 - x 3, u⟫ := by rw [← inner_sub_left]
    show 0 < ⟪x 5, u⟫ - ⟪x 3, u⟫
    rw [this]; exact h35
  have L45 := lexLt3_trans' L43 L35
  have hv : ∀ v : ℝ³, ⟪x 6, v⟫ = nu * ⟪x 2, v⟫ + la * ⟪x 4, v⟫ + mu * ⟪x 5, v⟫ := by
    intro v; rw [e, inner_add_left, inner_add_left, real_inner_smul_left, real_inner_smul_left,
      real_inner_smul_left]
  have C := lex_conv hnu hla hmu hs (hv u) (hv w) (hv n) L45
  constructor
  · intro _
    refine robUniLex_five_k0R (k0Z F rimK5) L35 L43 ?_
    rcases C with C | C | C
    · exact Or.inr (Or.inr C)
    · exact Or.inr (Or.inl C)
    · exact Or.inl C
  · intro _
    refine robUniLex_four_of_mixed ⟨(2, 1), by decide, L43⟩ ?_
    rcases C with C | C | C
    · exact ⟨(2, 3), by decide, C⟩
    · exact ⟨(0, 3), by decide, C⟩
    · exact ⟨(0, 1), by decide, lexLt3_trans' L35 C⟩

/-- **The K0 view from the acute angle `0 4 3`** (the region theorem): on `kJ = 0` with the frame signs, off the wall
`a4 = 1`, with the `236` condition `a4 (t - 1) < t a5`, the angle `0 4 3` acute and, for `t > 1`, `3` below `5` at
level 1, the K0 view is a lex cell (for `t ≤ 1` the second letter is `k0_z35`). -/
theorem k0ViewOK_of_acute (F : S0xFac 9 s0x_S24 x) (hkJ : det3 (x 5 - x 6) (x 2 - x 6) (x 4 - x 6) = 0)
    (h4 : 1 < oblX0 x 4) (h5 : 1 ≤ oblX0 x 5) (b3 : 0 < oblX0 x 4 * oblX2 x 5 - oblX0 x 5 * oblX2 x 4)
    (b4 : 0 < oblX0 x 5 * oblX6 x 4 - oblX0 x 4 * oblX6 x 5) {s t : ℝ} (hs0 : 0 < s) (ht0 : 0 < t)
    (hst : 1 < s + t) (hdec : x 3 - x 0 = s • (x 4 - x 0) + t • (x 5 - x 0))
    (h7 : oblX0 x 4 * (t - 1) < t * oblX0 x 5) (h43 : 0 < ⟪x 0 - x 4, x 3 - x 4⟫)
    (h35 : 1 < t → 0 < ⟪x 5 - x 3, x 0 - x 4⟫) : K0ViewOK F := by
  have hA := k0Aff_of F hkJ (by linarith) (by linarith) b3 b4
  have h35' : 0 < ⟪x 5 - x 3, x 0 - x 4⟫ := by
    rcases le_or_gt t 1 with ht | ht
    · exact k0_z35 F hs0 ht0 ht hst hdec h43
    · exact h35 ht
  exact k0ViewOK_of F hkJ h4 h5 hs0 ht0 hdec h7 (k0RU_of_aff F hA h43 h35' t)

/-- **The mirror region theorem**: the K0 view of `π24 x` (the view `(x 0 - x 5, x 0 - x 4, N3)` of `x`) from the
acute angle `0 5 3` (and, for `s > 1`, `3` below `4` along `x 0 - x 5`). -/
theorem k0ViewOK_sym_of_acute (F : S0xFac 9 s0x_S24 x) (hkJ : det3 (x 5 - x 6) (x 2 - x 6) (x 4 - x 6) = 0)
    (h5 : 1 < oblX0 x 5) (h4 : 1 ≤ oblX0 x 4) (b3 : 0 < oblX0 x 4 * oblX2 x 5 - oblX0 x 5 * oblX2 x 4)
    (b4 : 0 < oblX0 x 5 * oblX6 x 4 - oblX0 x 4 * oblX6 x 5) {s t : ℝ} (hs0 : 0 < s) (ht0 : 0 < t)
    (hst : 1 < s + t) (hdec : x 3 - x 0 = s • (x 4 - x 0) + t • (x 5 - x 0))
    (h7 : oblX0 x 5 * (s - 1) < s * oblX0 x 4) (h53 : 0 < ⟪x 0 - x 5, x 3 - x 5⟫)
    (h34 : 1 < s → 0 < ⟪x 4 - x 3, x 0 - x 5⟫) : K0ViewOK (Sym.sym24 F) := by
  have hA := k0Aff_sym (k0Aff_of F hkJ (by linarith) (by linarith) b3 b4)
  have hdec' : (x ∘ Sym.pi24) 3 - (x ∘ Sym.pi24) 0 =
      t • ((x ∘ Sym.pi24) 4 - (x ∘ Sym.pi24) 0) + s • ((x ∘ Sym.pi24) 5 - (x ∘ Sym.pi24) 0) := by
    simp only [Function.comp_apply, Sym.pi24_0, Sym.pi24_3, Sym.pi24_4, Sym.pi24_5]
    rw [hdec]; abel
  have g53 : 0 < ⟪(x ∘ Sym.pi24) 0 - (x ∘ Sym.pi24) 4, (x ∘ Sym.pi24) 3 - (x ∘ Sym.pi24) 4⟫ := by
    simpa only [Function.comp_apply, Sym.pi24_0, Sym.pi24_3, Sym.pi24_4] using h53
  have g34 : 0 < ⟪(x ∘ Sym.pi24) 5 - (x ∘ Sym.pi24) 3, (x ∘ Sym.pi24) 0 - (x ∘ Sym.pi24) 4⟫ := by
    rcases le_or_gt s 1 with hs | hs
    · exact k0_z35 (Sym.sym24 F) ht0 hs0 hs (by linarith) hdec' g53
    · simpa only [Function.comp_apply, Sym.pi24_0, Sym.pi24_3, Sym.pi24_4, Sym.pi24_5] using h34 hs
  exact k0ViewOK_sym_of F hkJ h5 h4 hs0 ht0 hdec h7 (k0RU_of_aff (Sym.sym24 F) hA g53 g34 s)

/-! ### The residue: the K0 rim letters made explicit -/

/-- What a residue point satisfies on `kJ = 0`: for each K0 view off its wall and with its `236` condition, an obtuse
or right angle `0 4 3` (mirror `0 5 3`), or `t > 1` with `3` not below `5` along `x 0 - x 4` (mirror `s > 1`, `3`
not below `4` along `x 0 - x 5`). -/
def K0Res (x : Fin 7 → ℝ³) (s t : ℝ) : Prop :=
  det3 (x 5 - x 6) (x 2 - x 6) (x 4 - x 6) = 0 →
    (1 < oblX0 x 4 → oblX0 x 4 * (t - 1) < t * oblX0 x 5 →
      ⟪x 0 - x 4, x 3 - x 4⟫ ≤ 0 ∨ (1 < t ∧ ⟪x 5 - x 3, x 0 - x 4⟫ ≤ 0)) ∧
    (1 < oblX0 x 5 → oblX0 x 5 * (s - 1) < s * oblX0 x 4 →
      ⟪x 0 - x 5, x 3 - x 5⟫ ≤ 0 ∨ (1 < s ∧ ⟪x 4 - x 3, x 0 - x 5⟫ ≤ 0))

/-- **Off both K0 views the rim letters hold** (`k0ViewOK_of_acute`, `k0ViewOK_sym_of_acute`). -/
theorem k0Res_of (F : S0xFac 9 s0x_S24 x) (h4 : 1 ≤ oblX0 x 4) (h5 : 1 ≤ oblX0 x 5)
    (b3 : 0 < oblX0 x 4 * oblX2 x 5 - oblX0 x 5 * oblX2 x 4)
    (b4 : 0 < oblX0 x 5 * oblX6 x 4 - oblX0 x 4 * oblX6 x 5) {s t : ℝ} (hs0 : 0 < s) (ht0 : 0 < t)
    (hst : 1 < s + t) (hdec : x 3 - x 0 = s • (x 4 - x 0) + t • (x 5 - x 0)) (hK : ¬ K0ViewOK F)
    (hKs : ¬ K0ViewOK (Sym.sym24 F)) : K0Res x s t := by
  intro hkJ
  constructor
  · intro ha h7
    by_contra hc
    push Not at hc
    exact hK (k0ViewOK_of_acute F hkJ ha h5 b3 b4 hs0 ht0 hst hdec h7 hc.1 hc.2)
  · intro ha h7
    by_contra hc
    push Not at hc
    exact hKs (k0ViewOK_sym_of_acute F hkJ ha h4 b3 b4 hs0 ht0 hst hdec h7 hc.1 hc.2)

/-- `Q45ResWR2U` with the explicit K0 rim letters `K0Res` at its decomposition. -/
def Q45ResWR3 (F : S0xFac 9 s0x_S24 x) : Prop :=
  Q45ResWR2U F ∧ ∃ s t : ℝ, 0 < s ∧ 0 < t ∧ 1 < s + t ∧ x 3 - x 0 = s • (x 4 - x 0) + t • (x 5 - x 0) ∧
    K0Res x s t

/-- **`Q45ResWR2U ⊆ Q45ResWR3`** under the frame signs (the K0 cuts of `Q45ResSTB` at the residue's decomposition). -/
theorem q45ResWR3_of_R2U {F : S0xFac 9 s0x_S24 x} (h4 : 1 ≤ oblX0 x 4) (h5 : 1 ≤ oblX0 x 5)
    (b3 : 0 < oblX0 x 4 * oblX2 x 5 - oblX0 x 5 * oblX2 x 4)
    (b4 : 0 < oblX0 x 5 * oblX6 x 4 - oblX0 x 4 * oblX6 x 5) (h : Q45ResWR2U F) : Q45ResWR3 F := by
  refine ⟨h, ?_⟩
  obtain ⟨s, t, hs, ht, hst, hd, hP⟩ := h.1.1.1.1
  have hB := hP.1.1.1.1.1.1.2
  exact ⟨s, t, hs, ht, hst, hd, k0Res_of F h4 h5 b3 b4 hs ht hst hd hB.2.2.2.1 hB.2.2.2.2⟩

/-- [OPEN] **The special piece with the K0 rim letters explicit, Rupert form**: `OpenSpecialR2U` with `Q45ResWR3` in
place of `Q45ResWR2U` (equivalent to it: `openSpecialR3_iff_R2U`). -/
def OpenSpecialR3 : Prop := ∀ (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x), ¬ H24K.SAT.OB1 x →
  1 ≤ oblX0 x 4 → 1 ≤ oblX0 x 5 →
  oblX0 x 4 * oblX6 x 3 - oblX0 x 3 * oblX6 x 4 < 0 →
  0 < oblX0 x 3 * oblX2 x 5 - oblX0 x 5 * oblX2 x 3 →
  0 < oblX0 x 4 * oblX2 x 5 - oblX0 x 5 * oblX2 x 4 →
  0 < oblX0 x 5 * oblX6 x 4 - oblX0 x 4 * oblX6 x 5 →
  Q45ResWR3 F → HoleFull x F → IsRupert (univ.image x)

/-- [PROVED] `OpenSpecialR3 ↔ OpenSpecialR2U` (`q45ResWR3_of_R2U`; the other direction is `Q45ResWR3 ⊆ Q45ResWR2U`). -/
theorem openSpecialR3_iff_R2U : OpenSpecialR3 ↔ OpenSpecialR2U :=
  ⟨fun h x F hO h4 h5 b1 b2 b3 b4 hr hF => h x F hO h4 h5 b1 b2 b3 b4 (q45ResWR3_of_R2U h4 h5 b3 b4 hr) hF,
    fun h x F hO h4 h5 b1 b2 b3 b4 hr hF => h x F hO h4 h5 b1 b2 b3 b4 hr.1 hF⟩

/-- [PROVED] `OpenSpecialR3 → OpenSpecialQU`. -/
theorem openSpecialQU_of_R3 (h : OpenSpecialR3) : OpenSpecialQU :=
  openSpecialQU_of_R2U (openSpecialR3_iff_R2U.1 h)

/-- [PROVED] Generic + special (K0 rim letters explicit) assemble to `Open24Rupert`. -/
theorem open24Rupert_of_split_R3 (h1 : OpenOB1) (h2 : OpenSpecialR3) : Open24Rupert :=
  open24Rupert_of_split_QU h1 (openSpecialQU_of_R3 h2)

end K0Aff

end Minimality.T24.OSpec

namespace Minimality.T24.Cell

/-- [PROVED] Headline chain with `cells28` and `OSpec.OpenSpecialR3` (OSPEC27). -/
theorem open24Rupert_of_cellCoverEmpty28_R3 (hN : CellCoverEmpty cells28) (hS : OSpec.OpenSpecialR3) :
    Open24Rupert :=
  open24Rupert_of_cellCoverEmpty28_R2U hN (OSpec.openSpecialR3_iff_R2U.1 hS)

/-- [PROVED] The `E4` cell chain with `OSpec.OpenSpecialR3`. -/
theorem open24Rupert_of_cellCoverEmptyE4_28_R3 (hN : CellCoverEmptyE4 cells28) (hS : OSpec.OpenSpecialR3) :
    Open24Rupert :=
  open24Rupert_of_cellCoverEmptyE4_28_R2U hN (OSpec.openSpecialR3_iff_R2U.1 hS)

/-- [PROVED] The `E10` cell chain with `OSpec.OpenSpecialR3`. -/
theorem open24Rupert_of_cellCoverEmptyE10_28_R3 (hN : CellCoverEmptyE10 cells28) (hS : OSpec.OpenSpecialR3) :
    Open24Rupert :=
  open24Rupert_of_cellCoverEmptyE10_28_R2U hN (OSpec.openSpecialR3_iff_R2U.1 hS)

end Minimality.T24.Cell
