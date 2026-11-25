module

public import Minimality.Type24HiddenCone
public import Minimality.RimCellClosed
public import Minimality.LexCell
public import Minimality.GenericLeaves
public import Minimality.GenRev24
public import Minimality.Type24SAT.Geo.Top

@[expose] public section

/-!
# EM: the lex triple `R^(c)_{±}` of the type-24 hidden-cap cover (Hydrogen task EM)

Formalization of `EMSpec.lean` in module form:
- Frame coordinates `lexRc`, `IsRcView`, `exists_RcView`, `LexCellAt`
- Five rim cycles `c1..c5`, cells `U1..U5`, `D1..D5`, `S0xCycUD`, injectivity
- Order lemmas `orderR1`, `orderR2`, `orderR3`, `orderR4_of_lt`, `orderR4_pos_iff`,
  `orderR4_neg_iff`, `orderR5m`, `orderR5p`, `one_lt_A5`
- Leaves `lexAny_of_Rc`, `lexAny_R1..R5p`, `isRupert_of_lexAny`

Note on `orderR4` from `EMSpec.lean`: for `s = 1`, `RobUniLex ↔ A3 < 1` holds (`orderR4_pos_iff`);
for `s = -1`, `RobUniLex ↔ A3 ≤ 1` holds (`orderR4_neg_iff`) because at the tie `A3 = 1`
positivity `a3, b3 > 0` gives `-1 < b3 - a3 < 1`, making `z 6 < z 0 < z 3 < z 2 < z 5`
strictly unimodal (`RobUniLex` = true while `A3 < 1` is false).  The leaves `lexAny_R4p` and
`lexAny_R4m` only require the `←` direction (`orderR4_of_lt`).
-/

set_option autoImplicit false
open scoped RealInnerProductSpace
open Finset

namespace Minimality.T24.EM

open Minimality Minimality.H21 Minimality.T24.SAT Minimality.RimCell Minimality.T24.HC Minimality.LexCell

variable {x : Fin 7 → ℝ³}

/-! ## The lex triple of a vertex and the view -/

/-- `lexRc s v = (a_v + b_v, s (a_v - b_v), c_v)`: the depth triple `(X_v·ζ0, X_v·ζ1, X_v·ζ2)` of vertex `v` (relative to `x 1`)
at `R^(c)_s`, with `ζ0 = (1,1,0)`, `ζ1 = s(1,-1,0)`, `ζ2 = (0,0,1)`. -/
noncomputable def lexRc (x : Fin 7 → ℝ³) (s : ℝ) (v : Fin 7) : ℝ × ℝ × ℝ :=
  (oblX0 x v + oblX2 x v, s * (oblX0 x v - oblX2 x v), oblX6 x v)

/-- `(b, d1, d2)` is the lex view `R^(c)_s`: its frame covectors are `(1,1,0)`, `s(1,-1,0)`, `(0,0,1)`. -/
def IsRcView (x : Fin 7 → ℝ³) (s : ℝ) (b d1 d2 : ℝ³) : Prop :=
  (⟪x 0 - x 1, b⟫ = 1 ∧ ⟪x 2 - x 1, b⟫ = 1 ∧ ⟪x 6 - x 1, b⟫ = 0) ∧
  (⟪x 0 - x 1, d1⟫ = s ∧ ⟪x 2 - x 1, d1⟫ = -s ∧ ⟪x 6 - x 1, d1⟫ = 0) ∧
  (⟪x 0 - x 1, d2⟫ = 0 ∧ ⟪x 2 - x 1, d2⟫ = 0 ∧ ⟪x 6 - x 1, d2⟫ = 1)

/-- The lex view `R^(c)_s` exists (no `OB1`, no sign hypothesis; under `OB1` the three levels lie in the cone `C`,
`cone24_of_zeta`, which the leaves below do not need). -/
theorem exists_RcView (F : S0xFac 9 s0x_S24 x) (s : ℝ) : ∃ b d1 d2 : ℝ³, IsRcView x s b d1 d2 := by
  obtain ⟨b, hb⟩ := Minimality.GenRev.exists_view_of_zeta F 1 1 0
  obtain ⟨d1, hd1⟩ := Minimality.GenRev.exists_view_of_zeta F s (-s) 0
  obtain ⟨d2, hd2⟩ := Minimality.GenRev.exists_view_of_zeta F 0 0 1
  exact ⟨b, d1, d2, hb, hd1, hd2⟩

/-- Facet signs at the lex view `(b, d1, d2)`: strictly lex-up on `U`, strictly lex-down on `Dn`
(exactly the hypotheses of `Gen.LexAny`). -/
def LexCellAt (F : S0xFac 9 s0x_S24 x) (U Dn : Finset (Fin 9)) (b d1 d2 : ℝ³) : Prop :=
  (∀ t ∈ U, LexPos3 ⟪F.N t, b⟫ ⟪F.N t, d1⟫ ⟪F.N t, d2⟫) ∧
  (∀ t ∈ Dn, LexPos3 (-⟪F.N t, b⟫) (-⟪F.N t, d1⟫) (-⟪F.N t, d2⟫))

/-! ## The rims: cycles and cells (engine cells, gated) -/

/-- Rim `0.2.6.4`, cell up `{2,3,6,7,8}` (025, 0345, 235, 236, 346), down `{0,1,4,5}`. -/
def c1 : ZMod 4 → Fin 7 := ![0, 2, 6, 4]
def U1 : Finset (Fin 9) := {2, 3, 6, 7, 8}
def D1 : Finset (Fin 9) := {0, 1, 4, 5}
/-- Rim `0.4.6.2.5`, cell up `{3,6,7,8}`, down `{0,1,2,4,5}`. -/
def c2 : ZMod 5 → Fin 7 := ![0, 4, 6, 2, 5]
def U2 : Finset (Fin 9) := {3, 6, 7, 8}
def D2 : Finset (Fin 9) := {0, 1, 2, 4, 5}
/-- Rim `0.2.3.6.4`, cell up `{2,3,6,8}`, down `{0,1,4,5,7}`. -/
def c3 : ZMod 5 → Fin 7 := ![0, 2, 3, 6, 4]
def U3 : Finset (Fin 9) := {2, 3, 6, 8}
def D3 : Finset (Fin 9) := {0, 1, 4, 5, 7}
/-- Rim `0.5.2.3.6`, cell up `{3,4,6,8}`, down `{0,1,2,5,7}`. -/
def c4 : ZMod 5 → Fin 7 := ![0, 5, 2, 3, 6]
def U4 : Finset (Fin 9) := {3, 4, 6, 8}
def D4 : Finset (Fin 9) := {0, 1, 2, 5, 7}
/-- Rim `0.2.3.4`, cell up `{2,3,6}`, down `{0,1,4,5,7,8}`. -/
def c5 : ZMod 4 → Fin 7 := ![0, 2, 3, 4]
def U5 : Finset (Fin 9) := {2, 3, 6}
def D5 : Finset (Fin 9) := {0, 1, 4, 5, 7, 8}

theorem cyc1 : S0xCycUD s0x_S24 c1 U1 D1 := by decide
theorem cyc2 : S0xCycUD s0x_S24 c2 U2 D2 := by decide
theorem cyc3 : S0xCycUD s0x_S24 c3 U3 D3 := by decide
theorem cyc4 : S0xCycUD s0x_S24 c4 U4 D4 := by decide
theorem cyc5 : S0xCycUD s0x_S24 c5 U5 D5 := by decide

theorem inj1 : Function.Injective c1 := by decide
theorem inj2 : Function.Injective c2 := by decide
theorem inj3 : Function.Injective c3 := by decide
theorem inj4 : Function.Injective c4 := by decide
theorem inj5 : Function.Injective c5 := by decide

/-! ## Frame values of the corner coordinates -/

theorem obl_frame (F : S0xFac 9 s0x_S24 x) :
    oblX0 x 0 = 1 ∧ oblX2 x 0 = 0 ∧ oblX6 x 0 = 0 ∧ oblX0 x 2 = 0 ∧ oblX2 x 2 = 1 ∧ oblX6 x 2 = 0 ∧
      oblX0 x 6 = 0 ∧ oblX2 x 6 = 0 ∧ oblX6 x 6 = 1 := by
  have T := Minimality.T24.M4.type24OfFac F
  exact ⟨T.oblX0_zero', Type24.oblX2_zero', Type24.oblX6_zero, Type24.oblX0_two, T.oblX2_two,
    Type24.oblX6_two, Type24.oblX0_six, Type24.oblX2_six, T.oblX6_six⟩

/-! ## (i) The order lemmas (corner coordinates only; `A_v := a_v + b_v`) -/

private lemma zmod5_cases (v : ZMod 5) : v = 0 ∨ v = 1 ∨ v = 2 ∨ v = 3 ∨ v = 4 := by
  fin_cases v
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))

private noncomputable def toLex3 (p : ℝ × ℝ × ℝ) := toLex (p.1, toLex (p.2.1, p.2.2))

private lemma toLex3_lt_first {p q : ℝ × ℝ × ℝ} (h : p.1 < q.1) : toLex3 p < toLex3 q :=
  Prod.Lex.lt_iff.2 (Or.inl h)

private lemma toLex3_lt_second {p q : ℝ × ℝ × ℝ} (h1 : p.1 = q.1) (h2 : p.2.1 < q.2.1) :
    toLex3 p < toLex3 q :=
  Prod.Lex.lt_iff.2 (Or.inr ⟨h1, Prod.Lex.lt_iff.2 (Or.inl h2)⟩)

/-- **EM(i)-R1.**  `R^(c)_+` on `0.2.6.4`: robustly unimodal with NO condition
(`z_6 = 0 <lex z_2 = 1` and `z_2 <lex z_0` at level 1; mixed diagonals `{0,6} × {2,4}`).  Gate: 0 failures. -/
theorem orderR1 (F : S0xFac 9 s0x_S24 x) : RobUniLex (fun i : ZMod 4 => lexRc x 1 (c1 i)) := by
  obtain ⟨a00, b00, c00, a02, b02, c02, a06, b06, c06⟩ := obl_frame F
  have e0 : c1 0 = 0 := rfl
  have e1 : c1 1 = 2 := rfl
  have e2 : c1 2 = 6 := rfl
  refine robUniLex_four_of_mixed ⟨(2, 1), by decide, ?_⟩ ⟨(0, 1), by decide, ?_⟩
  · simp only [e1, e2, lexRc, LexLt3, LexPos3, a02, b02, c02, a06, b06, c06]
    left; norm_num
  · simp only [e0, e1, lexRc, LexLt3, LexPos3, a00, b00, c00, a02, b02, c02]
    right; refine ⟨by norm_num, Or.inl ?_⟩; norm_num

/-- **EM(i)-R2.**  `R^(c)_+` on `0.4.6.2.5`: robustly unimodal when `a_4 + b_4 < 1` and `a_5 + b_5 > 1`
(`6 < 4 < 2 < 0 < 5` at level 0; `1 < a_5 + b_5` is `0 < ω_5` since `c_5 > 0`).  `a_5 + b_5 > 1` is needed (gate: 234 failures
without it, all with `ω_5 < 0`).  The converse is false at the tie `a_4 + b_4 = 1` (23 points in the random gate), so no iff. -/
theorem orderR2 (F : S0xFac 9 s0x_S24 x) (h4 : oblX0 x 4 + oblX2 x 4 < 1) (h5 : 1 < oblX0 x 5 + oblX2 x 5) :
    RobUniLex (fun i : ZMod 5 => lexRc x 1 (c2 i)) := by
  obtain ⟨a00, b00, c00, a02, b02, c02, a06, b06, c06⟩ := obl_frame F
  rw [Minimality.GenRev.robUniLex_iff_O]
  refine Minimality.GenRev.robUniO_of_noAlt {1, 2} {4} ?_ ?_ ?_
  · intro v hv
    rcases zmod5_cases v with rfl | rfl | rfl | rfl | rfl
    · right; apply toLex3_lt_first
      change oblX0 x 4 + oblX2 x 4 < oblX0 x 0 + oblX2 x 0
      linarith
    · exact absurd (by decide) hv
    · exact absurd (by decide) hv
    · left; apply toLex3_lt_first
      change oblX0 x 6 + oblX2 x 6 < oblX0 x 2 + oblX2 x 2
      linarith
    · left; apply toLex3_lt_first
      change oblX0 x 2 + oblX2 x 2 < oblX0 x 5 + oblX2 x 5
      linarith
  · intro v hv
    rcases zmod5_cases v with rfl | rfl | rfl | rfl | rfl
    · left; apply toLex3_lt_first
      change oblX0 x 0 + oblX2 x 0 < oblX0 x 5 + oblX2 x 5
      linarith
    · left; apply toLex3_lt_first
      change oblX0 x 4 + oblX2 x 4 < oblX0 x 0 + oblX2 x 0
      linarith
    · right; apply toLex3_lt_first
      change oblX0 x 6 + oblX2 x 6 < oblX0 x 2 + oblX2 x 2
      linarith
    · right; apply toLex3_lt_first
      change oblX0 x 2 + oblX2 x 2 < oblX0 x 5 + oblX2 x 5
      linarith
    · exact absurd (by decide) hv
  · intro B b c d hb hbc hcd hdk ⟨hB, _, hBc, _⟩
    simp only [mem_singleton] at hB hBc
    have hc5 : (c : ZMod 5) = 0 := by rw [← add_left_cancel_iff (a := B), hBc, add_zero]; exact hB.symm
    have : c = 0 := by
      rcases (by omega : c = 1 ∨ c = 2 ∨ c = 3 ∨ c = 4) with rfl | rfl | rfl | rfl <;>
        exact absurd hc5 (by decide)
    omega

/-- **EM(i)-R3.**  `R^(c)_-` on `0.2.3.6.4`: robustly unimodal when `a_4 + b_4 < 1` (no condition on `a_5 + b_5`; gate: 0 failures
without it).  Order at level 0: `6 < 4 < {0, 2} < 3`-side (vertex `3` unconstrained: the cycle is `0 2 3 6 4`). -/
theorem orderR3 (F : S0xFac 9 s0x_S24 x) (h4 : oblX0 x 4 + oblX2 x 4 < 1) :
    RobUniLex (fun i : ZMod 5 => lexRc x (-1) (c3 i)) := by
  have T := Minimality.T24.M4.type24OfFac F
  have a3 := T.X0_pos (v := 3) (by decide)
  have b3 := T.X2_pos (v := 3) (by decide)
  have a4 := T.X0_pos (v := 4) (by decide)
  have b4 := T.X2_pos (v := 4) (by decide)
  obtain ⟨a00, b00, c00, a02, b02, c02, a06, b06, c06⟩ := obl_frame F
  rw [Minimality.GenRev.robUniLex_iff_O]
  refine Minimality.GenRev.robUniO_of_noAlt {3} univ ?_ ?_ ?_
  · intro v hv
    rcases zmod5_cases v with rfl | rfl | rfl | rfl | rfl
    · left; apply toLex3_lt_first
      change oblX0 x 4 + oblX2 x 4 < oblX0 x 0 + oblX2 x 0
      linarith
    · left; apply toLex3_lt_second
      · change oblX0 x 0 + oblX2 x 0 = oblX0 x 2 + oblX2 x 2; linarith
      · change -1 * (oblX0 x 0 - oblX2 x 0) < -1 * (oblX0 x 2 - oblX2 x 2); linarith
    · right; apply toLex3_lt_first
      change oblX0 x 6 + oblX2 x 6 < oblX0 x 3 + oblX2 x 3
      linarith
    · exact absurd (by decide) hv
    · left; apply toLex3_lt_first
      change oblX0 x 6 + oblX2 x 6 < oblX0 x 4 + oblX2 x 4
      linarith
  · intro v hv; exact absurd (mem_univ v) hv
  · intro B b c d hb hbc hcd hdk ⟨_, hBb, _, hBd⟩
    simp only [mem_singleton] at hBb hBd
    have hbd5 : ((d - b : ℕ) : ZMod 5) = 0 := by
      have : (d : ZMod 5) = (b : ZMod 5) := by
        rw [← add_left_cancel_iff (a := B), hBb, hBd]
      rw [Nat.cast_sub (by omega), this, sub_self]
    rcases (by omega : d - b = 1 ∨ d - b = 2 ∨ d - b = 3) with h | h | h <;>
      rw [h] at hbd5 <;> exact absurd hbd5 (by decide)

/-- **EM(i)-R4 (sufficient direction, both signs).**  On `0.5.2.3.6`, with `1 < a_5 + b_5` and
`a_3 + b_3 < 1`, `R^(c)_s` (for any `s : ℝ`) is robustly unimodal. -/
theorem orderR4_of_lt (F : S0xFac 9 s0x_S24 x) (s : ℝ)
    (h3 : oblX0 x 3 + oblX2 x 3 < 1) (h5 : 1 < oblX0 x 5 + oblX2 x 5) :
    RobUniLex (fun i : ZMod 5 => lexRc x s (c4 i)) := by
  have T := Minimality.T24.M4.type24OfFac F
  have a3 := T.X0_pos (v := 3) (by decide)
  have b3 := T.X2_pos (v := 3) (by decide)
  obtain ⟨a00, b00, c00, a02, b02, c02, a06, b06, c06⟩ := obl_frame F
  rw [Minimality.GenRev.robUniLex_iff_O]
  refine Minimality.GenRev.robUniO_of_noAlt {4} {1} ?_ ?_ ?_
  · intro v hv
    rcases zmod5_cases v with rfl | rfl | rfl | rfl | rfl
    · left; apply toLex3_lt_first; change oblX0 x 6 + oblX2 x 6 < oblX0 x 0 + oblX2 x 0; linarith
    · left; apply toLex3_lt_first; change oblX0 x 0 + oblX2 x 0 < oblX0 x 5 + oblX2 x 5; linarith
    · right; apply toLex3_lt_first; change oblX0 x 3 + oblX2 x 3 < oblX0 x 2 + oblX2 x 2; linarith
    · right; apply toLex3_lt_first; change oblX0 x 6 + oblX2 x 6 < oblX0 x 3 + oblX2 x 3; linarith
    · exact absurd (by decide) hv
  · intro v hv
    rcases zmod5_cases v with rfl | rfl | rfl | rfl | rfl
    · right; apply toLex3_lt_first; change oblX0 x 0 + oblX2 x 0 < oblX0 x 5 + oblX2 x 5; linarith
    · exact absurd (by decide) hv
    · left; apply toLex3_lt_first; change oblX0 x 2 + oblX2 x 2 < oblX0 x 5 + oblX2 x 5; linarith
    · left; apply toLex3_lt_first; change oblX0 x 3 + oblX2 x 3 < oblX0 x 2 + oblX2 x 2; linarith
    · right; apply toLex3_lt_first; change oblX0 x 6 + oblX2 x 6 < oblX0 x 0 + oblX2 x 0; linarith
  · intro B b c d hb hbc hcd hdk ⟨_, hBb, _, hBd⟩
    simp only [mem_singleton] at hBb hBd
    have hbd5 : ((d - b : ℕ) : ZMod 5) = 0 := by
      have : (d : ZMod 5) = (b : ZMod 5) := by rw [← add_left_cancel_iff (a := B), hBb, hBd]
      rw [Nat.cast_sub (by omega), this, sub_self]
    rcases (by omega : d - b = 1 ∨ d - b = 2 ∨ d - b = 3) with h | h | h <;>
      rw [h] at hbd5 <;> exact absurd hbd5 (by decide)

/-- **EM(i)-R4 (`s = 1`, iff).**  On `0.5.2.3.6` with `1 < a_5 + b_5`, `R^(c)_+` is robustly
unimodal iff `a_3 + b_3 < 1`. -/
theorem orderR4_pos_iff (F : S0xFac 9 s0x_S24 x) (h5 : 1 < oblX0 x 5 + oblX2 x 5) :
    RobUniLex (fun i : ZMod 5 => lexRc x 1 (c4 i)) ↔ oblX0 x 3 + oblX2 x 3 < 1 := by
  constructor
  · intro h
    by_contra hnot
    push Not at hnot
    have T := Minimality.T24.M4.type24OfFac F
    have a3 := T.X0_pos (v := 3) (by decide)
    have b3 := T.X2_pos (v := 3) (by decide)
    obtain ⟨a00, b00, c00, a02, b02, c02, a06, b06, c06⟩ := obl_frame F
    rw [Minimality.GenRev.robUniLex_iff_O] at h
    refine h 1 1 2 3 (by decide) (by decide) (by decide) (by decide) ⟨?_, ?_, ?_, ?_⟩
    · exact le_of_lt (toLex3_lt_first (by change oblX0 x 2 + oblX2 x 2 < oblX0 x 5 + oblX2 x 5; linarith))
    · rcases lt_or_eq_of_le hnot with hgt | heq
      · exact le_of_lt (toLex3_lt_first (by change oblX0 x 2 + oblX2 x 2 < oblX0 x 3 + oblX2 x 3; linarith))
      · exact le_of_lt (toLex3_lt_second
          (by change oblX0 x 2 + oblX2 x 2 = oblX0 x 3 + oblX2 x 3; linarith)
          (by change 1 * (oblX0 x 2 - oblX2 x 2) < 1 * (oblX0 x 3 - oblX2 x 3); linarith))
    · exact le_of_lt (toLex3_lt_first (by change oblX0 x 6 + oblX2 x 6 < oblX0 x 5 + oblX2 x 5; linarith))
    · exact le_of_lt (toLex3_lt_first (by change oblX0 x 6 + oblX2 x 6 < oblX0 x 3 + oblX2 x 3; linarith))
  · exact fun h3 => orderR4_of_lt F 1 h3 h5

/-- **EM(i)-R4 (`s = -1`, iff).**  On `0.5.2.3.6` with `1 < a_5 + b_5`, `R^(c)_-` is robustly
unimodal iff `a_3 + b_3 ≤ 1` (at `a_3 + b_3 = 1`, `z 6 < z 0 < z 3 < z 2 < z 5` is strictly unimodal). -/
theorem orderR4_neg_iff (F : S0xFac 9 s0x_S24 x) (h5 : 1 < oblX0 x 5 + oblX2 x 5) :
    RobUniLex (fun i : ZMod 5 => lexRc x (-1) (c4 i)) ↔ oblX0 x 3 + oblX2 x 3 ≤ 1 := by
  constructor
  · intro h
    by_contra hnot
    push Not at hnot
    obtain ⟨a00, b00, c00, a02, b02, c02, a06, b06, c06⟩ := obl_frame F
    rw [Minimality.GenRev.robUniLex_iff_O] at h
    refine h 1 1 2 3 (by decide) (by decide) (by decide) (by decide) ⟨?_, ?_, ?_, ?_⟩
    · exact le_of_lt (toLex3_lt_first (by change oblX0 x 2 + oblX2 x 2 < oblX0 x 5 + oblX2 x 5; linarith))
    · exact le_of_lt (toLex3_lt_first (by change oblX0 x 2 + oblX2 x 2 < oblX0 x 3 + oblX2 x 3; linarith))
    · exact le_of_lt (toLex3_lt_first (by change oblX0 x 6 + oblX2 x 6 < oblX0 x 5 + oblX2 x 5; linarith))
    · exact le_of_lt (toLex3_lt_first (by change oblX0 x 6 + oblX2 x 6 < oblX0 x 3 + oblX2 x 3; linarith))
  · intro h3
    rcases lt_or_eq_of_le h3 with hlt | heq
    · exact orderR4_of_lt F (-1) hlt h5
    · have T := Minimality.T24.M4.type24OfFac F
      have a3 := T.X0_pos (v := 3) (by decide)
      have b3 := T.X2_pos (v := 3) (by decide)
      obtain ⟨a00, b00, c00, a02, b02, c02, a06, b06, c06⟩ := obl_frame F
      rw [Minimality.GenRev.robUniLex_iff_O]
      refine Minimality.GenRev.robUniO_of_noAlt {4} {1} ?_ ?_ ?_
      · intro v hv
        rcases zmod5_cases v with rfl | rfl | rfl | rfl | rfl
        · left; apply toLex3_lt_first; change oblX0 x 6 + oblX2 x 6 < oblX0 x 0 + oblX2 x 0; linarith
        · left; apply toLex3_lt_first; change oblX0 x 0 + oblX2 x 0 < oblX0 x 5 + oblX2 x 5; linarith
        · right; apply toLex3_lt_second
          · change oblX0 x 3 + oblX2 x 3 = oblX0 x 2 + oblX2 x 2; linarith
          · change -1 * (oblX0 x 3 - oblX2 x 3) < -1 * (oblX0 x 2 - oblX2 x 2); linarith
        · right; apply toLex3_lt_first; change oblX0 x 6 + oblX2 x 6 < oblX0 x 3 + oblX2 x 3; linarith
        · exact absurd (by decide) hv
      · intro v hv
        rcases zmod5_cases v with rfl | rfl | rfl | rfl | rfl
        · right; apply toLex3_lt_first; change oblX0 x 0 + oblX2 x 0 < oblX0 x 5 + oblX2 x 5; linarith
        · exact absurd (by decide) hv
        · left; apply toLex3_lt_first; change oblX0 x 2 + oblX2 x 2 < oblX0 x 5 + oblX2 x 5; linarith
        · left; apply toLex3_lt_second
          · change oblX0 x 3 + oblX2 x 3 = oblX0 x 2 + oblX2 x 2; linarith
          · change -1 * (oblX0 x 3 - oblX2 x 3) < -1 * (oblX0 x 2 - oblX2 x 2); linarith
        · right; apply toLex3_lt_first; change oblX0 x 6 + oblX2 x 6 < oblX0 x 0 + oblX2 x 0; linarith
      · intro B b c d hb hbc hcd hdk ⟨_, hBb, _, hBd⟩
        simp only [mem_singleton] at hBb hBd
        have hbd5 : ((d - b : ℕ) : ZMod 5) = 0 := by
          have : (d : ZMod 5) = (b : ZMod 5) := by rw [← add_left_cancel_iff (a := B), hBb, hBd]
          rw [Nat.cast_sub (by omega), this, sub_self]
        rcases (by omega : d - b = 1 ∨ d - b = 2 ∨ d - b = 3) with h | h | h <;>
          rw [h] at hbd5 <;> exact absurd hbd5 (by decide)

/-- **EM(i)-R5-.**  `R^(c)_-` on `0.2.3.4`: robustly unimodal if `a_4 + b_4 < 1` or `a_3 + b_3 > 1` (strict; the nonstrict
`≤ 1`, `≥ 1` version of Carbon is FALSE at ties: 23 points of the random gate with `a_4 + b_4 = 1`). -/
theorem orderR5m (F : S0xFac 9 s0x_S24 x) (h : oblX0 x 4 + oblX2 x 4 < 1 ∨ 1 < oblX0 x 3 + oblX2 x 3) :
    RobUniLex (fun i : ZMod 4 => lexRc x (-1) (c5 i)) := by
  obtain ⟨a00, b00, c00, a02, b02, c02, a06, b06, c06⟩ := obl_frame F
  have e0 : c5 0 = 0 := rfl
  have e1 : c5 1 = 2 := rfl
  have e2 : c5 2 = 3 := rfl
  have e3 : c5 3 = 4 := rfl
  have hp : ∃ p ∈ diagPairs, LexLt3 (lexRc x (-1) (c5 p.1)) (lexRc x (-1) (c5 p.2)) := by
    refine ⟨(0, 1), by decide, ?_⟩
    simp only [e0, e1, lexRc, LexLt3, LexPos3, a00, b00, c00, a02, b02, c02]
    right; refine ⟨by norm_num, Or.inl ?_⟩; norm_num
  rcases h with h | h
  · refine robUniLex_four_of_mixed hp ⟨(0, 3), by decide, ?_⟩
    simp only [e0, e3, lexRc, LexLt3, LexPos3, a00, b00, c00]
    left; linarith
  · refine robUniLex_four_of_mixed hp ⟨(2, 1), by decide, ?_⟩
    simp only [e1, e2, lexRc, LexLt3, LexPos3, a02, b02, c02]
    left; linarith

/-- **EM(i)-R5+.**  `R^(c)_+` on `0.2.3.4`: robustly unimodal if `a_3 + b_3 < 1` or `a_4 + b_4 > 1` (strict).  Together with
`orderR5m`: at least one sign is unimodal unless `a_3 + b_3 = a_4 + b_4 = 1`. -/
theorem orderR5p (F : S0xFac 9 s0x_S24 x) (h : oblX0 x 3 + oblX2 x 3 < 1 ∨ 1 < oblX0 x 4 + oblX2 x 4) :
    RobUniLex (fun i : ZMod 4 => lexRc x 1 (c5 i)) := by
  obtain ⟨a00, b00, c00, a02, b02, c02, a06, b06, c06⟩ := obl_frame F
  have e0 : c5 0 = 0 := rfl
  have e1 : c5 1 = 2 := rfl
  have e2 : c5 2 = 3 := rfl
  have e3 : c5 3 = 4 := rfl
  have hq : ∃ q ∈ diagPairs, LexLt3 (lexRc x 1 (c5 q.2)) (lexRc x 1 (c5 q.1)) := by
    refine ⟨(0, 1), by decide, ?_⟩
    simp only [e0, e1, lexRc, LexLt3, LexPos3, a00, b00, c00, a02, b02, c02]
    right; refine ⟨by norm_num, Or.inl ?_⟩; norm_num
  rcases h with h | h
  · refine robUniLex_four_of_mixed ⟨(2, 1), by decide, ?_⟩ hq
    simp only [e1, e2, lexRc, LexLt3, LexPos3, a02, b02, c02]
    left; linarith
  · refine robUniLex_four_of_mixed ⟨(0, 3), by decide, ?_⟩ hq
    simp only [e0, e3, lexRc, LexLt3, LexPos3, a00, b00, c00]
    left; linarith

/-- `a_5 + b_5 > 1` from `ω_5 > 0` and `c_5 > 0`. -/
theorem one_lt_A5 (hc : 0 < oblX6 x 5) (hω : 0 < omega5 x) : 1 < oblX0 x 5 + oblX2 x 5 := by
  unfold omega5 at hω
  have := (div_pos_iff_of_pos_right hc).1 hω
  linarith

/-! ## (ii) The leaves -/

/-- The metric-free order at `lexRc s` gives `RobUniLex` of the actual lex-view triples (`robUniLex_metric_free`), hence `LexAny`. -/
theorem lexAny_of_Rc (F : S0xFac 9 s0x_S24 x) {k : ℕ} [NeZero k] (hk : 4 ≤ k) (c : ZMod k → Fin 7)
    (hc : Function.Injective c) {U Dn : Finset (Fin 9)} (hcyc : S0xCycUD s0x_S24 c U Dn) (s : ℝ)
    {b d1 d2 : ℝ³} (hv : IsRcView x s b d1 d2) (hcell : LexCellAt F U Dn b d1 d2)
    (hR : RobUniLex (fun i : ZMod k => lexRc x s (c i))) : Gen.LexAny F := by
  obtain ⟨hb, h1, h2⟩ := hv
  refine ⟨k, inferInstance, c, U, Dn, b, d1, d2, hk, hc, hcyc, hcell.1, hcell.2, ?_⟩
  rw [Minimality.GenRev.robUniLex_metric_free F c b d1 d2 ![1, 1, 0] ![s, -s, 0] ![0, 0, 1]
    (by simpa using hb) (by simpa using h1) (by simpa using h2)]
  have e : (fun i : ZMod k => (oblX0 x (c i) * (![1, 1, 0] : Fin 3 → ℝ) 0 + oblX2 x (c i) * (![1, 1, 0] : Fin 3 → ℝ) 1 +
        oblX6 x (c i) * (![1, 1, 0] : Fin 3 → ℝ) 2,
      oblX0 x (c i) * (![s, -s, 0] : Fin 3 → ℝ) 0 + oblX2 x (c i) * (![s, -s, 0] : Fin 3 → ℝ) 1 +
        oblX6 x (c i) * (![s, -s, 0] : Fin 3 → ℝ) 2,
      oblX0 x (c i) * (![0, 0, 1] : Fin 3 → ℝ) 0 + oblX2 x (c i) * (![0, 0, 1] : Fin 3 → ℝ) 1 +
        oblX6 x (c i) * (![0, 0, 1] : Fin 3 → ℝ) 2)) = fun i => lexRc x s (c i) := by
    funext i
    simp only [lexRc, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    ext <;> (simp; try ring)
  rw [e]; exact hR

/-- **EM(ii)-R1.**  If the lex view `R^(c)_+` lies in the cell of rim `0.2.6.4` then `LexAny F` (no further condition). -/
theorem lexAny_R1 (F : S0xFac 9 s0x_S24 x) {b d1 d2 : ℝ³} (hv : IsRcView x 1 b d1 d2)
    (hcell : LexCellAt F U1 D1 b d1 d2) : Gen.LexAny F :=
  lexAny_of_Rc F (by norm_num) c1 inj1 cyc1 1 hv hcell (orderR1 F)

/-- **EM(ii)-R2.**  `R^(c)_+` in the cell of rim `0.4.6.2.5`, `a_4 + b_4 < 1`, `ω_5 > 0`: `LexAny F`. -/
theorem lexAny_R2 (F : S0xFac 9 s0x_S24 x) (h4 : oblX0 x 4 + oblX2 x 4 < 1) (h5 : 1 < oblX0 x 5 + oblX2 x 5)
    {b d1 d2 : ℝ³} (hv : IsRcView x 1 b d1 d2) (hcell : LexCellAt F U2 D2 b d1 d2) : Gen.LexAny F :=
  lexAny_of_Rc F (by norm_num) c2 inj2 cyc2 1 hv hcell (orderR2 F h4 h5)

/-- **EM(ii)-R3.**  `R^(c)_-` in the cell of rim `0.2.3.6.4`, `a_4 + b_4 < 1`: `LexAny F`. -/
theorem lexAny_R3 (F : S0xFac 9 s0x_S24 x) (h4 : oblX0 x 4 + oblX2 x 4 < 1)
    {b d1 d2 : ℝ³} (hv : IsRcView x (-1) b d1 d2) (hcell : LexCellAt F U3 D3 b d1 d2) : Gen.LexAny F :=
  lexAny_of_Rc F (by norm_num) c3 inj3 cyc3 (-1) hv hcell (orderR3 F h4)

/-- **EM(ii)-R4+.**  `R^(c)_+` in the cell of rim `0.5.2.3.6`, `a_3 + b_3 < 1`, `ω_5 > 0`: `LexAny F`. -/
theorem lexAny_R4p (F : S0xFac 9 s0x_S24 x) (h3 : oblX0 x 3 + oblX2 x 3 < 1) (h5 : 1 < oblX0 x 5 + oblX2 x 5)
    {b d1 d2 : ℝ³} (hv : IsRcView x 1 b d1 d2) (hcell : LexCellAt F U4 D4 b d1 d2) : Gen.LexAny F :=
  lexAny_of_Rc F (by norm_num) c4 inj4 cyc4 1 hv hcell (orderR4_of_lt F 1 h3 h5)

/-- **EM(ii)-R4-.**  `R^(c)_-` in the cell of rim `0.5.2.3.6`, `a_3 + b_3 < 1`, `ω_5 > 0`: `LexAny F`. -/
theorem lexAny_R4m (F : S0xFac 9 s0x_S24 x) (h3 : oblX0 x 3 + oblX2 x 3 < 1) (h5 : 1 < oblX0 x 5 + oblX2 x 5)
    {b d1 d2 : ℝ³} (hv : IsRcView x (-1) b d1 d2) (hcell : LexCellAt F U4 D4 b d1 d2) : Gen.LexAny F :=
  lexAny_of_Rc F (by norm_num) c4 inj4 cyc4 (-1) hv hcell (orderR4_of_lt F (-1) h3 h5)

/-- **EM(ii)-R5-.**  `R^(c)_-` in the cell of rim `0.2.3.4`, `a_4 + b_4 < 1` or `a_3 + b_3 > 1`: `LexAny F`. -/
theorem lexAny_R5m (F : S0xFac 9 s0x_S24 x) (h : oblX0 x 4 + oblX2 x 4 < 1 ∨ 1 < oblX0 x 3 + oblX2 x 3)
    {b d1 d2 : ℝ³} (hv : IsRcView x (-1) b d1 d2) (hcell : LexCellAt F U5 D5 b d1 d2) : Gen.LexAny F :=
  lexAny_of_Rc F (by norm_num) c5 inj5 cyc5 (-1) hv hcell (orderR5m F h)

/-- **EM(ii)-R5+.**  `R^(c)_+` in the cell of rim `0.2.3.4`, `a_3 + b_3 < 1` or `a_4 + b_4 > 1`: `LexAny F`. -/
theorem lexAny_R5p (F : S0xFac 9 s0x_S24 x) (h : oblX0 x 3 + oblX2 x 3 < 1 ∨ 1 < oblX0 x 4 + oblX2 x 4)
    {b d1 d2 : ℝ³} (hv : IsRcView x 1 b d1 d2) (hcell : LexCellAt F U5 D5 b d1 d2) : Gen.LexAny F :=
  lexAny_of_Rc F (by norm_num) c5 inj5 cyc5 1 hv hcell (orderR5p F h)

/-- Every leaf above yields `IsRupert` (`lexAny_isRupert`). -/
theorem isRupert_of_lexAny (F : S0xFac 9 s0x_S24 x) (h : Gen.LexAny F) : IsRupert (univ.image x) :=
  Gen.lexAny_isRupert F (Minimality.H24.SAT.inj_of_fac F) h

end Minimality.T24.EM
