module

public import Minimality.Type24HiddenCone
public import Minimality.RimCellClosed
public import Minimality.RDispatch24
public import Minimality.Type24SAT.Geo.Top
public import Minimality.SplitLeaf
public import Minimality.SplitRows

/-!
# EQ spec: the edge view `u_32 = x 3 - x 2` of the type-24 hidden-cap cover

STATEMENTS for an external prover (Hydrogen).  Gate: `gate.cc`, `GATE.md` (same directory).
Source: Carbon `A66 to Q66` Q66.2(d), `A67 to Q67` Q67.1 (Gate Handover) and Q67.3 (u_32 criterion); referee
`nopert229/tools/genleaves/FACENORM24.md` sections A66 TESTS claim 2(d), A67 TESTS claims 2 and 4.

Corner frame at vertex `1`: `e_a = x 0 - x 1`, `e_b = x 2 - x 1`, `e_c = x 6 - x 1`; `X_v = (a_v, b_v, c_v)` are the oblique
coordinates (`oblX0 x v`, `oblX2 x v`, `oblX6 x v`).  `u_32 = x 3 - x 2 = (a_3, b_3 - 1, c_3)` in corner coordinates.
For a facet `t`, `N_{t,a} = ⟪F.N t, x 0 - x 1⟫`, `N_{t,b} = ⟪F.N t, x 2 - x 1⟫`, `N_{t,c} = ⟪F.N t, x 6 - x 1⟫` (positive
multiples of Carbon's `N_{t,*}`).  Lean facet order `0:012 1:016 2:025 3:0345 4:046 5:126 6:235 7:236 8:346`.

Contents (no `sorry`: Hydrogen Task EQ proved `n6_handover` and `u32_splitRows`):
* (S-a) nine facet signs at `u_32` for `b_3 < 1`: `(- + - + + - 0 0 +)`, facets `6 = 235`, `7 = 236` contain the edge `x 2 x 3`
  (edge-on).  All proved from the facet data (`u32_n6`, `u32_n7`, `u32_free`, `u32_n1`, `u32_n4` via `fac_eval`).
* The four cells next to `u_32` (signs of `235`, `236` after a tilt): rims `0.1.6.3.5` (6-, 7-), `0.1.6.2.5` (6+, 7+),
  `0.1.6.3.2.5` (6+, 7-), `0.1.6.2.3.5` (6-, 7+); cycle facts `decide`d; `CellLe` at `u_32`, Lex facings and `CellAt` (tilt) proved.
* (S-b) Gate Handover: `n6b_pos` proved (`N_{6,b} > 0` is facet data), `n6_handover` (both conjuncts proved).
* (S-c) `u32_splitRows` (proved): rows of `SplitRows` (rim `0.1.6.3.5`, edge `[3,5]`, corner `6`) at `u_32` from `N_{6,c} < 0` and the depth
  condition; the Split leaf `isRupert_u32_split` is proved from it (`split_tope_rupert`).  General form without any shape hypothesis:
  `SplitAny5` (rows for some edge/corner/orientation on a 5-rim at `u_32`) with proved leaves `isRupert_u32_splitAny_mm/pp`.
* (S-d) Lex leaves `isRupert_u32_lex_mm`, `isRupert_u32_lex_pp` (`isRupert_of_closedCell` with `u₀ = u_32`), combined leaves
  `isRupert_u32` (RobUni or Carbon's Split, `¬ FacetCellF` not needed) and `isRupert_u32_any` (RobUni or any rows at `u_32` on the 5-rims: equals the engine verdict, GATE.md).
-/

@[expose] public section

set_option autoImplicit false
open scoped RealInnerProductSpace
open Finset

namespace Minimality.T24.EQ

open Minimality Minimality.H21 Minimality.T24.SAT Minimality.RimCell Minimality.T24.HC

variable {x : Fin 7 → ℝ³}

/-! ## The four cells next to `u_32` -/

/-- (6-, 7-): up `016, 0345, 046, 346`, down `012, 025, 126, 235, 236`; rim `0.1.6.3.5`. -/
def UMM : Finset (Fin 9) := {1, 3, 4, 8}
def DnMM : Finset (Fin 9) := {0, 2, 5, 6, 7}
def cMM : ZMod 5 → Fin 7 := ![0, 1, 6, 3, 5]
/-- (6+, 7+): up `016, 0345, 046, 235, 236, 346`, down `012, 025, 126`; rim `0.1.6.2.5`. -/
def UPP : Finset (Fin 9) := {1, 3, 4, 6, 7, 8}
def DnPP : Finset (Fin 9) := {0, 2, 5}
def cPP : ZMod 5 → Fin 7 := ![0, 1, 6, 2, 5]
/-- (6+, 7-): up `016, 0345, 046, 235, 346`, down `012, 025, 126, 236`; rim `0.1.6.3.2.5`. -/
def UPM : Finset (Fin 9) := {1, 3, 4, 6, 8}
def DnPM : Finset (Fin 9) := {0, 2, 5, 7}
def cPM : ZMod 6 → Fin 7 := ![0, 1, 6, 3, 2, 5]
/-- (6-, 7+): up `016, 0345, 046, 236, 346`, down `012, 025, 126, 235`; rim `0.1.6.2.3.5`. -/
def UMP : Finset (Fin 9) := {1, 3, 4, 7, 8}
def DnMP : Finset (Fin 9) := {0, 2, 5, 6}
def cMP : ZMod 6 → Fin 7 := ![0, 1, 6, 2, 3, 5]

theorem cycMM : S0xCycUD s0x_S24 cMM UMM DnMM := by decide
theorem cycPP : S0xCycUD s0x_S24 cPP UPP DnPP := by decide
theorem cycPM : S0xCycUD s0x_S24 cPM UPM DnPM := by decide
theorem cycMP : S0xCycUD s0x_S24 cMP UMP DnMP := by decide

theorem injMM : Function.Injective cMM := by
  intro i j h; fin_cases i <;> fin_cases j <;> first | rfl | exact absurd h (by decide)
theorem injPP : Function.Injective cPP := by
  intro i j h; fin_cases i <;> fin_cases j <;> first | rfl | exact absurd h (by decide)

/-! ## (S-a) The nine facet values at `u_32` -/

/-- Facets `235`, `236` contain the edge `x 2 x 3`: edge-on at `u_32`. -/
theorem u32_n6 (F : S0xFac 9 s0x_S24 x) : ⟪F.N 6, x 3 - x 2⟫ = 0 := by
  rw [F.inner_sub, F.zero 6 3 (by decide), F.zero 6 2 (by decide)]; simp

theorem u32_n7 (F : S0xFac 9 s0x_S24 x) : ⟪F.N 7, x 3 - x 2⟫ = 0 := by
  rw [F.inner_sub, F.zero 7 3 (by decide), F.zero 7 2 (by decide)]; simp

/-- Facets `012, 025, 126` strictly back, `0345, 346` strictly front at `u_32` (pure facet data: no shape hypothesis). -/
theorem u32_free (F : S0xFac 9 s0x_S24 x) :
    ⟪F.N 0, x 3 - x 2⟫ < 0 ∧ ⟪F.N 2, x 3 - x 2⟫ < 0 ∧ ⟪F.N 5, x 3 - x 2⟫ < 0 ∧
      0 < ⟪F.N 3, x 3 - x 2⟫ ∧ 0 < ⟪F.N 8, x 3 - x 2⟫ := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [F.inner_sub, F.zero 0 2 (by decide)]; linarith [F.neg 0 3 (by decide)]
  · rw [F.inner_sub, F.zero 2 2 (by decide)]; linarith [F.neg 2 3 (by decide)]
  · rw [F.inner_sub, F.zero 5 2 (by decide)]; linarith [F.neg 5 3 (by decide)]
  · rw [F.inner_sub, F.zero 3 3 (by decide)]; linarith [F.neg 3 2 (by decide)]
  · rw [F.inner_sub, F.zero 8 3 (by decide)]; linarith [F.neg 8 2 (by decide)]

/-- **EQ(a), facet `016`.**  `N_1 . u_32 = (1 - b_3) * (-f_1(x 2)) > 0` exactly for `b_3 < 1`. -/
theorem u32_n1 (F : S0xFac 9 s0x_S24 x) (hb3 : oblX2 x 3 < 1) : 0 < ⟪F.N 1, x 3 - x 2⟫ := by
  have ev := Minimality.T24.M4.fac_eval F 1 3
  rw [F.zero 1 0 (by decide), F.zero 1 1 (by decide), F.zero 1 6 (by decide)] at ev
  have f2 : F.f 1 (x 2) < 0 := F.neg 1 2 (by decide)
  rw [F.inner_sub, ev]
  nlinarith [mul_pos_of_neg_of_neg (sub_neg.2 hb3) f2]

/-- **EQ(a), facet `046`.**  `N_4 . u_32 = k_4 (a_3 + c_3 + ω4 (1 - b_3)) > 0` for `ω4 > 0`, `b_3 < 1` (`k_4 > 0`). -/
theorem u32_n4 (F : S0xFac 9 s0x_S24 x) (h4 : 0 < omega4 x) (hb3 : oblX2 x 3 < 1) : 0 < ⟪F.N 4, x 3 - x 2⟫ := by
  have T := Minimality.T24.M4.type24OfFac F
  have b4 : 0 < oblX2 x 4 := T.X2_pos (by decide)
  have a3p : 0 < oblX0 x 3 := T.X0_pos (by decide)
  have c3p : 0 < oblX6 x 3 := T.X6_pos (by decide)
  have e3 := Minimality.T24.M4.fac_eval F 4 3
  have e4 := Minimality.T24.M4.fac_eval F 4 4
  rw [F.zero 4 0 (by decide), F.zero 4 6 (by decide)] at e3 e4
  rw [F.zero 4 4 (by decide)] at e4
  have hk : F.f 4 (x 1) < 0 := F.neg 4 1 (by decide)
  have hw : omega4 x * oblX2 x 4 = oblX0 x 4 + oblX6 x 4 - 1 := by
    unfold omega4; field_simp
  have h2 : F.f 4 (x 2) - F.f 4 (x 1) = F.f 4 (x 1) * omega4 x := by
    apply mul_left_cancel₀ b4.ne'
    nlinarith
  have hω : 0 < omega4 x := h4
  rw [F.inner_sub, e3]
  nlinarith [mul_pos hω (sub_pos.2 hb3), mul_neg_of_neg_of_pos hk hω]

/-! ### Closed cells and cell points (proved from (S-a)) -/

theorem u32_cellLe_MM (F : S0xFac 9 s0x_S24 x) (hC : CbarIn x) (hb3 : oblX2 x 3 < 1) :
    CellLe F UMM DnMM (x 3 - x 2) := by
  obtain ⟨s0, s2, s5, s3, s8⟩ := u32_free F
  have s1 := u32_n1 F hb3
  have s4 := u32_n4 F hC.2.1 hb3
  have e6 := u32_n6 F
  have e7 := u32_n7 F
  constructor
  · intro t ht
    simp only [UMM, mem_insert, mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl <;> linarith
  · intro t ht
    simp only [DnMM, mem_insert, mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl <;> linarith

theorem u32_cellLe_PP (F : S0xFac 9 s0x_S24 x) (hC : CbarIn x) (hb3 : oblX2 x 3 < 1) :
    CellLe F UPP DnPP (x 3 - x 2) := by
  obtain ⟨s0, s2, s5, s3, s8⟩ := u32_free F
  have s1 := u32_n1 F hb3
  have s4 := u32_n4 F hC.2.1 hb3
  have e6 := u32_n6 F
  have e7 := u32_n7 F
  constructor
  · intro t ht
    simp only [UPP, mem_insert, mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl <;> linarith
  · intro t ht
    simp only [DnPP, mem_insert, mem_singleton] at ht
    rcases ht with rfl | rfl | rfl <;> linarith

/-- Tilt along the edge-on facets: `⟪N 6, x 2 - x 6⟫ > 0`, `⟪N 7, x 2 - x 6⟫ = 0`;
`⟪N 7, x 2 - x 5⟫ > 0`, `⟪N 6, x 2 - x 5⟫ = 0`. -/
theorem tilt_t7 (F : S0xFac 9 s0x_S24 x) : 0 < ⟪F.N 6, x 2 - x 6⟫ ∧ ⟪F.N 7, x 2 - x 6⟫ = 0 := by
  rw [F.inner_sub, F.inner_sub, F.zero 6 2 (by decide), F.zero 7 2 (by decide), F.zero 7 6 (by decide)]
  refine ⟨?_, by simp⟩
  linarith [F.neg 6 6 (by decide)]

theorem tilt_t6 (F : S0xFac 9 s0x_S24 x) : ⟪F.N 6, x 2 - x 5⟫ = 0 ∧ 0 < ⟪F.N 7, x 2 - x 5⟫ := by
  rw [F.inner_sub, F.inner_sub, F.zero 6 2 (by decide), F.zero 6 5 (by decide), F.zero 7 2 (by decide)]
  refine ⟨by simp, ?_⟩
  linarith [F.neg 7 5 (by decide)]

/-- Lex facings of the cell `(6-, 7-)` at `(u_32, v)`, `v = (x 6 - x 2) + (x 5 - x 2)`. -/
theorem u32_lp_MM (F : S0xFac 9 s0x_S24 x) (hC : CbarIn x) (hb3 : oblX2 x 3 < 1) :
    (∀ t ∈ UMM, h21b_LP ⟪F.N t, x 3 - x 2⟫ ⟪F.N t, (x 6 - x 2) + (x 5 - x 2)⟫) ∧
      ∀ t ∈ DnMM, h21b_LP (-⟪F.N t, x 3 - x 2⟫) (-⟪F.N t, (x 6 - x 2) + (x 5 - x 2)⟫) := by
  obtain ⟨s0, s2, s5, s3, s8⟩ := u32_free F
  have s1 := u32_n1 F hb3
  have s4 := u32_n4 F hC.2.1 hb3
  have e6 := u32_n6 F
  have e7 := u32_n7 F
  obtain ⟨p6, e76⟩ := tilt_t7 F
  obtain ⟨e65, p7⟩ := tilt_t6 F
  have v6 : ⟪F.N 6, (x 6 - x 2) + (x 5 - x 2)⟫ < 0 := by
    rw [inner_add_right, ← neg_sub (x 2) (x 6), ← neg_sub (x 2) (x 5), inner_neg_right, inner_neg_right]; linarith
  have v7 : ⟪F.N 7, (x 6 - x 2) + (x 5 - x 2)⟫ < 0 := by
    rw [inner_add_right, ← neg_sub (x 2) (x 6), ← neg_sub (x 2) (x 5), inner_neg_right, inner_neg_right]; linarith
  refine ⟨fun t ht => ?_, fun t ht => ?_⟩
  · simp only [UMM, mem_insert, mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl
    · exact Or.inl s1
    · exact Or.inl s3
    · exact Or.inl s4
    · exact Or.inl s8
  · simp only [DnMM, mem_insert, mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl
    · exact Or.inl (by linarith)
    · exact Or.inl (by linarith)
    · exact Or.inl (by linarith)
    · exact Or.inr ⟨by linarith, by linarith⟩
    · exact Or.inr ⟨by linarith, by linarith⟩

/-- (6-, 7-) is nonempty: tilt `v = (x 6 - x 2) + (x 5 - x 2)`. -/
theorem u32_cellAt_MM (F : S0xFac 9 s0x_S24 x) (hC : CbarIn x) (hb3 : oblX2 x 3 < 1) :
    ∃ a, CellAt F UMM DnMM a :=
  exists_cellAt_of_lex (u₀ := x 3 - x 2) (v := (x 6 - x 2) + (x 5 - x 2)) (u32_lp_MM F hC hb3).1
    (u32_lp_MM F hC hb3).2

/-- Lex facings of the cell `(6+, 7+)` at `(u_32, v)`, `v = (x 2 - x 6) + (x 2 - x 5)`. -/
theorem u32_lp_PP (F : S0xFac 9 s0x_S24 x) (hC : CbarIn x) (hb3 : oblX2 x 3 < 1) :
    (∀ t ∈ UPP, h21b_LP ⟪F.N t, x 3 - x 2⟫ ⟪F.N t, (x 2 - x 6) + (x 2 - x 5)⟫) ∧
      ∀ t ∈ DnPP, h21b_LP (-⟪F.N t, x 3 - x 2⟫) (-⟪F.N t, (x 2 - x 6) + (x 2 - x 5)⟫) := by
  obtain ⟨s0, s2, s5, s3, s8⟩ := u32_free F
  have s1 := u32_n1 F hb3
  have s4 := u32_n4 F hC.2.1 hb3
  have e6 := u32_n6 F
  have e7 := u32_n7 F
  obtain ⟨p6, e76⟩ := tilt_t7 F
  obtain ⟨e65, p7⟩ := tilt_t6 F
  have v6 : 0 < ⟪F.N 6, (x 2 - x 6) + (x 2 - x 5)⟫ := by
    rw [inner_add_right]; linarith
  have v7 : 0 < ⟪F.N 7, (x 2 - x 6) + (x 2 - x 5)⟫ := by
    rw [inner_add_right]; linarith
  refine ⟨fun t ht => ?_, fun t ht => ?_⟩
  · simp only [UPP, mem_insert, mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl s1
    · exact Or.inl s3
    · exact Or.inl s4
    · exact Or.inr ⟨e6, v6⟩
    · exact Or.inr ⟨e7, v7⟩
    · exact Or.inl s8
  · simp only [DnPP, mem_insert, mem_singleton] at ht
    rcases ht with rfl | rfl | rfl
    · exact Or.inl (by linarith)
    · exact Or.inl (by linarith)
    · exact Or.inl (by linarith)

/-- (6+, 7+) is nonempty: tilt `v = (x 2 - x 6) + (x 2 - x 5)`. -/
theorem u32_cellAt_PP (F : S0xFac 9 s0x_S24 x) (hC : CbarIn x) (hb3 : oblX2 x 3 < 1) :
    ∃ a, CellAt F UPP DnPP a :=
  exists_cellAt_of_lex (u₀ := x 3 - x 2) (v := (x 2 - x 6) + (x 2 - x 5)) (u32_lp_PP F hC hb3).1
    (u32_lp_PP F hC hb3).2

/-! ## (S-b) Gate Handover -/

/-- `N_{6,b} > 0` (facet `235` contains `x 2` but not `x 1`); no hypothesis needed in the facet-data form. -/
theorem n6b_pos (F : S0xFac 9 s0x_S24 x) : 0 < ⟪F.N 6, x 2 - x 1⟫ := by
  rw [F.inner_sub, F.zero 6 2 (by decide)]; linarith [F.neg 6 1 (by decide)]

/-- **EQ(b), Gate Handover** (Carbon Q67.1).  `b_3 < 1` and `N_{6,c} < 0` give `N_{6,c} < 0 < N_{6,a} < N_{6,b}`.
`N_{6,a} < N_{6,b}` is the facet-data fact `f_6(x 0) < 0`; `0 < N_{6,a}` is the content.  No `CbarIn`, no `¬ FacetCellF`:
the gate has 0 failures with both hypotheses violated (GATE.md). -/
theorem n6_handover (F : S0xFac 9 s0x_S24 x) (hb3 : oblX2 x 3 < 1)
    (h6c : ⟪F.N 6, x 6 - x 1⟫ < 0) :
    0 < ⟪F.N 6, x 0 - x 1⟫ ∧ ⟪F.N 6, x 0 - x 1⟫ < ⟪F.N 6, x 2 - x 1⟫ := by
  refine ⟨?_, ?_⟩
  · have T := Minimality.T24.M4.type24OfFac F
    have ha3 : 0 < oblX0 x 3 := T.X0_pos (v := 3) (by decide)
    have hc3 : 0 < oblX6 x 3 := T.X6_pos (v := 3) (by decide)
    have hev := Minimality.T24.M4.fac_eval F 6 3
    have hz3 : F.f 6 (x 3) = 0 := F.zero 6 3 (by decide)
    have hz2 : F.f 6 (x 2) = 0 := F.zero 6 2 (by decide)
    have h0 := F.inner_sub 6 0 1
    have h6 := F.inner_sub 6 6 1
    have hf1 : F.f 6 (x 1) < 0 := F.neg 6 1 (by decide)
    have h1b : 0 < (1 - oblX2 x 3) * (-F.f 6 (x 1)) := mul_pos (by linarith) (by linarith)
    have hcc : 0 < oblX6 x 3 * (-⟪F.N 6, x 6 - x 1⟫) := mul_pos hc3 (by linarith)
    rw [hz3, hz2, ← h0, ← h6] at hev
    have hprod : 0 < oblX0 x 3 * ⟪F.N 6, x 0 - x 1⟫ := by
      have heq : oblX0 x 3 * ⟪F.N 6, x 0 - x 1⟫ =
          (1 - oblX2 x 3) * (-F.f 6 (x 1)) + oblX6 x 3 * (-⟪F.N 6, x 6 - x 1⟫) := by
        linear_combination -hev
      linarith
    exact pos_of_mul_pos_right hprod ha3.le
  · rw [F.inner_sub, F.inner_sub, F.zero 6 2 (by decide)]
    linarith [F.neg 6 0 (by decide)]

/-! ## (S-c) The Split leaf at `u_32` -/

/-- Depth condition of Carbon Q67.3 / A67: `max(z_1, z_5, z_0) < z_6 < z_3` at `u_32` (depths `⟪x v, u_32⟫`;
`z_1 = 0` in the corner frame). -/
def DepthSplit (x : Fin 7 → ℝ³) : Prop :=
  max ⟪x 1, x 3 - x 2⟫ (max ⟪x 5, x 3 - x 2⟫ ⟪x 0, x 3 - x 2⟫) < ⟪x 6, x 3 - x 2⟫ ∧
    ⟪x 6, x 3 - x 2⟫ < ⟪x 3, x 3 - x 2⟫

/-- **EQ(c), rows at `u_32`.**  On the rim `0.1.6.3.5` (labels `cMM`: vertex `3` is index `3`, vertex `5` index `4`, vertex `6` index `2`)
the rows of `SplitRows` for edge `a = [3,5]`, corner `c = 6` hold at the view `u_32` itself, strictly, with an orientation
`σ`: on every gated point `σ * det24 x < 0`, i.e. `σ = -1` for `det24 x > 0` (the gate only sees `det24 x > 0`: its input format fixes
the orientation; the mirror image flips `σ` by the exact identity `det3 (E p) (E q) (E w) = det24 x * det3 p q w`, hence the `∃ σ`).  Hypotheses: `b_3 < 1`, `N_{6,c} < 0`, the depth condition
(NOT `CbarIn`, NOT `¬ FacetCellF`: 0 failures without them, GATE.md).  The rise signs (screen apex) are shape facts at `u_32` (from `n6_handover`);
the depth signs are the depth condition. -/
theorem u32_splitRows (F : S0xFac 9 s0x_S24 x) (hb3 : oblX2 x 3 < 1)
    (h6c : ⟪F.N 6, x 6 - x 1⟫ < 0) (hd : DepthSplit x) :
    ∃ σ : ℝ, Minimality.Split.SplitRows (fun i => x (cMM i)) (x 3 - x 2) 3 2 σ := by
  have det3_eq_inner_cross : ∀ u p q : ℝ³,
      Minimality.Split.det3 u p q = ⟪u, Minimality.cross p q⟫ := by
    intro u p q
    simp only [Minimality.Split.det3, Minimality.Split.inner3,
      Minimality.Split.cross_0, Minimality.Split.cross_1, Minimality.Split.cross_2]
    ring
  have cross_cross_eq : ∀ p q r : ℝ³,
      Minimality.cross (Minimality.cross p q) r = ⟪p, r⟫ • q - ⟪q, r⟫ • p := by
    intro p q r
    ext k
    have hk : ∀ j : Fin 3, j = 0 ∨ j = 1 ∨ j = 2 := by decide
    rcases hk k with rfl | rfl | rfl <;>
      simp only [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul, Minimality.Split.inner3,
        Minimality.Split.cross_0, Minimality.Split.cross_1, Minimality.Split.cross_2] <;> ring
  have smul_sub_inner_cross : ∀ p q : ℝ³,
      ⟪p, p⟫ • q - ⟪q, p⟫ • p = Minimality.cross p (Minimality.cross q p) := by
    intro p q
    ext k
    have hk : ∀ j : Fin 3, j = 0 ∨ j = 1 ∨ j = 2 := by decide
    rcases hk k with rfl | rfl | rfl <;>
      simp only [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul, Minimality.Split.inner3,
        Minimality.Split.cross_0, Minimality.Split.cross_1, Minimality.Split.cross_2] <;> ring
  set a : ℝ³ := x 5 - x 3
  set b : ℝ³ := x 3 - x 2
  set v : ℝ³ := Minimality.cross a b
  set n : ℝ³ := F.N 6
  have ha_n : ⟪a, n⟫ = 0 := by
    rw [real_inner_comm, F.inner_sub, F.zero 6 5 (by decide), F.zero 6 3 (by decide), sub_self]
  have hb_n : ⟪b, n⟫ = 0 := by
    rw [real_inner_comm, F.inner_sub, F.zero 6 3 (by decide), F.zero 6 2 (by decide), sub_self]
  have hcv : Minimality.cross v n = 0 := by
    rw [show v = Minimality.cross a b from rfl, cross_cross_eq, ha_n, hb_n,
      zero_smul, zero_smul, sub_self]
  have hn_ne : n ≠ 0 := by
    intro h0
    have hpos := n6b_pos F
    simp [n, h0] at hpos
  have hnn : 0 < ⟪n, n⟫ := real_inner_self_pos.mpr hn_ne
  have hv_smul : ⟪n, n⟫ • v = ⟪v, n⟫ • n := by
    have h := smul_sub_inner_cross n v
    have hcz : Minimality.cross n (0 : ℝ³) = 0 := by
      ext k; fin_cases k <;> simp [Minimality.Split.cross_0,
        Minimality.Split.cross_1, Minimality.Split.cross_2]
    rw [hcv, hcz] at h
    exact sub_eq_zero.mp h
  set σ : ℝ := ⟪v, n⟫ / ⟪n, n⟫
  have hv_eq : v = σ • n := by
    have h := congrArg (fun z : ℝ³ => (⟪n, n⟫)⁻¹ • z) hv_smul
    simp only [smul_smul, inv_mul_cancel₀ hnn.ne', one_smul] at h
    rw [h]
    simp [σ, div_eq_mul_inv, mul_comm]
  have hv_ne : v ≠ 0 := by
    intro hv0
    have hba0 : Minimality.cross b a = 0 := by
      have hneg : Minimality.cross b a = -Minimality.cross a b := by
        ext k; fin_cases k <;> simp [Minimality.Split.cross_0,
          Minimality.Split.cross_1, Minimality.Split.cross_2] <;> ring
      rw [hneg, show Minimality.cross a b = v from rfl, hv0, neg_zero]
    have hcz : Minimality.cross a (0 : ℝ³) = 0 := by
      ext k; fin_cases k <;> simp [Minimality.Split.cross_0,
        Minimality.Split.cross_1, Minimality.Split.cross_2]
    have hab : ⟪a, a⟫ • b = ⟪b, a⟫ • a := by
      have h := smul_sub_inner_cross a b
      rw [hba0, hcz] at h
      exact sub_eq_zero.mp h
    have ha7 : ⟪a, F.N 7⟫ < 0 := by
      rw [real_inner_comm, F.inner_sub, F.zero 7 3 (by decide), sub_zero]
      exact F.neg 7 5 (by decide)
    have hb7 : ⟪b, F.N 7⟫ = 0 := by
      rw [real_inner_comm, F.inner_sub, F.zero 7 3 (by decide), F.zero 7 2 (by decide), sub_self]
    have hdot7 := congrArg (fun z : ℝ³ => ⟪z, F.N 7⟫) hab
    simp only [real_inner_smul_left, hb7, mul_zero] at hdot7
    have hba_zero : ⟪b, a⟫ = 0 := (mul_eq_zero.mp hdot7.symm).resolve_right ha7.ne
    rw [hba_zero, zero_smul] at hab
    have ha_ne : a ≠ 0 := by
      intro ha0; simp [ha0] at ha7
    have haa : 0 < ⟪a, a⟫ := real_inner_self_pos.mpr ha_ne
    have hb0 : b = 0 := (smul_eq_zero.mp hab).resolve_left haa.ne'
    have hb2 : ⟪b, F.N 2⟫ < 0 := by
      rw [real_inner_comm, F.inner_sub, F.zero 2 2 (by decide), sub_zero]
      exact F.neg 2 3 (by decide)
    simp [hb0] at hb2
  have hσ_ne : σ ≠ 0 := by
    intro h0
    apply hv_ne
    rw [hv_eq, h0, zero_smul]
  have hσ2 : 0 < σ ^ 2 := sq_pos_of_ne_zero hσ_ne
  have hhand : 0 < ⟪n, x 0 - x 1⟫ := (n6_handover F hb3 h6c).1
  have hz0 : ⟪x 0 - x 6, b⟫ < 0 := by
    rw [inner_sub_left]
    linarith [hd.1, le_max_right ⟪x 5, b⟫ ⟪x 0, b⟫, le_max_right ⟪x 1, b⟫ (max ⟪x 5, b⟫ ⟪x 0, b⟫)]
  have hz1 : ⟪x 1 - x 6, b⟫ < 0 := by
    rw [inner_sub_left]
    linarith [hd.1, le_max_left ⟪x 1, b⟫ (max ⟪x 5, b⟫ ⟪x 0, b⟫)]
  have hz5 : ⟪x 5 - x 6, b⟫ < 0 := by
    rw [inner_sub_left]
    linarith [hd.1, le_max_left ⟪x 5, b⟫ ⟪x 0, b⟫, le_max_right ⟪x 1, b⟫ (max ⟪x 5, b⟫ ⟪x 0, b⟫)]
  have hz3 : 0 < ⟪x 3 - x 6, b⟫ := by
    rw [inner_sub_left]
    linarith [hd.2]
  have hn01 : ⟪x 1 - x 0, n⟫ < 0 := by
    have hneg : x 1 - x 0 = -(x 0 - x 1) := by abel
    rw [hneg, inner_neg_left, real_inner_comm]
    linarith
  have hn16 : ⟪x 6 - x 1, n⟫ < 0 := by
    rw [real_inner_comm]; exact h6c
  have hn63 : 0 < ⟪x 3 - x 6, n⟫ := by
    rw [real_inner_comm, F.inner_sub, F.zero 6 3 (by decide), zero_sub]
    linarith [F.neg 6 6 (by decide)]
  have hn50 : ⟪x 0 - x 5, n⟫ < 0 := by
    rw [real_inner_comm, F.inner_sub, F.zero 6 5 (by decide), sub_zero]
    exact F.neg 6 0 (by decide)
  refine ⟨σ, fun i j hi hij hjc => ?_⟩
  change 0 < σ * (⟪x (cMM j) - x (cMM 2), b⟫ *
    Minimality.Split.det3 (x (cMM (i + 1)) - x (cMM i)) (x (cMM (3 + 1)) - x (cMM 3)) b)
  rw [show x (cMM (3 + 1)) - x (cMM 3) = a from rfl, det3_eq_inner_cross,
    show Minimality.cross a b = v from rfl, hv_eq, real_inner_smul_right]
  have hmul : σ * (⟪x (cMM j) - x (cMM 2), b⟫ * (σ * ⟪x (cMM (i + 1)) - x (cMM i), n⟫)) =
      σ ^ 2 * (⟪x (cMM j) - x (cMM 2), b⟫ * ⟪x (cMM (i + 1)) - x (cMM i), n⟫) := by ring
  rw [hmul]
  apply mul_pos hσ2
  have hcMM0 : cMM 0 = 0 := rfl
  have hcMM1 : cMM 1 = 1 := rfl
  have hcMM2 : cMM 2 = 6 := rfl
  have hcMM3 : cMM 3 = 3 := rfl
  have hcMM4 : cMM 4 = 5 := rfl
  have hcMM01 : cMM (0 + 1) = 1 := rfl
  have hcMM11 : cMM (1 + 1) = 6 := rfl
  have hcMM21 : cMM (2 + 1) = 3 := rfl
  have hcMM41 : cMM (4 + 1) = 0 := rfl
  have hcases : ∀ k : ZMod 5, k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by decide
  rcases hcases i with rfl | rfl | rfl | rfl | rfl
  · rcases hij with rfl | rfl
    · rw [hcMM0, hcMM2, hcMM01]; exact mul_pos_of_neg_of_neg hz0 hn01
    · rw [hcMM01, hcMM2, hcMM0]; exact mul_pos_of_neg_of_neg hz1 hn01
  · rcases hij with rfl | rfl
    · rw [hcMM1, hcMM2, hcMM11]; exact mul_pos_of_neg_of_neg hz1 hn16
    · exact absurd rfl hjc
  · rcases hij with rfl | rfl
    · exact absurd rfl hjc
    · rw [hcMM21, hcMM2]; exact mul_pos hz3 hn63
  · exact absurd rfl hi
  · rcases hij with rfl | rfl
    · rw [hcMM4, hcMM2, hcMM41]; exact mul_pos_of_neg_of_neg hz5 hn50
    · rw [hcMM41, hcMM2, hcMM4]; exact mul_pos_of_neg_of_neg hz0 hn50

/-- **EQ(c), Split leaf.**  `N_{6,c} < 0` and the depth condition at `u_32` give a Rupert passage
(`split_tope_rupert` at the lex facings of the cell `(6-, 7-)`, tilt `(x 6 - x 2) + (x 5 - x 2)`). -/
theorem isRupert_u32_split (F : S0xFac 9 s0x_S24 x) (hC : CbarIn x) (hb3 : oblX2 x 3 < 1)
    (h6c : ⟪F.N 6, x 6 - x 1⟫ < 0) (hd : DepthSplit x) : IsRupert (univ.image x) := by
  obtain ⟨σ, hrows⟩ := u32_splitRows F hb3 h6c hd
  have hlp := u32_lp_MM F hC hb3
  have hfac : S0xFacOK F (fun t => decide (t ∈ UMM)) (x 3 - x 2) ((x 6 - x 2) + (x 5 - x 2)) := by
    intro t
    refine ⟨fun h => hlp.1 t (by simpa using h), fun h => hlp.2 t ?_⟩
    have ht : t ∉ UMM := by simpa using h
    revert ht
    revert t
    decide
  have hcyc : S0xCycOK s0x_S24 cMM (fun t => decide (t ∈ UMM)) := by decide
  exact Minimality.Split.split_tope_rupert F (Minimality.H24.SAT.inj_of_fac F)
    (Minimality.Split.noBetween_of_fac F (by decide)) ((x 6 - x 2) + (x 5 - x 2)) injMM (by norm_num) hcyc hfac
    3 2 σ (by decide) (by decide) hrows

/-- Rows of `SplitRows` at `u_32` on a 5-rim `c`, for some edge `a`, corner `cc` and orientation `σ`. -/
def SplitAny5 (x : Fin 7 → ℝ³) (c : ZMod 5 → Fin 7) : Prop :=
  ∃ (a cc : ZMod 5) (σ : ℝ), cc ≠ a ∧ cc ≠ a + 1 ∧ Minimality.Split.SplitRows (fun i => x (c i)) (x 3 - x 2) a cc σ

/-- **EQ(c'), general Split leaf on `0.1.6.3.5`.**  Any rows at `u_32` give a Rupert passage. -/
theorem isRupert_u32_splitAny_mm (F : S0xFac 9 s0x_S24 x) (hC : CbarIn x) (hb3 : oblX2 x 3 < 1)
    (h : SplitAny5 x cMM) : IsRupert (univ.image x) := by
  obtain ⟨a, cc, σ, hca, hca1, hrows⟩ := h
  have hlp := u32_lp_MM F hC hb3
  have hfac : S0xFacOK F (fun t => decide (t ∈ UMM)) (x 3 - x 2) ((x 6 - x 2) + (x 5 - x 2)) := by
    intro t
    refine ⟨fun h => hlp.1 t (by simpa using h), fun h => hlp.2 t ?_⟩
    have ht : t ∉ UMM := by simpa using h
    revert ht
    revert t
    decide
  have hcyc : S0xCycOK s0x_S24 cMM (fun t => decide (t ∈ UMM)) := by decide
  exact Minimality.Split.split_tope_rupert F (Minimality.H24.SAT.inj_of_fac F)
    (Minimality.Split.noBetween_of_fac F (by decide)) ((x 6 - x 2) + (x 5 - x 2)) injMM (by norm_num) hcyc hfac
    a cc σ hca hca1 hrows

/-- **EQ(c'), general Split leaf on `0.1.6.2.5`.** -/
theorem isRupert_u32_splitAny_pp (F : S0xFac 9 s0x_S24 x) (hC : CbarIn x) (hb3 : oblX2 x 3 < 1)
    (h : SplitAny5 x cPP) : IsRupert (univ.image x) := by
  obtain ⟨a, cc, σ, hca, hca1, hrows⟩ := h
  have hlp := u32_lp_PP F hC hb3
  have hfac : S0xFacOK F (fun t => decide (t ∈ UPP)) (x 3 - x 2) ((x 2 - x 6) + (x 2 - x 5)) := by
    intro t
    refine ⟨fun h => hlp.1 t (by simpa using h), fun h => hlp.2 t ?_⟩
    have ht : t ∉ UPP := by simpa using h
    revert ht
    revert t
    decide
  have hcyc : S0xCycOK s0x_S24 cPP (fun t => decide (t ∈ UPP)) := by decide
  exact Minimality.Split.split_tope_rupert F (Minimality.H24.SAT.inj_of_fac F)
    (Minimality.Split.noBetween_of_fac F (by decide)) ((x 2 - x 6) + (x 2 - x 5)) injPP (by norm_num) hcyc hfac
    a cc σ hca hca1 hrows

/-! ## (S-d) The Lex leaves at `u_32` -/

/-- **EQ(d), cell `(6-, 7-)`, rim `0.1.6.3.5`.**  RobUni of the five rim depths at `u_32`. -/
theorem isRupert_u32_lex_mm (F : S0xFac 9 s0x_S24 x) (hC : CbarIn x) (hb3 : oblX2 x 3 < 1)
    (hR : RobUni (fun i : ZMod 5 => ⟪x (cMM i), x 3 - x 2⟫)) : IsRupert (univ.image x) := by
  obtain ⟨a, ha⟩ := u32_cellAt_MM F hC hb3
  exact isRupert_of_closedCell (by norm_num) F (Minimality.H24.SAT.inj_of_fac F) injMM cycMM ha
    (u32_cellLe_MM F hC hb3) hR

/-- **EQ(d), cell `(6+, 7+)`, rim `0.1.6.2.5`.** -/
theorem isRupert_u32_lex_pp (F : S0xFac 9 s0x_S24 x) (hC : CbarIn x) (hb3 : oblX2 x 3 < 1)
    (hR : RobUni (fun i : ZMod 5 => ⟪x (cPP i), x 3 - x 2⟫)) : IsRupert (univ.image x) := by
  obtain ⟨a, ha⟩ := u32_cellAt_PP F hC hb3
  exact isRupert_of_closedCell (by norm_num) F (Minimality.H24.SAT.inj_of_fac F) injPP cycPP ha
    (u32_cellLe_PP F hC hb3) hR

/-- **EQ, combined leaf at `u_32`** (`b_3 < 1`): Lex on one of the two 5-rims at `u_32`, or the Split leaf. -/
theorem isRupert_u32 (F : S0xFac 9 s0x_S24 x) (hC : CbarIn x) (hb3 : oblX2 x 3 < 1)
    (h : RobUni (fun i : ZMod 5 => ⟪x (cMM i), x 3 - x 2⟫) ∨ RobUni (fun i : ZMod 5 => ⟪x (cPP i), x 3 - x 2⟫) ∨
      (⟪F.N 6, x 6 - x 1⟫ < 0 ∧ DepthSplit x)) : IsRupert (univ.image x) := by
  rcases h with h | h | ⟨h6c, hd⟩
  · exact isRupert_u32_lex_mm F hC hb3 h
  · exact isRupert_u32_lex_pp F hC hb3 h
  · exact isRupert_u32_split F hC hb3 h6c hd

/-- **EQ, general combined leaf at `u_32`** (`b_3 < 1`, no facet-cell hypothesis): RobUni or rows on one of the two 5-rims. -/
theorem isRupert_u32_any (F : S0xFac 9 s0x_S24 x) (hC : CbarIn x) (hb3 : oblX2 x 3 < 1)
    (h : RobUni (fun i : ZMod 5 => ⟪x (cMM i), x 3 - x 2⟫) ∨ RobUni (fun i : ZMod 5 => ⟪x (cPP i), x 3 - x 2⟫) ∨
      SplitAny5 x cMM ∨ SplitAny5 x cPP) : IsRupert (univ.image x) := by
  rcases h with h | h | h | h
  · exact isRupert_u32_lex_mm F hC hb3 h
  · exact isRupert_u32_lex_pp F hC hb3 h
  · exact isRupert_u32_splitAny_mm F hC hb3 h
  · exact isRupert_u32_splitAny_pp F hC hb3 h

end Minimality.T24.EQ
