module

public import Minimality.Type24OffOB1DW3
public import Minimality.Type24Wall5Cover
public import Minimality.Type24OffOB1S1

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21 Minimality.FaceChord Minimality.T24.SAT Minimality.T24.Stmt Minimality.T24.Q45
  Minimality.T24.Reg Minimality.T24.A19

/-!
# Type 24 off `OB1`: the codim-2 double-wall slice `τ = 0` (job OSPEC24)

nopert229 notes/OPENSPECIAL-STRATEGY.md section 2l.  On the double wall (`a4 = a5 = 1`, frame signs) with `DwSpec`
and `τ = ⟪x 0 - x 1, x 2 - x 6⟫ = 0` the e26 views of OSPEC23 fail (`0` ties `1` at level 1).  With `g v = x v - x 1`,
`τ = 0` says `⟪g0, g2⟫ = ⟪g0, g6⟫ =: σ`, and `¬ OB1` then gives `σ > 0` or `⟪g2, g6⟫ > 0`:

- `σ > 0`: the e26 view with the level-2 tilt `m*` (`(x 2 - x 6, m*, -N3)`, rim `0 1 6 3 5`) is a lex cell:
  `⟪g0, m*⟫ = σ (-(d·e5)(b4 + c4) + (d·e4)(b5 + c5)) > 0` decides the `0 / 1` tie, `⟪N7, m*⟫ > 0` keeps `236` up
  (`dw5_viewA`; no use of `¬ DwHorizOK`).
- `σ ≤ 0` (so `⟪g2, g6⟫ > 0`): the horizontal view `(x 1 - x 6, w, N3)` along the bottom edge `6 1`, `w` the inward
  normal of that edge in the bottom plane, rim `0 1 2 5 3 4` (the rim of class `01 | 52`), is a lex cell as soon as
  `5` is below `2` along `x 1 - x 6` (`dw5_viewB`; the other rim facts are the acute angles at `1` and `6` and the
  facet `235`), mirror `(x 1 - x 2, w', N3)` (`dw5_viewB_sym`).  If `5` is strictly above `2` the class `06 | 52`
  holds at `m = g6 + ε g2` (`dw5_c0652`), mirror `02 | 46` (`dw5_c0246`): both are cut before.

Residue: `Q45ResWQU` (double-wall piece inside `σ ≤ 0` and the two ties `⟪x 2 - x 5, x 1 - x 6⟫ = 0`,
`⟪x 6 - x 4, x 1 - x 2⟫ = 0`; codim 4 on the double wall), **`OpenSpecialQU`** (`openSpecialQU_iff_QT`), chains
`..._QU` (cell / 28 / E / EP / E4 / E10); combined with OSPEC25's `Q45ResWR2`: **`OpenSpecialR2U`**
(`openSpecialR2U_iff_R2`), chains `..._R2U` (28 / E4 / E10).
-/

namespace Minimality.T24.OSpec

variable {x : Fin 7 → ℝ³}

section DwTau0
open Minimality.LexCell

theorem dw5_lt_snd {p q : ℝ × ℝ × ℝ} (h1 : p.1 = q.1) (h2 : p.2.1 < q.2.1) : LexLt3 p q :=
  Or.inr ⟨by linarith, Or.inl (by linarith)⟩

/-- A top vertex: `⟪x v - x 0, y⟫ = b_v ⟪g2, y⟫ + c_v ⟪g6, y⟫`. -/
theorem dw5_top (F : S0xFac 9 s0x_S24 x) {v : Fin 7} (hv : oblX0 x v = 1) (y : ℝ³) :
    ⟪x v - x 0, y⟫ = oblX2 x v * ⟪x 2 - x 1, y⟫ + oblX6 x v * ⟪x 6 - x 1, y⟫ := by
  rw [dw3_e F hv, inner_add_left, real_inner_smul_left, real_inner_smul_left]

/-- On the double wall `f3` is constant on the bottom face. -/
theorem dw5_f3 (F : S0xFac 9 s0x_S24 x) (hw4 : oblX0 x 4 = 1) (hw5 : oblX0 x 5 = 1)
    (b3 : 0 < oblX0 x 4 * oblX2 x 5 - oblX0 x 5 * oblX2 x 4)
    (b4 : 0 < oblX0 x 5 * oblX6 x 4 - oblX0 x 4 * oblX6 x 5) :
    F.f 3 (x 2) = F.f 3 (x 1) ∧ F.f 3 (x 6) = F.f 3 (x 1) := by
  have hΔ := dw3_delta_pos F hw4 hw5 b3 b4
  have e4 := M4.fac_eval F 3 4
  have e5 := M4.fac_eval F 3 5
  rw [F.zero 3 4 (by decide), F.zero 3 0 (by decide), hw4] at e4
  rw [F.zero 3 5 (by decide), F.zero 3 0 (by decide), hw5] at e5
  set A := F.f 3 (x 2) - F.f 3 (x 1)
  set B := F.f 3 (x 6) - F.f 3 (x 1)
  have hA : (oblX2 x 5 * oblX6 x 4 - oblX2 x 4 * oblX6 x 5) * A = 0 := by
    linear_combination -(oblX6 x 4) * e5 + oblX6 x 5 * e4
  have hB : (oblX2 x 5 * oblX6 x 4 - oblX2 x 4 * oblX6 x 5) * B = 0 := by
    linear_combination -(oblX2 x 5) * e4 + oblX2 x 4 * e5
  rcases mul_eq_zero.1 hA with h | h
  · exact absurd h hΔ.ne'
  rcases mul_eq_zero.1 hB with h' | h'
  · exact absurd h' hΔ.ne'
  constructor <;> linarith

/-- `-⟪d, e5⟫ P + ⟪d, e4⟫ Q > 0` for `P, Q > 0` on `DwSpec` (`⟪d, e4⟫ ≥ 0 ≥ ⟪d, e5⟫`, not both zero). -/
theorem dw5_comb_pos (F : S0xFac 9 s0x_S24 x) (hw4 : oblX0 x 4 = 1) (hw5 : oblX0 x 5 = 1)
    (b3 : 0 < oblX0 x 4 * oblX2 x 5 - oblX0 x 5 * oblX2 x 4)
    (b4 : 0 < oblX0 x 5 * oblX6 x 4 - oblX0 x 4 * oblX6 x 5) (hS : DwSpec x) {P Q : ℝ} (hP : 0 < P)
    (hQ : 0 < Q) : 0 < -⟪x 6 - x 2, x 5 - x 0⟫ * P + ⟪x 6 - x 2, x 4 - x 0⟫ * Q := by
  obtain ⟨-, hd4, hd5, -, -⟩ := hS
  rcases hd5.lt_or_eq with h5 | h5
  · nlinarith [mul_pos (neg_pos.2 h5) hP, mul_nonneg hd4 hQ.le]
  · rcases hd4.lt_or_eq with h4 | h4
    · rw [h5]; nlinarith [mul_pos h4 hQ]
    · exact (dw4_d_not_both F hw4 hw5 b3 b4 h4.symm h5).elim

/-- On `τ = 0`: `⟪x 0 - x 1, x v - x 0⟫ = (b_v + c_v) σ` for a top vertex, `σ = ⟪x 0 - x 1, x 6 - x 1⟫`. -/
theorem dw5_g0_top (F : S0xFac 9 s0x_S24 x) {v : Fin 7} (hv : oblX0 x v = 1)
    (hτ : ⟪x 0 - x 1, x 2 - x 6⟫ = 0) :
    ⟪x 0 - x 1, x v - x 0⟫ = (oblX2 x v + oblX6 x v) * ⟪x 0 - x 1, x 6 - x 1⟫ := by
  have e : ⟪x 0 - x 1, x 2 - x 1⟫ = ⟪x 0 - x 1, x 6 - x 1⟫ := by
    have : x 2 - x 6 = (x 2 - x 1) - (x 6 - x 1) := by abel
    rw [this, inner_sub_right] at hτ; linarith
  rw [real_inner_comm, dw5_top F hv, real_inner_comm (x 0 - x 1) (x 2 - x 1), real_inner_comm (x 0 - x 1) (x 6 - x 1), e]
  ring

/-- `⟪N7, x v - x 0⟫ = -(b_v + c_v) f7(x 1)` for a top vertex. -/
theorem dw5_n7_top (F : S0xFac 9 s0x_S24 x) {v : Fin 7} (hv : oblX0 x v = 1) :
    ⟪F.N 7, x v - x 0⟫ = -(oblX2 x v + oblX6 x v) * F.f 7 (x 1) := by
  have e := M4.fac_eval F 7 v
  rw [F.zero 7 2 (by decide), F.zero 7 6 (by decide), hv] at e
  rw [F.inner_sub 7 v 0]; linarith

/-! ### `σ > 0`: the e26 view with the level-2 tilt `m*` -/

/-- **`σ > 0` on `DwSpec ∩ {τ = 0}`: the view `(x 2 - x 6, m*, -N3)` is a lex cell** (rim `0 1 6 3 5`; `126`, `0345`
edge-on to level 2 and decided at level 3, `236` up at level 2 by `⟪N7, m*⟫ > 0`, the tie `0 / 1` decided at level 2
by `⟪x 0 - x 1, m*⟫ > 0`). -/
theorem dw5_viewA (F : S0xFac 9 s0x_S24 x) (hw4 : oblX0 x 4 = 1) (hw5 : oblX0 x 5 = 1) {s t : ℝ} (hs : 0 < s)
    (ht1 : t < 1) (hd : x 3 - x 0 = s • (x 4 - x 0) + t • (x 5 - x 0))
    (b3 : 0 < oblX0 x 4 * oblX2 x 5 - oblX0 x 5 * oblX2 x 4)
    (b4 : 0 < oblX0 x 5 * oblX6 x 4 - oblX0 x 4 * oblX6 x 5) (hS : DwSpec x)
    (hτ : ⟪x 0 - x 1, x 2 - x 6⟫ = 0) (hσ : 0 < ⟪x 0 - x 1, x 6 - x 1⟫) : Gen.LexAny F := by
  have T := M4.type24OfFac F
  have hl4 : 0 < oblX2 x 4 + oblX6 x 4 := by
    linarith [T.X2_pos (v := 4) (by decide), T.X6_pos (v := 4) (by decide)]
  have hl5 : 0 < oblX2 x 5 + oblX6 x 5 := by
    linarith [T.X2_pos (v := 5) (by decide), T.X6_pos (v := 5) (by decide)]
  have hN3 : 0 < ⟪F.N 3, F.N 3⟫ := real_inner_self_pos.mpr (n3_ne_zero F)
  have h53 := bs_n53_neg F hw4 hw5
  obtain ⟨f32, f36⟩ := dw5_f3 F hw4 hw5 b3 b4
  -- `⟪N7, m*⟫ > 0`
  have n7 : 0 < ⟪F.N 7, dwMs x⟫ := by
    rw [dwMs_inner, dw5_n7_top F hw4, dw5_n7_top F hw5]
    have f1 := F.neg 7 1 (by decide)
    have := dw5_comb_pos F hw4 hw5 b3 b4 hS (mul_pos hl4 (neg_pos.2 f1)) (mul_pos hl5 (neg_pos.2 f1))
    linarith
  -- `⟪x 0 - x 1, m*⟫ > 0`
  have g0 : 0 < ⟪x 0 - x 1, dwMs x⟫ := by
    rw [dwMs_inner, dw5_g0_top F hw4 hτ, dw5_g0_top F hw5 hτ]
    have := dw5_comb_pos F hw4 hw5 b3 b4 hS (mul_pos hl4 hσ) (mul_pos hl5 hσ)
    linarith
  have hk := dw4_kappa_pos F hw4 hw5 b3 b4 hS
  have m5 : 0 < ⟪x 5 - x 0, dwMs x⟫ := by rw [dw4_ms_top F hw5]; exact mul_pos hl5 hk
  obtain ⟨a6, -⟩ := dw4_angles F hw4 hw5 hS
  have hS' := hS
  obtain ⟨-, hd4, hd5, -, -⟩ := hS'
  have l10 : ⟪x 1, x 2 - x 6⟫ = ⟪x 0, x 2 - x 6⟫ := by rw [inner_sub_left] at hτ; linarith
  have l61 : ⟪x 6, x 2 - x 6⟫ < ⟪x 1, x 2 - x 6⟫ := by rw [inner_sub_left] at a6; linarith
  have l35 : ⟪x 3, x 2 - x 6⟫ < ⟪x 5, x 2 - x 6⟫ := by
    have e : x 5 - x 3 = (1 - t) • (x 5 - x 0) - s • (x 4 - x 0) := by
      rw [show x 5 - x 3 = (x 5 - x 0) - (x 3 - x 0) by abel, hd]; module
    have h' : ⟪x 5 - x 3, x 2 - x 6⟫ = s * ⟪x 6 - x 2, x 4 - x 0⟫ - (1 - t) * ⟪x 6 - x 2, x 5 - x 0⟫ := by
      rw [e, inner_sub_left, real_inner_smul_left, real_inner_smul_left, ← neg_sub (x 6) (x 2), inner_neg_right,
        inner_neg_right, real_inner_comm (x 5 - x 0), real_inner_comm (x 4 - x 0)]; ring
    have : 0 < ⟪x 5 - x 3, x 2 - x 6⟫ := by
      rw [h']
      have := dw5_comb_pos F hw4 hw5 b3 b4 hS (sub_pos.2 ht1) hs
      linarith
    rw [inner_sub_left] at this; linarith
  have e05 : ⟪x 5 - x 0, x 2 - x 6⟫ = -⟪x 6 - x 2, x 5 - x 0⟫ := by
    rw [real_inner_comm, ← neg_sub (x 6) (x 2), inner_neg_left]
  rw [inner_sub_left] at e05 g0 m5
  refine ⟨5, inferInstance, rimEB, UEB, DnEB, x 2 - x 6, dwMs x, -F.N 3, by norm_num, rimEB_inj,
    rimEB_cyc, ?_, ?_, ?_⟩
  · intro u hu
    simp only [UEB, Finset.mem_insert, Finset.mem_singleton] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl
    · left; rw [F.inner_sub 0 2 6, F.zero 0 2 (by decide)]; linarith [F.neg 0 6 (by decide)]
    · left; rw [F.inner_sub 2 2 6, F.zero 2 2 (by decide)]; linarith [F.neg 2 6 (by decide)]
    · right
      refine ⟨by rw [F.inner_sub 5 2 6, F.zero 5 2 (by decide), F.zero 5 6 (by decide)]; ring,
        Or.inr ⟨dw_n5 F hw4 hw5 _ _, ?_⟩⟩
      rw [inner_neg_right]; linarith
    · left; rw [F.inner_sub 6 2 6, F.zero 6 2 (by decide)]; linarith [F.neg 6 6 (by decide)]
    · right
      exact ⟨by rw [F.inner_sub 7 2 6, F.zero 7 2 (by decide), F.zero 7 6 (by decide)]; ring, Or.inl n7⟩
  · intro u hu
    simp only [DnEB, Finset.mem_insert, Finset.mem_singleton] at hu
    rcases hu with rfl | rfl | rfl | rfl
    · left; rw [F.inner_sub 1 2 6, F.zero 1 6 (by decide)]; linarith [F.neg 1 2 (by decide)]
    · right
      refine ⟨by rw [F.inner_sub 3 2 6, f32, f36]; ring, Or.inr ⟨by rw [dwMs, dw_n3]; ring, ?_⟩⟩
      rw [inner_neg_right, neg_neg]; exact hN3
    · left; rw [F.inner_sub 4 2 6, F.zero 4 6 (by decide)]; linarith [F.neg 4 2 (by decide)]
    · left; rw [F.inner_sub 8 2 6, F.zero 8 6 (by decide)]; linarith [F.neg 8 2 (by decide)]
  · refine robUniLex_five_dw4 _ (dw5_lt_snd l10 (by show ⟪x 1, dwMs x⟫ < ⟪x 0, dwMs x⟫; linarith))
      (lexLt3_of_fst l61) (lexLt3_of_fst (by show ⟪x 6, x 2 - x 6⟫ < ⟪x 0, x 2 - x 6⟫; linarith))
      (lexLt3_of_fst l35) (Or.inl ⟨?_, ?_, lexLt3_of_fst (by show ⟪x 6, x 2 - x 6⟫ < ⟪x 5, x 2 - x 6⟫; linarith)⟩)
    · rcases hd5.lt_or_eq with h5 | h5
      · exact lexLt3_of_fst (by show ⟪x 0, x 2 - x 6⟫ < ⟪x 5, x 2 - x 6⟫; linarith)
      · exact dw5_lt_snd (by show ⟪x 0, x 2 - x 6⟫ = ⟪x 5, x 2 - x 6⟫; rw [h5] at e05; linarith)
          (by show ⟪x 0, dwMs x⟫ < ⟪x 5, dwMs x⟫; linarith)
    · rcases hd5.lt_or_eq with h5 | h5
      · exact lexLt3_of_fst (by show ⟪x 1, x 2 - x 6⟫ < ⟪x 5, x 2 - x 6⟫; linarith)
      · exact dw5_lt_snd (by show ⟪x 1, x 2 - x 6⟫ = ⟪x 5, x 2 - x 6⟫; rw [h5] at e05; linarith)
          (by show ⟪x 1, dwMs x⟫ < ⟪x 5, dwMs x⟫; linarith)

/-! ### `σ ≤ 0`: the horizontal view along the bottom edge `6 1` -/

/-- `c3 = s c4 + t c5` (the facet `012`: `f0 = c f0(x 6)`). -/
theorem dw5_c3 (F : S0xFac 9 s0x_S24 x) {s t : ℝ} (hd : x 3 - x 0 = s • (x 4 - x 0) + t • (x 5 - x 0)) :
    oblX6 x 3 = s * oblX6 x 4 + t * oblX6 x 5 := by
  have ev : ∀ v : Fin 7, F.f 0 (x v) = oblX6 x v * F.f 0 (x 6) := by
    intro v
    have e := M4.fac_eval F 0 v
    rw [F.zero 0 1 (by decide), F.zero 0 0 (by decide), F.zero 0 2 (by decide)] at e
    linarith
  have a := dw_aff F hd 0
  rw [ev 3, ev 4, ev 5, F.zero 0 0 (by decide)] at a
  have h6 := F.neg 0 6 (by decide)
  have : (oblX6 x 3 - (s * oblX6 x 4 + t * oblX6 x 5)) * F.f 0 (x 6) = 0 := by linear_combination a
  rcases mul_eq_zero.1 this with h | h
  · linarith
  · linarith

/-- `b3 = s b4 + t b5` (the facet `016`). -/
theorem dw5_b3 (F : S0xFac 9 s0x_S24 x) {s t : ℝ} (hd : x 3 - x 0 = s • (x 4 - x 0) + t • (x 5 - x 0)) :
    oblX2 x 3 = s * oblX2 x 4 + t * oblX2 x 5 := by
  have ev : ∀ v : Fin 7, F.f 1 (x v) = oblX2 x v * F.f 1 (x 2) := by
    intro v
    have e := M4.fac_eval F 1 v
    rw [F.zero 1 1 (by decide), F.zero 1 0 (by decide), F.zero 1 6 (by decide)] at e
    linarith
  have a := dw_aff F hd 1
  rw [ev 3, ev 4, ev 5, F.zero 1 0 (by decide)] at a
  have h2 := F.neg 1 2 (by decide)
  have : (oblX2 x 3 - (s * oblX2 x 4 + t * oblX2 x 5)) * F.f 1 (x 2) = 0 := by linear_combination a
  rcases mul_eq_zero.1 this with h | h
  · linarith
  · linarith

theorem dw5_g6_ne (F : S0xFac 9 s0x_S24 x) : x 6 - x 1 ≠ 0 := by
  intro h
  have e := F.inner_sub 0 6 1
  rw [h, inner_zero_right, F.zero 0 1 (by decide)] at e
  linarith [F.neg 0 6 (by decide)]

theorem dw5_g2_ne (F : S0xFac 9 s0x_S24 x) : x 2 - x 1 ≠ 0 := by
  intro h
  have e := F.inner_sub 1 2 1
  rw [h, inner_zero_right, F.zero 1 1 (by decide)] at e
  linarith [F.neg 1 2 (by decide)]

/-- The inward normal of the bottom edge `1 6` in the bottom plane: `w = |g6|² g2 - ⟪g2, g6⟫ g6`. -/
noncomputable def dwW (x : Fin 7 → ℝ³) : ℝ³ :=
  ⟪x 6 - x 1, x 6 - x 1⟫ • (x 2 - x 1) - ⟪x 2 - x 1, x 6 - x 1⟫ • (x 6 - x 1)

theorem dwW_n (F : S0xFac 9 s0x_S24 x) (u : Fin 9) : ⟪F.N u, dwW x⟫ =
    ⟪x 6 - x 1, x 6 - x 1⟫ * (F.f u (x 2) - F.f u (x 1)) - ⟪x 2 - x 1, x 6 - x 1⟫ * (F.f u (x 6) - F.f u (x 1)) := by
  rw [dwW, inner_sub_right, real_inner_smul_right, real_inner_smul_right, F.inner_sub u 2 1, F.inner_sub u 6 1]

set_option maxHeartbeats 1000000 in
/-- **`σ ≤ 0` side: the view `(x 1 - x 6, w, N3)` is a lex cell** when the face angles at `1` and `6` of the bottom
triangle are acute and `5` is below `2` along `x 1 - x 6` (rim `0 1 2 5 3 4` = `rimC0152`; `016` edge-on at level 1,
down at level 2; `0345` / `126` edge-on to level 2, decided by `N3`; `3` below `5` from the facet `235` and the angle
at `6`; `4` below `0` from the angle at `1`). -/
theorem dw5_viewB (F : S0xFac 9 s0x_S24 x) (hw4 : oblX0 x 4 = 1) (hw5 : oblX0 x 5 = 1) {s t : ℝ} (hs : 0 < s)
    (hst : 1 < s + t) (hd : x 3 - x 0 = s • (x 4 - x 0) + t • (x 5 - x 0))
    (b3 : 0 < oblX0 x 4 * oblX2 x 5 - oblX0 x 5 * oblX2 x 4)
    (b4 : 0 < oblX0 x 5 * oblX6 x 4 - oblX0 x 4 * oblX6 x 5) (hb35 : oblX2 x 3 < oblX2 x 5)
    (ha6 : 0 < ⟪x 1 - x 6, x 2 - x 6⟫) (hG : 0 < ⟪x 2 - x 1, x 6 - x 1⟫)
    (hR : 0 < ⟪x 2 - x 5, x 1 - x 6⟫) : Gen.LexAny F := by
  have T := M4.type24OfFac F
  have hw3 : oblX0 x 3 = 1 := by rw [obl3_a F hd, hw4, hw5]; ring
  have hb4 : 0 < oblX2 x 4 := T.X2_pos (by decide)
  have hc4 : 0 < oblX6 x 4 := T.X6_pos (by decide)
  have hb5 : 0 < oblX2 x 5 := T.X2_pos (by decide)
  have hc5 : 0 < oblX6 x 5 := T.X6_pos (by decide)
  have hc54 : oblX6 x 5 < oblX6 x 4 := by rw [hw4, hw5] at b4; linarith
  have hc3 := dw5_c3 F hd
  have hq : 0 < oblX6 x 3 - oblX6 x 5 := by
    rw [hc3]; nlinarith [mul_pos hs (sub_pos.2 hc54), mul_pos (sub_pos.2 hst) hc5]
  have hN3 : 0 < ⟪F.N 3, F.N 3⟫ := real_inner_self_pos.mpr (n3_ne_zero F)
  have h53 := bs_n53_neg F hw4 hw5
  obtain ⟨f32, f36⟩ := dw5_f3 F hw4 hw5 b3 b4
  have hG6 : 0 < ⟪x 6 - x 1, x 6 - x 1⟫ := real_inner_self_pos.2 (dw5_g6_ne F)
  -- the facet `235`: `(c3 - c5) K6 = (b5 - b3) K1`, `K1 = -f6(x 1)`, `K6 = f6(x 6) - f6(x 1)`
  have e3 := M4.fac_eval F 6 3
  have e5 := M4.fac_eval F 6 5
  rw [F.zero 6 3 (by decide), F.zero 6 2 (by decide), hw3] at e3
  rw [F.zero 6 5 (by decide), F.zero 6 2 (by decide), hw5] at e5
  have f61 := F.neg 6 1 (by decide)
  have f66 := F.neg 6 6 (by decide)
  have kk : (oblX6 x 3 - oblX6 x 5) * (F.f 6 (x 6) - F.f 6 (x 1)) =
      (oblX2 x 5 - oblX2 x 3) * (-F.f 6 (x 1)) := by linear_combination e5 - e3
  have hK6 : 0 < F.f 6 (x 6) - F.f 6 (x 1) := by
    by_contra hc; push Not at hc
    nlinarith [mul_pos (sub_pos.2 hb35) (neg_pos.2 f61), mul_nonneg hq.le (neg_nonneg.2 hc)]
  have hqb : oblX2 x 5 - oblX2 x 3 < oblX6 x 3 - oblX6 x 5 := by
    by_contra hc; push Not at hc
    nlinarith [mul_le_mul_of_nonneg_right hc (neg_pos.2 f61).le, mul_pos hq (by linarith : (0:ℝ) < -F.f 6 (x 6))]
  -- level-1 facts along `u = x 1 - x 6`
  have g66 : ⟪x 1 - x 6, x 2 - x 6⟫ = ⟪x 6 - x 1, x 6 - x 1⟫ - ⟪x 2 - x 1, x 6 - x 1⟫ := by
    rw [show x 1 - x 6 = -(x 6 - x 1) by abel, show x 2 - x 6 = (x 2 - x 1) - (x 6 - x 1) by abel, inner_neg_left,
      inner_sub_right, real_inner_comm (x 2 - x 1) (x 6 - x 1)]; ring
  have neg6 : ∀ v : Fin 7, ⟪x v - x 0, x 1 - x 6⟫ = -⟪x v - x 0, x 6 - x 1⟫ := by
    intro v; rw [show x 1 - x 6 = -(x 6 - x 1) by abel, inner_neg_right]
  have t4 := dw5_top F hw4 (x 6 - x 1)
  have t3 := dw5_top F hw3 (x 6 - x 1)
  have t5 := dw5_top F hw5 (x 6 - x 1)
  have l40 : ⟪x 4, x 1 - x 6⟫ < ⟪x 0, x 1 - x 6⟫ := by
    have := neg6 4
    rw [t4, inner_sub_left] at this
    nlinarith [mul_pos hb4 hG, mul_pos hc4 hG6]
  have l35 : ⟪x 3, x 1 - x 6⟫ < ⟪x 5, x 1 - x 6⟫ := by
    have h3 := neg6 3
    have h5 := neg6 5
    rw [t3, inner_sub_left] at h3
    rw [t5, inner_sub_left] at h5
    have P1 := mul_pos hq (by linarith : (0:ℝ) < ⟪x 6 - x 1, x 6 - x 1⟫ - ⟪x 2 - x 1, x 6 - x 1⟫)
    have P2 := mul_pos (sub_pos.2 hqb) hG
    have key : ⟪x 5, x 1 - x 6⟫ - ⟪x 3, x 1 - x 6⟫ =
        (oblX6 x 3 - oblX6 x 5) * (⟪x 6 - x 1, x 6 - x 1⟫ - ⟪x 2 - x 1, x 6 - x 1⟫) +
          (oblX6 x 3 - oblX6 x 5 - (oblX2 x 5 - oblX2 x 3)) * ⟪x 2 - x 1, x 6 - x 1⟫ := by
      linear_combination h5 - h3
    linarith
  have l52 : ⟪x 5, x 1 - x 6⟫ < ⟪x 2, x 1 - x 6⟫ := by rw [inner_sub_left] at hR; linarith
  have l21 : ⟪x 2, x 1 - x 6⟫ < ⟪x 1, x 1 - x 6⟫ := by
    have e : ⟪x 1 - x 2, x 1 - x 6⟫ = ⟪x 2 - x 1, x 6 - x 1⟫ := by
      rw [show x 1 - x 2 = -(x 2 - x 1) by abel, show x 1 - x 6 = -(x 6 - x 1) by abel, inner_neg_neg]
    rw [inner_sub_left] at e; linarith
  refine ⟨6, inferInstance, rimC0152, UC0152, DnC0152, x 1 - x 6, dwW x, F.N 3, by norm_num, rimC0152_inj,
    rimC0152_cyc, ?_, ?_, ?_⟩
  · intro u hu
    simp only [UC0152, Finset.mem_insert, Finset.mem_singleton] at hu
    rcases hu with rfl | rfl | rfl
    · left; rw [F.inner_sub 0 1 6, F.zero 0 1 (by decide)]; linarith [F.neg 0 6 (by decide)]
    · left
      have e := M4.fac_eval F 2 5
      rw [F.zero 2 5 (by decide), F.zero 2 0 (by decide), F.zero 2 2 (by decide), hw5] at e
      have f21 := F.neg 2 1 (by decide)
      have k : oblX6 x 5 * (F.f 2 (x 6) - F.f 2 (x 1)) = oblX2 x 5 * F.f 2 (x 1) := by
        linear_combination (-1 : ℝ) * e
      have hn : oblX6 x 5 * (F.f 2 (x 6) - F.f 2 (x 1)) < 0 := by rw [k]; exact mul_neg_of_pos_of_neg hb5 f21
      have := neg_of_mul_neg_right hn hc5.le
      rw [F.inner_sub 2 1 6]; linarith
    · right
      refine ⟨by rw [F.inner_sub 3 1 6, f36]; ring, Or.inr ⟨by rw [dwW_n, f32, f36]; ring, hN3⟩⟩
  · intro u hu
    simp only [DnC0152, Finset.mem_insert, Finset.mem_singleton] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl
    · right
      refine ⟨by rw [F.inner_sub 1 1 6, F.zero 1 1 (by decide), F.zero 1 6 (by decide)]; ring, Or.inl ?_⟩
      rw [dwW_n, F.zero 1 1 (by decide), F.zero 1 6 (by decide)]
      have := mul_neg_of_pos_of_neg hG6 (F.neg 1 2 (by decide))
      simp only [sub_zero, sub_self, mul_zero]; linarith
    · left; rw [F.inner_sub 4 1 6, F.zero 4 6 (by decide)]; linarith [F.neg 4 1 (by decide)]
    · right
      refine ⟨by rw [F.inner_sub 5 1 6, F.zero 5 1 (by decide), F.zero 5 6 (by decide)]; ring,
        Or.inr ⟨by rw [dwW_n, F.zero 5 1 (by decide), F.zero 5 2 (by decide), F.zero 5 6 (by decide)]; ring,
          by linarith⟩⟩
    · left; rw [F.inner_sub 6 1 6]; linarith
    · left; rw [F.inner_sub 7 1 6, F.zero 7 6 (by decide)]; linarith [F.neg 7 1 (by decide)]
    · left; rw [F.inner_sub 8 1 6, F.zero 8 6 (by decide)]; linarith [F.neg 8 1 (by decide)]
  · have L : ∀ p q : ℝ × ℝ × ℝ, p.1 < q.1 → LexLt3 p q := fun p q h => Or.inl (by linarith)
    apply robUniLex_six_dw
    · exact Or.inr (L _ _ (show ⟪x 4, x 1 - x 6⟫ < ⟪x 0, x 1 - x 6⟫ from l40))
    · exact Or.inr (L _ _ (show ⟪x 5, x 1 - x 6⟫ < ⟪x 2, x 1 - x 6⟫ from l52))
    · exact Or.inr (Or.inr (L _ _ (show ⟪x 2, x 1 - x 6⟫ < ⟪x 1, x 1 - x 6⟫ from l21)))
    · exact Or.inl (L _ _ (show ⟪x 3, x 1 - x 6⟫ < ⟪x 5, x 1 - x 6⟫ from l35))

/-- **The mirror view `(x 1 - x 2, w', N3)`** (`dw5_viewB` for `π24 x`): needs `6` below `4`... i.e.
`⟪x 6 - x 4, x 1 - x 2⟫ > 0`. -/
theorem dw5_viewB_sym (F : S0xFac 9 s0x_S24 x) (hw4 : oblX0 x 4 = 1) (hw5 : oblX0 x 5 = 1) {s t : ℝ}
    (ht : 0 < t) (hst : 1 < s + t) (hd : x 3 - x 0 = s • (x 4 - x 0) + t • (x 5 - x 0))
    (b3 : 0 < oblX0 x 4 * oblX2 x 5 - oblX0 x 5 * oblX2 x 4)
    (b4 : 0 < oblX0 x 5 * oblX6 x 4 - oblX0 x 4 * oblX6 x 5) (hc34 : oblX6 x 3 < oblX6 x 4)
    (ha2 : 0 < ⟪x 1 - x 2, x 6 - x 2⟫) (hG : 0 < ⟪x 2 - x 1, x 6 - x 1⟫)
    (hR : 0 < ⟪x 6 - x 4, x 1 - x 2⟫) : Gen.LexAny F := by
  have o4 : oblX0 (x ∘ Sym.pi24) 4 = oblX0 x 5 := by rw [Sym.oblX0_comp_pi24]; simp
  have o5 : oblX0 (x ∘ Sym.pi24) 5 = oblX0 x 4 := by rw [Sym.oblX0_comp_pi24]; simp
  have p3 : oblX2 (x ∘ Sym.pi24) 3 = oblX6 x 3 := by rw [Sym.oblX2_comp_pi24]; simp
  have p4 : oblX2 (x ∘ Sym.pi24) 4 = oblX6 x 5 := by rw [Sym.oblX2_comp_pi24]; simp
  have p5 : oblX2 (x ∘ Sym.pi24) 5 = oblX6 x 4 := by rw [Sym.oblX2_comp_pi24]; simp
  have q4 : oblX6 (x ∘ Sym.pi24) 4 = oblX2 x 5 := by rw [Sym.oblX6_comp_pi24]; simp
  have q5 : oblX6 (x ∘ Sym.pi24) 5 = oblX2 x 4 := by rw [Sym.oblX6_comp_pi24]; simp
  refine Sym.lexAny_sym F (dw5_viewB (Sym.sym24 F) (by rw [o4, hw5]) (by rw [o5, hw4]) (s := t) (t := s) ht
    (by linarith) ?_ ?_ ?_ ?_ ?_ ?_ ?_)
  · simp only [Function.comp_apply, Sym.pi24_0, Sym.pi24_3, Sym.pi24_4, Sym.pi24_5]
    rw [hd]; abel
  · rw [o4, o5, p4, p5]; linarith
  · rw [o4, o5, q4, q5]; linarith
  · rw [p3, p5]; exact hc34
  · simpa only [Function.comp_apply, Sym.pi24_1, Sym.pi24_2, Sym.pi24_6] using ha2
  · simp only [Function.comp_apply, Sym.pi24_1, Sym.pi24_2, Sym.pi24_6]
    rw [real_inner_comm]; exact hG
  · simpa only [Function.comp_apply, Sym.pi24_1, Sym.pi24_2, Sym.pi24_5, Sym.pi24_6] using hR

/-! ### `5` strictly above `2` along `x 1 - x 6`: the class `06 | 52` at `m = g6 + ε g2` -/

/-- **`C0652` near the bottom ray `g6`** (`g6` lies inside the top cone `(e4, x 3 - x 5)`): from
`⟪x 6 - x 0, g6⟫ > 0` and `⟪x 2 - x 5, g6⟫ > 0`. -/
theorem dw5_c0652 (F : S0xFac 9 s0x_S24 x) (hw4 : oblX0 x 4 = 1) (hw5 : oblX0 x 5 = 1) {s t : ℝ}
    (hd : x 3 - x 0 = s • (x 4 - x 0) + t • (x 5 - x 0)) (hb35 : oblX2 x 3 < oblX2 x 5)
    (hc53 : oblX6 x 5 < oblX6 x 3)
    (j1 : 0 < ⟪x 6 - x 0, x 6 - x 1⟫) (j2 : 0 < ⟪x 2 - x 5, x 6 - x 1⟫) : DwC0652 x := by
  have T := M4.type24OfFac F
  have hw3 : oblX0 x 3 = 1 := by rw [obl3_a F hd, hw4, hw5]; ring
  have hb4 : 0 < oblX2 x 4 := T.X2_pos (by decide)
  have hc4 : 0 < oblX6 x 4 := T.X6_pos (by decide)
  have hD : 0 < oblX2 x 4 * (oblX6 x 3 - oblX6 x 5) - oblX6 x 4 * (oblX2 x 3 - oblX2 x 5) := by
    nlinarith [mul_pos hb4 (sub_pos.2 hc53), mul_pos hc4 (sub_pos.2 hb35)]
  set D := oblX2 x 4 * (oblX6 x 3 - oblX6 x 5) - oblX6 x 4 * (oblX2 x 3 - oblX2 x 5) with hDdef
  obtain ⟨ε, ⟨e1, e2, e3, e4⟩, hε⟩ :=
    (((dw2_eventually (oblX6 x 3 - oblX6 x 5) (by linarith : 0 < -(oblX2 x 3 - oblX2 x 5))).and
      ((dw2_eventually (-oblX6 x 4) hb4).and
      ((dw2_eventually ⟪x 6 - x 0, x 2 - x 1⟫ j1).and (dw2_eventually ⟪x 2 - x 5, x 2 - x 1⟫ j2)))).and
      self_mem_nhdsWithin).exists
  have hε' : (0:ℝ) < ε := hε
  have hm : (-(oblX2 x 3 - oblX2 x 5) + ε * (oblX6 x 3 - oblX6 x 5)) • (x 4 - x 0) +
      (oblX2 x 4 + ε * -oblX6 x 4) • (x 3 - x 5) = (ε * D) • (x 2 - x 1) + D • (x 6 - x 1) := by
    rw [show x 3 - x 5 = (x 3 - x 0) - (x 5 - x 0) by abel, dw3_e F hw4, dw3_e F hw3, dw3_e F hw5, hDdef]
    module
  refine ⟨_, _, ε * D, D, e1, e2, mul_pos hε' hD, hD, hm, ?_, ?_⟩
  · rw [hm, inner_add_right, real_inner_smul_right, real_inner_smul_right]; nlinarith [mul_pos hD e3]
  · rw [hm, inner_add_right, real_inner_smul_right, real_inner_smul_right]; nlinarith [mul_pos hD e4]

/-- **Mirror: `C0246` near the bottom ray `g2`** (from `⟪x 2 - x 0, g2⟫ > 0` and `⟪x 6 - x 4, g2⟫ > 0`). -/
theorem dw5_c0246 (F : S0xFac 9 s0x_S24 x) (hw4 : oblX0 x 4 = 1) (hw5 : oblX0 x 5 = 1) {s t : ℝ}
    (hd : x 3 - x 0 = s • (x 4 - x 0) + t • (x 5 - x 0)) (hb43 : oblX2 x 4 < oblX2 x 3)
    (hc34 : oblX6 x 3 < oblX6 x 4)
    (j1 : 0 < ⟪x 2 - x 0, x 2 - x 1⟫) (j2 : 0 < ⟪x 6 - x 4, x 2 - x 1⟫) : DwC0246 x := by
  have T := M4.type24OfFac F
  have hw3 : oblX0 x 3 = 1 := by rw [obl3_a F hd, hw4, hw5]; ring
  have hb5 : 0 < oblX2 x 5 := T.X2_pos (by decide)
  have hc5 : 0 < oblX6 x 5 := T.X6_pos (by decide)
  have hD : 0 < oblX6 x 5 * (oblX2 x 3 - oblX2 x 4) - oblX2 x 5 * (oblX6 x 3 - oblX6 x 4) := by
    nlinarith [mul_pos hc5 (sub_pos.2 hb43), mul_pos hb5 (sub_pos.2 hc34)]
  set D := oblX6 x 5 * (oblX2 x 3 - oblX2 x 4) - oblX2 x 5 * (oblX6 x 3 - oblX6 x 4) with hDdef
  obtain ⟨ε, ⟨e1, e2, e3, e4⟩, hε⟩ :=
    (((dw2_eventually (oblX2 x 3 - oblX2 x 4) (by linarith : 0 < -(oblX6 x 3 - oblX6 x 4))).and
      ((dw2_eventually (-oblX2 x 5) hc5).and
      ((dw2_eventually ⟪x 2 - x 0, x 6 - x 1⟫ j1).and (dw2_eventually ⟪x 6 - x 4, x 6 - x 1⟫ j2)))).and
      self_mem_nhdsWithin).exists
  have hε' : (0:ℝ) < ε := hε
  have hm : (-(oblX6 x 3 - oblX6 x 4) + ε * (oblX2 x 3 - oblX2 x 4)) • (x 5 - x 0) +
      (oblX6 x 5 + ε * -oblX2 x 5) • (x 3 - x 4) = D • (x 2 - x 1) + (ε * D) • (x 6 - x 1) := by
    rw [show x 3 - x 4 = (x 3 - x 0) - (x 4 - x 0) by abel, dw3_e F hw4, dw3_e F hw3, dw3_e F hw5, hDdef]
    module
  refine ⟨_, _, D, ε * D, e1, e2, hD, mul_pos hε' hD, hm, ?_, ?_⟩
  · rw [hm, inner_add_right, real_inner_smul_right, real_inner_smul_right]; nlinarith [mul_pos hD e3]
  · rw [hm, inner_add_right, real_inner_smul_right, real_inner_smul_right]; nlinarith [mul_pos hD e4]

/-! ### The split on `τ = 0` -/

/-- **The double-wall slice `τ = 0`**: on `DwSpec` with `τ = 0`, off `OB1` and without the classes, a lex cell, or
the special position `σ ≤ 0`, `⟪x 2 - x 5, x 1 - x 6⟫ = 0 = ⟪x 6 - x 4, x 1 - x 2⟫` (no use of `¬ DwHorizOK`). -/
theorem dw5_tau0 (F : S0xFac 9 s0x_S24 x) (hO : ¬ H24K.SAT.OB1 x) (hw4 : oblX0 x 4 = 1) (hw5 : oblX0 x 5 = 1)
    (b1 : oblX0 x 4 * oblX6 x 3 - oblX0 x 3 * oblX6 x 4 < 0)
    (b2 : 0 < oblX0 x 3 * oblX2 x 5 - oblX0 x 5 * oblX2 x 3)
    (b3 : 0 < oblX0 x 4 * oblX2 x 5 - oblX0 x 5 * oblX2 x 4)
    (b4 : 0 < oblX0 x 5 * oblX6 x 4 - oblX0 x 4 * oblX6 x 5) {s t : ℝ} (hs : 0 < s) (ht : 0 < t)
    (hst : 1 < s + t) (hd : x 3 - x 0 = s • (x 4 - x 0) + t • (x 5 - x 0)) (hS : DwSpec x)
    (hτ : ⟪x 0 - x 1, x 2 - x 6⟫ = 0) (hc : ¬ DwCls x) :
    Gen.LexAny F ∨ (⟪x 0 - x 1, x 6 - x 1⟫ ≤ 0 ∧ ⟪x 2 - x 5, x 1 - x 6⟫ = 0 ∧ ⟪x 6 - x 4, x 1 - x 2⟫ = 0) := by
  have T := M4.type24OfFac F
  have hw3 : oblX0 x 3 = 1 := by rw [obl3_a F hd, hw4, hw5]; ring
  have ht1 := dw_t_lt_one F hs hd hw4 hw5 b2
  have hb35 : oblX2 x 3 < oblX2 x 5 := by rw [hw3, hw5] at b2; linarith
  have hc34 : oblX6 x 3 < oblX6 x 4 := by rw [hw3, hw4] at b1; linarith
  have hb45 : oblX2 x 4 < oblX2 x 5 := by rw [hw4, hw5] at b3; linarith
  have hc54 : oblX6 x 5 < oblX6 x 4 := by rw [hw4, hw5] at b4; linarith
  have hb4 : 0 < oblX2 x 4 := T.X2_pos (by decide)
  have hc5 : 0 < oblX6 x 5 := T.X6_pos (by decide)
  have e02 : ⟪x 0 - x 1, x 2 - x 1⟫ = ⟪x 0 - x 1, x 6 - x 1⟫ := by
    have : x 2 - x 6 = (x 2 - x 1) - (x 6 - x 1) := by abel
    rw [this, inner_sub_right] at hτ; linarith
  obtain ⟨a6, a2⟩ := dw4_angles F hw4 hw5 hS
  by_cases hσ : 0 < ⟪x 0 - x 1, x 6 - x 1⟫
  · exact Or.inl (dw5_viewA F hw4 hw5 hs ht1 hd b3 b4 hS hτ hσ)
  push Not at hσ
  have hG : 0 < ⟪x 2 - x 1, x 6 - x 1⟫ := by
    by_contra hg; push Not at hg
    exact hO ⟨by linarith, hσ, hg⟩
  have hc53 : oblX6 x 5 < oblX6 x 3 := by
    rw [dw5_c3 F hd]; nlinarith [mul_pos hs (sub_pos.2 hc54),
      mul_pos (sub_pos.2 hst) hc5]
  have hb43 : oblX2 x 4 < oblX2 x 3 := by
    rw [dw5_b3 F hd]; nlinarith [mul_pos ht (sub_pos.2 hb45),
      mul_pos (sub_pos.2 hst) hb4]
  have neg6 : ⟪x 2 - x 5, x 1 - x 6⟫ = -⟪x 2 - x 5, x 6 - x 1⟫ := by
    rw [show x 1 - x 6 = -(x 6 - x 1) by abel, inner_neg_right]
  have neg2 : ⟪x 6 - x 4, x 1 - x 2⟫ = -⟪x 6 - x 4, x 2 - x 1⟫ := by
    rw [show x 1 - x 2 = -(x 2 - x 1) by abel, inner_neg_right]
  rcases lt_trichotomy ⟪x 2 - x 5, x 1 - x 6⟫ 0 with hR | hR | hR
  · refine (hc (Or.inr (Or.inl (dw5_c0652 F hw4 hw5 hd hb35 hc53 ?_ (by linarith))))).elim
    have hG6 : 0 < ⟪x 6 - x 1, x 6 - x 1⟫ := real_inner_self_pos.2 (dw5_g6_ne F)
    rw [show x 6 - x 0 = (x 6 - x 1) - (x 0 - x 1) by abel, inner_sub_left]; linarith
  · rcases lt_trichotomy ⟪x 6 - x 4, x 1 - x 2⟫ 0 with hR' | hR' | hR'
    · refine (hc (Or.inl (dw5_c0246 F hw4 hw5 hd hb43 hc34 ?_ (by linarith)))).elim
      have hG2 : 0 < ⟪x 2 - x 1, x 2 - x 1⟫ := real_inner_self_pos.2 (dw5_g2_ne F)
      rw [show x 2 - x 0 = (x 2 - x 1) - (x 0 - x 1) by abel, inner_sub_left, real_inner_comm (x 2 - x 1)]
      linarith
    · exact Or.inr ⟨hσ, hR, hR'⟩
    · exact Or.inl (dw5_viewB_sym F hw4 hw5 ht hst hd b3 b4 hc34 a2 hG hR')
  · exact Or.inl (dw5_viewB F hw4 hw5 hs hst hd b3 b4 hb35 a6 hG hR)

/-! ### The residue after the slice `τ = 0` -/

/-- `Q45ResWQT` with its double-wall piece inside `σ ≤ 0` and the two ties (codim 4 on the double wall). -/
def Q45ResWQU (F : S0xFac 9 s0x_S24 x) : Prop :=
  Q45ResWQT F ∧ (oblX0 x 4 = 1 → oblX0 x 5 = 1 →
    ⟪x 0 - x 1, x 6 - x 1⟫ ≤ 0 ∧ ⟪x 2 - x 5, x 1 - x 6⟫ = 0 ∧ ⟪x 6 - x 4, x 1 - x 2⟫ = 0)

/-- [OPEN] **The special piece with the double wall reduced to the codim-4 tie stratum, Rupert form**:
`OpenSpecialQT` with `Q45ResWQU` in place of `Q45ResWQT` (equivalent to it: `openSpecialQU_iff_QT`). -/
def OpenSpecialQU : Prop := ∀ (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x), ¬ H24K.SAT.OB1 x →
  1 ≤ oblX0 x 4 → 1 ≤ oblX0 x 5 →
  oblX0 x 4 * oblX6 x 3 - oblX0 x 3 * oblX6 x 4 < 0 →
  0 < oblX0 x 3 * oblX2 x 5 - oblX0 x 5 * oblX2 x 3 →
  0 < oblX0 x 4 * oblX2 x 5 - oblX0 x 5 * oblX2 x 4 →
  0 < oblX0 x 5 * oblX6 x 4 - oblX0 x 4 * oblX6 x 5 →
  Q45ResWQU F → HoleFull x F → IsRupert (univ.image x)

/-- **On the hole, `Q45ResWQT ⊆ Q45ResWQU`** (`dw5_tau0`; `LexAny` is excluded by `HoleFull`). -/
theorem q45ResWQU_of_QT {F : S0xFac 9 s0x_S24 x} (hO : ¬ H24K.SAT.OB1 x)
    (b1 : oblX0 x 4 * oblX6 x 3 - oblX0 x 3 * oblX6 x 4 < 0)
    (b2 : 0 < oblX0 x 3 * oblX2 x 5 - oblX0 x 5 * oblX2 x 3)
    (b3 : 0 < oblX0 x 4 * oblX2 x 5 - oblX0 x 5 * oblX2 x 4)
    (b4 : 0 < oblX0 x 5 * oblX6 x 4 - oblX0 x 4 * oblX6 x 5) (hr : Q45ResWQT F) (hF : HoleFull x F) :
    Q45ResWQU F := by
  refine ⟨hr, fun hw4 hw5 => ?_⟩
  obtain ⟨⟨hP, hQ⟩, hT⟩ := hr
  obtain ⟨hS, -⟩ := hQ hw4 hw5
  have hc := (not_dwHoriz_of_resP hw4 hw5 b1 b2 hP).2
  obtain ⟨s, t, hs, ht, hst, hd, -⟩ := hP
  rcases dw5_tau0 F hO hw4 hw5 b1 b2 b3 b4 hs ht hst hd hS (hT hw4 hw5) hc with hL | h
  · exact (hF.1.2.2.2.1 hL).elim
  · exact h

/-- [PROVED] `OpenSpecialQU ↔ OpenSpecialQT` (`q45ResWQU_of_QT`). -/
theorem openSpecialQU_iff_QT : OpenSpecialQU ↔ OpenSpecialQT :=
  ⟨fun h x F hO h4 h5 b1 b2 b3 b4 hr hF => h x F hO h4 h5 b1 b2 b3 b4 (q45ResWQU_of_QT hO b1 b2 b3 b4 hr hF) hF,
    fun h x F hO h4 h5 b1 b2 b3 b4 hr hF => h x F hO h4 h5 b1 b2 b3 b4 hr.1 hF⟩

/-- [PROVED] Generic + special (double wall reduced to the tie stratum) assemble to `Open24Rupert`. -/
theorem open24Rupert_of_split_QU (h1 : OpenOB1) (h2 : OpenSpecialQU) : Open24Rupert :=
  open24Rupert_of_split_QT h1 (openSpecialQU_iff_QT.1 h2)

/-- [PROVED] `OpenSpecialQU → OpenSpecialQ` (for chains that take `OpenSpecialQ`, e.g. the `E10` cell chain). -/
theorem openSpecialQ_of_QU (h : OpenSpecialQU) : OpenSpecialQ :=
  openSpecialQT_iff_Q.1 (openSpecialQU_iff_QT.1 h)

/-- [PROVED] `OpenSpecialQU → OpenSpecialO`, for the cell chains that take `OpenSpecialO`. -/
theorem openSpecialO_of_QU (h : OpenSpecialQU) : OpenSpecialO :=
  openSpecialO_of_QT (openSpecialQU_iff_QT.1 h)

/-! ### Combined with OSPEC25 (`Q45ResWR2`: the s = 1 / t = 1 tie letters explicit) -/

/-- `Q45ResWR2` (OSPEC25) with the double-wall piece of `Q45ResWQU`. -/
def Q45ResWR2U (F : S0xFac 9 s0x_S24 x) : Prop :=
  Q45ResWR2 F ∧ (oblX0 x 4 = 1 → oblX0 x 5 = 1 →
    ⟪x 0 - x 1, x 6 - x 1⟫ ≤ 0 ∧ ⟪x 2 - x 5, x 1 - x 6⟫ = 0 ∧ ⟪x 6 - x 4, x 1 - x 2⟫ = 0)

/-- [OPEN] **The off-`OB1` Prop after OSPEC24 and OSPEC25**: `OpenSpecialR2` with `Q45ResWR2U` in place of
`Q45ResWR2` (equivalent: `openSpecialR2U_iff_R2`). -/
def OpenSpecialR2U : Prop := ∀ (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x), ¬ H24K.SAT.OB1 x →
  1 ≤ oblX0 x 4 → 1 ≤ oblX0 x 5 →
  oblX0 x 4 * oblX6 x 3 - oblX0 x 3 * oblX6 x 4 < 0 →
  0 < oblX0 x 3 * oblX2 x 5 - oblX0 x 5 * oblX2 x 3 →
  0 < oblX0 x 4 * oblX2 x 5 - oblX0 x 5 * oblX2 x 4 →
  0 < oblX0 x 5 * oblX6 x 4 - oblX0 x 4 * oblX6 x 5 →
  Q45ResWR2U F → HoleFull x F → IsRupert (univ.image x)

/-- [PROVED] `OpenSpecialR2U ↔ OpenSpecialR2` (`q45ResWQU_of_QT` on the `Q45ResWQT` part). -/
theorem openSpecialR2U_iff_R2 : OpenSpecialR2U ↔ OpenSpecialR2 :=
  ⟨fun h x F hO h4 h5 b1 b2 b3 b4 hr hF =>
      h x F hO h4 h5 b1 b2 b3 b4 ⟨hr, (q45ResWQU_of_QT hO b1 b2 b3 b4 hr.1 hF).2⟩ hF,
    fun h x F hO h4 h5 b1 b2 b3 b4 hr hF => h x F hO h4 h5 b1 b2 b3 b4 hr.1 hF⟩

/-- [PROVED] `OpenSpecialR2U → OpenSpecialQU`. -/
theorem openSpecialQU_of_R2U (h : OpenSpecialR2U) : OpenSpecialQU :=
  openSpecialQU_iff_QT.2 (openSpecialR2_iff_QT.1 (openSpecialR2U_iff_R2.1 h))

end DwTau0

end Minimality.T24.OSpec

namespace Minimality.T24.Cell

/-- [PROVED] `CellCoverEmpty L` and `OSpec.OpenSpecialQU` give `Stmt.Open24Rupert` (OSPEC24). -/
theorem open24Rupert_of_cellCoverEmpty_QU {L : List Cell24} (hN : CellCoverEmpty L) (hS : OSpec.OpenSpecialQU) :
    Open24Rupert :=
  OSpec.open24Rupert_of_split_QU (openOB1_of_cellCoverEmpty hN) hS

/-- [PROVED] Headline chain with `cells28` after OSPEC24. -/
theorem open24Rupert_of_cellCoverEmpty28_QU (hN : CellCoverEmpty cells28) (hS : OSpec.OpenSpecialQU) :
    Open24Rupert :=
  open24Rupert_of_cellCoverEmpty_QU hN hS

/-- [PROVED] The `E` cell chain with `OSpec.OpenSpecialQU` (OSPEC24). -/
theorem open24Rupert_of_cellCoverEmptyE28_QU (hN : CellCoverEmptyE cells28) (hS : OSpec.OpenSpecialQU) :
    Open24Rupert :=
  open24Rupert_of_cellCoverEmptyE28_O hN (OSpec.openSpecialO_of_QU hS)

/-- [PROVED] The `EP` cell chain with `OSpec.OpenSpecialQU` (OSPEC24). -/
theorem open24Rupert_of_cellCoverEmptyEP28_QU (hN : CellCoverEmptyEP cells28) (hS : OSpec.OpenSpecialQU) :
    Open24Rupert :=
  open24Rupert_of_cellCoverEmptyEP28_O hN (OSpec.openSpecialO_of_QU hS)

/-- [PROVED] Headline chain after WALL3 and OSPEC24: `CellCoverEmptyE4 cells28` and `OSpec.OpenSpecialQU`. -/
theorem open24Rupert_of_cellCoverEmptyE4_28_QU (hN : CellCoverEmptyE4 cells28) (hS : OSpec.OpenSpecialQU) :
    Open24Rupert :=
  open24Rupert_of_cellCoverEmptyE4_28_O hN (OSpec.openSpecialO_of_QU hS)

/-- [PROVED] Headline chain after WALL5 and OSPEC24: `CellCoverEmptyE10 cells28` and `OSpec.OpenSpecialQU`. -/
theorem open24Rupert_of_cellCoverEmptyE10_28_QU (hN : CellCoverEmptyE10 cells28) (hS : OSpec.OpenSpecialQU) :
    Open24Rupert :=
  open24Rupert_of_cellCoverEmptyE10_28_Q hN (OSpec.openSpecialQ_of_QU hS)

/-- [PROVED] Headline chain with the combined off-`OB1` Prop (OSPEC24 + OSPEC25). -/
theorem open24Rupert_of_cellCoverEmpty28_R2U (hN : CellCoverEmpty cells28) (hS : OSpec.OpenSpecialR2U) :
    Open24Rupert :=
  open24Rupert_of_cellCoverEmpty28_QU hN (OSpec.openSpecialQU_of_R2U hS)

/-- [PROVED] The `E4` cell chain with `OSpec.OpenSpecialR2U`. -/
theorem open24Rupert_of_cellCoverEmptyE4_28_R2U (hN : CellCoverEmptyE4 cells28) (hS : OSpec.OpenSpecialR2U) :
    Open24Rupert :=
  open24Rupert_of_cellCoverEmptyE4_28_QU hN (OSpec.openSpecialQU_of_R2U hS)

/-- [PROVED] The `E10` cell chain with `OSpec.OpenSpecialR2U`. -/
theorem open24Rupert_of_cellCoverEmptyE10_28_R2U (hN : CellCoverEmptyE10 cells28) (hS : OSpec.OpenSpecialR2U) :
    Open24Rupert :=
  open24Rupert_of_cellCoverEmptyE10_28_QU hN (OSpec.openSpecialQU_of_R2U hS)

end Minimality.T24.Cell
