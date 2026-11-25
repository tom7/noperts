module

public import Minimality.Type24HoleAtlas
public import Minimality.Type24HiddenCone
public import Minimality.MonoCorner
public import Minimality.Q4Lex
public import Minimality.Sym24Transport

@[expose] public section

/-!
# Type 24: Lemma RQ-face, the ray cell `0.1.2.5` at the edge view `e_c` (NOCSTRATUM)

Corner frame at vertex `1`: `e_a = x 0 - x 1`, `e_b = x 2 - x 1`, `e_c = x 6 - x 1`, coordinates
`(a_v, b_v, c_v) = (oblX0, oblX2, oblX6) x v`.  If `G_ac = G_bc = 0` and `G_ab < 0` and vertex `3`
projects strictly inside the quadrilateral `(1,0), (0,0), (0,1), (a_5, b_5)` along `e_c`, then
the view `u = -t e_a - t eta0 e_b + e_c` (small `t`, `eta0 = G_aa/|G_ab| + |G_ab|/G_bb`) lies in the open
cell with rim `0.1.2.5` (up `016, 126, 235, 0345`, down `012, 025`), vertex `1` is a strict monotone
corner, so the depths are `RobUni`: `Gen.LexAny F`.

General form (GENREV-RQ-APEX Q1): `cellAt_rq` is the open cell in frame coordinates (octant
`c_a, c_b < 0 < c_c` plus `0345`, `235` up), `lexAny_rqCell` any view of it with `RobUni` depths,
`robUni_rq_of_mono1` the monotone corner at vertex `1` (`<e_a,u><e_b,u> < 0`), and `lexAny_rqWall` the
**wall lemma**: `0345` and `235` face up at `W = capView x 0 (-eta) 1` and `<e_a, W> > 0 > <e_b, W>`
(no OB1, no sign hypothesis on `G`).  Lemma RQ-face is its corollary (small `eta`).  Data: the wall form
closes 46-64 % of the no-C sets versus 40-44 % for the face form.  `RQWall F` / `RQWallTwin F` bundle the
wall hypotheses; the ray form `lexAny_rqRay` is void on data and stays in scratch.
-/

set_option autoImplicit false

open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21 Minimality.T24.SAT Minimality.RimCell Minimality.T24.HC

namespace Minimality.T24.RQ

/-! ## A real lemma: the up-facing of `0345` and `235` at the ray -/

theorem rq_up (a3 b3 a5 b5 c3 c5 p A B C : ℝ) (ha3 : 0 < a3) (hb3 : 0 < b3) (hc3 : 0 < c3)
    (hq1 : 0 < a3 * (b5 - 1) + a5 * (1 - b3))
    (hq2 : 0 < b3 * (a5 - 1) + b5 * (1 - a3)) (hw : (a3 + b3 - 1) * c5 < (a5 + b5 - 1) * c3)
    (f1 : p < 0) (f0 : p + A ≤ 0) (f2 : p + B ≤ 0) (f02 : (p + A) + (p + B) < 0)
    (f5 : p + a5 * A + b5 * B + c5 * C ≤ 0) (f3 : p + a3 * A + b3 * B + c3 * C = 0) : 0 < C := by
  rcases le_or_gt (a3 + b3) 1 with h | h
  · have e : c3 * C = -((1 - a3 - b3) * p + a3 * (p + A) + b3 * (p + B)) := by linarith
    have h1 : 0 ≤ (1 - a3 - b3) * (-p) := mul_nonneg (by linarith) (by linarith)
    have h2 : a3 * (p + A) + b3 * (p + B) < 0 := by
      rcases lt_or_ge (p + A) 0 with h0 | h0
      · nlinarith [mul_neg_of_pos_of_neg ha3 h0, mul_nonpos_of_nonneg_of_nonpos hb3.le f2]
      · have : p + A = 0 := le_antisymm f0 h0
        have : p + B < 0 := by linarith
        nlinarith [mul_neg_of_pos_of_neg hb3 this]
    have : 0 < c3 * C := by nlinarith
    exact pos_of_mul_pos_right this hc3.le
  · have hw' : 0 < (a5 + b5 - 1) * c3 - (a3 + b3 - 1) * c5 := by linarith
    have e : ((a5 + b5 - 1) * c3 - (a3 + b3 - 1) * c5) * C =
        -((a3 * (b5 - 1) + a5 * (1 - b3)) * (p + A) + (b3 * (a5 - 1) + b5 * (1 - a3)) * (p + B)
          + (a3 + b3 - 1) * (p + a5 * A + b5 * B + c5 * C)) := by
      linear_combination (a5 + b5 - 1) * f3
    have h2 : (a3 * (b5 - 1) + a5 * (1 - b3)) * (p + A) + (b3 * (a5 - 1) + b5 * (1 - a3)) * (p + B)
        < 0 := by
      rcases lt_or_ge (p + A) 0 with h0 | h0
      · nlinarith [mul_neg_of_pos_of_neg hq1 h0, mul_nonpos_of_nonneg_of_nonpos hq2.le f2]
      · have h00 : p + A = 0 := le_antisymm f0 h0
        have : p + B < 0 := by linarith
        nlinarith [mul_neg_of_pos_of_neg hq2 this]
    have h3 : (a3 + b3 - 1) * (p + a5 * A + b5 * B + c5 * C) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by linarith) f5
    have : 0 < ((a5 + b5 - 1) * c3 - (a3 + b3 - 1) * c5) * C := by rw [e]; linarith
    exact pos_of_mul_pos_right this hw'.le

/-! ## Facet values along the corner frame -/

variable {x : Fin 7 → ℝ³}

/-- The rim `0 1 2 5`. -/
def cRQ : ZMod 4 → Fin 7 := ![0, 1, 2, 5]
/-- Up facets `016, 126, 235, 0345`. -/
def URQ : Finset (Fin 9) := {1, 5, 6, 3}
/-- Down facets `012, 025`. -/
def DnRQ : Finset (Fin 9) := {0, 2}

theorem cycRQ : S0xCycUD s0x_S24 cRQ URQ DnRQ := by decide
theorem injRQ : Function.Injective cRQ := by
  intro i j h; fin_cases i <;> fin_cases j <;> first | rfl | exact absurd h (by decide)

theorem exists_small (K3 K6 C3 C6 : ℝ) (hK3 : 0 ≤ K3) (hK6 : 0 ≤ K6) (h3 : 0 < C3) (h6 : 0 < C6) :
    ∃ t : ℝ, 0 < t ∧ t * K3 < C3 ∧ t * K6 < C6 := by
  refine ⟨min (C3 / (K3 + 1)) (C6 / (K6 + 1)), lt_min (by positivity) (by positivity), ?_, ?_⟩
  · have h := min_le_left (C3 / (K3 + 1)) (C6 / (K6 + 1))
    have h' : min (C3 / (K3 + 1)) (C6 / (K6 + 1)) * (K3 + 1) ≤ C3 := by
      calc _ ≤ C3 / (K3 + 1) * (K3 + 1) := by gcongr
        _ = C3 := by field_simp
    have : 0 < min (C3 / (K3 + 1)) (C6 / (K6 + 1)) := lt_min (by positivity) (by positivity)
    nlinarith
  · have h := min_le_right (C3 / (K3 + 1)) (C6 / (K6 + 1))
    have h' : min (C3 / (K3 + 1)) (C6 / (K6 + 1)) * (K6 + 1) ≤ C6 := by
      calc _ ≤ C6 / (K6 + 1) * (K6 + 1) := by gcongr
        _ = C6 := by field_simp
    have : 0 < min (C3 / (K3 + 1)) (C6 / (K6 + 1)) := lt_min (by positivity) (by positivity)
    nlinarith

open Minimality.T24.M4 in
/-- `0345` and `235` face up at the ray `e_c`: `⟪N, e_c⟫ > 0`. -/
theorem up_signs (F : S0xFac 9 s0x_S24 x) (hw5 : 0 < omega5 x)
    (h1 : 0 < oblX0 x 3 * (oblX2 x 5 - 1) + oblX0 x 5 * (1 - oblX2 x 3))
    (h2 : 0 < oblX2 x 3 * (oblX0 x 5 - 1) + oblX2 x 5 * (1 - oblX0 x 3)) :
    0 < F.f 3 (x 6) - F.f 3 (x 1) ∧ 0 < F.f 6 (x 6) - F.f 6 (x 1) := by
  have T := type24OfFac F
  have ha3 : 0 < oblX0 x 3 := T.X0_pos (v := 3) (by decide)
  have hb3 : 0 < oblX2 x 3 := T.X2_pos (v := 3) (by decide)
  have hc3 : 0 < oblX6 x 3 := T.X6_pos (v := 3) (by decide)
  have hc5 : 0 < oblX6 x 5 := T.X6_pos (v := 5) (by decide)
  have hs : oblX0 x 5 + oblX2 x 5 - 1 = omega5 x * oblX6 x 5 := by
    dsimp [omega5]; field_simp [hc5.ne']
  have hspos : 0 < oblX0 x 5 + oblX2 x 5 - 1 := by rw [hs]; positivity
  have hp2 : F.f 2 (x 1) < 0 := F.neg 2 1 (by decide)
  have e23 := fac_eval F 2 3
  have e25 := fac_eval F 2 5
  rw [F.zero 2 5 (by decide), F.zero 2 0 (by decide), F.zero 2 2 (by decide)] at e25
  have n23 := F.neg 2 3 (by decide)
  rw [F.zero 2 0 (by decide), F.zero 2 2 (by decide)] at e23
  have hw : (oblX0 x 3 + oblX2 x 3 - 1) * oblX6 x 5 < (oblX0 x 5 + oblX2 x 5 - 1) * oblX6 x 3 := by
    have e1 : oblX6 x 5 * (F.f 2 (x 6) - F.f 2 (x 1)) = F.f 2 (x 1) * (oblX0 x 5 + oblX2 x 5 - 1) := by
      linear_combination -e25
    have e2 : F.f 2 (x 3) * oblX6 x 5 = F.f 2 (x 1) *
        ((1 - oblX0 x 3 - oblX2 x 3) * oblX6 x 5 + oblX6 x 3 * (oblX0 x 5 + oblX2 x 5 - 1)) := by
      linear_combination oblX6 x 5 * e23 + oblX6 x 3 * e1
    have : F.f 2 (x 3) * oblX6 x 5 < 0 := mul_neg_of_neg_of_pos n23 hc5
    rw [e2] at this
    have := (mul_neg_iff.1 this)
    rcases this with ⟨_, h⟩ | ⟨h, _⟩
    · linarith
    · linarith
  have key : ∀ t : Fin 9, (3 ∈ s0x_S24 t) → F.f t (x 1) < 0 →
      F.f t (x 0) ≤ 0 → F.f t (x 2) ≤ 0 → F.f t (x 0) + F.f t (x 2) < 0 → F.f t (x 5) ≤ 0 →
      0 < F.f t (x 6) - F.f t (x 1) := by
    intro t ht f1 f0 f2 f02 f5
    have e3 := fac_eval F t 3
    rw [F.zero t 3 ht] at e3
    have e5 := fac_eval F t 5
    refine rq_up (oblX0 x 3) (oblX2 x 3) (oblX0 x 5) (oblX2 x 5) (oblX6 x 3) (oblX6 x 5)
      (F.f t (x 1)) (F.f t (x 0) - F.f t (x 1)) (F.f t (x 2) - F.f t (x 1))
      (F.f t (x 6) - F.f t (x 1)) ha3 hb3 hc3 h1 h2 hw f1 (by linarith) (by linarith)
      (by linarith) (by linarith) (by linarith)
  refine ⟨key 3 (by decide) (F.neg 3 1 (by decide)) (by rw [F.zero 3 0 (by decide)])
    (F.neg 3 2 (by decide)).le (by rw [F.zero 3 0 (by decide)]; linarith [F.neg 3 2 (by decide)])
    (by rw [F.zero 3 5 (by decide)]), key 6 (by decide) (F.neg 6 1 (by decide))
    (F.neg 6 0 (by decide)).le (by rw [F.zero 6 2 (by decide)]) 
    (by rw [F.zero 6 2 (by decide)]; linarith [F.neg 6 0 (by decide)])
    (by rw [F.zero 6 5 (by decide)])⟩

theorem inner_capView (F : S0xFac 9 s0x_S24 x) (t : Fin 9) (ca cb cc : ℝ) :
    ⟪F.N t, capView x ca cb cc⟫ =
      ca * (F.f t (x 0) - F.f t (x 1)) + cb * (F.f t (x 2) - F.f t (x 1)) +
        cc * (F.f t (x 6) - F.f t (x 1)) := by
  simp only [capView, inner_add_right, real_inner_smul_right, F.inner_sub]

/-- `025` faces down at `e_c` when `ω5 > 0` (extracted from `lexAny_rqFace`). -/
theorem f2_c_neg (F : S0xFac 9 s0x_S24 x) (hw5 : 0 < omega5 x) :
    F.f 2 (x 6) - F.f 2 (x 1) < 0 := by
  have hp2 := F.neg 2 1 (by decide)
  have hc5 : 0 < oblX6 x 5 := (Minimality.T24.M4.type24OfFac F).X6_pos (v := 5) (by decide)
  have hs : oblX0 x 5 + oblX2 x 5 - 1 = omega5 x * oblX6 x 5 := by
    dsimp [omega5]; field_simp [hc5.ne']
  have e25 := Minimality.T24.M4.fac_eval F 2 5
  rw [F.zero 2 5 (by decide), F.zero 2 0 (by decide), F.zero 2 2 (by decide)] at e25
  have e1 : oblX6 x 5 * (F.f 2 (x 6) - F.f 2 (x 1)) =
      F.f 2 (x 1) * (omega5 x * oblX6 x 5) := by linear_combination -e25 + F.f 2 (x 1) * hs
  have : oblX6 x 5 * (F.f 2 (x 6) - F.f 2 (x 1)) < 0 := by
    rw [e1]; exact mul_neg_of_neg_of_pos hp2 (by positivity)
  exact neg_of_mul_neg_right this hc5.le

/-- The open cell of rim `0.1.2.5` in frame coordinates: the octant `c_a, c_b < 0 < c_c` (facets `126, 016, 012`),
`025` automatic from `ω5 > 0`, and the two shape conditions `0345`, `235` up. -/
theorem cellAt_rq (F : S0xFac 9 s0x_S24 x) (hw5 : 0 < omega5 x) {ca cb cc : ℝ}
    (hca : ca < 0) (hcb : cb < 0) (hcc : 0 < cc)
    (h3 : 0 < ⟪F.N 3, capView x ca cb cc⟫) (h6 : 0 < ⟪F.N 6, capView x ca cb cc⟫) :
    CellAt F URQ DnRQ (capView x ca cb cc) := by
  have hC2 := f2_c_neg F hw5
  constructor
  · intro s hs
    simp only [URQ, Finset.mem_insert, Finset.mem_singleton] at hs
    rcases hs with rfl | rfl | rfl | rfl
    · rw [inner_capView, F.zero 1 0 (by decide), F.zero 1 1 (by decide), F.zero 1 6 (by decide)]
      have := F.neg 1 2 (by decide); nlinarith
    · rw [inner_capView, F.zero 5 1 (by decide), F.zero 5 2 (by decide), F.zero 5 6 (by decide)]
      have := F.neg 5 0 (by decide); nlinarith
    · exact h6
    · exact h3
  · intro s hs
    simp only [DnRQ, Finset.mem_insert, Finset.mem_singleton] at hs
    rcases hs with rfl | rfl
    · rw [inner_capView, F.zero 0 0 (by decide), F.zero 0 1 (by decide), F.zero 0 2 (by decide)]
      have := F.neg 0 6 (by decide); nlinarith
    · rw [inner_capView, F.zero 2 0 (by decide), F.zero 2 2 (by decide)]
      have := F.neg 2 1 (by decide); nlinarith

/-- **Lemma RQ (general, one view).**  Any view of the open cell `0.1.2.5` at which the four rim depths are
`RobUni` (for `k = 4`: some strict monotone corner) gives `LexAny`.  Covers the face, wall and ray regimes. -/
theorem lexAny_rqCell (F : S0xFac 9 s0x_S24 x) (hw5 : 0 < omega5 x) {ca cb cc : ℝ}
    (hca : ca < 0) (hcb : cb < 0) (hcc : 0 < cc)
    (h3 : 0 < ⟪F.N 3, capView x ca cb cc⟫) (h6 : 0 < ⟪F.N 6, capView x ca cb cc⟫)
    (hz : RobUni (fun i => ⟪x (cRQ i), capView x ca cb cc⟫)) : Gen.LexAny F := by
  have hc := cellAt_rq F hw5 hca hcb hcc h3 h6
  exact Minimality.GenRev.lexAny_of_closedCell (by norm_num) F injRQ cycRQ hc hc.cellLe hz

/-- Monotone corner at vertex `1` in metric form: `⟪e_a, u⟫ ⟪e_b, u⟫ < 0`. -/
theorem robUni_rq_of_mono1 (u : ℝ³) (h : ⟪x 0 - x 1, u⟫ * ⟪x 2 - x 1, u⟫ < 0) :
    RobUni (fun i => ⟪x (cRQ i), u⟫) := by
  refine Minimality.GenPlus.robUni_of_monoCorners (by norm_num) {1} (by simp) ?_
  intro v hv
  rw [Finset.mem_singleton] at hv
  subst hv
  have e1 : ⟪x (cRQ 1), u⟫ - ⟪x (cRQ (1 - 1)), u⟫ = -⟪x 0 - x 1, u⟫ := by
    simp only [cRQ]
    have : (1 : ZMod 4) - 1 = 0 := by decide
    rw [this]; simp [← inner_sub_left]
    rw [← inner_neg_left, neg_sub]
  have e2 : ⟪x (cRQ (1 + 1)), u⟫ - ⟪x (cRQ 1), u⟫ = ⟪x 2 - x 1, u⟫ := by
    simp only [cRQ]
    have : (1 : ZMod 4) + 1 = 2 := by decide
    rw [this]; simp [← inner_sub_left]
  rw [e1, e2]; nlinarith

/-- **Lemma RQ-wall** (door at the wall vertex `W = e_c - η e_b` of facet `126`, off the face).  If `0345`, `235`
face up at `W` and vertex `1` is a strict monotone corner there, `⟪e_a, W⟫ > 0 > ⟪e_b, W⟫` (for `G ≤ 0`:
`|G_ac| < η |G_ab|`), then `LexAny`.  The view `W - ε e_a` (small `ε`) is a strict cell point. -/
theorem lexAny_rqWall (F : S0xFac 9 s0x_S24 x) (hw5 : 0 < omega5 x) {η : ℝ} (hη : 0 < η)
    (h3 : 0 < ⟪F.N 3, capView x 0 (-η) 1⟫) (h6 : 0 < ⟪F.N 6, capView x 0 (-η) 1⟫)
    (ha : 0 < ⟪x 0 - x 1, capView x 0 (-η) 1⟫) (hb : ⟪x 2 - x 1, capView x 0 (-η) 1⟫ < 0) :
    Gen.LexAny F := by
  have hv : ∀ (w : ℝ³) (ε : ℝ), ⟪w, capView x (-ε) (-η) 1⟫ = ⟪w, capView x 0 (-η) 1⟫ - ε * ⟪w, x 0 - x 1⟫ := by
    intro w ε; simp only [capView, inner_add_right, real_inner_smul_right]; ring
  obtain ⟨t1, ht1, h1a, h1b⟩ := exists_small |⟪F.N 3, x 0 - x 1⟫| |⟪F.N 6, x 0 - x 1⟫| _ _
    (abs_nonneg _) (abs_nonneg _) h3 h6
  obtain ⟨t2, ht2, h2a, h2b⟩ := exists_small |⟪x 0 - x 1, x 0 - x 1⟫| |⟪x 2 - x 1, x 0 - x 1⟫| _ _
    (abs_nonneg _) (abs_nonneg _) ha (neg_pos.2 hb)
  set ε := min t1 t2 with hεdef
  have hε : 0 < ε := lt_min ht1 ht2
  have small : ∀ (t A B : ℝ), ε ≤ t → t * |A| < B → 0 < B - ε * A := by
    intro t A B hle h
    have : ε * A ≤ t * |A| :=
      (mul_le_mul_of_nonneg_left (le_abs_self A) hε.le).trans (mul_le_mul_of_nonneg_right hle (abs_nonneg A))
    linarith
  have hle1 : ε ≤ t1 := min_le_left _ _
  have hle2 : ε ≤ t2 := min_le_right _ _
  refine lexAny_rqCell F hw5 (ca := -ε) (cb := -η) (cc := 1) (by linarith) (by linarith) one_pos ?_ ?_ ?_
  · rw [hv]; exact small _ _ _ hle1 h1a
  · rw [hv]; exact small _ _ _ hle1 h1b
  · refine robUni_rq_of_mono1 _ ?_
    have p1 : 0 < ⟪x 0 - x 1, capView x (-ε) (-η) 1⟫ := by rw [hv]; exact small _ _ _ hle2 h2a
    have p2 : ⟪x 2 - x 1, capView x (-ε) (-η) 1⟫ < 0 := by
      rw [hv]
      have := small _ (-⟪x 2 - x 1, x 0 - x 1⟫) _ hle2 (by rwa [abs_neg])
      linarith
    nlinarith

/-- **Lemma RQ-face**, a corollary of `lexAny_rqWall` (small `η`; no `G_aa` or `η0` needed). -/
theorem lexAny_rqFace (F : S0xFac 9 s0x_S24 x) (hw5 : 0 < omega5 x)
    (hac : ⟪x 0 - x 1, x 6 - x 1⟫ = 0) (hbc : ⟪x 2 - x 1, x 6 - x 1⟫ = 0)
    (hab : ⟪x 0 - x 1, x 2 - x 1⟫ < 0)
    (h1 : 0 < oblX0 x 3 * (oblX2 x 5 - 1) + oblX0 x 5 * (1 - oblX2 x 3))
    (h2 : 0 < oblX2 x 3 * (oblX0 x 5 - 1) + oblX2 x 5 * (1 - oblX0 x 3)) :
    Gen.LexAny F := by
  obtain ⟨hC3, hC6⟩ := up_signs F hw5 h1 h2
  have hinj : Function.Injective x := Minimality.H24.SAT.inj_of_fac F
  have hGb : 0 < ⟪x 2 - x 1, x 2 - x 1⟫ :=
    real_inner_self_pos.2 (sub_ne_zero.2 (fun h => by simpa using hinj h))
  obtain ⟨η, hη, h3, h6⟩ := exists_small |F.f 3 (x 2) - F.f 3 (x 1)| |F.f 6 (x 2) - F.f 6 (x 1)| _ _
    (abs_nonneg _) (abs_nonneg _) hC3 hC6
  have small : ∀ (A B : ℝ), η * |A| < B → 0 < -η * A + B := by
    intro A B h
    have : η * A ≤ η * |A| := mul_le_mul_of_nonneg_left (le_abs_self A) hη.le
    linarith
  refine lexAny_rqWall F hw5 hη ?_ ?_ ?_ ?_
  · rw [inner_capView]; have := small _ _ h3; linarith
  · rw [inner_capView]; have := small _ _ h6; linarith
  · simp only [capView, inner_add_right, real_inner_smul_right, hac]
    have : ⟪x 0 - x 1, x 2 - x 1⟫ * η < 0 := mul_neg_of_neg_of_pos hab hη
    linarith
  · simp only [capView, inner_add_right, real_inner_smul_right, hbc]
    nlinarith

/-- The hypotheses of Lemma RQ-face (ray `e_c`, rim `0.1.2.5`), in the corner frame at vertex `1`:
`ω5 > 0` (implied by `CbarIn`), `G_ac = G_bc = 0`, `G_ab < 0`, and vertex `3` strictly inside the
quadrilateral `(1,0), (0,0), (0,1), (a_5, b_5)` in `(a, b)` coordinates (`a_3, b_3 > 0` automatic;
the other two edges are the two inequalities).  Vertex `4` is not used. -/
def RQFace (x : Fin 7 → ℝ³) : Prop :=
  0 < omega5 x ∧ ⟪x 0 - x 1, x 6 - x 1⟫ = 0 ∧ ⟪x 2 - x 1, x 6 - x 1⟫ = 0 ∧
    ⟪x 0 - x 1, x 2 - x 1⟫ < 0 ∧
    0 < oblX0 x 3 * (oblX2 x 5 - 1) + oblX0 x 5 * (1 - oblX2 x 3) ∧
    0 < oblX2 x 3 * (oblX0 x 5 - 1) + oblX2 x 5 * (1 - oblX0 x 3)

theorem lexAny_of_rqFace (F : S0xFac 9 s0x_S24 x) (h : RQFace x) : Gen.LexAny F :=
  lexAny_rqFace F h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2

/-- The twin (ray `e_b`, rim `0.1.6.4`): Lemma RQ-face for `x ∘ pi24`, `pi24 = (2 6)(4 5)`. -/
def RQFaceTwin (x : Fin 7 → ℝ³) : Prop := RQFace (x ∘ Minimality.T24.Sym.pi24)

theorem lexAny_of_rqFaceTwin (F : S0xFac 9 s0x_S24 x) (h : RQFaceTwin x) : Gen.LexAny F :=
  Minimality.T24.Sym.lexAny_sym F (lexAny_of_rqFace (Minimality.T24.Sym.sym24 F) h)

/-- Atlas contrapositive: on the hole the RQ-face criterion fails. -/
theorem holeLeaf_not_rqFace {F : S0xFac 9 s0x_S24 x} (h : T24.HoleLeaf x F) : ¬ RQFace x :=
  fun hr => (T24.holeLeaf_not_lexAny h) (lexAny_of_rqFace F hr)

theorem holeLeaf_not_rqFaceTwin {F : S0xFac 9 s0x_S24 x} (h : T24.HoleLeaf x F) : ¬ RQFaceTwin x :=
  fun hr => (T24.holeLeaf_not_lexAny h) (lexAny_of_rqFaceTwin F hr)

/-- The hypotheses of the wall lemma: `omega5 > 0` and some `eta > 0` with `0345`, `235` up at
`W = capView x 0 (-eta) 1`, `<e_a, W> > 0 > <e_b, W>`. -/
def RQWall (F : S0xFac 9 s0x_S24 x) : Prop :=
  0 < omega5 x ∧ ∃ η : ℝ, 0 < η ∧ 0 < ⟪F.N 3, capView x 0 (-η) 1⟫ ∧ 0 < ⟪F.N 6, capView x 0 (-η) 1⟫ ∧
    0 < ⟪x 0 - x 1, capView x 0 (-η) 1⟫ ∧ ⟪x 2 - x 1, capView x 0 (-η) 1⟫ < 0

theorem lexAny_of_rqWall (F : S0xFac 9 s0x_S24 x) (h : RQWall F) : Gen.LexAny F := by
  obtain ⟨hw, η, hη, h3, h6, ha, hb⟩ := h
  exact lexAny_rqWall F hw hη h3 h6 ha hb

/-- The twin (ray `e_b`, rim `0.1.6.4`): the wall lemma for `x ∘ pi24`. -/
def RQWallTwin (F : S0xFac 9 s0x_S24 x) : Prop := RQWall (Minimality.T24.Sym.sym24 F)

theorem lexAny_of_rqWallTwin (F : S0xFac 9 s0x_S24 x) (h : RQWallTwin F) : Gen.LexAny F :=
  Minimality.T24.Sym.lexAny_sym F (lexAny_of_rqWall (Minimality.T24.Sym.sym24 F) h)

theorem holeLeaf_not_rqWall {F : S0xFac 9 s0x_S24 x} (h : T24.HoleLeaf x F) : ¬ RQWall F :=
  fun hr => (T24.holeLeaf_not_lexAny h) (lexAny_of_rqWall F hr)

theorem holeLeaf_not_rqWallTwin {F : S0xFac 9 s0x_S24 x} (h : T24.HoleLeaf x F) : ¬ RQWallTwin F :=
  fun hr => (T24.holeLeaf_not_lexAny h) (lexAny_of_rqWallTwin F hr)

end Minimality.T24.RQ
