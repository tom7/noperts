module

public import Minimality.Type24OffOB1Res

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21 Minimality.FaceChord Minimality.T24.SAT Minimality.T24.Stmt Minimality.T24.Q45
  Minimality.T24.Reg Minimality.T24.A19

/-!
# Type 24 off `OB1`: the Bs view (job OSPEC10, nopert229 notes/OPENSPECIAL-STRATEGY.md)

The 3-level lex view `(x 0 - x 4, x 5 - x 0, -N3)` is a lex cell with rim `0 5 2 6` (`235` down) or `0 5 3 2 6` (`235`
up) as soon as its rim is `RobUniLex` (`lexAny_of_bsView`).  It is the K0 view `(x 0 - x 4, x 0 - x 5, N3)` with the
second and third levels reversed, so the facets edge-on at level 1 (`0345`, `046`) fall the other way.  Facet signs:
`012 016 025` up and `346` down at level 1, `046` down at level 2 (`f4(x 5) < 0`), `0345` down at level 3, all automatic;
`126` up off the wall `a4 = 1` (level 1) and ON the double wall `a4 = a5 = 1` (level 3: there `126 ∥ 0345`, so
`⟪N5, N3⟫ < 0`, `bs_n53_neg`, a Gram identity); `235` down for `t < 1`, up for `t ≥ 1` (`k0_f6`; level 2 at `t = 1`);
`236` down at level 1 for `t ≤ 1`: `s (f7(x 4) - f7(x 0)) = (t - 1) f7(x 0) - t f7(x 5)` (`bs_f7`), and on the wall
`a4 = 1`.  Not derived: the rim's `RobUniLex` (`BsRU`), and `236` for `t > 1` off the wall.

It closes the small residue pieces of `Q45ResWF` with known views: the three `Bs1` points (`s = 1`; two on the
tie `TBs1`) and, with its mirror `(x 0 - x 5, x 4 - x 0, -N3)` (`π24`), the five double-wall points.  The cut
`Q45ResWB` / `OpenSpecialB` removes every point where either view's conditions hold (`q45_resB_local`), on every piece,
and applies the face-on J0 views `JFaceOK` (OSPEC9) to every piece too: they close both `B2T` points (pattern B).
-/

namespace Minimality.T24.OSpec

variable {x : Fin 7 → ℝ³}

section Bs
open Minimality.LexCell

/-- Rim `0 5 2 6` (facets `012 016 025 126` up, `0345 046 235 236 346` down). -/
def rimBA : ZMod 4 → Fin 7 := ![0, 5, 2, 6]
def UBA : Finset (Fin 9) := {0, 1, 2, 5}
def DnBA : Finset (Fin 9) := {3, 4, 6, 7, 8}
/-- Rim `0 5 3 2 6` (facets `012 016 025 126 235` up, `0345 046 236 346` down). -/
def rimBB : ZMod 5 → Fin 7 := ![0, 5, 3, 2, 6]
def UBB : Finset (Fin 9) := {0, 1, 2, 5, 6}
def DnBB : Finset (Fin 9) := {3, 4, 7, 8}

theorem rimBA_cyc : S0xCycUD s0x_S24 rimBA UBA DnBA := by decide
theorem rimBA_inj : Function.Injective rimBA := by decide
theorem rimBB_cyc : S0xCycUD s0x_S24 rimBB UBB DnBB := by decide
theorem rimBB_inj : Function.Injective rimBB := by decide

/-- Facet `t` is up in the Bs view `(x 0 - x 4, x 5 - x 0, -N3)`. -/
def BsUp {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (t : Fin 9) : Prop :=
  LexPos3 ⟪F.N t, x 0 - x 4⟫ ⟪F.N t, x 5 - x 0⟫ ⟪F.N t, -F.N 3⟫
/-- Facet `t` is down in the Bs view. -/
def BsDn {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (t : Fin 9) : Prop :=
  LexPos3 (-⟪F.N t, x 0 - x 4⟫) (-⟪F.N t, x 5 - x 0⟫) (-⟪F.N t, -F.N 3⟫)

/-- Lex depth triples of a rim in the Bs view. -/
noncomputable def bsZ {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) {k : ℕ} (c : ZMod k → Fin 7) :
    ZMod k → ℝ × ℝ × ℝ :=
  fun i => (⟪x (c i), x 0 - x 4⟫, ⟪x (c i), x 5 - x 0⟫, ⟪x (c i), -F.N 3⟫)

/-- **The Bs view condition**: `126` up, `236` down, and `235` down with the rim `0 5 2 6` `RobUniLex`, or `235` up
with the rim `0 5 3 2 6` `RobUniLex` (the other facet signs are automatic). -/
def BsViewOK {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) : Prop :=
  BsUp F 5 ∧ BsDn F 7 ∧ ((BsDn F 6 ∧ RobUniLex (bsZ F rimBA)) ∨ (BsUp F 6 ∧ RobUniLex (bsZ F rimBB)))

/-- A facet through `0` but not `4` is up (level 1). -/
theorem bs_up_of_mem (F : S0xFac 9 s0x_S24 x) (t : Fin 9) (h0 : (0 : Fin 7) ∈ s0x_S24 t)
    (h4 : (4 : Fin 7) ∉ s0x_S24 t) : BsUp F t := by
  left
  rw [F.inner_sub t 0 4, F.zero t 0 h0]
  linarith [F.neg t 4 h4]

/-- `346` is down (level 1). -/
theorem bs_dn8 (F : S0xFac 9 s0x_S24 x) : BsDn F 8 := by
  left
  rw [F.inner_sub 8 0 4, F.zero 8 4 (by decide)]
  linarith [F.neg 8 0 (by decide)]

/-- `046` is down (level 2: `f4(x 5) < 0`). -/
theorem bs_dn4 (F : S0xFac 9 s0x_S24 x) : BsDn F 4 := by
  right
  refine ⟨?_, Or.inl ?_⟩
  · rw [F.inner_sub 4 0 4, F.zero 4 0 (by decide), F.zero 4 4 (by decide)]; ring
  · rw [F.inner_sub 4 5 0, F.zero 4 0 (by decide)]
    linarith [F.neg 4 5 (by decide)]

/-- `0345` is down (level 3: `|N3|² > 0`). -/
theorem bs_dn3 (F : S0xFac 9 s0x_S24 x) : BsDn F 3 := by
  right
  refine ⟨?_, Or.inr ⟨?_, ?_⟩⟩
  · rw [F.inner_sub 3 0 4, F.zero 3 0 (by decide), F.zero 3 4 (by decide)]; ring
  · rw [F.inner_sub 3 5 0, F.zero 3 0 (by decide), F.zero 3 5 (by decide)]; ring
  · rw [inner_neg_right, neg_neg]; exact real_inner_self_pos.mpr (n3_ne_zero F)

/-- **The Bs view is a lex cell** (either rim). -/
theorem lexAny_of_bsView (F : S0xFac 9 s0x_S24 x) (h : BsViewOK F) : Gen.LexAny F := by
  obtain ⟨h5, h7, ⟨h6, hR⟩ | ⟨h6, hR⟩⟩ := h
  · refine ⟨4, inferInstance, rimBA, UBA, DnBA, x 0 - x 4, x 5 - x 0, -F.N 3, le_refl _, rimBA_inj,
      rimBA_cyc, ?_, ?_, hR⟩
    · intro t ht
      simp only [UBA, Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl | rfl | rfl
      exacts [bs_up_of_mem F 0 (by decide) (by decide), bs_up_of_mem F 1 (by decide) (by decide),
        bs_up_of_mem F 2 (by decide) (by decide), h5]
    · intro t ht
      simp only [DnBA, Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl | rfl | rfl | rfl
      exacts [bs_dn3 F, bs_dn4 F, h6, h7, bs_dn8 F]
  · refine ⟨5, inferInstance, rimBB, UBB, DnBB, x 0 - x 4, x 5 - x 0, -F.N 3, by norm_num, rimBB_inj,
      rimBB_cyc, ?_, ?_, hR⟩
    · intro t ht
      simp only [UBB, Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl | rfl | rfl | rfl
      exacts [bs_up_of_mem F 0 (by decide) (by decide), bs_up_of_mem F 1 (by decide) (by decide),
        bs_up_of_mem F 2 (by decide) (by decide), h5, h6]
    · intro t ht
      simp only [DnBB, Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl | rfl | rfl
      exacts [bs_dn3 F, bs_dn4 F, h7, bs_dn8 F]

/-- **The mirror Bs view** (`π = (2 6)(4 5)`): the view `(x 0 - x 5, x 4 - x 0, -N3)` of `x`. -/
theorem lexAny_of_bsView_sym (F : S0xFac 9 s0x_S24 x) (h : BsViewOK (Sym.sym24 F)) : Gen.LexAny F :=
  Sym.lexAny_sym F (lexAny_of_bsView (Sym.sym24 F) h)

/-! ### The facet signs from the branch hypotheses -/

/-- `f5` in oblique coordinates: `f5(x v) = a_v f5(x 0)` (`126` through the frame vertices `1 2 6`). -/
theorem bs_f5_obl (F : S0xFac 9 s0x_S24 x) (v : Fin 7) : F.f 5 (x v) = oblX0 x v * F.f 5 (x 0) := by
  rw [M4.fac_eval F 5 v, F.zero 5 1 (by decide), F.zero 5 2 (by decide), F.zero 5 6 (by decide)]
  ring

/-- `126` is up off the wall `a4 = 1` (level 1). -/
theorem bs_up5 (F : S0xFac 9 s0x_S24 x) (h4 : 1 < oblX0 x 4) : BsUp F 5 := by
  have e := (sgn_a F 4 h4.le).resolve_right h4.ne'
  left
  rw [← neg_sub, inner_neg_right]; linarith

/-- **On the double wall `a4 = a5 = 1` the faces `126` and `0345` are parallel and opposite**: `⟪N5, N3⟫ < 0`.
Gram identities along `u = x 4 - x 0`, `v = x 5 - x 0` (both `⊥ N5, N3`; independent by `046`) and `w = x 0 - x 1`:
`G ⟪N5, w⟫ ⟪N3, w⟫ = D² ⟪N5, N3⟫` with `G = |u|²|v|² - ⟪u,v⟫² > 0`, `D = det (u, v, w)`. -/
theorem bs_n53_neg (F : S0xFac 9 s0x_S24 x) (hw4 : oblX0 x 4 = 1) (hw5 : oblX0 x 5 = 1) :
    ⟪F.N 5, F.N 3⟫ < 0 := by
  set u := x 4 - x 0
  set v := x 5 - x 0
  set w := x 0 - x 1
  have h5u : ⟪F.N 5, u⟫ = 0 := by rw [F.inner_sub 5 4 0, bs_f5_obl F 4, hw4]; ring
  have h5v : ⟪F.N 5, v⟫ = 0 := by rw [F.inner_sub 5 5 0, bs_f5_obl F 5, hw5]; ring
  have h3u : ⟪F.N 3, u⟫ = 0 := by rw [F.inner_sub 3 4 0, F.zero 3 4 (by decide), F.zero 3 0 (by decide)]; ring
  have h3v : ⟪F.N 3, v⟫ = 0 := by rw [F.inner_sub 3 5 0, F.zero 3 5 (by decide), F.zero 3 0 (by decide)]; ring
  have h5w : ⟪F.N 5, w⟫ < 0 := by
    rw [F.inner_sub 5 0 1, F.zero 5 1 (by decide)]; linarith [F.neg 5 0 (by decide)]
  have h3w : 0 < ⟪F.N 3, w⟫ := by
    rw [F.inner_sub 3 0 1, F.zero 3 0 (by decide)]; linarith [F.neg 3 1 (by decide)]
  have hu : u ≠ 0 := by
    intro h0
    have e := F.inner_sub 8 4 0
    rw [show x 4 - x 0 = u from rfl, h0, inner_zero_right, F.zero 8 4 (by decide)] at e
    linarith [F.neg 8 0 (by decide)]
  have h4u : ⟪F.N 4, u⟫ = 0 := by rw [F.inner_sub 4 4 0, F.zero 4 4 (by decide), F.zero 4 0 (by decide)]; ring
  have h4v : ⟪F.N 4, v⟫ ≠ 0 := by
    rw [F.inner_sub 4 5 0, F.zero 4 0 (by decide)]; linarith [F.neg 4 5 (by decide)]
  have hG := Q45.gram_pos u v (F.N 4) hu h4u h4v
  have g1 := Q45.gram_decomp u v w (F.N 5)
  have g2 := Q45.gram_decomp u v w (F.N 3)
  have g3 := Q45.gram_decomp u v (F.N 3) (F.N 5)
  rw [h5u, h5v] at g1 g3
  rw [h3u, h3v] at g2
  set G := ⟪u, u⟫ * ⟪v, v⟫ - ⟪u, v⟫ ^ 2
  set D := det3 u v w
  set A := det3 u v (F.N 5)
  set B := det3 u v (F.N 3)
  have key : G * (G * ⟪F.N 5, w⟫ * ⟪F.N 3, w⟫) = G * (D ^ 2 * ⟪F.N 5, F.N 3⟫) := by
    linear_combination (G * ⟪F.N 3, w⟫) * g1 + (D * A) * g2 - D ^ 2 * g3
  have k2 := mul_left_cancel₀ hG.ne' key
  have hL : G * ⟪F.N 5, w⟫ * ⟪F.N 3, w⟫ < 0 := by
    have := mul_neg_of_pos_of_neg hG h5w
    exact mul_neg_of_neg_of_pos this h3w
  by_contra hc
  push Not at hc
  have : 0 ≤ D ^ 2 * ⟪F.N 5, F.N 3⟫ := mul_nonneg (sq_nonneg D) hc
  linarith

/-- `126` is up on the double wall `a4 = a5 = 1` (level 3: `⟪N5, -N3⟫ > 0`, `bs_n53_neg`). -/
theorem bs_up5_dw (F : S0xFac 9 s0x_S24 x) (hw4 : oblX0 x 4 = 1) (hw5 : oblX0 x 5 = 1) : BsUp F 5 := by
  right
  refine ⟨?_, Or.inr ⟨?_, ?_⟩⟩
  · rw [F.inner_sub 5 0 4, bs_f5_obl F 4, hw4]; ring
  · rw [F.inner_sub 5 5 0, bs_f5_obl F 5, hw5]; ring
  · rw [inner_neg_right]; linarith [bs_n53_neg F hw4 hw5]

/-- `235` is down for `t < 1` (level 1, `k0_f6`). -/
theorem bs_dn6 (F : S0xFac 9 s0x_S24 x) {s t : ℝ} (hs0 : 0 < s) (ht1 : t < 1)
    (hdec : x 3 - x 0 = s • (x 4 - x 0) + t • (x 5 - x 0)) : BsDn F 6 := by
  have e := k0_f6 F hdec
  have h0 := F.neg 6 0 (by decide)
  left
  have : s * ⟪F.N 6, x 0 - x 4⟫ < 0 := by rw [e]; nlinarith
  have : ⟪F.N 6, x 0 - x 4⟫ < 0 := by
    by_contra hc; push Not at hc; nlinarith
  linarith

/-- `235` is up for `t ≥ 1` (level 1 for `t > 1`; level 2 at `t = 1`: `⟪N6, x 5 - x 0⟫ = -f6(x 0) > 0`). -/
theorem bs_up6 (F : S0xFac 9 s0x_S24 x) {s t : ℝ} (hs0 : 0 < s) (ht1 : 1 ≤ t)
    (hdec : x 3 - x 0 = s • (x 4 - x 0) + t • (x 5 - x 0)) : BsUp F 6 := by
  have e := k0_f6 F hdec
  have h0 := F.neg 6 0 (by decide)
  rcases ht1.lt_or_eq with ht | rfl
  · left
    have : 0 < s * ⟪F.N 6, x 0 - x 4⟫ := by rw [e]; nlinarith
    by_contra hc; push Not at hc; nlinarith
  · right
    have : ⟪F.N 6, x 0 - x 4⟫ = 0 := by
      have : s * ⟪F.N 6, x 0 - x 4⟫ = 0 := by rw [e]; ring
      rcases mul_eq_zero.mp this with h | h
      · exact absurd h hs0.ne'
      · exact h
    refine ⟨this, Or.inl ?_⟩
    rw [F.inner_sub 6 5 0, F.zero 6 5 (by decide)]; linarith

/-- `236` at level 1: `s (f7(x 4) - f7(x 0)) = (t - 1) f7(x 0) - t f7(x 5)` (`f7(x 3) = 0`). -/
theorem bs_f7 (F : S0xFac 9 s0x_S24 x) {s t : ℝ} (hdec : x 3 - x 0 = s • (x 4 - x 0) + t • (x 5 - x 0)) :
    s * (-⟪F.N 7, x 0 - x 4⟫) = (t - 1) * F.f 7 (x 0) - t * F.f 7 (x 5) := by
  have h3 := congrArg (fun v => ⟪F.N 7, v⟫) hdec
  simp only [inner_add_right, real_inner_smul_right] at h3
  rw [F.inner_sub 7 3 0, F.inner_sub 7 4 0, F.inner_sub 7 5 0, F.zero 7 3 (by decide)] at h3
  rw [F.inner_sub 7 0 4]; linarith

/-- `236` is down for `t ≤ 1` (level 1, `bs_f7`). -/
theorem bs_dn7 (F : S0xFac 9 s0x_S24 x) {s t : ℝ} (hs0 : 0 < s) (ht0 : 0 < t) (ht1 : t ≤ 1)
    (hdec : x 3 - x 0 = s • (x 4 - x 0) + t • (x 5 - x 0)) : BsDn F 7 := by
  have e := bs_f7 F hdec
  have h0 := F.neg 7 0 (by decide)
  have h5 := F.neg 7 5 (by decide)
  left
  have : 0 < s * (-⟪F.N 7, x 0 - x 4⟫) := by rw [e]; nlinarith
  by_contra hc; push Not at hc; nlinarith

/-- `236` is down on the wall `a4 = 1` (level 1: `f7(x 4) - f7(x 0) = -(b4 + c4) f7(x 1) > 0`). -/
theorem bs_dn7_wall (F : S0xFac 9 s0x_S24 x) (hw4 : oblX0 x 4 = 1) : BsDn F 7 := by
  have T := M4.type24OfFac F
  have hb4 : 0 < oblX2 x 4 := T.X2_pos (by decide)
  have hc4 : 0 < oblX6 x 4 := T.X6_pos (by decide)
  have e74 := M4.fac_eval F 7 4
  rw [F.zero 7 2 (by decide), F.zero 7 6 (by decide), hw4] at e74
  have h1 := F.neg 7 1 (by decide)
  left
  rw [F.inner_sub 7 0 4]; nlinarith

/-- The rim condition of the Bs view at the decomposition `t`: rim `0 5 2 6` for `t < 1`, `0 5 3 2 6` for `t ≥ 1`. -/
def BsRU {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (t : ℝ) : Prop :=
  (t < 1 → RobUniLex (bsZ F rimBA)) ∧ (1 ≤ t → RobUniLex (bsZ F rimBB))

/-- The branch conditions of the Bs view at `(s, t)`: off the wall `a4 = 1` or on the double wall; `236` derived
(`t ≤ 1` or `a4 = 1`) or assumed; the rim. -/
def BsCond {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (t : ℝ) : Prop :=
  (1 < oblX0 x 4 ∨ (oblX0 x 4 = 1 ∧ oblX0 x 5 = 1)) ∧ (t ≤ 1 ∨ oblX0 x 4 = 1 ∨ BsDn F 7) ∧ BsRU F t

/-- **The Bs view from branch hypotheses**. -/
theorem bsViewOK_of (F : S0xFac 9 s0x_S24 x) {s t : ℝ} (hs0 : 0 < s) (ht0 : 0 < t)
    (hdec : x 3 - x 0 = s • (x 4 - x 0) + t • (x 5 - x 0)) (h : BsCond F t) : BsViewOK F := by
  obtain ⟨h5, h7, hR⟩ := h
  refine ⟨h5.elim (bs_up5 F) (fun h => bs_up5_dw F h.1 h.2), ?_, ?_⟩
  · rcases h7 with h7 | h7 | h7
    · exact bs_dn7 F hs0 ht0 h7 hdec
    · exact bs_dn7_wall F h7
    · exact h7
  · rcases lt_or_ge t 1 with ht | ht
    · exact Or.inl ⟨bs_dn6 F hs0 ht hdec, hR.1 ht⟩
    · exact Or.inr ⟨bs_up6 F hs0 ht hdec, hR.2 ht⟩

/-- The mirror conditions (the Bs view of `π24 x` at `(t, s)`), in the coordinates of `x`. -/
def BsCondSym {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (s : ℝ) : Prop :=
  (1 < oblX0 x 5 ∨ (oblX0 x 5 = 1 ∧ oblX0 x 4 = 1)) ∧ (s ≤ 1 ∨ oblX0 x 5 = 1 ∨ BsDn (Sym.sym24 F) 7) ∧
    BsRU (Sym.sym24 F) s

/-- **The mirror form**: the Bs view of the mirrored solid (the view `(x 0 - x 5, x 4 - x 0, -N3)` of `x`). -/
theorem bsViewOK_sym_of (F : S0xFac 9 s0x_S24 x) {s t : ℝ} (hs0 : 0 < s) (ht0 : 0 < t)
    (hdec : x 3 - x 0 = s • (x 4 - x 0) + t • (x 5 - x 0)) (h : BsCondSym F s) : BsViewOK (Sym.sym24 F) := by
  have o4 : oblX0 (x ∘ Sym.pi24) 4 = oblX0 x 5 := by rw [Sym.oblX0_comp_pi24]; simp
  have o5 : oblX0 (x ∘ Sym.pi24) 5 = oblX0 x 4 := by rw [Sym.oblX0_comp_pi24]; simp
  obtain ⟨h5, h7, hR⟩ := h
  refine bsViewOK_of (Sym.sym24 F) (s := t) (t := s) ht0 hs0 ?_ ⟨?_, ?_, hR⟩
  · simp only [Function.comp_apply, Sym.pi24_0, Sym.pi24_3, Sym.pi24_4, Sym.pi24_5]
    rw [hdec]; abel
  · rw [o4, o5]; exact h5
  · rw [o4]; exact h7

/-! ### The residue after the Bs views -/

/-- `Q45ResSTF` where neither Bs view's conditions hold and no face-on J0 view applies (`JFaceOK`, so far used on the
J0 pieces only; it also closes both `B2T` points, pattern B). -/
def Q45ResSTB {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (s t : ℝ) : Prop :=
  Q45ResSTF F s t ∧ ¬ BsCond F t ∧ ¬ BsCondSym F s ∧ ¬ JFaceOK F

/-- The branch-tagged residue after the Bs views. -/
def Q45ResWB {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) : Prop :=
  ∃ s t : ℝ, 0 < s ∧ 0 < t ∧ 1 < s + t ∧ x 3 - x 0 = s • (x 4 - x 0) + t • (x 5 - x 0) ∧ Q45ResSTB F s t

/-- **The Bs views (and the face-on J0 views) cut the residue**: a point of `Q45ResSTF` is `LexAny` or in
`Q45ResSTB`. -/
theorem q45_resB_local (F : S0xFac 9 s0x_S24 x) {s t : ℝ} (hs0 : 0 < s) (ht0 : 0 < t)
    (hdec : x 3 - x 0 = s • (x 4 - x 0) + t • (x 5 - x 0)) (h : Q45ResSTF F s t) :
    Gen.LexAny F ∨ Q45ResSTB F s t := by
  by_cases hA : BsCond F t
  · exact Or.inl (lexAny_of_bsView F (bsViewOK_of F hs0 ht0 hdec hA))
  by_cases hB : BsCondSym F s
  · exact Or.inl (lexAny_of_bsView_sym F (bsViewOK_sym_of F hs0 ht0 hdec hB))
  by_cases hJ : JFaceOK F
  · exact Or.inl (lexAny_of_jFace F hJ)
  exact Or.inr ⟨h, hA, hB, hJ⟩

/-- `Q45ResWB ⊆ Q45ResWF`. -/
theorem q45ResWF_of_B {F : S0xFac 9 s0x_S24 x} (h : Q45ResWB F) : Q45ResWF F := by
  obtain ⟨s, t, hs, ht, hst, hd, h⟩ := h
  exact ⟨s, t, hs, ht, hst, hd, h.1⟩

/-- **Global form**: on the corner every point has `LexAny`, `AnyFaceChord`, is Rupert, or lies in `Q45ResWB`. -/
theorem q45_resB (F : S0xFac 9 s0x_S24 x) (h4 : 1 ≤ oblX0 x 4) (h5 : 1 ≤ oblX0 x 5) :
    Gen.LexAny F ∨ Gen.AnyFaceChord F ∨ IsRupert (univ.image x) ∨ Q45ResWB F := by
  rcases q45_resF F h4 h5 with h | h | h | ⟨s, t, hs0, ht, hst, hd, h⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · rcases q45_resB_local F hs0 ht hd h with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inr ⟨s, t, hs0, ht, hst, hd, h⟩))

/-- [OPEN] **The special piece after the Bs views, Rupert form**: `OpenSpecialF` with `Q45ResWB` in place of
`Q45ResWF`. -/
def OpenSpecialB : Prop := ∀ (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x), ¬ H24K.SAT.OB1 x →
  1 ≤ oblX0 x 4 → 1 ≤ oblX0 x 5 →
  oblX0 x 4 * oblX6 x 3 - oblX0 x 3 * oblX6 x 4 < 0 →
  0 < oblX0 x 3 * oblX2 x 5 - oblX0 x 5 * oblX2 x 3 →
  0 < oblX0 x 4 * oblX2 x 5 - oblX0 x 5 * oblX2 x 4 →
  0 < oblX0 x 5 * oblX6 x 4 - oblX0 x 4 * oblX6 x 5 →
  Q45ResWB F → HoleFull x F → IsRupert (univ.image x)

/-- [PROVED] `OpenSpecialF → OpenSpecialB` (`q45ResWF_of_B`). -/
theorem openSpecialB_of_openSpecialF (h : OpenSpecialF) : OpenSpecialB :=
  fun x F hO h4 h5 b1 b2 b3 b4 hr hF => h x F hO h4 h5 b1 b2 b3 b4 (q45ResWF_of_B hr) hF

/-- Every `Hole24` point off `OB1` is Rupert, given `OpenSpecialB`. -/
theorem hole24_offOB1_B {F : S0xFac 9 s0x_S24 x} (h : Hole24 x F) (hO : ¬ H24K.SAT.OB1 x)
    (hS : OpenSpecialB) : IsRupert (univ.image x) := by
  obtain ⟨b1, b2, b3⟩ := resid24_frame_signs h.2.2.1 hO
  have b4 := resid24_b1245 h.2.2.1 hO
  obtain ⟨-, h4, h5⟩ := offWall_of_hole24 h hO
  have hF := holeFull_of_hole24 h
  rcases q45_resB F h4 h5 with hL | hA | hR | hr
  · exact (hF.1.2.2.2.1 hL).elim
  · exact (hF.1.2.2.1 hA).elim
  · exact hR
  · exact hS x F hO h4 h5 b1 b2 b3 b4 hr hF

/-- [PROVED] Generic + special (after the Bs views) assemble to `Open24Rupert`. -/
theorem open24Rupert_of_split_B (h1 : OpenOB1) (h2 : OpenSpecialB) : Open24Rupert := by
  intro x fs hh hH
  by_cases hO : H24K.SAT.OB1 x
  · exact (h1 x _ hO (holeFull_of_hole24 hH)).elim
  · exact hole24_offOB1_B hH hO h2

end Bs

end Minimality.T24.OSpec
