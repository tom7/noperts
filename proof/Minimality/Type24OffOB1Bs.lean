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
and applies the face-on J0 views `JFaceOK` and the K0 views `K0ViewOK` (OSPEC9) to every piece too: they close both
`B2T` points (pattern B), the three acute J0 double normals and the J0b point `S3_730`.  On the `64` tie the face
angle `0 4 3` splits the J0 points: obtuse -> face-on view (`faceOnCell_of_tie64`), acute -> K0 view, every
condition derived for `t ≤ 1` (`k0ViewOK_of_tie64`); no face-on pattern exists at an acute angle
(`not_j64ViewOK_of_acute`).
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

/-- `Q45ResSTF` where neither Bs view's conditions hold and neither the face-on J0 views (`JFaceOK`, so far used on
the J0 pieces only; they also close both `B2T` points, pattern B) nor the K0 views (`K0ViewOK`, so far used on
`kJ = 0` only; they close the acute `64` / `52` ties, `k0ViewOK_of_tie64`, and the J0b point `S3_730`) apply. -/
def Q45ResSTB {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (s t : ℝ) : Prop :=
  Q45ResSTF F s t ∧ ¬ BsCond F t ∧ ¬ BsCondSym F s ∧ ¬ JFaceOK F ∧ ¬ K0ViewOK F ∧ ¬ K0ViewOK (Sym.sym24 F)

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
  by_cases hK : K0ViewOK F
  · exact Or.inl (lexAny_of_k0View F hK)
  by_cases hK' : K0ViewOK (Sym.sym24 F)
  · exact Or.inl (lexAny_of_k0View_sym F hK')
  exact Or.inr ⟨h, hA, hB, hJ, hK, hK'⟩

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

/-! ### The face-on J0 view on the `64` tie

On the adjacent S2 tie `64` (`x 6 - x 4 ⊥ e4, e5`, i.e. `x 6 - x 4 ∥ N3`) the facets `046` and `346` through the
edge `4 6` are edge-on at level 1 of the face-on view `(N3, bB2, x 0 - x 4)` (`j64_perp`), so level 2 (`bB2`, in
the face plane perpendicular to edge `3 4`) decides them: `346` is always down (`n8_bB2_neg`), `046` is down iff the
face angle of `0345` at `4` is obtuse (`b2_dn4_of_obtuse`; up when acute, `n4_bB2_pos_of_acute`).  Hence on the tie
`0345 046 346` are derived for the four patterns of `J64ViewOK` when the angle `0 4 3` is obtuse
(`faceOnCell_of_tie64`), and NO pattern can hold when it is acute (`not_j64ViewOK_of_acute`): the two open `64` J0
points (and, in the mirror, the open `52` point) are exactly the acute ones of the J0 residue [SAMPLED]. -/

section J64Tie
open Minimality.LexCell

/-- **On the `64` tie the facets through the edge `4 6` are perpendicular to `0345`**: `⟪N4, N3⟫ = ⟪N8, N3⟫ = 0`.
Gram identities along `u = x 4 - x 0`, `v = x 5 - x 0`: `G ⟪N, N3⟫ = det(u,v,N3) det(u,v,N)` and
`G ⟪N, d⟫ = det(u,v,d) det(u,v,N)` for `d = x 6 - x 4 ⊥ u, v`, with `det(u,v,d) ≠ 0` (`G |d|² = det(u,v,d)²`). -/
theorem j64_perp (F : S0xFac 9 s0x_S24 x) (h4 : ⟪x 6 - x 4, x 4 - x 0⟫ = 0) (h5 : ⟪x 6 - x 4, x 5 - x 0⟫ = 0) :
    ⟪F.N 4, F.N 3⟫ = 0 ∧ ⟪F.N 8, F.N 3⟫ = 0 := by
  set u := x 4 - x 0
  set v := x 5 - x 0
  set d := x 6 - x 4
  have h3u : ⟪F.N 3, u⟫ = 0 := by rw [F.inner_sub 3 4 0, F.zero 3 4 (by decide), F.zero 3 0 (by decide)]; ring
  have h3v : ⟪F.N 3, v⟫ = 0 := by rw [F.inner_sub 3 5 0, F.zero 3 5 (by decide), F.zero 3 0 (by decide)]; ring
  have hdu : ⟪d, u⟫ = 0 := h4
  have hdv : ⟪d, v⟫ = 0 := h5
  have hu : u ≠ 0 := by
    intro h0
    have e := F.inner_sub 8 4 0
    rw [show x 4 - x 0 = u from rfl, h0, inner_zero_right, F.zero 8 4 (by decide)] at e
    linarith [F.neg 8 0 (by decide)]
  have h4u : ⟪F.N 4, u⟫ = 0 := by rw [F.inner_sub 4 4 0, F.zero 4 4 (by decide), F.zero 4 0 (by decide)]; ring
  have h4v : ⟪F.N 4, v⟫ ≠ 0 := by
    rw [F.inner_sub 4 5 0, F.zero 4 0 (by decide)]; linarith [F.neg 4 5 (by decide)]
  have hG := Q45.gram_pos u v (F.N 4) hu h4u h4v
  have h3d : ⟪F.N 3, d⟫ < 0 := by
    rw [F.inner_sub 3 6 4, F.zero 3 4 (by decide)]; linarith [F.neg 3 6 (by decide)]
  have hdd := Q45.gram_decomp u v d d
  rw [hdu, hdv] at hdd
  simp only [mul_zero, sub_zero, zero_add] at hdd
  have hD : det3 u v d ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hdd
    have hd0 : d = 0 := by
      have := (mul_eq_zero.mp hdd).resolve_left hG.ne'
      exact inner_self_eq_zero.mp this
    rw [hd0, inner_zero_right] at h3d; exact lt_irrefl _ h3d
  have key : ∀ t : Fin 9, ⟪F.N t, d⟫ = 0 → ⟪F.N t, F.N 3⟫ = 0 := by
    intro t ht
    have g1 := Q45.gram_decomp u v d (F.N t)
    have g2 := Q45.gram_decomp u v (F.N 3) (F.N t)
    rw [hdu, hdv, ht] at g1
    rw [h3u, h3v] at g2
    simp only [mul_zero, zero_mul, sub_zero, zero_add] at g1 g2
    have hA := (mul_eq_zero.mp g1.symm).resolve_left hD
    rw [hA, mul_zero] at g2
    exact (mul_eq_zero.mp g2).resolve_left hG.ne'
  refine ⟨key 4 ?_, key 8 ?_⟩
  · rw [F.inner_sub 4 6 4, F.zero 4 6 (by decide), F.zero 4 4 (by decide)]; ring
  · rw [F.inner_sub 8 6 4, F.zero 8 6 (by decide), F.zero 8 4 (by decide)]; ring

/-- `346` is down at `bB2`: `|N3|² ⟪N8, bB2⟫ = -|bB2|²`. -/
theorem n8_bB2_neg (F : S0xFac 9 s0x_S24 x) : ⟪F.N 8, bB2 F⟫ < 0 := by
  have hNN : 0 < ⟪F.N 3, F.N 3⟫ := real_inner_self_pos.mpr (n3_ne_zero F)
  have hbb : 0 < ⟪bB2 F, bB2 F⟫ := real_inner_self_pos.mpr (bB2_ne_zero F)
  have e := inner_sub_left (𝕜 := ℝ) (⟪F.N 8, F.N 3⟫ • F.N 3) (⟪F.N 3, F.N 3⟫ • F.N 8) (bB2 F)
  rw [real_inner_smul_left, real_inner_smul_left, inner_N3_bB2 F] at e
  change ⟪bB2 F, bB2 F⟫ = _ at e
  nlinarith

/-- **Facet `046` is up at `bB2` if the face angle of `0345` at `4` is acute** (the converse of
`b2_dn4_of_obtuse`). -/
theorem n4_bB2_pos_of_acute (F : S0xFac 9 s0x_S24 x) (h : 0 < ⟪x 0 - x 4, x 3 - x 4⟫) : 0 < ⟪F.N 4, bB2 F⟫ := by
  have hNu : ⟪F.N 4, x 0 - x 4⟫ = 0 := by
    rw [F.inner_sub 4 0 4, F.zero 4 0 (by decide), F.zero 4 4 (by decide)]; ring
  have hNv : ⟪F.N 4, x 3 - x 4⟫ = F.f 4 (x 3) := by rw [F.inner_sub 4 3 4, F.zero 4 4 (by decide)]; ring
  have hf : F.f 4 (x 3) < 0 := F.neg 4 3 (by decide)
  have hwv : ⟪bB2 F, x 3 - x 4⟫ = 0 := by
    rw [inner_bB2_face F 3 4 (by decide) (by decide), F.zero 8 3 (by decide), F.zero 8 4 (by decide)]; ring
  have hwu : 0 < ⟪bB2 F, x 0 - x 4⟫ := by
    rw [inner_bB2_face F 0 4 (by decide) (by decide), F.zero 8 4 (by decide)]
    have := F.neg 8 0 (by decide); have hNN : 0 < ⟪F.N 3, F.N 3⟫ := real_inner_self_pos.mpr (n3_ne_zero F)
    nlinarith
  have hd := det_bB2 F (n3_perp_face F 0 4 (by decide) (by decide)) (n3_perp_face F 3 4 (by decide) (by decide))
  have key := Q45.sign_side _ _ _ _ hNu hwv hd
  have hG := Q45.gram_nonneg (x 0 - x 4) (x 3 - x 4)
  rw [hNv] at key
  by_contra hc
  have : (⟪x 0 - x 4, x 0 - x 4⟫ * ⟪x 3 - x 4, x 3 - x 4⟫ - ⟪x 0 - x 4, x 3 - x 4⟫ ^ 2) * ⟪F.N 4, bB2 F⟫ ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hG (not_lt.mp hc)
  have h2 : ⟪x 0 - x 4, x 3 - x 4⟫ * ⟪bB2 F, x 0 - x 4⟫ * F.f 4 (x 3) < 0 :=
    mul_neg_of_pos_of_neg (mul_pos h hwu) hf
  linarith

/-- **On the `64` tie with the angle `0 4 3` obtuse the facets `0345 046 346` are derived**: a face-on cell whose
pattern has `0345` up and `046 346` down needs only its other facet signs and its rim. -/
theorem faceOnCell_of_tie64 (F : S0xFac 9 s0x_S24 x) (h4 : ⟪x 6 - x 4, x 4 - x 0⟫ = 0)
    (h5 : ⟪x 6 - x 4, x 5 - x 0⟫ = 0) (hob : ⟪x 0 - x 4, x 3 - x 4⟫ < 0) {k : ℕ} {c : ZMod k → Fin 7}
    {U Dn : Finset (Fin 9)}
    (hU : ∀ t ∈ U, t ≠ 3 → LexPos3 ⟪F.N t, F.N 3⟫ ⟪F.N t, bB2 F⟫ ⟪F.N t, x 0 - x 4⟫)
    (hD : ∀ t ∈ Dn, t ≠ 4 → t ≠ 8 → LexPos3 (-⟪F.N t, F.N 3⟫) (-⟪F.N t, bB2 F⟫) (-⟪F.N t, x 0 - x 4⟫))
    (hR : RobUniLex (fun i => (⟪x (c i), F.N 3⟫, ⟪x (c i), bB2 F⟫, ⟪x (c i), x 0 - x 4⟫))) :
    FaceOnCell F c U Dn := by
  obtain ⟨p4, p8⟩ := j64_perp F h4 h5
  refine ⟨fun t ht => ?_, fun t ht => ?_, hR⟩
  · by_cases e : t = 3
    · subst e; exact Or.inl (real_inner_self_pos.mpr (n3_ne_zero F))
    · exact hU t ht e
  · by_cases e4 : t = 4
    · subst e4
      exact Or.inr ⟨by rw [p4, neg_zero], Or.inl (by linarith [b2_dn4_of_obtuse F hob])⟩
    by_cases e8 : t = 8
    · subst e8
      exact Or.inr ⟨by rw [p8, neg_zero], Or.inl (by linarith [n8_bB2_neg F])⟩
    exact hD t ht e4 e8

/-- **No face-on J0 pattern at an acute angle `0 4 3` on the `64` tie**: `046` is edge-on at level 1 and up at
level 2, while all four patterns of `J64ViewOK` need it down. -/
theorem not_j64ViewOK_of_acute (F : S0xFac 9 s0x_S24 x) (h4 : ⟪x 6 - x 4, x 4 - x 0⟫ = 0)
    (h5 : ⟪x 6 - x 4, x 5 - x 0⟫ = 0) (hac : 0 < ⟪x 0 - x 4, x 3 - x 4⟫) : ¬ J64ViewOK F := by
  have p4 := (j64_perp F h4 h5).1
  have q := n4_bB2_pos_of_acute F hac
  have bad : ¬ LexPos3 (-⟪F.N 4, F.N 3⟫) (-⟪F.N 4, bB2 F⟫) (-⟪F.N 4, x 0 - x 4⟫) := by
    rintro (h | ⟨-, h | ⟨h, -⟩⟩)
    · rw [p4] at h; linarith
    · linarith
    · linarith
  rintro (h | h | h | h)
  · exact bad (h.2.1 4 (by decide))
  · exact bad (h.2.1 4 (by decide))
  · exact bad (h.2.1 4 (by decide))
  · exact bad (h.2.1 4 (by decide))

end J64Tie

/-! ### The K0 view on the acute `64` tie

At an ACUTE angle `0 4 3` on the `64` tie (where no face-on pattern exists, `not_j64ViewOK_of_acute`) the K0 view
`(x 0 - x 4, x 0 - x 5, N3)` (`K0ViewOK`, used so far on `kJ = 0` only) holds with every condition derived for `t ≤ 1`:
its rim `2 5 3 4 6` is lex-monotone `6 < 4 < 3 < 5` (`6 < 4` at level 3 by the tie, `4 < 3` at level 1 by the acute
angle, `3 < 5` at level 1 from the acute angle and `s + t > 1`, `k0_z35`), which is `RobUniLex` whatever the depth of
`2` (`robUniLex_five_k0`); for `t > 1` the rim `2 3 4 6` needs only `6 < 4 < 3` and `236` stays a hypothesis.  So on
the `64` tie: obtuse angle `0 4 3` -> the face-on J0 view (`faceOnCell_of_tie64`, six dihedral signs and the rim
assumed), acute -> the K0 view (`k0ViewOK_of_tie64`); the `52` ties by the mirror. -/

section K0Tie
open Minimality.LexCell

/-- A 5-cycle with `z4 < z3` at level 3 only and `z3 < z2 < z1` at level 1 is `RobUniLex`, whatever `z0`. -/
theorem robUniLex_five_k0 (z : ZMod 5 → ℝ × ℝ × ℝ) (e1 : (z 4).1 = (z 3).1) (e2 : (z 4).2.1 = (z 3).2.1)
    (h43 : (z 4).2.2 < (z 3).2.2) (h32 : (z 3).1 < (z 2).1) (h21 : (z 2).1 < (z 1).1) : RobUniLex z := by
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
  all_goals first
    | exact Or.inl (Or.inl (by linarith))
    | exact Or.inr (Or.inl (Or.inl (by linarith)))
    | exact Or.inr (Or.inr (Or.inl (Or.inl (by linarith))))
    | exact Or.inr (Or.inl (Or.inr ⟨by linarith, Or.inr ⟨by linarith, by linarith⟩⟩))
    | exact Or.inr (Or.inr (Or.inl (Or.inr ⟨by linarith, Or.inr ⟨by linarith, by linarith⟩⟩)))

/-- `3` below `5` in the K0 view (level 1) for `t ≤ 1`, from the acute angle `0 4 3` and `s + t > 1`:
`(1 - s) (s E - (1 - t) c) = s ((1 - s) E - t c) + c (s + t - 1)`, `E = |e4|²`, `c = ⟪e5, e4⟫`. -/
theorem k0_z35 (F : S0xFac 9 s0x_S24 x) {s t : ℝ} (hs0 : 0 < s) (ht0 : 0 < t) (ht1 : t ≤ 1) (hst : 1 < s + t)
    (hdec : x 3 - x 0 = s • (x 4 - x 0) + t • (x 5 - x 0)) (hac : 0 < ⟪x 0 - x 4, x 3 - x 4⟫) :
    0 < ⟪x 5 - x 3, x 0 - x 4⟫ := by
  have hu : x 4 - x 0 ≠ 0 := by
    intro h0
    have e := F.inner_sub 8 4 0
    rw [h0, inner_zero_right, F.zero 8 4 (by decide)] at e
    linarith [F.neg 8 0 (by decide)]
  have hE : 0 < ⟪x 4 - x 0, x 4 - x 0⟫ := real_inner_self_pos.mpr hu
  set E := ⟪x 4 - x 0, x 4 - x 0⟫
  set c := ⟪x 5 - x 0, x 4 - x 0⟫
  have A : ⟪x 3 - x 0, x 4 - x 0⟫ = s * E + t * c := by
    rw [hdec, inner_add_left, real_inner_smul_left, real_inner_smul_left]
  have g : ⟪x 5 - x 3, x 0 - x 4⟫ = s * E - (1 - t) * c := by
    rw [show x 5 - x 3 = (x 5 - x 0) - (x 3 - x 0) by abel, show x 0 - x 4 = -(x 4 - x 0) by abel,
      inner_neg_right, inner_sub_left, A]; ring
  have ha : ⟪x 0 - x 4, x 3 - x 4⟫ = (1 - s) * E - t * c := by
    rw [show x 0 - x 4 = -(x 4 - x 0) by abel, show x 3 - x 4 = (x 3 - x 0) - (x 4 - x 0) by abel,
      inner_neg_left, real_inner_comm, inner_sub_left, A]; ring
  rw [g]; rw [ha] at hac
  rcases le_or_gt c 0 with hc | hc
  · nlinarith
  · have hs1 : s < 1 := by
      by_contra h; push Not at h
      nlinarith [mul_nonneg (sub_nonneg.mpr h) hE.le, mul_pos ht0 hc]
    have key : (1 - s) * (s * E - (1 - t) * c) = s * ((1 - s) * E - t * c) + c * (s + t - 1) := by ring
    have : 0 < (1 - s) * (s * E - (1 - t) * c) := by
      rw [key]; have := mul_pos hs0 hac; have := mul_pos hc (by linarith : (0 : ℝ) < s + t - 1); linarith
    by_contra hn; push Not at hn
    nlinarith [mul_nonpos_of_nonneg_of_nonpos (by linarith : (0 : ℝ) ≤ 1 - s) hn]

/-- **The K0 view on the acute `64` tie**: `x 6 - x 4 ⊥ e4, e5`, angle `0 4 3` acute, `a4 > 1`, and `236` down when
`t > 1`.  Every other condition of `K0ViewOK` is derived. -/
theorem k0ViewOK_of_tie64 (F : S0xFac 9 s0x_S24 x) (h4 : ⟪x 6 - x 4, x 4 - x 0⟫ = 0)
    (h5 : ⟪x 6 - x 4, x 5 - x 0⟫ = 0) (hac : 0 < ⟪x 0 - x 4, x 3 - x 4⟫) (ha4 : 1 < oblX0 x 4) {s t : ℝ}
    (hs0 : 0 < s) (ht0 : 0 < t) (hst : 1 < s + t) (hdec : x 3 - x 0 = s • (x 4 - x 0) + t • (x 5 - x 0))
    (h7 : t ≤ 1 ∨ K0Dn F 7) : K0ViewOK F := by
  -- the depths of the rim vertices 6, 4, 3
  have e1 : ⟪x 6, x 0 - x 4⟫ = ⟪x 4, x 0 - x 4⟫ := by
    have : ⟪x 6 - x 4, x 0 - x 4⟫ = 0 := by
      rw [show x 0 - x 4 = -(x 4 - x 0) by abel, inner_neg_right, h4, neg_zero]
    rw [inner_sub_left] at this; linarith
  have e2 : ⟪x 6, x 0 - x 5⟫ = ⟪x 4, x 0 - x 5⟫ := by
    have : ⟪x 6 - x 4, x 0 - x 5⟫ = 0 := by
      rw [show x 0 - x 5 = -(x 5 - x 0) by abel, inner_neg_right, h5, neg_zero]
    rw [inner_sub_left] at this; linarith
  have h64 : ⟪x 6, F.N 3⟫ < ⟪x 4, F.N 3⟫ := by
    have e := F.inner_sub 3 6 4
    rw [F.zero 3 4 (by decide), real_inner_comm, inner_sub_left] at e
    linarith [F.neg 3 6 (by decide)]
  have h43 : ⟪x 4, x 0 - x 4⟫ < ⟪x 3, x 0 - x 4⟫ := by
    have := hac
    rw [real_inner_comm, inner_sub_left] at this; linarith
  refine ⟨k0_up5 F ha4, ?_, ?_⟩
  · rcases h7 with h7 | h7
    · have e := bs_f7 F hdec
      have q0 := F.neg 7 0 (by decide)
      have q5 := F.neg 7 5 (by decide)
      left
      have : 0 < s * (-⟪F.N 7, x 0 - x 4⟫) := by rw [e]; nlinarith
      by_contra hc; push Not at hc; nlinarith
    · exact h7
  · rcases le_or_gt t 1 with ht | ht
    · refine Or.inl ⟨k0_dn6 F hs0 ht hdec, ?_⟩
      have h35 := k0_z35 F hs0 ht0 ht hst hdec hac
      have h35' : ⟪x 3, x 0 - x 4⟫ < ⟪x 5, x 0 - x 4⟫ := by
        rw [← sub_pos, ← inner_sub_left]; exact h35
      exact robUniLex_five_k0 _ e1 e2 h64 h43 h35'
    · refine Or.inr ⟨k0_up6 F hs0 ht hdec, ?_⟩
      refine robUniLex_four_of_mixed ⟨(2, 1), by decide, Or.inl ?_⟩ ⟨(2, 3), by decide, ?_⟩
      · show 0 < ⟪x 3, x 0 - x 4⟫ - ⟪x 4, x 0 - x 4⟫
        linarith
      · show LexPos3 (⟪x 4, x 0 - x 4⟫ - ⟪x 6, x 0 - x 4⟫) (⟪x 4, x 0 - x 5⟫ - ⟪x 6, x 0 - x 5⟫)
          (⟪x 4, F.N 3⟫ - ⟪x 6, F.N 3⟫)
        exact Or.inr ⟨by linarith, Or.inr ⟨by linarith, by linarith⟩⟩

/-- **The mirror form on the acute `52` tie**: `x 2 - x 5 ⊥ e4, e5`, angle `0 5 3` acute, `a5 > 1`, and `236` down
(mirror) when `s > 1`: the K0 view of `π24 x` (the view `(x 0 - x 5, x 0 - x 4, N3)` of `x`). -/
theorem k0ViewOK_sym_of_tie52 (F : S0xFac 9 s0x_S24 x) (h4 : ⟪x 2 - x 5, x 5 - x 0⟫ = 0)
    (h5 : ⟪x 2 - x 5, x 4 - x 0⟫ = 0) (hac : 0 < ⟪x 0 - x 5, x 3 - x 5⟫) (ha5 : 1 < oblX0 x 5) {s t : ℝ}
    (hs0 : 0 < s) (ht0 : 0 < t) (hst : 1 < s + t) (hdec : x 3 - x 0 = s • (x 4 - x 0) + t • (x 5 - x 0))
    (h7 : s ≤ 1 ∨ K0Dn (Sym.sym24 F) 7) : K0ViewOK (Sym.sym24 F) := by
  have o4 : oblX0 (x ∘ Sym.pi24) 4 = oblX0 x 5 := by rw [Sym.oblX0_comp_pi24]; simp
  refine k0ViewOK_of_tie64 (Sym.sym24 F) (s := t) (t := s) ?_ ?_ ?_ (by rw [o4]; exact ha5) ht0 hs0
    (by linarith) ?_ h7
  · simp only [Function.comp_apply, Sym.pi24_0, Sym.pi24_4, Sym.pi24_6]; exact h4
  · simp only [Function.comp_apply, Sym.pi24_0, Sym.pi24_5, Sym.pi24_4, Sym.pi24_6]; exact h5
  · simp only [Function.comp_apply, Sym.pi24_0, Sym.pi24_3, Sym.pi24_4]; exact hac
  · simp only [Function.comp_apply, Sym.pi24_0, Sym.pi24_3, Sym.pi24_4, Sym.pi24_5]
    rw [hdec]; abel

end K0Tie

/-! ### The K0 view on the double wall (job OSPEC11)

On the double wall `a4 = a5 = 1` every vertex lies on one of the parallel planes `126` (`a = 0`) and `0345`
(`a = 1`), so the K0 view `(x 0 - x 4, x 0 - x 5, N3)` has `126` DOWN (level 3, `bs_n53_neg`; `K0ViewOK` needs it up)
and the rim `1 2 5 3 4 6`: the chain `5 3 4` of `0345` facing `x 4 - x 0` and the chain `6 1 2` of `126` facing
`x 0 - x 4`.  Level 1 is convex on the first chain (`3` is never a peak, `k0_vee`, for `t ≤ 1`) and concave on the
second (`1` is never a valley, `k0_lam_wall`: `x 4 - x 0 = b4 (x 2 - x 1) + c4 (x 6 - x 1)`), so the 6-cycle is
`RobUniLex` as soon as the two junctions `4 6` and `2 5` are tame (`DwK0C`, `robUniLex_six_dw`).  The junction clauses
are exactly the rim condition on 20000 double-wall points [SAMPLED, ospec11]; they are explicit, not derived.
-/

section DwK0
open Minimality.GenRev Minimality.LexCell


/-- The no-alternation hypothesis of `robUniO_of_noAlt` for `k = 6` from a finite (decidable) check. -/
theorem halt6_of (Mn Mx : Finset (ZMod 6))
    (h : ∀ B : ZMod 6, ∀ b c d : Fin 6, 0 < b.val → b.val < c.val → c.val < d.val →
      ¬ (B ∈ Mx ∧ B + (b.val : ZMod 6) ∈ Mn ∧ B + (c.val : ZMod 6) ∈ Mx ∧ B + (d.val : ZMod 6) ∈ Mn)) :
    ∀ (B : ZMod 6) (b c d : ℕ), 0 < b → b < c → c < d → d < 6 →
      ¬ (B ∈ Mx ∧ B + b ∈ Mn ∧ B + c ∈ Mx ∧ B + d ∈ Mn) :=
  fun B b c d hb hbc hcd hd => h B ⟨b, by omega⟩ ⟨c, by omega⟩ ⟨d, hd⟩ hb hbc hcd

/-- Typing aid for the valley condition of `robUniO_of_noAlt` (`k = 6`). -/
theorem hMn_aux {α : Type*} [LinearOrder α] (z : ZMod 6 → α) (Mn : Finset (ZMod 6))
    (h : ∀ v ∉ Mn, z (v - 1) < z v ∨ z (v + 1) < z v) : ∀ v ∉ Mn, z (v - 1) < z v ∨ z (v + 1) < z v := h
/-- Typing aid for the peak condition of `robUniO_of_noAlt` (`k = 6`). -/
theorem hMx_aux {α : Type*} [LinearOrder α] (z : ZMod 6 → α) (Mx : Finset (ZMod 6))
    (h : ∀ v ∉ Mx, z v < z (v - 1) ∨ z v < z (v + 1)) : ∀ v ∉ Mx, z v < z (v - 1) ∨ z v < z (v + 1) := h

set_option linter.unusedSimpArgs false in
set_option linter.unreachableTactic false in
set_option linter.unusedTactic false in
/-- The combinatorial core of `robUniLex_six_dw` over any linear order: with `3 ∉ Mx` (`hV`), `0 ∉ Mn` (`hL`) and
one clause of each junction, `robUniO_of_noAlt` applies with the sets of the 9 cases (two candidate peaks and two
candidate valleys never alternate). -/
theorem robUniO_six_dw {α : Type*} [LinearOrder α] (z : ZMod 6 → α)
    (hV : z 3 < z 2 ∨ z 3 < z 4) (hL : z 5 < z 0 ∨ z 1 < z 0)
    (c1 : z 4 < z 5 ∨ z 4 < z 3 ∨ z 0 < z 5) (c2 : z 2 < z 1 ∨ z 2 < z 3 ∨ z 0 < z 1) : RobUniO z := by
  rcases c1 with p | p | p <;> rcases c2 with q | q | q
  · exact robUniO_of_noAlt (z := z) {2, 3, 4} {0, 1, 5} (hMn_aux z _ (by intro v hv; rcases zmod6_cases v with rfl | rfl | rfl | rfl | rfl | rfl <;>   first | (exfalso; revert hv; decide) | (simp only [show (0 : ZMod 6) + 1 = 1 from rfl, show (1 : ZMod 6) + 1 = 2 from rfl, show (2 : ZMod 6) + 1 = 3 from rfl, show (3 : ZMod 6) + 1 = 4 from rfl, show (4 : ZMod 6) + 1 = 5 from rfl, show (5 : ZMod 6) + 1 = 0 from rfl, show (0 : ZMod 6) - 1 = 5 from rfl, show (1 : ZMod 6) - 1 = 0 from rfl, show (2 : ZMod 6) - 1 = 1 from rfl, show (3 : ZMod 6) - 1 = 2 from rfl, show (4 : ZMod 6) - 1 = 3 from rfl, show (5 : ZMod 6) - 1 = 4 from rfl]; first | assumption | (left; assumption) | (right; assumption)))) (hMx_aux z _ (by intro v hv; rcases zmod6_cases v with rfl | rfl | rfl | rfl | rfl | rfl <;>   first | (exfalso; revert hv; decide) | (simp only [show (0 : ZMod 6) + 1 = 1 from rfl, show (1 : ZMod 6) + 1 = 2 from rfl, show (2 : ZMod 6) + 1 = 3 from rfl, show (3 : ZMod 6) + 1 = 4 from rfl, show (4 : ZMod 6) + 1 = 5 from rfl, show (5 : ZMod 6) + 1 = 0 from rfl, show (0 : ZMod 6) - 1 = 5 from rfl, show (1 : ZMod 6) - 1 = 0 from rfl, show (2 : ZMod 6) - 1 = 1 from rfl, show (3 : ZMod 6) - 1 = 2 from rfl, show (4 : ZMod 6) - 1 = 3 from rfl, show (5 : ZMod 6) - 1 = 4 from rfl]; first | assumption | (left; assumption) | (right; assumption)))) (halt6_of _ _ (by decide))
  · exact robUniO_of_noAlt (z := z) {1, 2, 4} {0, 1, 5} (hMn_aux z _ (by intro v hv; rcases zmod6_cases v with rfl | rfl | rfl | rfl | rfl | rfl <;>   first | (exfalso; revert hv; decide) | (simp only [show (0 : ZMod 6) + 1 = 1 from rfl, show (1 : ZMod 6) + 1 = 2 from rfl, show (2 : ZMod 6) + 1 = 3 from rfl, show (3 : ZMod 6) + 1 = 4 from rfl, show (4 : ZMod 6) + 1 = 5 from rfl, show (5 : ZMod 6) + 1 = 0 from rfl, show (0 : ZMod 6) - 1 = 5 from rfl, show (1 : ZMod 6) - 1 = 0 from rfl, show (2 : ZMod 6) - 1 = 1 from rfl, show (3 : ZMod 6) - 1 = 2 from rfl, show (4 : ZMod 6) - 1 = 3 from rfl, show (5 : ZMod 6) - 1 = 4 from rfl]; first | assumption | (left; assumption) | (right; assumption)))) (hMx_aux z _ (by intro v hv; rcases zmod6_cases v with rfl | rfl | rfl | rfl | rfl | rfl <;>   first | (exfalso; revert hv; decide) | (simp only [show (0 : ZMod 6) + 1 = 1 from rfl, show (1 : ZMod 6) + 1 = 2 from rfl, show (2 : ZMod 6) + 1 = 3 from rfl, show (3 : ZMod 6) + 1 = 4 from rfl, show (4 : ZMod 6) + 1 = 5 from rfl, show (5 : ZMod 6) + 1 = 0 from rfl, show (0 : ZMod 6) - 1 = 5 from rfl, show (1 : ZMod 6) - 1 = 0 from rfl, show (2 : ZMod 6) - 1 = 1 from rfl, show (3 : ZMod 6) - 1 = 2 from rfl, show (4 : ZMod 6) - 1 = 3 from rfl, show (5 : ZMod 6) - 1 = 4 from rfl]; first | assumption | (left; assumption) | (right; assumption)))) (halt6_of _ _ (by decide))
  · exact robUniO_of_noAlt (z := z) {2, 3, 4} {1, 2, 5} (hMn_aux z _ (by intro v hv; rcases zmod6_cases v with rfl | rfl | rfl | rfl | rfl | rfl <;>   first | (exfalso; revert hv; decide) | (simp only [show (0 : ZMod 6) + 1 = 1 from rfl, show (1 : ZMod 6) + 1 = 2 from rfl, show (2 : ZMod 6) + 1 = 3 from rfl, show (3 : ZMod 6) + 1 = 4 from rfl, show (4 : ZMod 6) + 1 = 5 from rfl, show (5 : ZMod 6) + 1 = 0 from rfl, show (0 : ZMod 6) - 1 = 5 from rfl, show (1 : ZMod 6) - 1 = 0 from rfl, show (2 : ZMod 6) - 1 = 1 from rfl, show (3 : ZMod 6) - 1 = 2 from rfl, show (4 : ZMod 6) - 1 = 3 from rfl, show (5 : ZMod 6) - 1 = 4 from rfl]; first | assumption | (left; assumption) | (right; assumption)))) (hMx_aux z _ (by intro v hv; rcases zmod6_cases v with rfl | rfl | rfl | rfl | rfl | rfl <;>   first | (exfalso; revert hv; decide) | (simp only [show (0 : ZMod 6) + 1 = 1 from rfl, show (1 : ZMod 6) + 1 = 2 from rfl, show (2 : ZMod 6) + 1 = 3 from rfl, show (3 : ZMod 6) + 1 = 4 from rfl, show (4 : ZMod 6) + 1 = 5 from rfl, show (5 : ZMod 6) + 1 = 0 from rfl, show (0 : ZMod 6) - 1 = 5 from rfl, show (1 : ZMod 6) - 1 = 0 from rfl, show (2 : ZMod 6) - 1 = 1 from rfl, show (3 : ZMod 6) - 1 = 2 from rfl, show (4 : ZMod 6) - 1 = 3 from rfl, show (5 : ZMod 6) - 1 = 4 from rfl]; first | assumption | (left; assumption) | (right; assumption)))) (halt6_of _ _ (by decide))
  · exact robUniO_of_noAlt (z := z) {2, 4, 5} {0, 1, 5} (hMn_aux z _ (by intro v hv; rcases zmod6_cases v with rfl | rfl | rfl | rfl | rfl | rfl <;>   first | (exfalso; revert hv; decide) | (simp only [show (0 : ZMod 6) + 1 = 1 from rfl, show (1 : ZMod 6) + 1 = 2 from rfl, show (2 : ZMod 6) + 1 = 3 from rfl, show (3 : ZMod 6) + 1 = 4 from rfl, show (4 : ZMod 6) + 1 = 5 from rfl, show (5 : ZMod 6) + 1 = 0 from rfl, show (0 : ZMod 6) - 1 = 5 from rfl, show (1 : ZMod 6) - 1 = 0 from rfl, show (2 : ZMod 6) - 1 = 1 from rfl, show (3 : ZMod 6) - 1 = 2 from rfl, show (4 : ZMod 6) - 1 = 3 from rfl, show (5 : ZMod 6) - 1 = 4 from rfl]; first | assumption | (left; assumption) | (right; assumption)))) (hMx_aux z _ (by intro v hv; rcases zmod6_cases v with rfl | rfl | rfl | rfl | rfl | rfl <;>   first | (exfalso; revert hv; decide) | (simp only [show (0 : ZMod 6) + 1 = 1 from rfl, show (1 : ZMod 6) + 1 = 2 from rfl, show (2 : ZMod 6) + 1 = 3 from rfl, show (3 : ZMod 6) + 1 = 4 from rfl, show (4 : ZMod 6) + 1 = 5 from rfl, show (5 : ZMod 6) + 1 = 0 from rfl, show (0 : ZMod 6) - 1 = 5 from rfl, show (1 : ZMod 6) - 1 = 0 from rfl, show (2 : ZMod 6) - 1 = 1 from rfl, show (3 : ZMod 6) - 1 = 2 from rfl, show (4 : ZMod 6) - 1 = 3 from rfl, show (5 : ZMod 6) - 1 = 4 from rfl]; first | assumption | (left; assumption) | (right; assumption)))) (halt6_of _ _ (by decide))
  · exact robUniO_of_noAlt (z := z) {1, 2, 4, 5} {0, 1, 5} (hMn_aux z _ (by intro v hv; rcases zmod6_cases v with rfl | rfl | rfl | rfl | rfl | rfl <;>   first | (exfalso; revert hv; decide) | (simp only [show (0 : ZMod 6) + 1 = 1 from rfl, show (1 : ZMod 6) + 1 = 2 from rfl, show (2 : ZMod 6) + 1 = 3 from rfl, show (3 : ZMod 6) + 1 = 4 from rfl, show (4 : ZMod 6) + 1 = 5 from rfl, show (5 : ZMod 6) + 1 = 0 from rfl, show (0 : ZMod 6) - 1 = 5 from rfl, show (1 : ZMod 6) - 1 = 0 from rfl, show (2 : ZMod 6) - 1 = 1 from rfl, show (3 : ZMod 6) - 1 = 2 from rfl, show (4 : ZMod 6) - 1 = 3 from rfl, show (5 : ZMod 6) - 1 = 4 from rfl]; first | assumption | (left; assumption) | (right; assumption)))) (hMx_aux z _ (by intro v hv; rcases zmod6_cases v with rfl | rfl | rfl | rfl | rfl | rfl <;>   first | (exfalso; revert hv; decide) | (simp only [show (0 : ZMod 6) + 1 = 1 from rfl, show (1 : ZMod 6) + 1 = 2 from rfl, show (2 : ZMod 6) + 1 = 3 from rfl, show (3 : ZMod 6) + 1 = 4 from rfl, show (4 : ZMod 6) + 1 = 5 from rfl, show (5 : ZMod 6) + 1 = 0 from rfl, show (0 : ZMod 6) - 1 = 5 from rfl, show (1 : ZMod 6) - 1 = 0 from rfl, show (2 : ZMod 6) - 1 = 1 from rfl, show (3 : ZMod 6) - 1 = 2 from rfl, show (4 : ZMod 6) - 1 = 3 from rfl, show (5 : ZMod 6) - 1 = 4 from rfl]; first | assumption | (left; assumption) | (right; assumption)))) (halt6_of _ _ (by decide))
  · exact robUniO_of_noAlt (z := z) {2, 4, 5} {1, 2, 5} (hMn_aux z _ (by intro v hv; rcases zmod6_cases v with rfl | rfl | rfl | rfl | rfl | rfl <;>   first | (exfalso; revert hv; decide) | (simp only [show (0 : ZMod 6) + 1 = 1 from rfl, show (1 : ZMod 6) + 1 = 2 from rfl, show (2 : ZMod 6) + 1 = 3 from rfl, show (3 : ZMod 6) + 1 = 4 from rfl, show (4 : ZMod 6) + 1 = 5 from rfl, show (5 : ZMod 6) + 1 = 0 from rfl, show (0 : ZMod 6) - 1 = 5 from rfl, show (1 : ZMod 6) - 1 = 0 from rfl, show (2 : ZMod 6) - 1 = 1 from rfl, show (3 : ZMod 6) - 1 = 2 from rfl, show (4 : ZMod 6) - 1 = 3 from rfl, show (5 : ZMod 6) - 1 = 4 from rfl]; first | assumption | (left; assumption) | (right; assumption)))) (hMx_aux z _ (by intro v hv; rcases zmod6_cases v with rfl | rfl | rfl | rfl | rfl | rfl <;>   first | (exfalso; revert hv; decide) | (simp only [show (0 : ZMod 6) + 1 = 1 from rfl, show (1 : ZMod 6) + 1 = 2 from rfl, show (2 : ZMod 6) + 1 = 3 from rfl, show (3 : ZMod 6) + 1 = 4 from rfl, show (4 : ZMod 6) + 1 = 5 from rfl, show (5 : ZMod 6) + 1 = 0 from rfl, show (0 : ZMod 6) - 1 = 5 from rfl, show (1 : ZMod 6) - 1 = 0 from rfl, show (2 : ZMod 6) - 1 = 1 from rfl, show (3 : ZMod 6) - 1 = 2 from rfl, show (4 : ZMod 6) - 1 = 3 from rfl, show (5 : ZMod 6) - 1 = 4 from rfl]; first | assumption | (left; assumption) | (right; assumption)))) (halt6_of _ _ (by decide))
  · exact robUniO_of_noAlt (z := z) {2, 3, 4} {1, 4, 5} (hMn_aux z _ (by intro v hv; rcases zmod6_cases v with rfl | rfl | rfl | rfl | rfl | rfl <;>   first | (exfalso; revert hv; decide) | (simp only [show (0 : ZMod 6) + 1 = 1 from rfl, show (1 : ZMod 6) + 1 = 2 from rfl, show (2 : ZMod 6) + 1 = 3 from rfl, show (3 : ZMod 6) + 1 = 4 from rfl, show (4 : ZMod 6) + 1 = 5 from rfl, show (5 : ZMod 6) + 1 = 0 from rfl, show (0 : ZMod 6) - 1 = 5 from rfl, show (1 : ZMod 6) - 1 = 0 from rfl, show (2 : ZMod 6) - 1 = 1 from rfl, show (3 : ZMod 6) - 1 = 2 from rfl, show (4 : ZMod 6) - 1 = 3 from rfl, show (5 : ZMod 6) - 1 = 4 from rfl]; first | assumption | (left; assumption) | (right; assumption)))) (hMx_aux z _ (by intro v hv; rcases zmod6_cases v with rfl | rfl | rfl | rfl | rfl | rfl <;>   first | (exfalso; revert hv; decide) | (simp only [show (0 : ZMod 6) + 1 = 1 from rfl, show (1 : ZMod 6) + 1 = 2 from rfl, show (2 : ZMod 6) + 1 = 3 from rfl, show (3 : ZMod 6) + 1 = 4 from rfl, show (4 : ZMod 6) + 1 = 5 from rfl, show (5 : ZMod 6) + 1 = 0 from rfl, show (0 : ZMod 6) - 1 = 5 from rfl, show (1 : ZMod 6) - 1 = 0 from rfl, show (2 : ZMod 6) - 1 = 1 from rfl, show (3 : ZMod 6) - 1 = 2 from rfl, show (4 : ZMod 6) - 1 = 3 from rfl, show (5 : ZMod 6) - 1 = 4 from rfl]; first | assumption | (left; assumption) | (right; assumption)))) (halt6_of _ _ (by decide))
  · exact robUniO_of_noAlt (z := z) {1, 2, 4} {1, 4, 5} (hMn_aux z _ (by intro v hv; rcases zmod6_cases v with rfl | rfl | rfl | rfl | rfl | rfl <;>   first | (exfalso; revert hv; decide) | (simp only [show (0 : ZMod 6) + 1 = 1 from rfl, show (1 : ZMod 6) + 1 = 2 from rfl, show (2 : ZMod 6) + 1 = 3 from rfl, show (3 : ZMod 6) + 1 = 4 from rfl, show (4 : ZMod 6) + 1 = 5 from rfl, show (5 : ZMod 6) + 1 = 0 from rfl, show (0 : ZMod 6) - 1 = 5 from rfl, show (1 : ZMod 6) - 1 = 0 from rfl, show (2 : ZMod 6) - 1 = 1 from rfl, show (3 : ZMod 6) - 1 = 2 from rfl, show (4 : ZMod 6) - 1 = 3 from rfl, show (5 : ZMod 6) - 1 = 4 from rfl]; first | assumption | (left; assumption) | (right; assumption)))) (hMx_aux z _ (by intro v hv; rcases zmod6_cases v with rfl | rfl | rfl | rfl | rfl | rfl <;>   first | (exfalso; revert hv; decide) | (simp only [show (0 : ZMod 6) + 1 = 1 from rfl, show (1 : ZMod 6) + 1 = 2 from rfl, show (2 : ZMod 6) + 1 = 3 from rfl, show (3 : ZMod 6) + 1 = 4 from rfl, show (4 : ZMod 6) + 1 = 5 from rfl, show (5 : ZMod 6) + 1 = 0 from rfl, show (0 : ZMod 6) - 1 = 5 from rfl, show (1 : ZMod 6) - 1 = 0 from rfl, show (2 : ZMod 6) - 1 = 1 from rfl, show (3 : ZMod 6) - 1 = 2 from rfl, show (4 : ZMod 6) - 1 = 3 from rfl, show (5 : ZMod 6) - 1 = 4 from rfl]; first | assumption | (left; assumption) | (right; assumption)))) (halt6_of _ _ (by decide))
  · exact robUniO_of_noAlt (z := z) {2, 3, 4} {1, 2, 4, 5} (hMn_aux z _ (by intro v hv; rcases zmod6_cases v with rfl | rfl | rfl | rfl | rfl | rfl <;>   first | (exfalso; revert hv; decide) | (simp only [show (0 : ZMod 6) + 1 = 1 from rfl, show (1 : ZMod 6) + 1 = 2 from rfl, show (2 : ZMod 6) + 1 = 3 from rfl, show (3 : ZMod 6) + 1 = 4 from rfl, show (4 : ZMod 6) + 1 = 5 from rfl, show (5 : ZMod 6) + 1 = 0 from rfl, show (0 : ZMod 6) - 1 = 5 from rfl, show (1 : ZMod 6) - 1 = 0 from rfl, show (2 : ZMod 6) - 1 = 1 from rfl, show (3 : ZMod 6) - 1 = 2 from rfl, show (4 : ZMod 6) - 1 = 3 from rfl, show (5 : ZMod 6) - 1 = 4 from rfl]; first | assumption | (left; assumption) | (right; assumption)))) (hMx_aux z _ (by intro v hv; rcases zmod6_cases v with rfl | rfl | rfl | rfl | rfl | rfl <;>   first | (exfalso; revert hv; decide) | (simp only [show (0 : ZMod 6) + 1 = 1 from rfl, show (1 : ZMod 6) + 1 = 2 from rfl, show (2 : ZMod 6) + 1 = 3 from rfl, show (3 : ZMod 6) + 1 = 4 from rfl, show (4 : ZMod 6) + 1 = 5 from rfl, show (5 : ZMod 6) + 1 = 0 from rfl, show (0 : ZMod 6) - 1 = 5 from rfl, show (1 : ZMod 6) - 1 = 0 from rfl, show (2 : ZMod 6) - 1 = 1 from rfl, show (3 : ZMod 6) - 1 = 2 from rfl, show (4 : ZMod 6) - 1 = 3 from rfl, show (5 : ZMod 6) - 1 = 4 from rfl]; first | assumption | (left; assumption) | (right; assumption)))) (halt6_of _ _ (by decide))



/-- `LexLt3` as the order of `toLex` triples. -/
theorem lexLt3_toLex_dw {p q : ℝ × ℝ × ℝ} (h : LexLt3 p q) :
    toLex (p.1, toLex (p.2.1, p.2.2)) < toLex (q.1, toLex (q.2.1, q.2.2)) := by
  simp only [LexLt3, LexPos3] at h
  simp only [Prod.Lex.lt_iff, ofLex_toLex]
  rcases h with h | ⟨h1, h2 | ⟨h2', h3⟩⟩
  · exact Or.inl (by linarith)
  · exact Or.inr ⟨by linarith, Or.inl (by linarith)⟩
  · exact Or.inr ⟨by linarith, Or.inr ⟨by linarith, by linarith⟩⟩

/-- **A 6-cycle `0 1 2 3 4 5` is `RobUniLex`** when `3` is below a neighbour (`hV`), `0` above a neighbour (`hL`),
and the two junction clauses `c1`, `c2` hold (`robUniO_six_dw` via `robUniO_of_noAlt`, 9 cases). -/
theorem robUniLex_six_dw (z : ZMod 6 → ℝ × ℝ × ℝ)
    (hV : LexLt3 (z 3) (z 2) ∨ LexLt3 (z 3) (z 4)) (hL : LexLt3 (z 5) (z 0) ∨ LexLt3 (z 1) (z 0))
    (c1 : LexLt3 (z 4) (z 5) ∨ LexLt3 (z 4) (z 3) ∨ LexLt3 (z 0) (z 5))
    (c2 : LexLt3 (z 2) (z 1) ∨ LexLt3 (z 2) (z 3) ∨ LexLt3 (z 0) (z 1)) : RobUniLex z := by
  rw [robUniLex_iff_O]
  apply robUniO_six_dw
  · exact hV.imp lexLt3_toLex_dw lexLt3_toLex_dw
  · exact hL.imp lexLt3_toLex_dw lexLt3_toLex_dw
  · exact c1.imp lexLt3_toLex_dw (Or.imp lexLt3_toLex_dw lexLt3_toLex_dw)
  · exact c2.imp lexLt3_toLex_dw (Or.imp lexLt3_toLex_dw lexLt3_toLex_dw)

/-- Rim `1 2 5 3 4 6` of the K0 view on the double wall (facets `012 016 025 0345 046` up, `126 235 236 346`
down). -/
def rimKD : ZMod 6 → Fin 7 := ![1, 2, 5, 3, 4, 6]
def UKD : Finset (Fin 9) := {0, 1, 2, 3, 4}
def DnKD : Finset (Fin 9) := {5, 6, 7, 8}

theorem rimKD_cyc : S0xCycUD s0x_S24 rimKD UKD DnKD := by decide
theorem rimKD_inj : Function.Injective rimKD := by decide

/-- The K0 view depth triple of a vertex. -/
noncomputable def k0P {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (v : Fin 7) : ℝ × ℝ × ℝ :=
  (⟪x v, x 0 - x 4⟫, ⟪x v, x 0 - x 5⟫, ⟪x v, F.N 3⟫)

/-- **The K0 view on the double wall**: `126`, `235`, `236` down and the rim `1 2 5 3 4 6` `RobUniLex`. -/
def K0DViewOK {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) : Prop :=
  K0Dn F 5 ∧ K0Dn F 6 ∧ K0Dn F 7 ∧ RobUniLex (k0Z F rimKD)

theorem lexAny_of_k0DView (F : S0xFac 9 s0x_S24 x) (h : K0DViewOK F) : Gen.LexAny F := by
  obtain ⟨h5, h6, h7, hR⟩ := h
  refine ⟨6, inferInstance, rimKD, UKD, DnKD, x 0 - x 4, x 0 - x 5, F.N 3, by norm_num, rimKD_inj,
    rimKD_cyc, ?_, ?_, hR⟩
  · intro t ht
    simp only [UKD, Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl
    exacts [k0_up_of_mem F 0 (by decide) (by decide), k0_up_of_mem F 1 (by decide) (by decide),
      k0_up_of_mem F 2 (by decide) (by decide), k0_up3 F, k0_up4 F]
  · intro t ht
    simp only [DnKD, Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl
    exacts [h5, h6, h7, k0_dn8 F]

theorem lexAny_of_k0DView_sym (F : S0xFac 9 s0x_S24 x) (h : K0DViewOK (Sym.sym24 F)) : Gen.LexAny F :=
  Sym.lexAny_sym F (lexAny_of_k0DView (Sym.sym24 F) h)

/-- `126` is down on the double wall (level 3, `bs_n53_neg`). -/
theorem k0_dn5_dw (F : S0xFac 9 s0x_S24 x) (hw4 : oblX0 x 4 = 1) (hw5 : oblX0 x 5 = 1) : K0Dn F 5 := by
  right
  refine ⟨?_, Or.inr ⟨?_, ?_⟩⟩
  · rw [F.inner_sub 5 0 4, bs_f5_obl F 4, hw4]; ring
  · rw [F.inner_sub 5 0 5, bs_f5_obl F 5, hw5]; ring
  · linarith [bs_n53_neg F hw4 hw5]

/-- `236` is down on the wall `a4 = 1` (level 1). -/
theorem k0_dn7_wall (F : S0xFac 9 s0x_S24 x) (hw4 : oblX0 x 4 = 1) : K0Dn F 7 := by
  have T := M4.type24OfFac F
  have hb4 : 0 < oblX2 x 4 := T.X2_pos (by decide)
  have hc4 : 0 < oblX6 x 4 := T.X6_pos (by decide)
  have e74 := M4.fac_eval F 7 4
  rw [F.zero 7 2 (by decide), F.zero 7 6 (by decide), hw4] at e74
  have h1 := F.neg 7 1 (by decide)
  left
  rw [F.inner_sub 7 0 4]; nlinarith

/-- On the wall `a4 = 1`, `1` is above `6` or `2` (level 1): `x 4 - x 0 = b4 (x 2 - x 1) + c4 (x 6 - x 1)`, so
`|e4|² = b4 ⟪x 2 - x 1, e4⟫ + c4 ⟪x 6 - x 1, e4⟫ > 0`. -/
theorem k0_lam_wall (F : S0xFac 9 s0x_S24 x) (hw4 : oblX0 x 4 = 1) :
    LexLt3 (k0P F 6) (k0P F 1) ∨ LexLt3 (k0P F 2) (k0P F 1) := by
  have T := M4.type24OfFac F
  have hb4 : 0 < oblX2 x 4 := T.X2_pos (by decide)
  have hc4 : 0 < oblX6 x 4 := T.X6_pos (by decide)
  have r4 := T.rep 4
  rw [hw4] at r4
  have e4 : x 4 - x 0 = oblX2 x 4 • (x 2 - x 1) + oblX6 x 4 • (x 6 - x 1) := by rw [r4]; module
  have hu : x 4 - x 0 ≠ 0 := by
    intro h0
    have e := F.inner_sub 8 4 0
    rw [h0, inner_zero_right, F.zero 8 4 (by decide)] at e
    linarith [F.neg 8 0 (by decide)]
  have hE : 0 < ⟪x 4 - x 0, x 4 - x 0⟫ := real_inner_self_pos.mpr hu
  have hsum : ⟪x 4 - x 0, x 4 - x 0⟫ =
      oblX2 x 4 * ⟪x 2 - x 1, x 4 - x 0⟫ + oblX6 x 4 * ⟪x 6 - x 1, x 4 - x 0⟫ := by
    conv_lhs => rw [e4]
    rw [inner_add_left, real_inner_smul_left, real_inner_smul_left]
    conv_lhs => rw [← e4]
  have k6 : ⟪x 1, x 0 - x 4⟫ - ⟪x 6, x 0 - x 4⟫ = ⟪x 6 - x 1, x 4 - x 0⟫ := by
    rw [show x 0 - x 4 = -(x 4 - x 0) by abel, inner_neg_right, inner_neg_right, inner_sub_left]; ring
  have k2 : ⟪x 1, x 0 - x 4⟫ - ⟪x 2, x 0 - x 4⟫ = ⟪x 2 - x 1, x 4 - x 0⟫ := by
    rw [show x 0 - x 4 = -(x 4 - x 0) by abel, inner_neg_right, inner_neg_right, inner_sub_left]; ring
  by_contra hc
  push Not at hc
  obtain ⟨n6, n2⟩ := hc
  have a6 : ¬ 0 < ⟪x 6 - x 1, x 4 - x 0⟫ := fun h => n6 (Or.inl (by simp only [k0P]; rw [k6]; exact h))
  have a2 : ¬ 0 < ⟪x 2 - x 1, x 4 - x 0⟫ := fun h => n2 (Or.inl (by simp only [k0P]; rw [k2]; exact h))
  push Not at a6 a2
  nlinarith

/-- For `t ≤ 1` (and `s + t > 1`) `3` is below `5` or `4` (level 1): the chain `5 3 4` is not peaked at `3`. -/
theorem k0_vee (F : S0xFac 9 s0x_S24 x) {s t : ℝ} (hs0 : 0 < s) (ht0 : 0 < t) (ht1 : t ≤ 1) (hst : 1 < s + t)
    (hdec : x 3 - x 0 = s • (x 4 - x 0) + t • (x 5 - x 0)) :
    LexLt3 (k0P F 3) (k0P F 5) ∨ LexLt3 (k0P F 3) (k0P F 4) := by
  have hu : x 4 - x 0 ≠ 0 := by
    intro h0
    have e := F.inner_sub 8 4 0
    rw [h0, inner_zero_right, F.zero 8 4 (by decide)] at e
    linarith [F.neg 8 0 (by decide)]
  have hE : 0 < ⟪x 4 - x 0, x 4 - x 0⟫ := real_inner_self_pos.mpr hu
  set E := ⟪x 4 - x 0, x 4 - x 0⟫
  set c := ⟪x 5 - x 0, x 4 - x 0⟫
  have A : ⟪x 3 - x 0, x 4 - x 0⟫ = s * E + t * c := by
    rw [hdec, inner_add_left, real_inner_smul_left, real_inner_smul_left]
  have g5 : ⟪x 5, x 0 - x 4⟫ - ⟪x 3, x 0 - x 4⟫ = s * E - (1 - t) * c := by
    rw [← inner_sub_left, show x 5 - x 3 = (x 5 - x 0) - (x 3 - x 0) by abel,
      show x 0 - x 4 = -(x 4 - x 0) by abel, inner_neg_right, inner_sub_left, A]; ring
  have g4 : ⟪x 4, x 0 - x 4⟫ - ⟪x 3, x 0 - x 4⟫ = t * c - (1 - s) * E := by
    rw [← inner_sub_left, show x 4 - x 3 = (x 4 - x 0) - (x 3 - x 0) by abel,
      show x 0 - x 4 = -(x 4 - x 0) by abel, inner_neg_right, inner_sub_left, A]; ring
  by_contra hc
  push Not at hc
  obtain ⟨n5, n4⟩ := hc
  have a5 : ¬ 0 < s * E - (1 - t) * c := fun h => n5 (Or.inl (by simp only [k0P]; rw [g5]; exact h))
  have a4 : ¬ 0 < t * c - (1 - s) * E := fun h => n4 (Or.inl (by simp only [k0P]; rw [g4]; exact h))
  push Not at a5 a4
  rcases le_or_gt c 0 with hc0 | hc0
  · nlinarith
  · nlinarith [mul_pos hs0 hE, mul_pos ht0 hc0]

/-- The junction clauses of the K0 view on the double wall: `4` below `6` or `3`, or `1` below `6`; and `5` below
`2` or `3`, or `1` below `2` (lex depths in `(x 0 - x 4, x 0 - x 5, N3)`). -/
def DwK0C {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) : Prop :=
  (LexLt3 (k0P F 4) (k0P F 6) ∨ LexLt3 (k0P F 4) (k0P F 3) ∨ LexLt3 (k0P F 1) (k0P F 6)) ∧
    (LexLt3 (k0P F 5) (k0P F 2) ∨ LexLt3 (k0P F 5) (k0P F 3) ∨ LexLt3 (k0P F 1) (k0P F 2))

/-- **The K0 view on the double wall from the junction clauses**: `a4 = a5 = 1`, `t ≤ 1`, `DwK0C`. -/
theorem k0DViewOK_of (F : S0xFac 9 s0x_S24 x) (hw4 : oblX0 x 4 = 1) (hw5 : oblX0 x 5 = 1) {s t : ℝ}
    (hs0 : 0 < s) (ht0 : 0 < t) (ht1 : t ≤ 1) (hst : 1 < s + t)
    (hdec : x 3 - x 0 = s • (x 4 - x 0) + t • (x 5 - x 0)) (hC : DwK0C F) : K0DViewOK F := by
  refine ⟨k0_dn5_dw F hw4 hw5, k0_dn6 F hs0 ht1 hdec, k0_dn7_wall F hw4, ?_⟩
  obtain ⟨c1, c2⟩ := hC
  exact robUniLex_six_dw (k0Z F rimKD) (k0_vee F hs0 ht0 ht1 hst hdec) (k0_lam_wall F hw4) c1 c2

/-- The mirror form (the K0 view of `π24 x` on the double wall, at `(t, s)`). -/
theorem k0DViewOK_sym_of (F : S0xFac 9 s0x_S24 x) (hw4 : oblX0 x 4 = 1) (hw5 : oblX0 x 5 = 1) {s t : ℝ}
    (hs0 : 0 < s) (ht0 : 0 < t) (hs1 : s ≤ 1) (hst : 1 < s + t)
    (hdec : x 3 - x 0 = s • (x 4 - x 0) + t • (x 5 - x 0)) (hC : DwK0C (Sym.sym24 F)) :
    K0DViewOK (Sym.sym24 F) := by
  have o4 : oblX0 (x ∘ Sym.pi24) 4 = oblX0 x 5 := by rw [Sym.oblX0_comp_pi24]; simp
  have o5 : oblX0 (x ∘ Sym.pi24) 5 = oblX0 x 4 := by rw [Sym.oblX0_comp_pi24]; simp
  refine k0DViewOK_of (Sym.sym24 F) (by rw [o4]; exact hw5) (by rw [o5]; exact hw4) (s := t) (t := s) ht0 hs0 hs1
    (by linarith) ?_ hC
  simp only [Function.comp_apply, Sym.pi24_0, Sym.pi24_3, Sym.pi24_4, Sym.pi24_5]
  rw [hdec]; abel


/-! ### The residue after the double-wall K0 views -/

/-- The double-wall K0 view's conditions at `(s, t)` (`k0DViewOK_of`). -/
def DwK0Cut {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (t : ℝ) : Prop :=
  oblX0 x 4 = 1 ∧ oblX0 x 5 = 1 ∧ t ≤ 1 ∧ DwK0C F

/-- `Q45ResSTB` where neither double-wall K0 view applies: off the double wall this is `Q45ResSTB`; on it, the
explicit failure of the junction clauses `DwK0C` (or `t > 1`), for both views. -/
def Q45ResSTD {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (s t : ℝ) : Prop :=
  Q45ResSTB F s t ∧ ¬ DwK0Cut F t ∧ ¬ DwK0Cut (Sym.sym24 F) s

/-- The branch-tagged residue after the double-wall K0 views. -/
def Q45ResWD {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) : Prop :=
  ∃ s t : ℝ, 0 < s ∧ 0 < t ∧ 1 < s + t ∧ x 3 - x 0 = s • (x 4 - x 0) + t • (x 5 - x 0) ∧ Q45ResSTD F s t

/-- **The double-wall K0 views cut the residue**: a point of `Q45ResSTB` is `LexAny` or in `Q45ResSTD`. -/
theorem q45_resD_local (F : S0xFac 9 s0x_S24 x) {s t : ℝ} (hs0 : 0 < s) (ht0 : 0 < t) (hst : 1 < s + t)
    (hdec : x 3 - x 0 = s • (x 4 - x 0) + t • (x 5 - x 0)) (h : Q45ResSTB F s t) :
    Gen.LexAny F ∨ Q45ResSTD F s t := by
  by_cases hA : DwK0Cut F t
  · obtain ⟨h4, h5, ht, hC⟩ := hA
    exact Or.inl (lexAny_of_k0DView F (k0DViewOK_of F h4 h5 hs0 ht0 ht hst hdec hC))
  by_cases hB : DwK0Cut (Sym.sym24 F) s
  · obtain ⟨h4, h5, hs, hC⟩ := hB
    have o4 : oblX0 (x ∘ Sym.pi24) 4 = oblX0 x 5 := by rw [Sym.oblX0_comp_pi24]; simp
    have o5 : oblX0 (x ∘ Sym.pi24) 5 = oblX0 x 4 := by rw [Sym.oblX0_comp_pi24]; simp
    rw [o4] at h4; rw [o5] at h5
    exact Or.inl (lexAny_of_k0DView_sym F (k0DViewOK_sym_of F h5 h4 hs0 ht0 hs hst hdec hC))
  exact Or.inr ⟨h, hA, hB⟩

/-- `Q45ResWD ⊆ Q45ResWB`. -/
theorem q45ResWB_of_D {F : S0xFac 9 s0x_S24 x} (h : Q45ResWD F) : Q45ResWB F := by
  obtain ⟨s, t, hs, ht, hst, hd, h⟩ := h
  exact ⟨s, t, hs, ht, hst, hd, h.1⟩

/-- **Global form**: on the corner every point has `LexAny`, `AnyFaceChord`, is Rupert, or lies in `Q45ResWD`. -/
theorem q45_resD (F : S0xFac 9 s0x_S24 x) (h4 : 1 ≤ oblX0 x 4) (h5 : 1 ≤ oblX0 x 5) :
    Gen.LexAny F ∨ Gen.AnyFaceChord F ∨ IsRupert (univ.image x) ∨ Q45ResWD F := by
  rcases q45_resB F h4 h5 with h | h | h | ⟨s, t, hs0, ht, hst, hd, h⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · rcases q45_resD_local F hs0 ht hst hd h with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inr ⟨s, t, hs0, ht, hst, hd, h⟩))

/-- [OPEN] **The special piece after the double-wall K0 views, Rupert form**: `OpenSpecialB` with `Q45ResWD` in
place of `Q45ResWB`. -/
def OpenSpecialD : Prop := ∀ (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x), ¬ H24K.SAT.OB1 x →
  1 ≤ oblX0 x 4 → 1 ≤ oblX0 x 5 →
  oblX0 x 4 * oblX6 x 3 - oblX0 x 3 * oblX6 x 4 < 0 →
  0 < oblX0 x 3 * oblX2 x 5 - oblX0 x 5 * oblX2 x 3 →
  0 < oblX0 x 4 * oblX2 x 5 - oblX0 x 5 * oblX2 x 4 →
  0 < oblX0 x 5 * oblX6 x 4 - oblX0 x 4 * oblX6 x 5 →
  Q45ResWD F → HoleFull x F → IsRupert (univ.image x)

/-- [PROVED] `OpenSpecialB → OpenSpecialD` (`q45ResWB_of_D`). -/
theorem openSpecialD_of_openSpecialB (h : OpenSpecialB) : OpenSpecialD :=
  fun x F hO h4 h5 b1 b2 b3 b4 hr hF => h x F hO h4 h5 b1 b2 b3 b4 (q45ResWB_of_D hr) hF

/-- Every `Hole24` point off `OB1` is Rupert, given `OpenSpecialD`. -/
theorem hole24_offOB1_D {F : S0xFac 9 s0x_S24 x} (h : Hole24 x F) (hO : ¬ H24K.SAT.OB1 x)
    (hS : OpenSpecialD) : IsRupert (univ.image x) := by
  obtain ⟨b1, b2, b3⟩ := resid24_frame_signs h.2.2.1 hO
  have b4 := resid24_b1245 h.2.2.1 hO
  obtain ⟨-, h4, h5⟩ := offWall_of_hole24 h hO
  have hF := holeFull_of_hole24 h
  rcases q45_resD F h4 h5 with hL | hA | hR | hr
  · exact (hF.1.2.2.2.1 hL).elim
  · exact (hF.1.2.2.1 hA).elim
  · exact hR
  · exact hS x F hO h4 h5 b1 b2 b3 b4 hr hF

/-- [PROVED] Generic + special (after the double-wall K0 views) assemble to `Open24Rupert`. -/
theorem open24Rupert_of_split_D (h1 : OpenOB1) (h2 : OpenSpecialD) : Open24Rupert := by
  intro x fs hh hH
  by_cases hO : H24K.SAT.OB1 x
  · exact (h1 x _ hO (holeFull_of_hole24 hH)).elim
  · exact hole24_offOB1_D hH hO h2

end DwK0

end Minimality.T24.OSpec
