module

public import Minimality.Type24OffOB1D15

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21 Minimality.FaceChord Minimality.T24.SAT Minimality.T24.Stmt Minimality.T24.Q45
  Minimality.T24.Reg Minimality.T24.A19

/-!
# Type 24 off `OB1`: the plane-234 view on the B2 valley (job OSPEC14, nopert229 notes/OPENSPECIAL-STRATEGY.md)

On the B2 / C2 corner ties the face-plane view `B2ViewOK` fails exactly when vertex `1` is a strict valley of its rim
`0 1 2 3 4` (`z1 < z0`, `z1 < z2` at `bB2`).  The cell `B` of that rim (facets `012 025 0345 235` up, the five facets
through `6` down) still carries good views on every such sampled point; their region (depth order `3 < 4 < 2 < 1 < 0`)
has the corner `z2 = z3 = z4`, the normal `n234` of the plane through `x 2`, `x 3`, `x 4`.  The **T234 view** is the lex
view `(b, x 4 - x 3, x 5 - x 6)` with `b = ± n234`:

* the depths of `2`, `3`, `4` agree at level 1 (`t234_tie3`, `t234_tie4`: `b ⊥` the plane), and level 2 puts `3`
  strictly below `4` (`t234_lt34`: `⟪x 4 - x 3, x 4 - x 3⟫ > 0`), so `3` is never a peak;
* with `z2 < z1` and `z2 < z0` at level 1 the rim `0 1 2 3 4` is `RobUniLex` (`t234_rim_B`, via `robUniLex_five_e26`),
  and with `z2 < z0` alone the rim `0 2 3 4` is (`t234_rim_D`, mixed diagonal pairs).

`T234ViewOK` asks for the facet signs (`0345 235` up, `016 046 126 236 346` down, `012` up with `z2 < z1` or `012` down
with `025` up) and `z2 < z0`; the rim condition is derived (`lexAny_of_t234View`, mirror `lexAny_of_t234View_sym`).  The
facet pattern is the pair-view pattern of the diagonal `5`, `6` (`pairView_up` / `_dn`), but at level 1 the signs
`⟪N t, n234⟫` are metric and stay hypotheses.  Data (SAMPLED, exact, nopert229 tools/genleaves/runs/ospec14 t234.exe):
all 25 sampled valley points (incl. `TC2_3888_hlex`, the OSPEC13 counterexample), B2T 580 / 587, C2T 588 / 595.

**OSPEC15** (section `T234D`): on the B2 branch (`T234Br`: `s > 1`, `t > 0`, frame sign `b1`, the tie `⟪x 2, e34⟫ =
⟪x 5, e34⟫`, `⟪x 2 - x 5, e5⟫ ≥ 0`, all supplied by `ResB2T`, `t234Br_of_resB2T`) three letters are derived at the
orientation `t234b` with `x 5` above: `z2 < z0` (`t234_z0`, affine), `z2 < z1` (`t234_z1`, from `b1` and
`cross35_pos`), `0345` up (`t234_up3_prod`, metric: `⟪N3, n⟫ ⟪x5 - x2, n⟫ = -f3(x 2) q1`, `q1 > 0` by the tie and
`s > 1`).  `t234ViewOK_iff_red`: there `T234ViewOK ↔ T234Red` (seven facet letters).  Reduced residue `Q45ResWI`,
`OpenSpecialI` (equivalent to `OpenSpecialH`, `openSpecialI_iff_H`).
-/

namespace Minimality.T24.OSpec

section T234
open Minimality.LexCell

variable {x : Fin 7 → ℝ³}

/-- Normal of the plane through `x 2`, `x 3`, `x 4`. -/
noncomputable def n234 (x : Fin 7 → ℝ³) : ℝ³ := cross (x 3 - x 2) (x 4 - x 2)

/-- Facet `t` is up in the lex view `(b, x 4 - x 3, x 5 - x 6)`. -/
def T234Up {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (b : ℝ³) (t : Fin 9) : Prop :=
  LexPos3 ⟪F.N t, b⟫ ⟪F.N t, x 4 - x 3⟫ ⟪F.N t, x 5 - x 6⟫
/-- Facet `t` is down in the lex view `(b, x 4 - x 3, x 5 - x 6)`. -/
def T234Dn {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (b : ℝ³) (t : Fin 9) : Prop :=
  LexPos3 (-⟪F.N t, b⟫) (-⟪F.N t, x 4 - x 3⟫) (-⟪F.N t, x 5 - x 6⟫)

/-- Lex depth triples of a rim in the view `(b, x 4 - x 3, x 5 - x 6)`. -/
noncomputable def t234Z (x : Fin 7 → ℝ³) (b : ℝ³) {k : ℕ} (c : ZMod k → Fin 7) : ZMod k → ℝ × ℝ × ℝ :=
  fun i => (⟪x (c i), b⟫, ⟪x (c i), x 4 - x 3⟫, ⟪x (c i), x 5 - x 6⟫)

/-- The T234 view at the level-1 direction `b`: facets `0345 235` up, `016 046 126 236 346` down, `z2 < z0` at level
1, and `012` up with `z2 < z1` (rim `0 1 2 3 4`) or `012` down with `025` up (rim `0 2 3 4`). -/
def T234At {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (b : ℝ³) : Prop :=
  T234Up F b 3 ∧ T234Up F b 6 ∧ T234Dn F b 1 ∧ T234Dn F b 4 ∧ T234Dn F b 5 ∧ T234Dn F b 7 ∧ T234Dn F b 8 ∧
    ⟪x 2, b⟫ < ⟪x 0, b⟫ ∧ ((T234Up F b 0 ∧ ⟪x 2, b⟫ < ⟪x 1, b⟫) ∨ (T234Dn F b 0 ∧ T234Up F b 2))

/-- **The T234 view condition** (either orientation of the plane normal `n234`). -/
def T234ViewOK {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) : Prop :=
  T234At F (n234 x) ∨ T234At F (-n234 x)

/-- Rim `0 2 3 4` with facets `025 0345 235` up (the reverse orientation of `rimDB`). -/
def UTD : Finset (Fin 9) := {2, 3, 6}
def DnTD : Finset (Fin 9) := {0, 1, 4, 5, 7, 8}

theorem rimTD_cyc : S0xCycUD s0x_S24 rimDB UTD DnTD := by decide

/-- `x 3` is at the depth of `x 2` along `± n234`. -/
theorem t234_tie3 {b : ℝ³} (hb : b = n234 x ∨ b = -n234 x) : ⟪x 3, b⟫ = ⟪x 2, b⟫ := by
  have h : ⟪x 3 - x 2, b⟫ = 0 := by
    rcases hb with rfl | rfl
    · rw [real_inner_comm]; exact inner_cross_left _ _
    · rw [inner_neg_right, real_inner_comm, n234, inner_cross_left, neg_zero]
  rw [inner_sub_left] at h; linarith

/-- `x 4` is at the depth of `x 2` along `± n234`. -/
theorem t234_tie4 {b : ℝ³} (hb : b = n234 x ∨ b = -n234 x) : ⟪x 4, b⟫ = ⟪x 2, b⟫ := by
  have h : ⟪x 4 - x 2, b⟫ = 0 := by
    rcases hb with rfl | rfl
    · rw [real_inner_comm]; exact inner_cross_right _ _
    · rw [inner_neg_right, real_inner_comm, n234, inner_cross_right, neg_zero]
  rw [inner_sub_left] at h; linarith

/-- Level 2 puts `x 3` strictly below `x 4`: `⟪x 4 - x 3, x 4 - x 3⟫ > 0` (`x 3 ≠ x 4`, facet `046`). -/
theorem t234_lt34 (F : S0xFac 9 s0x_S24 x) : ⟪x 3, x 4 - x 3⟫ < ⟪x 4, x 4 - x 3⟫ := by
  have hne : x 4 - x 3 ≠ 0 := by
    intro h
    have h43 : x 4 = x 3 := sub_eq_zero.mp h
    have h0 : F.f 4 (x 4) = 0 := F.zero 4 4 (by decide)
    have h1 : F.f 4 (x 3) < 0 := F.neg 4 3 (by decide)
    rw [h43] at h0; linarith
  have hp : 0 < ⟪x 4 - x 3, x 4 - x 3⟫ := real_inner_self_pos.mpr hne
  rw [inner_sub_left] at hp; linarith

/-- **The rim `0 1 2 3 4` in the T234 view**: `RobUniLex` from `z2 < z1`, `z2 < z0` at level 1. -/
theorem t234_rim_B (F : S0xFac 9 s0x_S24 x) {b : ℝ³} (hb : b = n234 x ∨ b = -n234 x)
    (h20 : ⟪x 2, b⟫ < ⟪x 0, b⟫) (h21 : ⟪x 2, b⟫ < ⟪x 1, b⟫) : RobUniLex (t234Z x b rimB2B) := by
  have e0 : rimB2B 0 = 0 := by decide
  have e1 : rimB2B 1 = 1 := by decide
  have e2 : rimB2B 2 = 2 := by decide
  have e3 : rimB2B 3 = 3 := by decide
  have e4 : rimB2B 4 = 4 := by decide
  have t3 := t234_tie3 hb
  have t4 := t234_tie4 hb
  have l34 := t234_lt34 F
  apply robUniLex_five_e26
  · simp only [t234Z, e1, e2]; exact lexLt3_of_fst h21
  · simp only [t234Z, e3, e4]
    exact Or.inr ⟨by simp only; linarith, Or.inl (by simp only; linarith)⟩
  · simp only [t234Z, e4, e0]; exact lexLt3_of_fst (by simp only; linarith)
  · simp only [t234Z, e3, e0]; exact lexLt3_of_fst (by simp only; linarith)

/-- **The rim `0 2 3 4` in the T234 view**: `RobUniLex` from `z2 < z0` at level 1 (mixed diagonal pairs). -/
theorem t234_rim_D (F : S0xFac 9 s0x_S24 x) {b : ℝ³} (hb : b = n234 x ∨ b = -n234 x)
    (h20 : ⟪x 2, b⟫ < ⟪x 0, b⟫) : RobUniLex (t234Z x b rimDB) := by
  have e0 : rimDB 0 = 0 := by decide
  have e1 : rimDB 1 = 2 := by decide
  have e2 : rimDB 2 = 3 := by decide
  have e3 : rimDB 3 = 4 := by decide
  have t3 := t234_tie3 hb
  have t4 := t234_tie4 hb
  have l34 := t234_lt34 F
  apply robUniLex_four_of_mixed
  · refine ⟨(2, 3), by decide, ?_⟩
    simp only [t234Z, e2, e3]
    exact Or.inr ⟨by simp only; linarith, Or.inl (by simp only; linarith)⟩
  · refine ⟨(0, 1), by decide, ?_⟩
    simp only [t234Z, e0, e1]; exact lexLt3_of_fst h20

/-- **The T234 view is a lex cell** at either orientation of `n234`. -/
theorem lexAny_of_t234At (F : S0xFac 9 s0x_S24 x) {b : ℝ³} (hb : b = n234 x ∨ b = -n234 x) (h : T234At F b) :
    Gen.LexAny F := by
  obtain ⟨u3, u6, n1, n4, n5, n7, n8, h20, ⟨u0, h21⟩ | ⟨n0, u2⟩⟩ := h
  · refine ⟨5, inferInstance, rimB2B, UB2B, DnB2B, b, x 4 - x 3, x 5 - x 6, by norm_num, rimB2B_inj,
      rimB2B_cyc, ?_, ?_, t234_rim_B F hb h20 h21⟩
    · intro t ht
      simp only [UB2B, Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl | rfl
      exacts [u0, u3, u6]
    · intro t ht
      simp only [DnB2B, Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl | rfl | rfl | rfl
      exacts [n1, n4, n5, n7, n8]
  · refine ⟨4, inferInstance, rimDB, UTD, DnTD, b, x 4 - x 3, x 5 - x 6, le_rfl, rimDB_inj,
      rimTD_cyc, ?_, ?_, t234_rim_D F hb h20⟩
    · intro t ht
      simp only [UTD, Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl | rfl
      exacts [u2, u3, u6]
    · intro t ht
      simp only [DnTD, Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl | rfl | rfl | rfl | rfl
      exacts [n0, n1, n4, n5, n7, n8]

/-- **The T234 view condition gives a lex cell.** -/
theorem lexAny_of_t234View (F : S0xFac 9 s0x_S24 x) (h : T234ViewOK F) : Gen.LexAny F := by
  rcases h with h | h
  · exact lexAny_of_t234At F (Or.inl rfl) h
  · exact lexAny_of_t234At F (Or.inr rfl) h

/-- **The mirror T234 view** (`π = (2 6)(4 5)`): the plane through `x 6`, `x 3`, `x 5`, view `(± n, x 5 - x 3, x 4 -
x 2)` of `x`. -/
theorem lexAny_of_t234View_sym (F : S0xFac 9 s0x_S24 x) (h : T234ViewOK (Sym.sym24 F)) : Gen.LexAny F :=
  Sym.lexAny_sym F (lexAny_of_t234View (Sym.sym24 F) h)

/-! ### The residue after the T234 views -/

/-- `Q45ResSTG` where neither T234 view (nor its mirror) applies. -/
def Q45ResSTH {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (s t : ℝ) : Prop :=
  Q45ResSTG F s t ∧ ¬ T234ViewOK F ∧ ¬ T234ViewOK (Sym.sym24 F)

/-- The branch-tagged residue after the T234 views. -/
def Q45ResWH {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) : Prop :=
  ∃ s t : ℝ, 0 < s ∧ 0 < t ∧ 1 < s + t ∧ x 3 - x 0 = s • (x 4 - x 0) + t • (x 5 - x 0) ∧ Q45ResSTH F s t

/-- **The T234 views cut the residue**: a point of `Q45ResSTG` is `LexAny` or in `Q45ResSTH`. -/
theorem q45_resH_local (F : S0xFac 9 s0x_S24 x) {s t : ℝ} (h : Q45ResSTG F s t) :
    Gen.LexAny F ∨ Q45ResSTH F s t := by
  by_cases hA : T234ViewOK F
  · exact Or.inl (lexAny_of_t234View F hA)
  by_cases hB : T234ViewOK (Sym.sym24 F)
  · exact Or.inl (lexAny_of_t234View_sym F hB)
  exact Or.inr ⟨h, hA, hB⟩

/-- `Q45ResWH ⊆ Q45ResWG`. -/
theorem q45ResWG_of_H {F : S0xFac 9 s0x_S24 x} (h : Q45ResWH F) : Q45ResWG F := by
  obtain ⟨s, t, hs, ht, hst, hd, h⟩ := h
  exact ⟨s, t, hs, ht, hst, hd, h.1⟩

/-- **Global form**: on the corner every point has `LexAny`, `AnyFaceChord`, is Rupert, or lies in `Q45ResWH`. -/
theorem q45_resH (F : S0xFac 9 s0x_S24 x) (h4 : 1 ≤ oblX0 x 4) (h5 : 1 ≤ oblX0 x 5) :
    Gen.LexAny F ∨ Gen.AnyFaceChord F ∨ IsRupert (univ.image x) ∨ Q45ResWH F := by
  rcases q45_resG F h4 h5 with h | h | h | ⟨s, t, hs0, ht, hst, hd, h⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · rcases q45_resH_local F h with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inr ⟨s, t, hs0, ht, hst, hd, h⟩))

/-- [OPEN] **The special piece after the T234 views, Rupert form**: `OpenSpecialG` with `Q45ResWH` in place of
`Q45ResWG`. -/
def OpenSpecialH : Prop := ∀ (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x), ¬ H24K.SAT.OB1 x →
  1 ≤ oblX0 x 4 → 1 ≤ oblX0 x 5 →
  oblX0 x 4 * oblX6 x 3 - oblX0 x 3 * oblX6 x 4 < 0 →
  0 < oblX0 x 3 * oblX2 x 5 - oblX0 x 5 * oblX2 x 3 →
  0 < oblX0 x 4 * oblX2 x 5 - oblX0 x 5 * oblX2 x 4 →
  0 < oblX0 x 5 * oblX6 x 4 - oblX0 x 4 * oblX6 x 5 →
  Q45ResWH F → HoleFull x F → IsRupert (univ.image x)

/-- [PROVED] `OpenSpecialG → OpenSpecialH` (`q45ResWG_of_H`). -/
theorem openSpecialH_of_openSpecialG (h : OpenSpecialG) : OpenSpecialH :=
  fun x F hO h4 h5 b1 b2 b3 b4 hr hF => h x F hO h4 h5 b1 b2 b3 b4 (q45ResWG_of_H hr) hF

/-- Every `Hole24` point off `OB1` is Rupert, given `OpenSpecialH`. -/
theorem hole24_offOB1_H {F : S0xFac 9 s0x_S24 x} (h : Hole24 x F) (hO : ¬ H24K.SAT.OB1 x)
    (hS : OpenSpecialH) : IsRupert (univ.image x) := by
  obtain ⟨b1, b2, b3⟩ := resid24_frame_signs h.2.2.1 hO
  have b4 := resid24_b1245 h.2.2.1 hO
  obtain ⟨-, h4, h5⟩ := offWall_of_hole24 h hO
  have hF := holeFull_of_hole24 h
  rcases q45_resH F h4 h5 with hL | hA | hR | hr
  · exact (hF.1.2.2.2.1 hL).elim
  · exact (hF.1.2.2.1 hA).elim
  · exact hR
  · exact hS x F hO h4 h5 b1 b2 b3 b4 hr hF

/-- [PROVED] Generic + special (after the T234 views) assemble to `Open24Rupert`. -/
theorem open24Rupert_of_split_H (h1 : OpenOB1) (h2 : OpenSpecialH) : Open24Rupert := by
  intro x fs hh hH
  by_cases hO : H24K.SAT.OB1 x
  · exact (h1 x _ hO (holeFull_of_hole24 hH)).elim
  · exact hole24_offOB1_H hH hO h2

end T234

section T234D
open Minimality.LexCell

variable {x : Fin 7 → ℝ³}

theorem t234_inner3 (a b : ℝ³) : ⟪a, b⟫ = a 0 * b 0 + a 1 * b 1 + a 2 * b 2 := by
  simp only [PiLp.inner_apply, Fin.sum_univ_three, RCLike.inner_apply, conj_trivial]; ring

/-- `b ⊥` the plane `2 3 4`. -/
theorem t234_perp {b : ℝ³} (hb : b = n234 x ∨ b = -n234 x) :
    ⟪x 3 - x 2, b⟫ = 0 ∧ ⟪x 4 - x 2, b⟫ = 0 := by
  have h3 := t234_tie3 (x := x) hb
  have h4 := t234_tie4 (x := x) hb
  rw [inner_sub_left, inner_sub_left]; exact ⟨by linarith, by linarith⟩

/-- **The z0 letter is affine**: across the plane `2 3 4`, `x 0` and `x 5` lie on one side, `(s + t - 1) ⟪x0 - x2, b⟫ =
t ⟪x5 - x2, b⟫` (`x 0`, `x 5` in the face `0345`, on one side of its edge line `3 4`). -/
theorem t234_z0 {b : ℝ³} (hb : b = n234 x ∨ b = -n234 x) {s t : ℝ}
    (hd : x 3 - x 0 = s • (x 4 - x 0) + t • (x 5 - x 0)) :
    (s + t - 1) * ⟪x 0 - x 2, b⟫ = t * ⟪x 5 - x 2, b⟫ := by
  obtain ⟨h3, h4⟩ := t234_perp hb
  have h := congrArg (fun w => ⟪w, b⟫) hd
  simp only [inner_sub_left, inner_add_left, real_inner_smul_left] at h h3 h4 ⊢
  linear_combination h - h3 + s * h4

/-- The oblique coordinates `b`, `c` of `x 3` from the face decomposition (as `oblX_of_affine` of Type24E23). -/
theorem t234_obl3_bc (F : S0xFac 9 s0x_S24 x) {s t : ℝ} (hd : x 3 - x 0 = s • (x 4 - x 0) + t • (x 5 - x 0)) :
    oblX2 x 3 = s * oblX2 x 4 + t * oblX2 x 5 ∧ oblX6 x 3 = s * oblX6 x 4 + t * oblX6 x 5 := by
  have hrep3 : x 3 - x 1 = (1 - s - t) • (x 0 - x 1) + s • (x 4 - x 1) + t • (x 5 - x 1) := by
    have e3 : x 3 - x 1 = (x 3 - x 0) + (x 0 - x 1) := by abel
    have e5 : x 5 - x 0 = (x 5 - x 1) - (x 0 - x 1) := by abel
    have e4 : x 4 - x 0 = (x 4 - x 1) - (x 0 - x 1) := by abel
    rw [e3, hd, e5, e4]; module
  have eval_fac : ∀ u : Fin 9, F.f u (x 3) = (1 - s - t) * F.f u (x 0) + s * F.f u (x 4) + t * F.f u (x 5) := by
    intro u
    have h1 := congrArg (fun w => ⟪F.N u, w⟫) hrep3
    simp only [inner_add_right, real_inner_smul_right, ← F.hN] at h1
    linarith
  constructor
  · have e1_3 := M4.fac_eval F 1 3
    have e1_4 := M4.fac_eval F 1 4
    have e1_5 := M4.fac_eval F 1 5
    rw [F.zero 1 0 (by decide), F.zero 1 1 (by decide), F.zero 1 6 (by decide)] at e1_3 e1_4 e1_5
    have h1 := eval_fac 1
    rw [F.zero 1 0 (by decide), mul_zero, zero_add] at h1
    have h12 : F.f 1 (x 2) < 0 := F.neg 1 2 (by decide)
    have hid : F.f 1 (x 2) * (oblX2 x 3 - (s * oblX2 x 4 + t * oblX2 x 5)) = 0 := by
      linear_combination -e1_3 + s * e1_4 + t * e1_5 + h1
    exact sub_eq_zero.mp ((mul_eq_zero.mp hid).resolve_left h12.ne)
  · have e0_3 := M4.fac_eval F 0 3
    have e0_4 := M4.fac_eval F 0 4
    have e0_5 := M4.fac_eval F 0 5
    rw [F.zero 0 0 (by decide), F.zero 0 1 (by decide), F.zero 0 2 (by decide)] at e0_3 e0_4 e0_5
    have h0' := eval_fac 0
    rw [F.zero 0 0 (by decide), mul_zero, zero_add] at h0'
    have h06 : F.f 0 (x 6) < 0 := F.neg 0 6 (by decide)
    have hid : F.f 0 (x 6) * (oblX6 x 3 - (s * oblX6 x 4 + t * oblX6 x 5)) = 0 := by
      linear_combination -e0_3 + s * e0_4 + t * e0_5 + h0'
    exact sub_eq_zero.mp ((mul_eq_zero.mp hid).resolve_left h06.ne)

/-- **The z1 letter from the frame sign `b1`** (`a4 c3 - a3 c4 < 0`, a hypothesis of `OpenSpecialH`): on the side of
the plane `2 3 4` where `x 0` lies, `x 1` lies too.  With `G_i = ⟪x i - x 1, b⟫`: `G0 P = G2 R` (`P = a3 c4 - a4 c3 >
0`) and `P - R = c4 A3 - c3 A4 > 0` (`A = a + b - 1`; `α (c4 A3 - c3 A4) = f3(x 2) (c3 b4 - c4 b3)` from the face
`0345`, and `c4 b3 - c3 b4 = (t / s) (c3 b5 - c5 b3) > 0` by `cross35_pos`). -/
theorem t234_z1 (F : S0xFac 9 s0x_S24 x) {b : ℝ³} (hb : b = n234 x ∨ b = -n234 x) {s t : ℝ} (hs : 0 < s)
    (ht : 0 < t) (hd : x 3 - x 0 = s • (x 4 - x 0) + t • (x 5 - x 0))
    (hb1 : oblX0 x 4 * oblX6 x 3 - oblX0 x 3 * oblX6 x 4 < 0) (h0 : 0 < ⟪x 0 - x 2, b⟫) :
    0 < ⟪x 1 - x 2, b⟫ := by
  obtain ⟨h3, h4⟩ := t234_perp hb
  obtain ⟨hb3, hc3⟩ := t234_obl3_bc F hd
  have r3 := M4.inner_rep F 3 b
  have r4 := M4.inner_rep F 4 b
  have c35 := M4.cross35_pos F
  -- the face `0345` at `x 3`, `x 4`
  have ev3 := M4.fac_eval F 3 3
  have ev4 := M4.fac_eval F 3 4
  rw [F.zero 3 3 (by decide), F.zero 3 0 (by decide)] at ev3
  rw [F.zero 3 4 (by decide), F.zero 3 0 (by decide)] at ev4
  have f31 : F.f 3 (x 1) < 0 := F.neg 3 1 (by decide)
  have f32 : F.f 3 (x 2) < 0 := F.neg 3 2 (by decide)
  set a3 := oblX0 x 3; set b3 := oblX2 x 3; set c3 := oblX6 x 3
  set a4 := oblX0 x 4; set b4 := oblX2 x 4; set c4 := oblX6 x 4
  set b5 := oblX2 x 5; set c5 := oblX6 x 5
  -- `c4 b5 - c5 b4 > 0`
  have hk : 0 < c4 * b5 - c5 * b4 := by
    have : c3 * b5 - c5 * b3 = s * (c4 * b5 - c5 * b4) := by rw [hb3, hc3]; ring
    have := M4.cross35_pos F
    nlinarith
  have hcb : 0 < c4 * b3 - c3 * b4 := by
    have : c4 * b3 - c3 * b4 = t * (c4 * b5 - c5 * b4) := by rw [hb3, hc3]; ring
    rw [this]; exact mul_pos ht hk
  -- `α (c4 A3 - c3 A4) = f3(x 2) (c3 b4 - c4 b3)`, `α = -f3(x 1)`
  have hPR : 0 < c4 * (a3 + b3 - 1) - c3 * (a4 + b4 - 1) := by
    have hid : (-F.f 3 (x 1)) * (c4 * (a3 + b3 - 1) - c3 * (a4 + b4 - 1)) =
        F.f 3 (x 2) * (c3 * b4 - c4 * b3) := by
      linear_combination -(c4 * ev3) + c3 * ev4
    have hr : 0 < F.f 3 (x 2) * (c3 * b4 - c4 * b3) := mul_pos_of_neg_of_neg f32 (by linarith)
    rw [← hid] at hr
    exact pos_of_mul_pos_right hr (by linarith)
  -- depths relative to `x 1`
  set G0 := ⟪x 0 - x 1, b⟫; set G2 := ⟪x 2 - x 1, b⟫; set G6 := ⟪x 6 - x 1, b⟫
  have e3 : ⟪x 3 - x 1, b⟫ = G2 := by
    have : x 3 - x 1 = (x 3 - x 2) + (x 2 - x 1) := by abel
    rw [this, inner_add_left, h3, zero_add]
  have e4 : ⟪x 4 - x 1, b⟫ = G2 := by
    have : x 4 - x 1 = (x 4 - x 2) + (x 2 - x 1) := by abel
    rw [this, inner_add_left, h4, zero_add]
  have e0 : ⟪x 0 - x 2, b⟫ = G0 - G2 := by
    have : x 0 - x 2 = (x 0 - x 1) - (x 2 - x 1) := by abel
    rw [this, inner_sub_left]
  have e1 : ⟪x 1 - x 2, b⟫ = -G2 := by
    have : x 1 - x 2 = -(x 2 - x 1) := by abel
    rw [this, inner_neg_left]
  rw [e3] at r3; rw [e4] at r4
  rw [e0] at h0; rw [e1]
  have hP : 0 < a3 * c4 - a4 * c3 := by linarith
  -- `G0 P = G2 R`, so `(G0 - G2) P = G2 (R - P)`
  have key : (G0 - G2) * (a3 * c4 - a4 * c3) =
      -G2 * (c4 * (a3 + b3 - 1) - c3 * (a4 + b4 - 1)) := by
    linear_combination -(c4 * r3) + c3 * r4
  by_contra hneg
  replace hneg := not_lt.mp hneg
  have : (G0 - G2) * (a3 * c4 - a4 * c3) ≤ 0 := by rw [key]; exact mul_nonpos_of_nonpos_of_nonneg hneg hPR.le
  nlinarith [mul_pos h0 hP]

/-- Scalar-triple expansion with `N ⊥ e, a`: `⟪N, e × c⟫ ⟪a - c, e × c⟫ = -⟪N, c⟫ (|e|² ⟪a, c⟫ - ⟪e, a⟫ ⟪e, c⟫)`. -/
theorem t234_triple_perp (N e a c : ℝ³) (hNe : ⟪N, e⟫ = 0) (hNa : ⟪N, a⟫ = 0) :
    ⟪N, cross e c⟫ * ⟪a - c, cross e c⟫ = -(⟪N, c⟫ * (⟪e, e⟫ * ⟪a, c⟫ - ⟪e, a⟫ * ⟪e, c⟫)) := by
  rw [t234_inner3] at hNe hNa
  simp only [t234_inner3, cross_apply_zero, cross_apply_one, cross_apply_two, PiLp.sub_apply]
  linear_combination
    (-(((a 1 * c 2 - a 2 * c 1) * (e 1 * c 2 - e 2 * c 1) + (a 2 * c 0 - a 0 * c 2) * (e 2 * c 0 - e 0 * c 2) +
      (a 0 * c 1 - a 1 * c 0) * (e 0 * c 1 - e 1 * c 0)))) * hNe +
    (-(((c 1 * e 2 - c 2 * e 1) * (e 1 * c 2 - e 2 * c 1) + (c 2 * e 0 - c 0 * e 2) * (e 2 * c 0 - e 0 * c 2) +
      (c 0 * e 1 - c 1 * e 0) * (e 0 * c 1 - e 1 * c 0)))) * hNa

/-- `n234 = (x 4 - x 3) × (x 2 - x 3)`. -/
theorem n234_eq (x : Fin 7 → ℝ³) : n234 x = cross (x 4 - x 3) (x 2 - x 3) := by
  ext i; fin_cases i <;>
    simp [n234] <;> ring

/-- **0345 up at the side of `x 5`** (B2 branch): on the tie `⟪x 2, e34⟫ = ⟪x 5, e34⟫`, with `s > 1` and `⟪x 2 - x 5, x 5
- x 0⟫ ≥ 0` (not `HlexB2` on the tie), `⟪N3, n234⟫ ⟪x 5 - x 2, n234⟫ > 0`.  Mechanism: `= -f3(x 2) q1`, `q1 = |e|² ⟪a,
c⟫ - ⟪e, a⟫ ⟪e, c⟫` (`e = x4 - x3`, `a = x5 - x3`, `c = x2 - x3`) is `|e|² ⟪x5 - Q, x2 - Q⟫` (`Q` on the line `3 4` at
the tie height) and `(s + t - 1) ⟪x2 - x5, e5⟫ = (s - 1) ⟪x2 - x5, a⟫` (`x 5` is farther than `x 0` from the edge line
`3 4` iff `s > 1`). -/
theorem t234_up3_prod (F : S0xFac 9 s0x_S24 x) {s t : ℝ} (hs : 1 < s) (ht : 0 < t)
    (hd : x 3 - x 0 = s • (x 4 - x 0) + t • (x 5 - x 0)) (htie : ⟪x 2, x 3 - x 4⟫ = ⟪x 5, x 3 - x 4⟫)
    (h25 : 0 ≤ ⟪x 2 - x 5, x 5 - x 0⟫) : 0 < ⟪F.N 3, n234 x⟫ * ⟪x 5 - x 2, n234 x⟫ := by
  set e := x 4 - x 3 with he
  set a := x 5 - x 3 with ha
  set c := x 2 - x 3 with hc
  have hNe : ⟪F.N 3, e⟫ = 0 := by rw [he, F.inner_sub 3 4 3, F.zero 3 4 (by decide), F.zero 3 3 (by decide)]; ring
  have hNa : ⟪F.N 3, a⟫ = 0 := by rw [ha, F.inner_sub 3 5 3, F.zero 3 5 (by decide), F.zero 3 3 (by decide)]; ring
  have hNc : ⟪F.N 3, c⟫ = F.f 3 (x 2) := by rw [hc, F.inner_sub 3 2 3, F.zero 3 3 (by decide)]; ring
  have hac : x 5 - x 2 = a - c := by rw [ha, hc]; abel
  have hT := t234_triple_perp (F.N 3) e a c hNe hNa
  rw [n234_eq, hac, hT, hNc]
  have f32 : F.f 3 (x 2) < 0 := F.neg 3 2 (by decide)
  -- `d = x2 - x5 ⊥ e` (tie), `⟪d, a⟫ ≥ 0`
  set d := x 2 - x 5 with hdd
  have hcd : c = a + d := by rw [hc, ha, hdd]; abel
  have hde : ⟪d, e⟫ = 0 := by
    have : ⟪x 2 - x 5, x 3 - x 4⟫ = 0 := by rw [inner_sub_left]; linarith
    have h' : e = -(x 3 - x 4) := by rw [he]; abel
    rw [h', inner_neg_right, this, neg_zero]
  have hda : 0 ≤ ⟪d, a⟫ := by
    have hv : (s + t - 1) • (x 5 - x 0) = (s - 1) • a - s • e := by
      have h3 : x 3 = x 0 + (s • (x 4 - x 0) + t • (x 5 - x 0)) := by rw [← hd]; abel
      rw [ha, he, h3]; module
    have h := congrArg (fun w => ⟪d, w⟫) hv
    simp only [inner_sub_right, real_inner_smul_right, hde] at h
    have h25' : 0 ≤ ⟪d, x 5⟫ - ⟪d, x 0⟫ := by rw [← inner_sub_right]; exact h25
    have : 0 ≤ (s + t - 1) * (⟪d, x 5⟫ - ⟪d, x 0⟫) := mul_nonneg (by linarith) h25'
    by_contra hn
    have := mul_neg_of_pos_of_neg (sub_pos.mpr hs) (not_le.mp hn)
    linarith
  -- strict Gram of `e`, `a` (via `N8 ⊥ e`, `f8(x 5) < 0`)
  have hee : 0 < ⟪e, e⟫ := by
    have := t234_lt34 F
    rw [he, inner_sub_left, inner_sub_right, inner_sub_right]
    rw [inner_sub_right, inner_sub_right] at this
    nlinarith [real_inner_comm (x 3) (x 4)]
  have hgram : 0 < ⟪e, e⟫ * ⟪a, a⟫ - ⟪e, a⟫ ^ 2 := by
    set w := ⟪e, e⟫ • a - ⟪e, a⟫ • e
    have h8e : ⟪F.N 8, e⟫ = 0 := by rw [he, F.inner_sub 8 4 3, F.zero 8 4 (by decide), F.zero 8 3 (by decide)]; ring
    have h8a : ⟪F.N 8, a⟫ = F.f 8 (x 5) := by rw [ha, F.inner_sub 8 5 3, F.zero 8 3 (by decide)]; ring
    have f85 : F.f 8 (x 5) < 0 := F.neg 8 5 (by decide)
    have hw8 : ⟪F.N 8, w⟫ = ⟪e, e⟫ * F.f 8 (x 5) := by
      simp only [w, inner_sub_right, real_inner_smul_right, h8e, h8a]; ring
    have hw0 : w ≠ 0 := by
      intro h0; rw [h0, inner_zero_right] at hw8; nlinarith [mul_neg_of_pos_of_neg hee f85]
    have hww : 0 < ⟪w, w⟫ := real_inner_self_pos.mpr hw0
    have hww' : ⟪w, w⟫ = ⟪e, e⟫ * (⟪e, e⟫ * ⟪a, a⟫ - ⟪e, a⟫ ^ 2) := by
      simp only [w, inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right]
      rw [real_inner_comm a e]; ring
    rw [hww'] at hww
    exact pos_of_mul_pos_right hww hee.le
  have hq : 0 < ⟪e, e⟫ * ⟪a, c⟫ - ⟪e, a⟫ * ⟪e, c⟫ := by
    rw [hcd, inner_add_right, inner_add_right, real_inner_comm d e, hde]
    rw [real_inner_comm a d] at hda
    nlinarith [mul_nonneg hee.le hda]
  nlinarith [mul_pos (neg_pos.mpr f32) hq]


/-! ### The T234 view on the B2 branch: three letters derived (OSPEC15) -/

/-- The orientation of `n234` with `x 5` above the plane `2 3 4`. -/
noncomputable def t234b (x : Fin 7 → ℝ³) : ℝ³ := if 0 < ⟪x 5 - x 2, n234 x⟫ then n234 x else -n234 x

theorem t234b_cases (x : Fin 7 → ℝ³) : t234b x = n234 x ∨ t234b x = -n234 x := by
  unfold t234b; split_ifs; exacts [Or.inl rfl, Or.inr rfl]

/-- The B2-branch hypotheses used by the derivation: `x 3 - x 0 = s e4 + t e5` with `s > 1`, `t > 0`, the frame sign `b1`
(`a4 c3 - a3 c4 < 0`, a hypothesis of `OpenSpecialH`), the tie `⟪x 2, e34⟫ = ⟪x 5, e34⟫` and `⟪x 2 - x 5, e5⟫ ≥ 0`
(both from `ResB2T`: `t234Br_of_resB2T`). -/
def T234Br {x : Fin 7 → ℝ³} (_F : S0xFac 9 s0x_S24 x) : Prop :=
  ∃ s t : ℝ, 1 < s ∧ 0 < t ∧ x 3 - x 0 = s • (x 4 - x 0) + t • (x 5 - x 0) ∧
    oblX0 x 4 * oblX6 x 3 - oblX0 x 3 * oblX6 x 4 < 0 ∧ ⟪x 2, x 3 - x 4⟫ = ⟪x 5, x 3 - x 4⟫ ∧
    0 ≤ ⟪x 2 - x 5, x 5 - x 0⟫

/-- **The remaining T234 letters** at the orientation `t234b` (`x 5` above): `235` up, `016 046 126 236 346` down, and
`012` up or (`012` down, `025` up).  On `T234Br` the letters `0345` up, `z2 < z0` and `z2 < z1` are derived. -/
def T234Red {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) : Prop :=
  T234Up F (t234b x) 6 ∧ T234Dn F (t234b x) 1 ∧ T234Dn F (t234b x) 4 ∧ T234Dn F (t234b x) 5 ∧
    T234Dn F (t234b x) 7 ∧ T234Dn F (t234b x) 8 ∧
    (T234Up F (t234b x) 0 ∨ (T234Dn F (t234b x) 0 ∧ T234Up F (t234b x) 2))

/-- The derived letters at `t234b`: `x 5`, `x 0`, `x 1` above the plane `2 3 4` and `0345` up. -/
theorem t234_derived (F : S0xFac 9 s0x_S24 x) (hB : T234Br F) :
    0 < ⟪x 5 - x 2, t234b x⟫ ∧ 0 < ⟪F.N 3, t234b x⟫ ∧ ⟪x 2, t234b x⟫ < ⟪x 0, t234b x⟫ ∧
      ⟪x 2, t234b x⟫ < ⟪x 1, t234b x⟫ := by
  obtain ⟨s, t, hs, ht, hd, hb1, htie, h25⟩ := hB
  have hp := t234_up3_prod F hs ht hd htie h25
  have h53 : 0 < ⟪x 5 - x 2, t234b x⟫ ∧ 0 < ⟪F.N 3, t234b x⟫ := by
    unfold t234b
    split_ifs with h
    · exact ⟨h, pos_of_mul_pos_left hp h.le⟩
    · have h' : ⟪x 5 - x 2, n234 x⟫ < 0 := by
        rcases (not_lt.mp h).lt_or_eq with h' | h'
        · exact h'
        · rw [h', mul_zero] at hp; exact (lt_irrefl _ hp).elim
      have hN : ⟪F.N 3, n234 x⟫ < 0 := by
        by_contra hc; nlinarith [mul_nonpos_of_nonneg_of_nonpos (not_lt.mp hc) h'.le]
      rw [inner_neg_right, inner_neg_right]; exact ⟨by linarith, by linarith⟩
  have hb := t234b_cases x
  have h0 : 0 < ⟪x 0 - x 2, t234b x⟫ := by
    have e := t234_z0 hb hd
    have : 0 < (s + t - 1) * ⟪x 0 - x 2, t234b x⟫ := by rw [e]; exact mul_pos ht h53.1
    exact pos_of_mul_pos_right this (by linarith)
  have h1 := t234_z1 F hb (by linarith) ht hd hb1 h0
  rw [inner_sub_left] at h0 h1
  exact ⟨h53.1, h53.2, by linarith, by linarith⟩

/-- **On the B2 branch the T234 view needs only the remaining letters.** -/
theorem t234At_of_red (F : S0xFac 9 s0x_S24 x) (hB : T234Br F) (hR : T234Red F) : T234At F (t234b x) := by
  obtain ⟨-, h3, h20, h21⟩ := t234_derived F hB
  obtain ⟨u6, n1, n4, n5, n7, n8, h0⟩ := hR
  refine ⟨Or.inl h3, u6, n1, n4, n5, n7, n8, h20, ?_⟩
  rcases h0 with u0 | h0
  · exact Or.inl ⟨u0, h21⟩
  · exact Or.inr h0

/-- **Exactness**: on the B2 branch `T234ViewOK` is equivalent to the remaining letters (an orientation with `z2 < z0`
puts `x 5` above, so it is `t234b`). -/
theorem t234ViewOK_iff_red (F : S0xFac 9 s0x_S24 x) (hB : T234Br F) : T234ViewOK F ↔ T234Red F := by
  constructor
  · obtain ⟨s, t, hs, ht, hd, -⟩ := hB
    have key : ∀ b : ℝ³, (b = n234 x ∨ b = -n234 x) → T234At F b → T234Red F := by
      intro b hb hA
      obtain ⟨-, u6, n1, n4, n5, n7, n8, h20, h0⟩ := hA
      have h5 : 0 < ⟪x 5 - x 2, b⟫ := by
        have e := t234_z0 hb hd
        rw [inner_sub_left] at e
        have : 0 < t * ⟪x 5 - x 2, b⟫ := by rw [← e]; exact mul_pos (by linarith) (by linarith)
        exact pos_of_mul_pos_right this ht.le
      have hbb : t234b x = b := by
        unfold t234b
        rcases hb with rfl | rfl
        · simp [h5]
        · rw [inner_neg_right] at h5
          have hn : ¬ 0 < ⟪x 5 - x 2, n234 x⟫ := by linarith
          simp [hn]
      unfold T234Red; rw [hbb]
      refine ⟨u6, n1, n4, n5, n7, n8, ?_⟩
      rcases h0 with ⟨u0, -⟩ | h0
      · exact Or.inl u0
      · exact Or.inr h0
    rintro (h | h)
    · exact key _ (Or.inl rfl) h
    · exact key _ (Or.inr rfl) h
  · intro hR
    rcases t234b_cases x with e | e
    · exact Or.inl (e ▸ t234At_of_red F hB hR)
    · exact Or.inr (e ▸ t234At_of_red F hB hR)

/-- The B2 corner tie supplies `T234Br` (`⟪x 2 - x 5, e5⟫ ≥ 0` is `¬ HlexB2` at the pair `2, 5` on the tie). -/
theorem t234Br_of_resB2T (F : S0xFac 9 s0x_S24 x) {s t : ℝ} (h : ResB2T x s) (ht : 0 < t)
    (hd : x 3 - x 0 = s • (x 4 - x 0) + t • (x 5 - x 0))
    (hb1 : oblX0 x 4 * oblX6 x 3 - oblX0 x 3 * oblX6 x 4 < 0) : T234Br F := by
  obtain ⟨-, hs, -, hl, htie, -⟩ := h
  refine ⟨s, t, hs, ht, hd, hb1, htie, ?_⟩
  by_contra hn
  apply hl
  refine ⟨2, by decide, 5, by decide, Or.inr ⟨?_, not_le.mp hn⟩⟩
  rw [inner_sub_left]; linarith

/-! ### The residue with the derived letters removed (OSPEC15) -/

/-- The T234 view condition in reduced form: on `T234Br` only the remaining letters `T234Red`, elsewhere `T234ViewOK`. -/
def T234ViewI {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) : Prop :=
  (T234Br F ∧ T234Red F) ∨ (¬ T234Br F ∧ T234ViewOK F)

/-- `T234ViewI` is `T234ViewOK` (the reduced form loses nothing). -/
theorem t234ViewI_iff (F : S0xFac 9 s0x_S24 x) : T234ViewI F ↔ T234ViewOK F := by
  by_cases hB : T234Br F
  · unfold T234ViewI; rw [t234ViewOK_iff_red F hB]; tauto
  · unfold T234ViewI
    constructor
    · rintro (⟨h, -⟩ | ⟨-, h⟩)
      · exact (hB h).elim
      · exact h
    · intro h; exact Or.inr ⟨hB, h⟩

theorem lexAny_of_t234ViewI (F : S0xFac 9 s0x_S24 x) (h : T234ViewI F) : Gen.LexAny F :=
  lexAny_of_t234View F ((t234ViewI_iff F).mp h)

/-- `Q45ResSTG` where neither reduced T234 view (nor its mirror) applies: on the B2 branch the piece is the failure of
`T234Red` (seven facet letters; sampled failures only `126` with `236`, `346`, and `012` with `025`). -/
def Q45ResSTI {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (s t : ℝ) : Prop :=
  Q45ResSTG F s t ∧ ¬ T234ViewI F ∧ ¬ T234ViewI (Sym.sym24 F)

/-- The branch-tagged residue in the reduced form. -/
def Q45ResWI {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) : Prop :=
  ∃ s t : ℝ, 0 < s ∧ 0 < t ∧ 1 < s + t ∧ x 3 - x 0 = s • (x 4 - x 0) + t • (x 5 - x 0) ∧ Q45ResSTI F s t

/-- `Q45ResWI = Q45ResWH`. -/
theorem q45ResWI_iff_H (F : S0xFac 9 s0x_S24 x) : Q45ResWI F ↔ Q45ResWH F := by
  unfold Q45ResWI Q45ResWH Q45ResSTI Q45ResSTH
  simp only [t234ViewI_iff]

/-- [OPEN] **The special piece in the reduced T234 form, Rupert form**: `OpenSpecialH` with `Q45ResWI` in place of
`Q45ResWH` (equivalent: `openSpecialI_iff_H`). -/
def OpenSpecialI : Prop := ∀ (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x), ¬ H24K.SAT.OB1 x →
  1 ≤ oblX0 x 4 → 1 ≤ oblX0 x 5 →
  oblX0 x 4 * oblX6 x 3 - oblX0 x 3 * oblX6 x 4 < 0 →
  0 < oblX0 x 3 * oblX2 x 5 - oblX0 x 5 * oblX2 x 3 →
  0 < oblX0 x 4 * oblX2 x 5 - oblX0 x 5 * oblX2 x 4 →
  0 < oblX0 x 5 * oblX6 x 4 - oblX0 x 4 * oblX6 x 5 →
  Q45ResWI F → HoleFull x F → IsRupert (univ.image x)

/-- [PROVED] `OpenSpecialI ↔ OpenSpecialH`. -/
theorem openSpecialI_iff_H : OpenSpecialI ↔ OpenSpecialH := by
  unfold OpenSpecialI OpenSpecialH
  simp only [q45ResWI_iff_H]

/-- Every `Hole24` point off `OB1` is Rupert, given `OpenSpecialI`. -/
theorem hole24_offOB1_I {F : S0xFac 9 s0x_S24 x} (h : Hole24 x F) (hO : ¬ H24K.SAT.OB1 x)
    (hS : OpenSpecialI) : IsRupert (univ.image x) :=
  hole24_offOB1_H h hO (openSpecialI_iff_H.mp hS)

/-- [PROVED] Generic + special (reduced T234 form) assemble to `Open24Rupert`. -/
theorem open24Rupert_of_split_I (h1 : OpenOB1) (h2 : OpenSpecialI) : Open24Rupert :=
  open24Rupert_of_split_H h1 (openSpecialI_iff_H.mp h2)

end T234D

end Minimality.T24.OSpec
