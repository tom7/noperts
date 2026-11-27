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

**OSPEC16** (section `T234E`): `235` up (`t234_up6`, on `T234BrJ` = full tie and `h5 ≤ h3`); `OpenSpecialJ`.

**OSPEC17** (section `T234F`): the tie-section picture.  `t234_z6_of` (no branch hypothesis): `x 5` and `x 6` lie on
opposite sides of the plane `2 3 4` (`x 2` lies in the dihedral wedge of the edge `3 4` between `0345` and `346`;
`t234_cramer`).  On the branch `236` down iff `t234C = ⟪x2 - x3, x2 - x6⟫ ≥ 0` (`t234_dn7_iff`), `346` down iff `X6 ≥ 0`
(`t234_dn8_iff`), and with `h4 ≤ h5` (`T234BrL`) `126` flips with `236` off `t234C = 0` (`t234_prod5` via the
Binet-Cauchy `t234_gram`; `t234_dn5_of`, `t234_up5_of`).  So the residue letters are `016 046` down, the cone condition
`T234Cone` (`0 ≤ X6`, `X6 ≤ X2`) and the rim choice (`T234RedL`, `t234ViewOK_iff_redL`); `OpenSpecialL`
(equivalent to `OpenSpecialJ`).  Section `T234G`: off the cone the same view is still a lex cell, with the rim `0 1 6 3 4`
(`t234C < 0`: `126 236` up), `0 1 2 3 6 4` or `0 2 3 6 4` (`X6 < 0`: `346` up), all depth letters derived
(`t234_depths`); so on `T234BrL` the view needs only `T234RedM` (`016 046` down, `012` up or (`012` down, `025` up,
`t234C ≥ 0`), `126` down at `t234C = 0`; `lexAny_of_t234RedM`).  Residue `Q45ResWM`, `OpenSpecialM` (implied by
`OpenSpecialL`, a strictly smaller piece).
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

/-- `⟪x 2 - x 5, x 5 - x 3⟫ ≥ 0` on the B2 branch (`x 5` is farther than `x 0` from the edge line `3 4`, `s > 1`). -/
theorem t234_da {s t : ℝ} (hs : 1 < s) (ht : 0 < t) (hd : x 3 - x 0 = s • (x 4 - x 0) + t • (x 5 - x 0))
    (htie : ⟪x 2, x 3 - x 4⟫ = ⟪x 5, x 3 - x 4⟫) (h25 : 0 ≤ ⟪x 2 - x 5, x 5 - x 0⟫) :
    0 ≤ ⟪x 2 - x 5, x 5 - x 3⟫ := by
  have hde : ⟪x 2 - x 5, x 4 - x 3⟫ = 0 := by
    have : ⟪x 2 - x 5, x 3 - x 4⟫ = 0 := by rw [inner_sub_left]; linarith
    have h' : x 4 - x 3 = -(x 3 - x 4) := by abel
    rw [h', inner_neg_right, this, neg_zero]
  have hv : (s + t - 1) • (x 5 - x 0) = (s - 1) • (x 5 - x 3) - s • (x 4 - x 3) := by
    have h3 : x 3 = x 0 + (s • (x 4 - x 0) + t • (x 5 - x 0)) := by rw [← hd]; abel
    rw [h3]; module
  have h := congrArg (fun w => ⟪x 2 - x 5, w⟫) hv
  simp only [inner_sub_right, real_inner_smul_right] at h hde h25 ⊢
  by_contra hn
  have h1 : 0 ≤ (s + t - 1) * (⟪x 2 - x 5, x 5⟫ - ⟪x 2 - x 5, x 0⟫) := mul_nonneg (by linarith) h25
  have h2 := mul_neg_of_pos_of_neg (sub_pos.mpr hs) (not_le.mp hn)
  rw [hde, mul_zero, sub_zero] at h
  linarith

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
  have hda : 0 ≤ ⟪d, a⟫ := t234_da hs ht hd htie h25
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

section T234E
open Minimality.LexCell

variable {x : Fin 7 → ℝ³}

/-! ### OSPEC16: `235` up derived on the B2 branch (full tie, `¬ HlexB2` at `3, 5`) -/

/-- Three vectors `⊥ E ≠ 0` with `N ⊥ g, a`, `⟪N, w⟫ ≠ 0`, `M ⊥ a`, `⟪M, g⟫ ≠ 0`, `a ≠ 0` cannot exist (they would be
coplanar, so `g × a = 0`, so `g ∥ a`). -/
theorem t234_coplanar_false (N M E g a w : ℝ³) (hNg : ⟪N, g⟫ = 0) (hNa : ⟪N, a⟫ = 0) (hNw : ⟪N, w⟫ ≠ 0)
    (hMa : ⟪M, a⟫ = 0) (hMg : ⟪M, g⟫ ≠ 0) (ha : a ≠ 0) (hE : E ≠ 0) (hEg : ⟪E, g⟫ = 0) (hEa : ⟪E, a⟫ = 0)
    (hEw : ⟪E, w⟫ = 0) : False := by
  rw [t234_inner3] at hNg hNa hNw hMa hMg hEg hEa hEw
  set D := g 0 * (a 1 * w 2 - a 2 * w 1) - g 1 * (a 0 * w 2 - a 2 * w 0) + g 2 * (a 0 * w 1 - a 1 * w 0) with hD
  have hEE : 0 < E 0 * E 0 + E 1 * E 1 + E 2 * E 2 := by
    have := real_inner_self_pos.mpr hE; rwa [t234_inner3] at this
  have hD0 : D * (E 0 * E 0 + E 1 * E 1 + E 2 * E 2) = 0 := by
    linear_combination
      (E 0 * (a 1 * w 2 - a 2 * w 1) + E 1 * (a 2 * w 0 - a 0 * w 2) + E 2 * (a 0 * w 1 - a 1 * w 0)) * hEg +
      (E 0 * (w 1 * g 2 - w 2 * g 1) + E 1 * (w 2 * g 0 - w 0 * g 2) + E 2 * (w 0 * g 1 - w 1 * g 0)) * hEa +
      (E 0 * (g 1 * a 2 - g 2 * a 1) + E 1 * (g 2 * a 0 - g 0 * a 2) + E 2 * (g 0 * a 1 - g 1 * a 0)) * hEw
  have hD' : D = 0 := (mul_eq_zero.mp hD0).resolve_right hEE.ne'
  set nw := N 0 * w 0 + N 1 * w 1 + N 2 * w 2
  have c0 : nw * (g 1 * a 2 - g 2 * a 1) = 0 := by
    linear_combination (-(a 1 * w 2 - a 2 * w 1)) * hNg + (-(w 1 * g 2 - w 2 * g 1)) * hNa + N 0 * hD'
  have c1 : nw * (g 2 * a 0 - g 0 * a 2) = 0 := by
    linear_combination (-(a 2 * w 0 - a 0 * w 2)) * hNg + (-(w 2 * g 0 - w 0 * g 2)) * hNa + N 1 * hD'
  have c2 : nw * (g 0 * a 1 - g 1 * a 0) = 0 := by
    linear_combination (-(a 0 * w 1 - a 1 * w 0)) * hNg + (-(w 0 * g 1 - w 1 * g 0)) * hNa + N 2 * hD'
  have k0 := (mul_eq_zero.mp c0).resolve_left hNw
  have k1 := (mul_eq_zero.mp c1).resolve_left hNw
  have k2 := (mul_eq_zero.mp c2).resolve_left hNw
  have haa : 0 < a 0 * a 0 + a 1 * a 1 + a 2 * a 2 := by
    have := real_inner_self_pos.mpr ha; rwa [t234_inner3] at this
  have hk : (a 0 * a 0 + a 1 * a 1 + a 2 * a 2) * (M 0 * g 0 + M 1 * g 1 + M 2 * g 2) = 0 := by
    linear_combination (g 0 * a 0 + g 1 * a 1 + g 2 * a 2) * hMa +
      (M 1 * a 2 - M 2 * a 1) * k0 + (M 2 * a 0 - M 0 * a 2) * k1 + (M 0 * a 1 - M 1 * a 0) * k2
  exact hMg ((mul_eq_zero.mp hk).resolve_left haa.ne')


/-- **`x 3` strictly above the tie plane** (B2 branch): `τ = ⟪x 5 - x 3, x 4 - x 3⟫ > 0`.  `≥` is `¬ HlexB2` at the
pair `3, 5`; equality would put `x 2, x 3, x 5, x 6` in one plane `⊥ e34` (with the tie `h2 = h5 = h6`), impossible
since `x 6` is off the facet `235` (`t234_coplanar_false`). -/
theorem t234_tau_pos (F : S0xFac 9 s0x_S24 x) (htie : ⟪x 2, x 3 - x 4⟫ = ⟪x 5, x 3 - x 4⟫)
    (htie6 : ⟪x 5, x 3 - x 4⟫ = ⟪x 6, x 3 - x 4⟫) (h35 : ⟪x 5, x 3 - x 4⟫ ≤ ⟪x 3, x 3 - x 4⟫) :
    0 < ⟪x 5 - x 3, x 4 - x 3⟫ := by
  have e : ⟪x 5 - x 3, x 4 - x 3⟫ = ⟪x 3, x 3 - x 4⟫ - ⟪x 5, x 3 - x 4⟫ := by
    have h' : x 4 - x 3 = -(x 3 - x 4) := by abel
    rw [h', inner_neg_right, inner_sub_left]; ring
  rw [e]
  rcases h35.lt_or_eq with h | h
  · linarith
  exfalso
  have hperp : ∀ i : Fin 7, ⟪x i, x 3 - x 4⟫ = ⟪x 3, x 3 - x 4⟫ → ⟪x 4 - x 3, x i - x 3⟫ = 0 := by
    intro i hi
    have h' : x 4 - x 3 = -(x 3 - x 4) := by abel
    rw [h', inner_neg_left, real_inner_comm, inner_sub_left, hi, sub_self, neg_zero]
  have hE : x 4 - x 3 ≠ 0 := by
    intro h0
    have := t234_lt34 F
    rw [← sub_pos, ← inner_sub_left, h0, inner_zero_left] at this
    exact lt_irrefl _ this
  have ha : x 5 - x 3 ≠ 0 := by
    intro h0
    have h8 := F.inner_sub 8 5 3
    rw [h0, inner_zero_right, F.zero 8 3 (by decide)] at h8
    have := F.neg 8 5 (by decide); linarith
  refine t234_coplanar_false (F.N 6) (F.N 3) (x 4 - x 3) (x 2 - x 3) (x 5 - x 3) (x 6 - x 3) ?_ ?_ ?_ ?_ ?_ ha hE
    (hperp 2 (by linarith)) (hperp 5 h) (hperp 6 (by linarith))
  · rw [F.inner_sub 6 2 3, F.zero 6 2 (by decide), F.zero 6 3 (by decide)]; ring
  · rw [F.inner_sub 6 5 3, F.zero 6 5 (by decide), F.zero 6 3 (by decide)]; ring
  · rw [F.inner_sub 6 6 3, F.zero 6 3 (by decide), sub_zero]; exact (F.neg 6 6 (by decide)).ne
  · rw [F.inner_sub 3 5 3, F.zero 3 5 (by decide), F.zero 3 3 (by decide)]; ring
  · rw [F.inner_sub 3 2 3, F.zero 3 3 (by decide), sub_zero]; exact (F.neg 3 2 (by decide)).ne

/-- `n234 = (x 2 - x 3) × (x 4 - x 3)` up to sign. -/
theorem n234_eq_neg (x : Fin 7 → ℝ³) : cross (x 2 - x 3) (x 4 - x 3) = -n234 x := by
  ext i; fin_cases i <;>
    simp [n234] <;> ring

/-- **235 up at the side of `x 5`** (B2 branch with the full tie and `¬ HlexB2`): `⟪N6, n234⟫ ⟪x 5 - x 2, n234⟫ > 0`.
Mechanism: `= -f6(x 4) q6`, `q6 = |g|² ⟪a, E⟫ - ⟪g, a⟫ ⟪g, E⟫` (`g = x2 - x3`, `a = x5 - x3`, `E = x4 - x3`) `= τ ⟪g,
x2 - x5⟫` on the tie, `τ > 0` (`t234_tau_pos`) and `⟪g, x2 - x5⟫ = ⟪a, d⟫ + |d|² > 0` (`t234_da`, `x 2 ≠ x 5`). -/
theorem t234_up6_prod (F : S0xFac 9 s0x_S24 x) {s t : ℝ} (hs : 1 < s) (ht : 0 < t)
    (hd : x 3 - x 0 = s • (x 4 - x 0) + t • (x 5 - x 0)) (htie : ⟪x 2, x 3 - x 4⟫ = ⟪x 5, x 3 - x 4⟫)
    (htie6 : ⟪x 5, x 3 - x 4⟫ = ⟪x 6, x 3 - x 4⟫) (h35 : ⟪x 5, x 3 - x 4⟫ ≤ ⟪x 3, x 3 - x 4⟫)
    (h25 : 0 ≤ ⟪x 2 - x 5, x 5 - x 0⟫) : 0 < ⟪F.N 6, n234 x⟫ * ⟪x 5 - x 2, n234 x⟫ := by
  set g := x 2 - x 3 with hg
  set a := x 5 - x 3 with ha
  set E := x 4 - x 3 with hE
  have hNg : ⟪F.N 6, g⟫ = 0 := by rw [hg, F.inner_sub 6 2 3, F.zero 6 2 (by decide), F.zero 6 3 (by decide)]; ring
  have hNa : ⟪F.N 6, a⟫ = 0 := by rw [ha, F.inner_sub 6 5 3, F.zero 6 5 (by decide), F.zero 6 3 (by decide)]; ring
  have hNE : ⟪F.N 6, E⟫ = F.f 6 (x 4) := by rw [hE, F.inner_sub 6 4 3, F.zero 6 3 (by decide)]; ring
  have hT := t234_triple_perp (F.N 6) g a E hNg hNa
  have hae : a - E = x 5 - x 4 := by rw [ha, hE]; abel
  have h54 : ⟪x 5 - x 4, n234 x⟫ = ⟪x 5 - x 2, n234 x⟫ := by
    rw [inner_sub_left, inner_sub_left, t234_tie4 (x := x) (Or.inl rfl)]
  rw [hg, hE, n234_eq_neg, ← hg, ← hE, hae, inner_neg_right, inner_neg_right, neg_mul_neg, h54, hNE] at hT
  rw [hT]
  have f64 : F.f 6 (x 4) < 0 := F.neg 6 4 (by decide)
  set d := x 2 - x 5 with hdd
  have hgd : g = a + d := by rw [hg, ha, hdd]; abel
  have hdE : ⟪d, E⟫ = 0 := by
    have : ⟪x 2 - x 5, x 3 - x 4⟫ = 0 := by rw [inner_sub_left]; linarith
    have h' : E = -(x 3 - x 4) := by rw [hE]; abel
    rw [h', inner_neg_right, this, neg_zero]
  have hda : 0 ≤ ⟪d, a⟫ := t234_da hs ht hd htie h25
  have hd0 : d ≠ 0 := by
    intro h0
    have h3 := F.inner_sub 3 2 5
    rw [← hdd, h0, inner_zero_right, F.zero 3 5 (by decide)] at h3
    have := F.neg 3 2 (by decide); linarith
  have hdd' : 0 < ⟪d, d⟫ := real_inner_self_pos.mpr hd0
  have htau : 0 < ⟪a, E⟫ := t234_tau_pos F htie htie6 h35
  have hq : 0 < ⟪g, g⟫ * ⟪a, E⟫ - ⟪g, a⟫ * ⟪g, E⟫ := by
    have e1 : ⟪g, E⟫ = ⟪a, E⟫ := by rw [hgd, inner_add_left, hdE, add_zero]
    have e2 : ⟪g, g⟫ - ⟪g, a⟫ = ⟪a, d⟫ + ⟪d, d⟫ := by
      rw [hgd]; simp only [inner_add_left, inner_add_right]; rw [real_inner_comm d a]; ring
    have : ⟪g, g⟫ * ⟪a, E⟫ - ⟪g, a⟫ * ⟪g, E⟫ = ⟪a, E⟫ * (⟪a, d⟫ + ⟪d, d⟫) := by rw [e1, ← e2]; ring
    rw [this]; exact mul_pos htau (by have := real_inner_comm a d; linarith)
  nlinarith [mul_pos (neg_pos.mpr f64) hq]

/-- **236 at `n234` as a metric sign** (identity; only the tie `h2 = h6`): `⟪N7, n⟫ ⟪x 6 - x 2, n⟫ = -f7(x 4) τ6 ⟪x 2 -
x 3, x 2 - x 6⟫`, `τ6 = ⟪x 6 - x 3, x 4 - x 3⟫`.  So with `z6 < z2` and `τ > 0`, `236` down at `t234b` iff the angle
at `x 2` between `x 3` and `x 6` is acute (OSPEC16 census: `126` and `236` flip together exactly there). -/
theorem t234_prod7 (F : S0xFac 9 s0x_S24 x) (htie : ⟪x 2, x 3 - x 4⟫ = ⟪x 6, x 3 - x 4⟫) :
    ⟪F.N 7, n234 x⟫ * ⟪x 6 - x 2, n234 x⟫ =
      -(F.f 7 (x 4) * (⟪x 6 - x 3, x 4 - x 3⟫ * ⟪x 2 - x 3, x 2 - x 6⟫)) := by
  set g := x 2 - x 3 with hg
  set a := x 6 - x 3 with ha
  set E := x 4 - x 3 with hE
  have hNg : ⟪F.N 7, g⟫ = 0 := by rw [hg, F.inner_sub 7 2 3, F.zero 7 2 (by decide), F.zero 7 3 (by decide)]; ring
  have hNa : ⟪F.N 7, a⟫ = 0 := by rw [ha, F.inner_sub 7 6 3, F.zero 7 6 (by decide), F.zero 7 3 (by decide)]; ring
  have hNE : ⟪F.N 7, E⟫ = F.f 7 (x 4) := by rw [hE, F.inner_sub 7 4 3, F.zero 7 3 (by decide)]; ring
  have hT := t234_triple_perp (F.N 7) g a E hNg hNa
  have hae : a - E = x 6 - x 4 := by rw [ha, hE]; abel
  have h64 : ⟪x 6 - x 4, n234 x⟫ = ⟪x 6 - x 2, n234 x⟫ := by
    rw [inner_sub_left, inner_sub_left, t234_tie4 (x := x) (Or.inl rfl)]
  rw [hg, hE, n234_eq_neg, ← hg, ← hE, hae, inner_neg_right, inner_neg_right, neg_mul_neg, h64, hNE] at hT
  rw [hT]
  have hdE : ⟪g - a, E⟫ = 0 := by
    have e1 : g - a = x 2 - x 6 := by rw [hg, ha]; abel
    have : ⟪x 2 - x 6, x 3 - x 4⟫ = 0 := by rw [inner_sub_left]; linarith
    have h' : E = -(x 3 - x 4) := by rw [hE]; abel
    rw [e1, h', inner_neg_right, this, neg_zero]
  have e2 : x 2 - x 6 = g - a := by rw [hg, ha]; abel
  rw [inner_sub_left] at hdE
  have e3 : ⟪g, g - a⟫ = ⟪g, g⟫ - ⟪g, a⟫ := inner_sub_right g g a
  have : ⟪g, E⟫ = ⟪a, E⟫ := by linarith
  rw [e2, e3, this]; ring

/-- **346 at `n234` as a metric sign** (identity): `⟪N8, n⟫ ⟪x 6 - x 2, n⟫ = -f8(x 2) X6`, `X6 = |E|² ⟪x 6 - x 3, x 2 -
x 3⟫ - ⟪E, x 6 - x 3⟫ ⟪E, x 2 - x 3⟫` (`E = x 4 - x 3`; the coordinate of `x 6` along the foot direction of `x 2` in the
tie plane).  With `z6 < z2`, `346` down at `t234b` iff `X6 > 0` (OSPEC16 census). -/
theorem t234_prod8 (F : S0xFac 9 s0x_S24 x) :
    ⟪F.N 8, n234 x⟫ * ⟪x 6 - x 2, n234 x⟫ =
      -(F.f 8 (x 2) * (⟪x 4 - x 3, x 4 - x 3⟫ * ⟪x 6 - x 3, x 2 - x 3⟫ -
        ⟪x 4 - x 3, x 6 - x 3⟫ * ⟪x 4 - x 3, x 2 - x 3⟫)) := by
  have hNe : ⟪F.N 8, x 4 - x 3⟫ = 0 := by rw [F.inner_sub 8 4 3, F.zero 8 4 (by decide), F.zero 8 3 (by decide)]; ring
  have hNa : ⟪F.N 8, x 6 - x 3⟫ = 0 := by rw [F.inner_sub 8 6 3, F.zero 8 6 (by decide), F.zero 8 3 (by decide)]; ring
  have hNc : ⟪F.N 8, x 2 - x 3⟫ = F.f 8 (x 2) := by rw [F.inner_sub 8 2 3, F.zero 8 3 (by decide)]; ring
  have hT := t234_triple_perp (F.N 8) (x 4 - x 3) (x 6 - x 3) (x 2 - x 3) hNe hNa
  have hac : x 6 - x 3 - (x 2 - x 3) = x 6 - x 2 := by abel
  rw [← n234_eq, hac, hNc] at hT
  exact hT

/-- The B2 branch with the full tie `h2 = h5 = h6` (`Q45TieLocusB2`) and `h5 ≤ h3` (`¬ HlexB2` at the pair `3, 5`),
heights along `e34 = x 3 - x 4`. -/
def T234BrJ {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) : Prop :=
  T234Br F ∧ ⟪x 5, x 3 - x 4⟫ = ⟪x 6, x 3 - x 4⟫ ∧ ⟪x 5, x 3 - x 4⟫ ≤ ⟪x 3, x 3 - x 4⟫

/-- **235 up at `t234b`** on `T234BrJ`. -/
theorem t234_up6 (F : S0xFac 9 s0x_S24 x) (hB : T234BrJ F) : T234Up F (t234b x) 6 := by
  obtain ⟨⟨s, t, hs, ht, hd, -, htie, h25⟩, h56, h35⟩ := hB
  have hp := t234_up6_prod F hs ht hd htie h56 h35 h25
  left
  unfold t234b
  split_ifs with h
  · exact pos_of_mul_pos_left hp h.le
  · have h' : ⟪x 5 - x 2, n234 x⟫ < 0 := by
      rcases (not_lt.mp h).lt_or_eq with h' | h'
      · exact h'
      · rw [h', mul_zero] at hp; exact (lt_irrefl _ hp).elim
    have hN : ⟪F.N 6, n234 x⟫ < 0 := by
      by_contra hc; nlinarith [mul_nonpos_of_nonneg_of_nonpos (not_lt.mp hc) h'.le]
    rw [inner_neg_right]; linarith

/-- **The remaining T234 letters after OSPEC16**: `016 046 126 236 346` down and `012` up or (`012` down, `025` up) at
`t234b`; `0345` up, `235` up, `z2 < z0`, `z2 < z1` are derived on `T234BrJ`. -/
def T234RedJ {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) : Prop :=
  T234Dn F (t234b x) 1 ∧ T234Dn F (t234b x) 4 ∧ T234Dn F (t234b x) 5 ∧ T234Dn F (t234b x) 7 ∧
    T234Dn F (t234b x) 8 ∧ (T234Up F (t234b x) 0 ∨ (T234Dn F (t234b x) 0 ∧ T234Up F (t234b x) 2))

theorem t234Red_iff_J (F : S0xFac 9 s0x_S24 x) (hB : T234BrJ F) : T234Red F ↔ T234RedJ F := by
  have u6 := t234_up6 F hB
  unfold T234Red T234RedJ
  exact ⟨fun h => h.2, fun h => ⟨u6, h⟩⟩

/-- **Exactness**: on `T234BrJ`, `T234ViewOK ↔ T234RedJ`. -/
theorem t234ViewOK_iff_redJ (F : S0xFac 9 s0x_S24 x) (hB : T234BrJ F) : T234ViewOK F ↔ T234RedJ F :=
  (t234ViewOK_iff_red F hB.1).trans (t234Red_iff_J F hB)

/-- The B2 corner tie supplies `T234BrJ`. -/
theorem t234BrJ_of_resB2T (F : S0xFac 9 s0x_S24 x) {s t : ℝ} (h : ResB2T x s) (ht : 0 < t)
    (hd : x 3 - x 0 = s • (x 4 - x 0) + t • (x 5 - x 0))
    (hb1 : oblX0 x 4 * oblX6 x 3 - oblX0 x 3 * oblX6 x 4 < 0) : T234BrJ F := by
  refine ⟨t234Br_of_resB2T F h ht hd hb1, h.2.2.2.2.2, ?_⟩
  obtain ⟨-, -, -, hl, -⟩ := h
  by_contra hn
  apply hl
  refine ⟨3, by decide, 5, by decide, Or.inl ?_⟩
  rw [inner_sub_left]; linarith

/-! ### The residue with `235` removed (OSPEC16) -/

/-- The T234 view condition with the OSPEC16 letters removed: on `T234BrJ` only `T234RedJ`, elsewhere `T234ViewOK`. -/
def T234ViewJ {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) : Prop :=
  (T234BrJ F ∧ T234RedJ F) ∨ (¬ T234BrJ F ∧ T234ViewOK F)

/-- `T234ViewJ` is `T234ViewOK`. -/
theorem t234ViewJ_iff (F : S0xFac 9 s0x_S24 x) : T234ViewJ F ↔ T234ViewOK F := by
  by_cases hB : T234BrJ F
  · unfold T234ViewJ; rw [t234ViewOK_iff_redJ F hB]; tauto
  · unfold T234ViewJ
    constructor
    · rintro (⟨h, -⟩ | ⟨-, h⟩)
      · exact (hB h).elim
      · exact h
    · intro h; exact Or.inr ⟨hB, h⟩

theorem lexAny_of_t234ViewJ (F : S0xFac 9 s0x_S24 x) (h : T234ViewJ F) : Gen.LexAny F :=
  lexAny_of_t234View F ((t234ViewJ_iff F).mp h)

/-- `Q45ResSTG` where neither `T234ViewJ` (nor its mirror) applies: on the B2 branch the failure of `T234RedJ` (six
letters; sampled failures only `126` with `236`, `346`, and `012` with `025`). -/
def Q45ResSTJ {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (s t : ℝ) : Prop :=
  Q45ResSTG F s t ∧ ¬ T234ViewJ F ∧ ¬ T234ViewJ (Sym.sym24 F)

/-- The branch-tagged residue after OSPEC16. -/
def Q45ResWJ {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) : Prop :=
  ∃ s t : ℝ, 0 < s ∧ 0 < t ∧ 1 < s + t ∧ x 3 - x 0 = s • (x 4 - x 0) + t • (x 5 - x 0) ∧ Q45ResSTJ F s t

/-- `Q45ResWJ = Q45ResWI`. -/
theorem q45ResWJ_iff_I (F : S0xFac 9 s0x_S24 x) : Q45ResWJ F ↔ Q45ResWI F := by
  unfold Q45ResWJ Q45ResWI Q45ResSTJ Q45ResSTI
  simp only [t234ViewJ_iff, t234ViewI_iff]

/-- [OPEN] **The special piece after OSPEC16, Rupert form**: `OpenSpecialI` with `Q45ResWJ` in place of `Q45ResWI`
(equivalent: `openSpecialJ_iff_I`). -/
def OpenSpecialJ : Prop := ∀ (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x), ¬ H24K.SAT.OB1 x →
  1 ≤ oblX0 x 4 → 1 ≤ oblX0 x 5 →
  oblX0 x 4 * oblX6 x 3 - oblX0 x 3 * oblX6 x 4 < 0 →
  0 < oblX0 x 3 * oblX2 x 5 - oblX0 x 5 * oblX2 x 3 →
  0 < oblX0 x 4 * oblX2 x 5 - oblX0 x 5 * oblX2 x 4 →
  0 < oblX0 x 5 * oblX6 x 4 - oblX0 x 4 * oblX6 x 5 →
  Q45ResWJ F → HoleFull x F → IsRupert (univ.image x)

/-- [PROVED] `OpenSpecialJ ↔ OpenSpecialI`. -/
theorem openSpecialJ_iff_I : OpenSpecialJ ↔ OpenSpecialI := by
  unfold OpenSpecialJ OpenSpecialI
  simp only [q45ResWJ_iff_I]

/-- Every `Hole24` point off `OB1` is Rupert, given `OpenSpecialJ`. -/
theorem hole24_offOB1_J {F : S0xFac 9 s0x_S24 x} (h : Hole24 x F) (hO : ¬ H24K.SAT.OB1 x)
    (hS : OpenSpecialJ) : IsRupert (univ.image x) :=
  hole24_offOB1_I h hO (openSpecialJ_iff_I.mp hS)

/-- [PROVED] Generic + special (OSPEC16 form) assemble to `Open24Rupert`. -/
theorem open24Rupert_of_split_J (h1 : OpenOB1) (h2 : OpenSpecialJ) : Open24Rupert :=
  open24Rupert_of_split_I h1 (openSpecialJ_iff_I.mp h2)

end T234E

section T234F
open Minimality.LexCell

variable {x : Fin 7 → ℝ³}

/-! ### OSPEC17: `z6 < z2`; `236`, `346`, `126` as signs of the tie section -/

/-- Cramer's rule dotted with `N`: `⟪a, E × g⟫ ⟪N, w⟫ - ⟪a, E × w⟫ ⟪N, g⟫ + ⟪g, E × w⟫ ⟪N, a⟫ + ⟪a, g × w⟫ ⟪N, E⟫ = 0`. -/
theorem t234_cramer (N a E w g : ℝ³) :
    ⟪a, cross E g⟫ * ⟪N, w⟫ - ⟪a, cross E w⟫ * ⟪N, g⟫ + ⟪g, cross E w⟫ * ⟪N, a⟫ + ⟪a, cross g w⟫ * ⟪N, E⟫ = 0 := by
  simp only [t234_inner3, cross_apply_zero, cross_apply_one, cross_apply_two]; ring

/-- `⟪w, E × a⟫ = -⟪a, E × w⟫`. -/
theorem t234_triple_swap (a E w : ℝ³) : ⟪w, cross E a⟫ = -⟪a, cross E w⟫ := by
  simp only [t234_inner3, cross_apply_zero, cross_apply_one, cross_apply_two]; ring

/-- Binet-Cauchy for two triple products sharing `E`, `g` (the Gram determinant of `(N, E, g)` against `(d, E, g)`). -/
theorem t234_gram (N d E g : ℝ³) :
    ⟪N, cross E g⟫ * ⟪d, cross E g⟫ =
      ⟪N, d⟫ * (⟪E, E⟫ * ⟪g, g⟫ - ⟪E, g⟫ * ⟪E, g⟫) - ⟪N, E⟫ * (⟪E, d⟫ * ⟪g, g⟫ - ⟪E, g⟫ * ⟪g, d⟫) +
        ⟪N, g⟫ * (⟪E, d⟫ * ⟪g, E⟫ - ⟪E, E⟫ * ⟪g, d⟫) := by
  simp only [t234_inner3, cross_apply_zero, cross_apply_one, cross_apply_two]; ring

/-- **`x 5` and `x 6` lie on opposite sides of the plane `2 3 4`** (no branch hypothesis): `x 2` lies in the dihedral
wedge of the edge `3 4` between the faces `0345` (through `x 5`) and `346` (through `x 6`), and a plane through the
edge and a point of the wedge separates the two faces.  With `D = ⟪x5 - x3, E × (x6 - x3)⟫`, `E = x4 - x3`:
`⟪x5 - x2, n⟫ f3(x6) = D f3(x2)` and `⟪x6 - x2, n⟫ f8(x5) = -D f8(x2)` (`t234_cramer` with `N3 ⊥ x5 - x3, E` and
`N8 ⊥ x6 - x3, E`). -/
theorem t234_z6_of (F : S0xFac 9 s0x_S24 x) {b : ℝ³} (hb : b = n234 x ∨ b = -n234 x)
    (h5 : 0 < ⟪x 5 - x 2, b⟫) : ⟪x 6 - x 2, b⟫ < 0 := by
  have hP : ∀ i : Fin 7, ⟪x i - x 2, n234 x⟫ = ⟪x i - x 3, cross (x 4 - x 3) (x 2 - x 3)⟫ := by
    intro i
    have e : x i - x 2 = (x i - x 3) - (x 2 - x 3) := by abel
    have h0 : ⟪x 2 - x 3, n234 x⟫ = 0 := by
      have := (t234_perp (x := x) (Or.inl rfl)).1
      have e' : x 2 - x 3 = -(x 3 - x 2) := by abel
      rw [e', inner_neg_left, this, neg_zero]
    rw [e, inner_sub_left, h0, sub_zero, n234_eq]
  set D := ⟪x 5 - x 3, cross (x 4 - x 3) (x 6 - x 3)⟫ with hD
  have n3a : ⟪F.N 3, x 5 - x 3⟫ = 0 := by rw [F.inner_sub 3 5 3, F.zero 3 5 (by decide), F.zero 3 3 (by decide)]; ring
  have n3e : ⟪F.N 3, x 4 - x 3⟫ = 0 := by rw [F.inner_sub 3 4 3, F.zero 3 4 (by decide), F.zero 3 3 (by decide)]; ring
  have n3w : ⟪F.N 3, x 6 - x 3⟫ = F.f 3 (x 6) := by rw [F.inner_sub 3 6 3, F.zero 3 3 (by decide)]; ring
  have n3g : ⟪F.N 3, x 2 - x 3⟫ = F.f 3 (x 2) := by rw [F.inner_sub 3 2 3, F.zero 3 3 (by decide)]; ring
  have n8w : ⟪F.N 8, x 6 - x 3⟫ = 0 := by rw [F.inner_sub 8 6 3, F.zero 8 6 (by decide), F.zero 8 3 (by decide)]; ring
  have n8e : ⟪F.N 8, x 4 - x 3⟫ = 0 := by rw [F.inner_sub 8 4 3, F.zero 8 4 (by decide), F.zero 8 3 (by decide)]; ring
  have n8a : ⟪F.N 8, x 5 - x 3⟫ = F.f 8 (x 5) := by rw [F.inner_sub 8 5 3, F.zero 8 3 (by decide)]; ring
  have n8g : ⟪F.N 8, x 2 - x 3⟫ = F.f 8 (x 2) := by rw [F.inner_sub 8 2 3, F.zero 8 3 (by decide)]; ring
  have I3 : ⟪x 5 - x 2, n234 x⟫ * F.f 3 (x 6) = D * F.f 3 (x 2) := by
    have c := t234_cramer (F.N 3) (x 5 - x 3) (x 4 - x 3) (x 6 - x 3) (x 2 - x 3)
    rw [n3a, n3e, n3w, n3g] at c
    rw [hP 5]; linarith
  have I8 : ⟪x 6 - x 2, n234 x⟫ * F.f 8 (x 5) = -D * F.f 8 (x 2) := by
    have c := t234_cramer (F.N 8) (x 6 - x 3) (x 4 - x 3) (x 5 - x 3) (x 2 - x 3)
    rw [n8a, n8e, n8w, n8g, t234_triple_swap (x 5 - x 3) (x 4 - x 3) (x 6 - x 3)] at c
    rw [hP 6]; linarith
  have f36 : F.f 3 (x 6) < 0 := F.neg 3 6 (by decide)
  have f32 : F.f 3 (x 2) < 0 := F.neg 3 2 (by decide)
  have f85 : F.f 8 (x 5) < 0 := F.neg 8 5 (by decide)
  have f82 : F.f 8 (x 2) < 0 := F.neg 8 2 (by decide)
  rcases hb with rfl | rfl
  · have hD0 : 0 < D := by
      by_contra hc
      have : 0 ≤ D * F.f 3 (x 2) := mul_nonneg_of_nonpos_of_nonpos (not_lt.mp hc) f32.le
      nlinarith [mul_neg_of_pos_of_neg h5 f36]
    by_contra hc
    have : 0 ≤ ⟪x 6 - x 2, n234 x⟫ * F.f 8 (x 5) := by
      rw [I8]; nlinarith [mul_pos hD0 (neg_pos.mpr f82)]
    have h0 : ⟪x 6 - x 2, n234 x⟫ = 0 := by
      rcases (not_lt.mp hc).lt_or_eq with h | h
      · nlinarith [mul_neg_of_pos_of_neg h f85]
      · exact h.symm
    rw [h0, zero_mul] at I8; nlinarith [mul_pos hD0 (neg_pos.mpr f82)]
  · rw [inner_neg_right] at h5 ⊢
    have h5' : ⟪x 5 - x 2, n234 x⟫ < 0 := by linarith
    have hD0 : D < 0 := by
      by_contra hc
      have : D * F.f 3 (x 2) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (not_lt.mp hc) f32.le
      nlinarith [mul_pos_of_neg_of_neg h5' f36]
    have : ⟪x 6 - x 2, n234 x⟫ * F.f 8 (x 5) < 0 := by rw [I8]; nlinarith [mul_pos_of_neg_of_neg hD0 f82]
    have : 0 < ⟪x 6 - x 2, n234 x⟫ := by
      by_contra hc; nlinarith [mul_nonneg_of_nonpos_of_nonpos (not_lt.mp hc) f85.le]
    linarith

/-- **`z6 < z2` at `t234b`** on the B2 branch (`x 5` above the plane `2 3 4` by `t234_derived`). -/
theorem t234_z6 (F : S0xFac 9 s0x_S24 x) (hB : T234Br F) : ⟪x 6 - x 2, t234b x⟫ < 0 :=
  t234_z6_of F (t234b_cases x) (t234_derived F hB).1

/-- A product sign decides a down letter: if `A q = K c` with `q < 0 < K` and the facet is down at the lower levels
when edge-on at level 1, then the facet is down iff `c ≥ 0`. -/
theorem t234_lexDn_iff {A B C q K c : ℝ} (hq : q < 0) (hK : 0 < K) (hp : A * q = K * c)
    (h0 : 0 < -B ∨ (-B = 0 ∧ 0 < -C)) : LexPos3 (-A) (-B) (-C) ↔ 0 ≤ c := by
  constructor
  · intro h
    by_contra hc
    have hKc : K * c < 0 := mul_neg_of_pos_of_neg hK (not_le.mp hc)
    rcases h with h | ⟨h, -⟩
    · nlinarith [mul_pos_of_neg_of_neg (by linarith : A < 0) hq]
    · have : A = 0 := by linarith
      rw [this, zero_mul] at hp; linarith
  · intro hc
    have hKc : 0 ≤ K * c := mul_nonneg hK.le hc
    rcases lt_trichotomy A 0 with hA | hA | hA
    · exact Or.inl (by linarith)
    · exact Or.inr ⟨by rw [hA, neg_zero], h0⟩
    · nlinarith [mul_neg_of_pos_of_neg hA hq]

/-- The product `⟪v, t234b⟫ ⟪x6 - x2, t234b⟫` does not depend on the orientation. -/
theorem t234b_prod (v : ℝ³) : ⟪v, t234b x⟫ * ⟪x 6 - x 2, t234b x⟫ = ⟪v, n234 x⟫ * ⟪x 6 - x 2, n234 x⟫ := by
  rcases t234b_cases x with e | e <;> rw [e]
  rw [inner_neg_right, inner_neg_right, neg_mul_neg]

/-- The tie-plane coordinate of `x 6` along the foot direction of `x 2` (`X6` of OSPEC16; `X(P0) = 0`). -/
noncomputable def t234X6 (x : Fin 7 → ℝ³) : ℝ :=
  ⟪x 4 - x 3, x 4 - x 3⟫ * ⟪x 6 - x 3, x 2 - x 3⟫ - ⟪x 4 - x 3, x 6 - x 3⟫ * ⟪x 4 - x 3, x 2 - x 3⟫

/-- `⟪x2 - x3, x2 - x6⟫` (`X2 - X6 = |e|² t234C` on the tie: the angle at `x 2` between `x 3` and `x 6`). -/
noncomputable def t234C (x : Fin 7 → ℝ³) : ℝ := ⟪x 2 - x 3, x 2 - x 6⟫

/-- **`346` down at `t234b` iff `X6 ≥ 0`** on the B2 branch (`t234_prod8`; edge-on at level 1 it is down at level 3,
`f8(x 5) < 0`). -/
theorem t234_dn8_iff (F : S0xFac 9 s0x_S24 x) (hB : T234Br F) : T234Dn F (t234b x) 8 ↔ 0 ≤ t234X6 x := by
  have hq := t234_z6 F hB
  have hp : ⟪F.N 8, t234b x⟫ * ⟪x 6 - x 2, t234b x⟫ = (-F.f 8 (x 2)) * t234X6 x := by
    rw [t234b_prod, t234_prod8, t234X6]; ring
  have n8e : ⟪F.N 8, x 4 - x 3⟫ = 0 := by rw [F.inner_sub 8 4 3, F.zero 8 4 (by decide), F.zero 8 3 (by decide)]; ring
  have n856 : ⟪F.N 8, x 5 - x 6⟫ = F.f 8 (x 5) := by rw [F.inner_sub 8 5 6, F.zero 8 6 (by decide)]; ring
  unfold T234Dn
  refine t234_lexDn_iff hq (neg_pos.mpr (F.neg 8 2 (by decide))) hp (Or.inr ⟨by rw [n8e, neg_zero], ?_⟩)
  rw [n856]; exact neg_pos.mpr (F.neg 8 5 (by decide))

/-- The heights along `e34` on `T234BrJ`: `τ = ⟪x5 - x3, x4 - x3⟫ = ⟪x6 - x3, x4 - x3⟫ = ⟪x4 - x3, x2 - x3⟫ > 0`. -/
theorem t234_tau_eqs (F : S0xFac 9 s0x_S24 x) (hB : T234BrJ F) :
    0 < ⟪x 5 - x 3, x 4 - x 3⟫ ∧ ⟪x 6 - x 3, x 4 - x 3⟫ = ⟪x 5 - x 3, x 4 - x 3⟫ ∧
      ⟪x 4 - x 3, x 2 - x 3⟫ = ⟪x 5 - x 3, x 4 - x 3⟫ := by
  obtain ⟨⟨-, -, -, -, -, -, htie, -⟩, h56, h35⟩ := hB
  refine ⟨t234_tau_pos F htie h56 h35, ?_, ?_⟩
  · simp only [t234_inner3, PiLp.sub_apply] at h56 ⊢; linear_combination h56
  · simp only [t234_inner3, PiLp.sub_apply] at htie ⊢; linear_combination -htie

/-- **`236` down at `t234b` iff the angle at `x 2` between `x 3` and `x 6` is not obtuse** on `T234BrJ`
(`t234_prod7`, `τ > 0`; edge-on at level 1 it is down at level 2, `f7(x 4) < 0`). -/
theorem t234_dn7_iff (F : S0xFac 9 s0x_S24 x) (hB : T234BrJ F) : T234Dn F (t234b x) 7 ↔ 0 ≤ t234C x := by
  have hq := t234_z6 F hB.1
  obtain ⟨htau, e6, -⟩ := t234_tau_eqs F hB
  have htie26 : ⟪x 2, x 3 - x 4⟫ = ⟪x 6, x 3 - x 4⟫ := by
    obtain ⟨⟨-, -, -, -, -, -, htie, -⟩, h56, -⟩ := hB; exact htie.trans h56
  have hp : ⟪F.N 7, t234b x⟫ * ⟪x 6 - x 2, t234b x⟫ =
      (-F.f 7 (x 4) * ⟪x 5 - x 3, x 4 - x 3⟫) * t234C x := by
    rw [t234b_prod, t234_prod7 F htie26, e6, t234C]; ring
  have n7e : ⟪F.N 7, x 4 - x 3⟫ = F.f 7 (x 4) := by rw [F.inner_sub 7 4 3, F.zero 7 3 (by decide)]; ring
  unfold T234Dn
  refine t234_lexDn_iff hq (mul_pos (neg_pos.mpr (F.neg 7 4 (by decide))) htau) hp (Or.inl ?_)
  rw [n7e]; exact neg_pos.mpr (F.neg 7 4 (by decide))

/-- The B2 branch with `h4 ≤ h5` (the `h6hi` half `max h4 h2 ≤ min h6 h5` of `ResB2T`, heights along `e34`). -/
def T234BrL {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) : Prop :=
  T234BrJ F ∧ ⟪x 4, x 3 - x 4⟫ ≤ ⟪x 5, x 3 - x 4⟫

/-- **`126` as a tie-section sign** on `T234BrL`: `⟪N5, t234b⟫ ⟪x6 - x2, t234b⟫ = t234C · β`, `β = -(f5(x 4) τ +
f5(x 3) (h2 - h4)) > 0` (`t234_gram` with `N5 ⊥ x6 - x2 ⊥ e34`: `126` and `236` both contain the line `2 6` of the
tie plane). -/
theorem t234_prod5 (F : S0xFac 9 s0x_S24 x) (hB : T234BrL F) :
    ∃ β : ℝ, 0 < β ∧ ⟪F.N 5, t234b x⟫ * ⟪x 6 - x 2, t234b x⟫ = t234C x * β := by
  obtain ⟨hJ, h45⟩ := hB
  obtain ⟨htau, -, eg⟩ := t234_tau_eqs F hJ
  obtain ⟨⟨-, -, -, -, -, -, htie, -⟩, h56, -⟩ := id hJ
  have htie26 : ⟪x 2, x 3 - x 4⟫ = ⟪x 6, x 3 - x 4⟫ := htie.trans h56
  have n5d : ⟪F.N 5, x 6 - x 2⟫ = 0 := by rw [F.inner_sub 5 6 2, F.zero 5 6 (by decide), F.zero 5 2 (by decide)]; ring
  have n5e : ⟪F.N 5, x 4 - x 3⟫ = F.f 5 (x 4) - F.f 5 (x 3) := F.inner_sub 5 4 3
  have n5g : ⟪F.N 5, x 2 - x 3⟫ = -F.f 5 (x 3) := by rw [F.inner_sub 5 2 3, F.zero 5 2 (by decide)]; ring
  have hed : ⟪x 4 - x 3, x 6 - x 2⟫ = 0 := by
    simp only [t234_inner3, PiLp.sub_apply] at htie26 ⊢; linear_combination htie26
  have hgd : ⟪x 2 - x 3, x 6 - x 2⟫ = -t234C x := by
    rw [t234C]; simp only [t234_inner3, PiLp.sub_apply]; ring
  have hh : 0 ≤ ⟪x 4 - x 3, x 4 - x 3⟫ - ⟪x 4 - x 3, x 2 - x 3⟫ := by
    have : ⟪x 4 - x 3, x 4 - x 3⟫ - ⟪x 4 - x 3, x 2 - x 3⟫ = ⟪x 5, x 3 - x 4⟫ - ⟪x 4, x 3 - x 4⟫ := by
      simp only [t234_inner3, PiLp.sub_apply] at htie ⊢; linear_combination htie
    rw [this]; linarith
  have hG := t234_gram (F.N 5) (x 6 - x 2) (x 4 - x 3) (x 2 - x 3)
  rw [n5d, n5e, n5g, hed, hgd, ← n234_eq] at hG
  refine ⟨-(F.f 5 (x 4) * ⟪x 5 - x 3, x 4 - x 3⟫ +
    F.f 5 (x 3) * (⟪x 4 - x 3, x 4 - x 3⟫ - ⟪x 4 - x 3, x 2 - x 3⟫)), ?_, ?_⟩
  · have f54 : F.f 5 (x 4) < 0 := F.neg 5 4 (by decide)
    have f53 : F.f 5 (x 3) < 0 := F.neg 5 3 (by decide)
    nlinarith [mul_neg_of_neg_of_pos f54 htau, mul_nonpos_of_nonpos_of_nonneg f53.le hh]
  · rw [t234b_prod, hG, real_inner_comm (x 4 - x 3) (x 2 - x 3), eg]; ring

/-- **`126` down at `t234b` when the angle at `x 2` is acute** (`T234BrL`, `t234C > 0`). -/
theorem t234_dn5_of (F : S0xFac 9 s0x_S24 x) (hB : T234BrL F) (hc : 0 < t234C x) : T234Dn F (t234b x) 5 := by
  have hq := t234_z6 F hB.1.1
  obtain ⟨β, hβ, hp⟩ := t234_prod5 F hB
  left
  have : 0 < ⟪F.N 5, t234b x⟫ * ⟪x 6 - x 2, t234b x⟫ := by rw [hp]; exact mul_pos hc hβ
  by_contra hn
  nlinarith [mul_nonpos_of_nonneg_of_nonpos (by linarith : (0:ℝ) ≤ ⟪F.N 5, t234b x⟫) hq.le]

/-- **`126` up at `t234b` when the angle at `x 2` is obtuse** (`T234BrL`, `t234C < 0`): off `t234C = 0`, `126` and
`236` flip together. -/
theorem t234_up5_of (F : S0xFac 9 s0x_S24 x) (hB : T234BrL F) (hc : t234C x < 0) : T234Up F (t234b x) 5 := by
  have hq := t234_z6 F hB.1.1
  obtain ⟨β, hβ, hp⟩ := t234_prod5 F hB
  left
  have : ⟪F.N 5, t234b x⟫ * ⟪x 6 - x 2, t234b x⟫ < 0 := by rw [hp]; exact mul_neg_of_neg_of_pos hc hβ
  by_contra hn
  nlinarith [mul_nonneg_of_nonpos_of_nonpos (not_lt.mp hn) hq.le]

/-- **The tie-section cone condition** at `t234b`: `t234b` lies in the tangent cone of the section quadrilateral `P0 6 2
5` at `x 6`, i.e. `0 ≤ X6` (`346`) and `X6 ≤ X2` (`t234C ≥ 0`, `236`), with `126` explicit only on the boundary
`t234C = 0`. -/
def T234Cone {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) : Prop :=
  0 ≤ t234X6 x ∧ (0 < t234C x ∨ (t234C x = 0 ∧ T234Dn F (t234b x) 5))

/-- **The remaining T234 letters after OSPEC17**: `016 046` down, the cone condition, and `012` up or (`012` down,
`025` up). -/
def T234RedL {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) : Prop :=
  T234Dn F (t234b x) 1 ∧ T234Dn F (t234b x) 4 ∧ T234Cone F ∧
    (T234Up F (t234b x) 0 ∨ (T234Dn F (t234b x) 0 ∧ T234Up F (t234b x) 2))

theorem t234RedJ_iff_L (F : S0xFac 9 s0x_S24 x) (hB : T234BrL F) : T234RedJ F ↔ T234RedL F := by
  have h7 := t234_dn7_iff F hB.1
  have h8 := t234_dn8_iff F hB.1.1
  unfold T234RedJ T234RedL T234Cone
  rw [h7, h8]
  constructor
  · rintro ⟨n1, n4, n5, hc, hX, hr⟩
    refine ⟨n1, n4, ⟨hX, ?_⟩, hr⟩
    rcases hc.lt_or_eq with h | h
    · exact Or.inl h
    · exact Or.inr ⟨h.symm, n5⟩
  · rintro ⟨n1, n4, ⟨hX, hc⟩, hr⟩
    rcases hc with h | ⟨h, n5⟩
    · exact ⟨n1, n4, t234_dn5_of F hB h, h.le, hX, hr⟩
    · exact ⟨n1, n4, n5, h.ge, hX, hr⟩

/-- **Exactness**: on `T234BrL`, `T234ViewOK ↔ T234RedL`. -/
theorem t234ViewOK_iff_redL (F : S0xFac 9 s0x_S24 x) (hB : T234BrL F) : T234ViewOK F ↔ T234RedL F :=
  (t234ViewOK_iff_redJ F hB.1).trans (t234RedJ_iff_L F hB)

/-- The B2 corner tie supplies `T234BrL`. -/
theorem t234BrL_of_resB2T (F : S0xFac 9 s0x_S24 x) {s t : ℝ} (h : ResB2T x s) (ht : 0 < t)
    (hd : x 3 - x 0 = s • (x 4 - x 0) + t • (x 5 - x 0))
    (hb1 : oblX0 x 4 * oblX6 x 3 - oblX0 x 3 * oblX6 x 4 < 0) : T234BrL F :=
  ⟨t234BrJ_of_resB2T F h ht hd hb1, (le_max_left _ _).trans (h.2.2.1.trans (min_le_right _ _))⟩

/-! ### The residue in the tie-section form (OSPEC17) -/

/-- The T234 view condition in the tie-section form: on `T234BrL` only `T234RedL`, elsewhere `T234ViewOK`. -/
def T234ViewL {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) : Prop :=
  (T234BrL F ∧ T234RedL F) ∨ (¬ T234BrL F ∧ T234ViewOK F)

/-- `T234ViewL` is `T234ViewOK`. -/
theorem t234ViewL_iff (F : S0xFac 9 s0x_S24 x) : T234ViewL F ↔ T234ViewOK F := by
  by_cases hB : T234BrL F
  · unfold T234ViewL; rw [t234ViewOK_iff_redL F hB]; tauto
  · unfold T234ViewL
    constructor
    · rintro (⟨h, -⟩ | ⟨-, h⟩)
      · exact (hB h).elim
      · exact h
    · intro h; exact Or.inr ⟨hB, h⟩

theorem lexAny_of_t234ViewL (F : S0xFac 9 s0x_S24 x) (h : T234ViewL F) : Gen.LexAny F :=
  lexAny_of_t234View F ((t234ViewL_iff F).mp h)

/-- `Q45ResSTG` where neither `T234ViewL` (nor its mirror) applies: on the B2 branch the failure of `T234RedL` (`016` or
`046` up, the cone condition, or the rim letters; sampled failures only the cone condition and `012` with `025`). -/
def Q45ResSTL {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (s t : ℝ) : Prop :=
  Q45ResSTG F s t ∧ ¬ T234ViewL F ∧ ¬ T234ViewL (Sym.sym24 F)

/-- The branch-tagged residue after OSPEC17. -/
def Q45ResWL {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) : Prop :=
  ∃ s t : ℝ, 0 < s ∧ 0 < t ∧ 1 < s + t ∧ x 3 - x 0 = s • (x 4 - x 0) + t • (x 5 - x 0) ∧ Q45ResSTL F s t

/-- `Q45ResWL = Q45ResWJ`. -/
theorem q45ResWL_iff_J (F : S0xFac 9 s0x_S24 x) : Q45ResWL F ↔ Q45ResWJ F := by
  unfold Q45ResWL Q45ResWJ Q45ResSTL Q45ResSTJ
  simp only [t234ViewL_iff, t234ViewJ_iff]

/-- [OPEN] **The special piece after OSPEC17, Rupert form**: `OpenSpecialJ` with `Q45ResWL` in place of `Q45ResWJ`
(equivalent: `openSpecialL_iff_J`). -/
def OpenSpecialL : Prop := ∀ (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x), ¬ H24K.SAT.OB1 x →
  1 ≤ oblX0 x 4 → 1 ≤ oblX0 x 5 →
  oblX0 x 4 * oblX6 x 3 - oblX0 x 3 * oblX6 x 4 < 0 →
  0 < oblX0 x 3 * oblX2 x 5 - oblX0 x 5 * oblX2 x 3 →
  0 < oblX0 x 4 * oblX2 x 5 - oblX0 x 5 * oblX2 x 4 →
  0 < oblX0 x 5 * oblX6 x 4 - oblX0 x 4 * oblX6 x 5 →
  Q45ResWL F → HoleFull x F → IsRupert (univ.image x)

/-- [PROVED] `OpenSpecialL ↔ OpenSpecialJ`. -/
theorem openSpecialL_iff_J : OpenSpecialL ↔ OpenSpecialJ := by
  unfold OpenSpecialL OpenSpecialJ
  simp only [q45ResWL_iff_J]

/-- Every `Hole24` point off `OB1` is Rupert, given `OpenSpecialL`. -/
theorem hole24_offOB1_L {F : S0xFac 9 s0x_S24 x} (h : Hole24 x F) (hO : ¬ H24K.SAT.OB1 x)
    (hS : OpenSpecialL) : IsRupert (univ.image x) :=
  hole24_offOB1_J h hO (openSpecialL_iff_J.mp hS)

/-- [PROVED] Generic + special (OSPEC17 form) assemble to `Open24Rupert`. -/
theorem open24Rupert_of_split_L (h1 : OpenOB1) (h2 : OpenSpecialL) : Open24Rupert :=
  open24Rupert_of_split_J h1 (openSpecialL_iff_J.mp h2)

end T234F


section T234G
open Minimality.LexCell

variable {x : Fin 7 → ℝ³}

/-! ### OSPEC17 (b): the T234 view off the cone (three more rims, all depth letters derived) -/

/-- Rim `0 1 6 3 4` (`126 236` up: `t234b` past the line `2 6` of the tie section). -/
def rimTE : ZMod 5 → Fin 7 := ![0, 1, 6, 3, 4]
def UTE : Finset (Fin 9) := {0, 3, 5, 7}
def DnTE : Finset (Fin 9) := {1, 4, 8}
theorem rimTE_cyc : S0xCycUD s0x_S24 rimTE UTE DnTE := by decide
theorem rimTE_inj : Function.Injective rimTE := by decide

/-- Rim `0 1 2 3 6 4` (`346` up: `t234b` past the line `6 P0`). -/
def rimTF : ZMod 6 → Fin 7 := ![0, 1, 2, 3, 6, 4]
def UTF : Finset (Fin 9) := {0, 3, 6, 8}
def DnTF : Finset (Fin 9) := {1, 4, 5, 7}
theorem rimTF_cyc : S0xCycUD s0x_S24 rimTF UTF DnTF := by decide
theorem rimTF_inj : Function.Injective rimTF := by decide

/-- Rim `0 2 3 6 4` (`012` down, `025 346` up). -/
def rimTG : ZMod 5 → Fin 7 := ![0, 2, 3, 6, 4]
def UTG : Finset (Fin 9) := {2, 3, 6, 8}
def DnTG : Finset (Fin 9) := {0, 4, 7}
theorem rimTG_cyc : S0xCycUD s0x_S24 rimTG UTG DnTG := by decide
theorem rimTG_inj : Function.Injective rimTG := by decide

/-- The depth letters of the T234 view at `t234b` on `T234BrJ`, all derived: `z2 = z3 = z4` (level 1), `z6 < z2 <
z0, z1` (level 1), `z3 < z4` and `z3 < z2` (level 2, `|e34|² > 0` and `τ > 0`). -/
theorem t234_depths (F : S0xFac 9 s0x_S24 x) (hB : T234BrJ F) :
    ⟪x 3, t234b x⟫ = ⟪x 2, t234b x⟫ ∧ ⟪x 4, t234b x⟫ = ⟪x 2, t234b x⟫ ∧ ⟪x 2, t234b x⟫ < ⟪x 0, t234b x⟫ ∧
      ⟪x 2, t234b x⟫ < ⟪x 1, t234b x⟫ ∧ ⟪x 6, t234b x⟫ < ⟪x 2, t234b x⟫ ∧
      ⟪x 3, x 4 - x 3⟫ < ⟪x 4, x 4 - x 3⟫ ∧ ⟪x 3, x 4 - x 3⟫ < ⟪x 2, x 4 - x 3⟫ := by
  obtain ⟨-, -, h20, h21⟩ := t234_derived F hB.1
  have h6 := t234_z6 F hB.1
  rw [inner_sub_left] at h6
  obtain ⟨htau, -, eg⟩ := t234_tau_eqs F hB
  have h32 : ⟪x 3, x 4 - x 3⟫ < ⟪x 2, x 4 - x 3⟫ := by
    have h : 0 < ⟪x 4 - x 3, x 2 - x 3⟫ := eg ▸ htau
    rw [← sub_pos, ← inner_sub_left, real_inner_comm]; exact h
  exact ⟨t234_tie3 (t234b_cases x), t234_tie4 (t234b_cases x), h20, h21, by linarith, t234_lt34 F, h32⟩

/-- `236` up at `t234b` when the angle at `x 2` is obtuse (`T234BrJ`, `t234C < 0`). -/
theorem t234_up7_of (F : S0xFac 9 s0x_S24 x) (hB : T234BrJ F) (hc : t234C x < 0) : T234Up F (t234b x) 7 := by
  have hq := t234_z6 F hB.1
  obtain ⟨htau, e6, -⟩ := t234_tau_eqs F hB
  have htie26 : ⟪x 2, x 3 - x 4⟫ = ⟪x 6, x 3 - x 4⟫ := by
    obtain ⟨⟨-, -, -, -, -, -, htie, -⟩, h56, -⟩ := hB; exact htie.trans h56
  have hp : ⟪F.N 7, t234b x⟫ * ⟪x 6 - x 2, t234b x⟫ =
      (-F.f 7 (x 4) * ⟪x 5 - x 3, x 4 - x 3⟫) * t234C x := by
    rw [t234b_prod, t234_prod7 F htie26, e6, t234C]; ring
  have hK : 0 < -F.f 7 (x 4) * ⟪x 5 - x 3, x 4 - x 3⟫ := mul_pos (neg_pos.mpr (F.neg 7 4 (by decide))) htau
  left
  have : ⟪F.N 7, t234b x⟫ * ⟪x 6 - x 2, t234b x⟫ < 0 := by rw [hp]; exact mul_neg_of_pos_of_neg hK hc
  by_contra hn
  nlinarith [mul_nonneg_of_nonpos_of_nonpos (not_lt.mp hn) hq.le]

/-- `346` up at `t234b` when `X6 < 0` (`T234Br`). -/
theorem t234_up8_of (F : S0xFac 9 s0x_S24 x) (hB : T234Br F) (hX : t234X6 x < 0) : T234Up F (t234b x) 8 := by
  have hq := t234_z6 F hB
  have hp : ⟪F.N 8, t234b x⟫ * ⟪x 6 - x 2, t234b x⟫ = (-F.f 8 (x 2)) * t234X6 x := by
    rw [t234b_prod, t234_prod8, t234X6]; ring
  have hK : 0 < -F.f 8 (x 2) := neg_pos.mpr (F.neg 8 2 (by decide))
  left
  have : ⟪F.N 8, t234b x⟫ * ⟪x 6 - x 2, t234b x⟫ < 0 := by rw [hp]; exact mul_neg_of_pos_of_neg hK hX
  by_contra hn
  nlinarith [mul_nonneg_of_nonpos_of_nonpos (not_lt.mp hn) hq.le]

/-- On the tie `h2 = h6`: `X2 - X6 = |e|² t234C` with `X2 = |e|² |g|² - ⟪e, g⟫² ≥ 0`, so `X6 < 0` forces `t234C > 0`. -/
theorem t234C_pos_of_X6 (F : S0xFac 9 s0x_S24 x) (hB : T234BrJ F) (hX : t234X6 x < 0) : 0 < t234C x := by
  have htie26 : ⟪x 2, x 3 - x 4⟫ = ⟪x 6, x 3 - x 4⟫ := by
    obtain ⟨⟨-, -, -, -, -, -, htie, -⟩, h56, -⟩ := hB; exact htie.trans h56
  have hEd : ⟪x 4 - x 3, x 2 - x 6⟫ = 0 := by
    simp only [t234_inner3, PiLp.sub_apply] at htie26 ⊢; linear_combination -htie26
  have hw : x 6 - x 3 = (x 2 - x 3) - (x 2 - x 6) := by abel
  have hX6 : t234X6 x = (⟪x 4 - x 3, x 4 - x 3⟫ * ⟪x 2 - x 3, x 2 - x 3⟫ - ⟪x 4 - x 3, x 2 - x 3⟫ ^ 2) -
      ⟪x 4 - x 3, x 4 - x 3⟫ * t234C x := by
    have e1 : ⟪x 4 - x 3, x 6 - x 3⟫ = ⟪x 4 - x 3, x 2 - x 3⟫ - ⟪x 4 - x 3, x 2 - x 6⟫ := by rw [hw, inner_sub_right]
    have e2 : ⟪x 6 - x 3, x 2 - x 3⟫ = ⟪x 2 - x 3, x 2 - x 3⟫ - ⟪x 2 - x 6, x 2 - x 3⟫ := by rw [hw, inner_sub_left]
    rw [t234X6, t234C, e1, e2, hEd, real_inner_comm (x 2 - x 3) (x 2 - x 6)]; ring
  have hCS := real_inner_mul_inner_self_le (x 4 - x 3) (x 2 - x 3)
  have hee : 0 ≤ ⟪x 4 - x 3, x 4 - x 3⟫ := real_inner_self_nonneg
  by_contra hc
  have : 0 ≤ -(⟪x 4 - x 3, x 4 - x 3⟫ * t234C x) := by
    have := mul_nonneg hee (neg_nonneg.mpr (not_lt.mp hc)); linarith
  nlinarith

/-- **The general T234 residue letters** on `T234BrL` (OSPEC17 (b)): `016 046` down, `012` up or (`012` down, `025` up,
`t234C ≥ 0`), and `126` down on the boundary `t234C = 0`.  The cone condition is gone: off the cone the same view
`(t234b, x 4 - x 3, x 5 - x 6)` has the rim `0 1 6 3 4` (`t234C < 0`) or `0 1 2 3 6 4` / `0 2 3 6 4` (`X6 < 0`). -/
def T234RedM {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) : Prop :=
  T234Dn F (t234b x) 1 ∧ T234Dn F (t234b x) 4 ∧
    (T234Up F (t234b x) 0 ∨ (T234Dn F (t234b x) 0 ∧ T234Up F (t234b x) 2 ∧ 0 ≤ t234C x)) ∧
    (t234C x = 0 → T234Dn F (t234b x) 5)

/-- **The T234 view is a lex cell on the B2 branch from the general letters** (five rims). -/
theorem lexAny_of_t234RedM (F : S0xFac 9 s0x_S24 x) (hB : T234BrL F) (h : T234RedM F) : Gen.LexAny F := by
  obtain ⟨n1, n4, h0, h5⟩ := h
  obtain ⟨t3, t4, h20, h21, h62, l34, l32⟩ := t234_depths F hB.1
  have u3 : T234Up F (t234b x) 3 := Or.inl (t234_derived F hB.1.1).2.1
  have u6 := t234_up6 F hB.1
  set b := t234b x with hbdef
  -- the three new rims
  have rimE : RobUniLex (t234Z x b rimTE) := by
    have e0 : rimTE 0 = 0 := by decide
    have e1 : rimTE 1 = 1 := by decide
    have e2 : rimTE 2 = 6 := by decide
    have e3 : rimTE 3 = 3 := by decide
    have e4 : rimTE 4 = 4 := by decide
    apply robUniLex_five_e26
    · simp only [t234Z, e1, e2]; exact lexLt3_of_fst (by simp only; linarith)
    · simp only [t234Z, e3, e4]
      exact Or.inr ⟨by simp only; linarith, Or.inl (by simp only; linarith)⟩
    · simp only [t234Z, e4, e0]; exact lexLt3_of_fst (by simp only; linarith)
    · simp only [t234Z, e3, e0]; exact lexLt3_of_fst (by simp only; linarith)
  have rimG : RobUniLex (t234Z x b rimTG) := by
    have e0 : rimTG 0 = 0 := by decide
    have e1 : rimTG 1 = 2 := by decide
    have e2 : rimTG 2 = 3 := by decide
    have e3 : rimTG 3 = 6 := by decide
    have e4 : rimTG 4 = 4 := by decide
    apply robUniLex_five_e26
    · simp only [t234Z, e1, e2]
      exact Or.inr ⟨by simp only; linarith, Or.inl (by simp only; linarith)⟩
    · simp only [t234Z, e3, e4]; exact lexLt3_of_fst (by simp only; linarith)
    · simp only [t234Z, e4, e0]; exact lexLt3_of_fst (by simp only; linarith)
    · simp only [t234Z, e3, e0]; exact lexLt3_of_fst (by simp only; linarith)
  have rimF : RobUniLex (t234Z x b rimTF) := by
    have e0 : rimTF 0 = 0 := by decide
    have e1 : rimTF 1 = 1 := by decide
    have e2 : rimTF 2 = 2 := by decide
    have e3 : rimTF 3 = 3 := by decide
    have e4 : rimTF 4 = 6 := by decide
    have e5 : rimTF 5 = 4 := by decide
    apply robUniLex_six_dw
    · left; simp only [t234Z, e3, e2]
      exact Or.inr ⟨by simp only; linarith, Or.inl (by simp only; linarith)⟩
    · left; simp only [t234Z, e5, e0]; exact lexLt3_of_fst (by simp only; linarith)
    · left; simp only [t234Z, e4, e5]; exact lexLt3_of_fst (by simp only; linarith)
    · left; simp only [t234Z, e2, e1]; exact lexLt3_of_fst (by simp only; linarith)
  -- facet cases
  have hcell : ∀ {k : ℕ} [NeZero k] (c : ZMod k → Fin 7) (U Dn : Finset (Fin 9)), 4 ≤ k → Function.Injective c →
      S0xCycUD s0x_S24 c U Dn → (∀ t ∈ U, T234Up F b t) → (∀ t ∈ Dn, T234Dn F b t) → RobUniLex (t234Z x b c) →
      Gen.LexAny F := by
    intro k _ c U Dn hk hc hcyc hU hD hR
    exact ⟨k, inferInstance, c, U, Dn, b, x 4 - x 3, x 5 - x 6, hk, hc, hcyc, hU, hD, hR⟩
  have hb := t234b_cases x
  rcases lt_or_ge (t234X6 x) 0 with hX | hX
  · -- `X6 < 0`: `346` up, `t234C > 0`, `126 236` down
    have u8 := t234_up8_of F hB.1.1 hX
    have hc := t234C_pos_of_X6 F hB.1 hX
    have n5 := t234_dn5_of F hB hc
    have n7 := (t234_dn7_iff F hB.1).mpr hc.le
    rcases h0 with u0 | ⟨n0, u2, -⟩
    · refine hcell rimTF UTF DnTF (by norm_num) rimTF_inj rimTF_cyc ?_ ?_ rimF
      · intro t ht; simp only [UTF, Finset.mem_insert, Finset.mem_singleton] at ht
        rcases ht with rfl | rfl | rfl | rfl
        exacts [u0, u3, u6, u8]
      · intro t ht; simp only [DnTF, Finset.mem_insert, Finset.mem_singleton] at ht
        rcases ht with rfl | rfl | rfl | rfl
        exacts [n1, n4, n5, n7]
    · refine hcell rimTG UTG DnTG (by norm_num) rimTG_inj rimTG_cyc ?_ ?_ rimG
      · intro t ht; simp only [UTG, Finset.mem_insert, Finset.mem_singleton] at ht
        rcases ht with rfl | rfl | rfl | rfl
        exacts [u2, u3, u6, u8]
      · intro t ht; simp only [DnTG, Finset.mem_insert, Finset.mem_singleton] at ht
        rcases ht with rfl | rfl | rfl
        exacts [n0, n4, n7]
  · have n8 := (t234_dn8_iff F hB.1.1).mpr hX
    rcases lt_or_ge (t234C x) 0 with hc | hc
    · -- `t234C < 0`: `126 236` up, rim `0 1 6 3 4`; `012` must be up
      have u5 := t234_up5_of F hB hc
      have u7 := t234_up7_of F hB.1 hc
      have u0 : T234Up F b 0 := by
        rcases h0 with u0 | ⟨-, -, hc'⟩
        · exact u0
        · exact absurd hc' (not_le.mpr hc)
      refine hcell rimTE UTE DnTE (by norm_num) rimTE_inj rimTE_cyc ?_ ?_ rimE
      · intro t ht; simp only [UTE, Finset.mem_insert, Finset.mem_singleton] at ht
        rcases ht with rfl | rfl | rfl | rfl
        exacts [u0, u3, u5, u7]
      · intro t ht; simp only [DnTE, Finset.mem_insert, Finset.mem_singleton] at ht
        rcases ht with rfl | rfl | rfl
        exacts [n1, n4, n8]
    · -- the cone: the OSPEC14 rims
      have n7 := (t234_dn7_iff F hB.1).mpr hc
      have n5 : T234Dn F b 5 := by
        rcases hc.lt_or_eq with hc | hc
        · exact t234_dn5_of F hB hc
        · exact h5 hc.symm
      refine lexAny_of_t234At F hb ⟨u3, u6, n1, n4, n5, n7, n8, h20, ?_⟩
      rcases h0 with u0 | ⟨n0, u2, -⟩
      · exact Or.inl ⟨u0, h21⟩
      · exact Or.inr ⟨n0, u2⟩

/-- `T234RedM` is weaker than `T234RedL` (the old letters imply the new ones). -/
theorem t234RedM_of_L (F : S0xFac 9 s0x_S24 x) (h : T234RedL F) : T234RedM F := by
  obtain ⟨n1, n4, ⟨-, hc⟩, h0⟩ := h
  refine ⟨n1, n4, ?_, ?_⟩
  · rcases h0 with u0 | ⟨n0, u2⟩
    · exact Or.inl u0
    · refine Or.inr ⟨n0, u2, ?_⟩
      rcases hc with hc | ⟨hc, -⟩
      · exact hc.le
      · exact hc.ge
  · intro h0c
    rcases hc with hc | ⟨-, n5⟩
    · exact absurd h0c hc.ne'
    · exact n5

/-! ### The residue after the general T234 view (OSPEC17 (b)) -/

/-- The general T234 view: `T234ViewOK`, or on `T234BrL` the letters `T234RedM`. -/
def T234ViewM {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) : Prop :=
  T234ViewOK F ∨ (T234BrL F ∧ T234RedM F)

theorem lexAny_of_t234ViewM (F : S0xFac 9 s0x_S24 x) (h : T234ViewM F) : Gen.LexAny F := by
  rcases h with h | ⟨hB, h⟩
  · exact lexAny_of_t234View F h
  · exact lexAny_of_t234RedM F hB h

/-- `Q45ResSTG` where neither general T234 view (nor its mirror) applies: on the B2 branch the failure of `T234RedM`
(`016` or `046` up, `012` down with `025` down or `t234C < 0`, or `126` not down at `t234C = 0`). -/
def Q45ResSTM {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (s t : ℝ) : Prop :=
  Q45ResSTG F s t ∧ ¬ T234ViewM F ∧ ¬ T234ViewM (Sym.sym24 F)

/-- The branch-tagged residue after OSPEC17 (b). -/
def Q45ResWM {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) : Prop :=
  ∃ s t : ℝ, 0 < s ∧ 0 < t ∧ 1 < s + t ∧ x 3 - x 0 = s • (x 4 - x 0) + t • (x 5 - x 0) ∧ Q45ResSTM F s t

/-- **The general T234 views cut the residue**: a point of `Q45ResSTG` is `LexAny` or in `Q45ResSTM`. -/
theorem q45_resM_local (F : S0xFac 9 s0x_S24 x) {s t : ℝ} (h : Q45ResSTG F s t) :
    Gen.LexAny F ∨ Q45ResSTM F s t := by
  by_cases hA : T234ViewM F
  · exact Or.inl (lexAny_of_t234ViewM F hA)
  by_cases hB : T234ViewM (Sym.sym24 F)
  · exact Or.inl (Sym.lexAny_sym F (lexAny_of_t234ViewM (Sym.sym24 F) hB))
  exact Or.inr ⟨h, hA, hB⟩

/-- `Q45ResWM ⊆ Q45ResWH` (so also `⊆ Q45ResWL`). -/
theorem q45ResWH_of_M {F : S0xFac 9 s0x_S24 x} (h : Q45ResWM F) : Q45ResWH F := by
  obtain ⟨s, t, hs, ht, hst, hd, h, hA, hB⟩ := h
  exact ⟨s, t, hs, ht, hst, hd, h, fun h' => hA (Or.inl h'), fun h' => hB (Or.inl h')⟩

/-- **Global form**: on the corner every point has `LexAny`, `AnyFaceChord`, is Rupert, or lies in `Q45ResWM`. -/
theorem q45_resM (F : S0xFac 9 s0x_S24 x) (h4 : 1 ≤ oblX0 x 4) (h5 : 1 ≤ oblX0 x 5) :
    Gen.LexAny F ∨ Gen.AnyFaceChord F ∨ IsRupert (univ.image x) ∨ Q45ResWM F := by
  rcases q45_resG F h4 h5 with h | h | h | ⟨s, t, hs0, ht, hst, hd, h⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · rcases q45_resM_local F h with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inr ⟨s, t, hs0, ht, hst, hd, h⟩))

/-- [OPEN] **The special piece after the general T234 view, Rupert form**: `OpenSpecialL` with `Q45ResWM` in place of
`Q45ResWL` (implied by it: `openSpecialM_of_openSpecialL`). -/
def OpenSpecialM : Prop := ∀ (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x), ¬ H24K.SAT.OB1 x →
  1 ≤ oblX0 x 4 → 1 ≤ oblX0 x 5 →
  oblX0 x 4 * oblX6 x 3 - oblX0 x 3 * oblX6 x 4 < 0 →
  0 < oblX0 x 3 * oblX2 x 5 - oblX0 x 5 * oblX2 x 3 →
  0 < oblX0 x 4 * oblX2 x 5 - oblX0 x 5 * oblX2 x 4 →
  0 < oblX0 x 5 * oblX6 x 4 - oblX0 x 4 * oblX6 x 5 →
  Q45ResWM F → HoleFull x F → IsRupert (univ.image x)

/-- [PROVED] `OpenSpecialL → OpenSpecialM` (`Q45ResWM ⊆ Q45ResWH = Q45ResWI = Q45ResWJ = Q45ResWL`). -/
theorem openSpecialM_of_openSpecialL (h : OpenSpecialL) : OpenSpecialM :=
  fun x F hO h4 h5 b1 b2 b3 b4 hr hF => h x F hO h4 h5 b1 b2 b3 b4
    ((q45ResWL_iff_J F).mpr ((q45ResWJ_iff_I F).mpr ((q45ResWI_iff_H F).mpr (q45ResWH_of_M hr)))) hF

/-- Every `Hole24` point off `OB1` is Rupert, given `OpenSpecialM`. -/
theorem hole24_offOB1_M {F : S0xFac 9 s0x_S24 x} (h : Hole24 x F) (hO : ¬ H24K.SAT.OB1 x)
    (hS : OpenSpecialM) : IsRupert (univ.image x) := by
  obtain ⟨b1, b2, b3⟩ := resid24_frame_signs h.2.2.1 hO
  have b4 := resid24_b1245 h.2.2.1 hO
  obtain ⟨-, h4, h5⟩ := offWall_of_hole24 h hO
  have hF := holeFull_of_hole24 h
  rcases q45_resM F h4 h5 with hL | hA | hR | hr
  · exact (hF.1.2.2.2.1 hL).elim
  · exact (hF.1.2.2.1 hA).elim
  · exact hR
  · exact hS x F hO h4 h5 b1 b2 b3 b4 hr hF

/-- [PROVED] Generic + special (after the general T234 view) assemble to `Open24Rupert`. -/
theorem open24Rupert_of_split_M (h1 : OpenOB1) (h2 : OpenSpecialM) : Open24Rupert := by
  intro x fs hh hH
  by_cases hO : H24K.SAT.OB1 x
  · exact (h1 x _ hO (holeFull_of_hole24 hH)).elim
  · exact hole24_offOB1_M hH hO h2

end T234G

end Minimality.T24.OSpec
