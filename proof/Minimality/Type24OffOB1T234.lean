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

end Minimality.T24.OSpec
