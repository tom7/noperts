module

public import Minimality.Type24OffOB1E26

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21 Minimality.FaceChord Minimality.T24.SAT Minimality.T24.Stmt Minimality.T24.Q45
  Minimality.T24.Reg Minimality.T24.A19

/-!
# Type 24 off `OB1`: the diagonal view `x 1 - x 5` (job OSPEC13, nopert229 notes/OPENSPECIAL-STRATEGY.md)

A **diagonal view** looks along the difference `x a - x b` of two vertices that share no facet.  Every facet through
`a` is then up and every facet through `b` down at level 1 (`pairView_up`, `pairView_dn`: `⟪N t, x a - x b⟫ = -f_t(x
b) > 0`), for any `S0xFac` family.  For type 24 the pair `1, 5` is such a diagonal (facets `012 016 126` through `1`,
`025 0345 235` through `5`), so only `046`, `236`, `346` are left.  `D15ViewOK` (lex view `(x 1 - x 5, -N3, x 0 -
x 4)`) asks `046` up and one of the three observed patterns of `236`, `346` with its rim `RobUniLex`: `(down, down)`
rim `0 2 6 4`, `(up, up)` rim `0 2 3 4`, `(down, up)` rim `0 2 6 3 4` (`lexAny_of_d15View`; mirror
`lexAny_of_d15View_sym` = the view `(x 1 - x 4, -N3', x 0 - x 5)` of `x`).

The **edge view** `(x 0 - x 2, x 6 - x 0, x 4 - x 5)` is the same device along the edge `0 2`: facets through `0` only
are up, through `2` only down (level 1), and the two facets `012`, `025` through the edge are edge-on at level 1 and
down at level 2 (`d02_dn_edge`: `x 6` lies below both).  Only `346` is left: `D02ViewOK` = `346` up and the rim `0 1 6 3
5` `RobUniLex` (`lexAny_of_d02View`, mirror `lexAny_of_d02View_sym`).

Where it is used: on the B2 / C2 corner ties the face-plane view `B2ViewOK` fails when vertex `1` is a strict valley of
the rim `0 1 2 3 4` (`z1 < z0` at level 1, `bB2`).  On the dedicated OSPEC12 samples (seeds 1211 / 1212) the residue of
`Q45ResWS` is exactly six such points (2 B2T, 4 C2T) and the diagonal views close all six, level 1 alone deciding;
fresh 20000-point samples (seeds 1311 / 1312) leave 3 more after the diagonal views, and the edge views close all nine
(SAMPLED, exact; nopert229 tools/genleaves/runs/ospec13).  The conditions are explicit view conditions, not derived.
-/

namespace Minimality.T24.OSpec

section D15
open Minimality.LexCell

/-- **Diagonal view, up side**: a facet through `a` and not through `b` faces the view `x a - x b` (level 1). -/
theorem pairView_up {n m : ℕ} {S : Fin m → Finset (Fin n)} {y : Fin n → ℝ³} (F : S0xFac m S y) (t : Fin m)
    {a b : Fin n} (ha : a ∈ S t) (hb : b ∉ S t) : 0 < ⟪F.N t, y a - y b⟫ := by
  rw [F.inner_sub t a b, F.zero t a ha]; linarith [F.neg t b hb]

/-- **Diagonal view, down side**: a facet through `b` and not through `a` faces away from `x a - x b`. -/
theorem pairView_dn {n m : ℕ} {S : Fin m → Finset (Fin n)} {y : Fin n → ℝ³} (F : S0xFac m S y) (t : Fin m)
    {a b : Fin n} (hb : b ∈ S t) (ha : a ∉ S t) : ⟪F.N t, y a - y b⟫ < 0 := by
  rw [F.inner_sub t a b, F.zero t b hb]; linarith [F.neg t a ha]

variable {x : Fin 7 → ℝ³}

/-- Rim `0 2 6 4` (`236`, `346` down). -/
def rimDA : ZMod 4 → Fin 7 := ![0, 2, 6, 4]
def UDA : Finset (Fin 9) := {0, 1, 4, 5}
def DnDA : Finset (Fin 9) := {2, 3, 6, 7, 8}
/-- Rim `0 2 3 4` (`236`, `346` up). -/
def rimDB : ZMod 4 → Fin 7 := ![0, 2, 3, 4]
def UDB : Finset (Fin 9) := {0, 1, 4, 5, 7, 8}
def DnDB : Finset (Fin 9) := {2, 3, 6}
/-- Rim `0 2 6 3 4` (`236` down, `346` up). -/
def rimDC : ZMod 5 → Fin 7 := ![0, 2, 6, 3, 4]
def UDC : Finset (Fin 9) := {0, 1, 4, 5, 8}
def DnDC : Finset (Fin 9) := {2, 3, 6, 7}

theorem rimDA_cyc : S0xCycUD s0x_S24 rimDA UDA DnDA := by decide
theorem rimDA_inj : Function.Injective rimDA := by decide
theorem rimDB_cyc : S0xCycUD s0x_S24 rimDB UDB DnDB := by decide
theorem rimDB_inj : Function.Injective rimDB := by decide
theorem rimDC_cyc : S0xCycUD s0x_S24 rimDC UDC DnDC := by decide
theorem rimDC_inj : Function.Injective rimDC := by decide

/-- Facet `t` is up in the diagonal view `(x 1 - x 5, -N3, x 0 - x 4)`. -/
def D15Up {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (t : Fin 9) : Prop :=
  LexPos3 ⟪F.N t, x 1 - x 5⟫ ⟪F.N t, -F.N 3⟫ ⟪F.N t, x 0 - x 4⟫
/-- Facet `t` is down in the diagonal view. -/
def D15Dn {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (t : Fin 9) : Prop :=
  LexPos3 (-⟪F.N t, x 1 - x 5⟫) (-⟪F.N t, -F.N 3⟫) (-⟪F.N t, x 0 - x 4⟫)

/-- Lex depth triples of a rim in the diagonal view. -/
noncomputable def d15Z {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) {k : ℕ} (c : ZMod k → Fin 7) :
    ZMod k → ℝ × ℝ × ℝ :=
  fun i => (⟪x (c i), x 1 - x 5⟫, ⟪x (c i), -F.N 3⟫, ⟪x (c i), x 0 - x 4⟫)

/-- **The diagonal view condition**: `046` up, and `236`, `346` down with the rim `0 2 6 4` `RobUniLex`, or both up
with the rim `0 2 3 4`, or `236` down, `346` up with the rim `0 2 6 3 4` (the other six facet signs are automatic). -/
def D15ViewOK {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) : Prop :=
  D15Up F 4 ∧ ((D15Dn F 7 ∧ D15Dn F 8 ∧ RobUniLex (d15Z F rimDA)) ∨
    (D15Up F 7 ∧ D15Up F 8 ∧ RobUniLex (d15Z F rimDB)) ∨ (D15Dn F 7 ∧ D15Up F 8 ∧ RobUniLex (d15Z F rimDC)))

/-- A facet through `1` but not `5` is up (level 1). -/
theorem d15_up_of_mem (F : S0xFac 9 s0x_S24 x) (t : Fin 9) (h1 : (1 : Fin 7) ∈ s0x_S24 t)
    (h5 : (5 : Fin 7) ∉ s0x_S24 t) : D15Up F t :=
  Or.inl (pairView_up F t h1 h5)

/-- A facet through `5` but not `1` is down (level 1). -/
theorem d15_dn_of_mem (F : S0xFac 9 s0x_S24 x) (t : Fin 9) (h5 : (5 : Fin 7) ∈ s0x_S24 t)
    (h1 : (1 : Fin 7) ∉ s0x_S24 t) : D15Dn F t :=
  Or.inl (by linarith [pairView_dn F t h5 h1])

/-- **The diagonal view is a lex cell** (any of the three rims). -/
theorem lexAny_of_d15View (F : S0xFac 9 s0x_S24 x) (h : D15ViewOK F) : Gen.LexAny F := by
  have u0 := d15_up_of_mem F 0 (by decide) (by decide)
  have u1 := d15_up_of_mem F 1 (by decide) (by decide)
  have u5 := d15_up_of_mem F 5 (by decide) (by decide)
  have n2 := d15_dn_of_mem F 2 (by decide) (by decide)
  have n3 := d15_dn_of_mem F 3 (by decide) (by decide)
  have n6 := d15_dn_of_mem F 6 (by decide) (by decide)
  obtain ⟨h4, ⟨h7, h8, hR⟩ | ⟨h7, h8, hR⟩ | ⟨h7, h8, hR⟩⟩ := h
  · refine ⟨4, inferInstance, rimDA, UDA, DnDA, x 1 - x 5, -F.N 3, x 0 - x 4, le_rfl, rimDA_inj,
      rimDA_cyc, ?_, ?_, hR⟩
    · intro t ht
      simp only [UDA, Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl | rfl | rfl
      exacts [u0, u1, h4, u5]
    · intro t ht
      simp only [DnDA, Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl | rfl | rfl | rfl
      exacts [n2, n3, n6, h7, h8]
  · refine ⟨4, inferInstance, rimDB, UDB, DnDB, x 1 - x 5, -F.N 3, x 0 - x 4, le_rfl, rimDB_inj,
      rimDB_cyc, ?_, ?_, hR⟩
    · intro t ht
      simp only [UDB, Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl | rfl | rfl | rfl | rfl
      exacts [u0, u1, h4, u5, h7, h8]
    · intro t ht
      simp only [DnDB, Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl | rfl
      exacts [n2, n3, n6]
  · refine ⟨5, inferInstance, rimDC, UDC, DnDC, x 1 - x 5, -F.N 3, x 0 - x 4, by norm_num, rimDC_inj,
      rimDC_cyc, ?_, ?_, hR⟩
    · intro t ht
      simp only [UDC, Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl | rfl | rfl | rfl
      exacts [u0, u1, h4, u5, h8]
    · intro t ht
      simp only [DnDC, Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl | rfl | rfl
      exacts [n2, n3, n6, h7]

/-- **The mirror diagonal view** (`π = (2 6)(4 5)`): the view `(x 1 - x 4, -N3', x 0 - x 5)` of `x`. -/
theorem lexAny_of_d15View_sym (F : S0xFac 9 s0x_S24 x) (h : D15ViewOK (Sym.sym24 F)) : Gen.LexAny F :=
  Sym.lexAny_sym F (lexAny_of_d15View (Sym.sym24 F) h)

/-! ### The edge view `x 0 - x 2` -/

/-- Rim `0 1 6 3 5` of the edge view (facets `016 0345 046 346` up, `012 025 126 235 236` down). -/
def rimDE : ZMod 5 → Fin 7 := ![0, 1, 6, 3, 5]
def UDE : Finset (Fin 9) := {1, 3, 4, 8}
def DnDE : Finset (Fin 9) := {0, 2, 5, 6, 7}

theorem rimDE_cyc : S0xCycUD s0x_S24 rimDE UDE DnDE := by decide
theorem rimDE_inj : Function.Injective rimDE := by decide

/-- Facet `t` is up in the edge view `(x 0 - x 2, x 6 - x 0, x 4 - x 5)`. -/
def D02Up {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (t : Fin 9) : Prop :=
  LexPos3 ⟪F.N t, x 0 - x 2⟫ ⟪F.N t, x 6 - x 0⟫ ⟪F.N t, x 4 - x 5⟫
/-- Facet `t` is down in the edge view. -/
def D02Dn {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (t : Fin 9) : Prop :=
  LexPos3 (-⟪F.N t, x 0 - x 2⟫) (-⟪F.N t, x 6 - x 0⟫) (-⟪F.N t, x 4 - x 5⟫)

/-- Lex depth triples of a rim in the edge view (no facet normal is involved). -/
noncomputable def d02Z (x : Fin 7 → ℝ³) {k : ℕ} (c : ZMod k → Fin 7) :
    ZMod k → ℝ × ℝ × ℝ :=
  fun i => (⟪x (c i), x 0 - x 2⟫, ⟪x (c i), x 6 - x 0⟫, ⟪x (c i), x 4 - x 5⟫)

/-- **The edge view condition**: `346` up and the rim `0 1 6 3 5` `RobUniLex` (the other eight facet signs are
automatic: `d02_up_of_mem`, `d02_dn_of_mem`, `d02_dn_edge`). -/
def D02ViewOK {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) : Prop :=
  D02Up F 8 ∧ RobUniLex (d02Z x rimDE)

/-- A facet through `0` but not `2` is up (level 1). -/
theorem d02_up_of_mem (F : S0xFac 9 s0x_S24 x) (t : Fin 9) (h0 : (0 : Fin 7) ∈ s0x_S24 t)
    (h2 : (2 : Fin 7) ∉ s0x_S24 t) : D02Up F t :=
  Or.inl (pairView_up F t h0 h2)

/-- A facet through `2` but not `0` is down (level 1). -/
theorem d02_dn_of_mem (F : S0xFac 9 s0x_S24 x) (t : Fin 9) (h2 : (2 : Fin 7) ∈ s0x_S24 t)
    (h0 : (0 : Fin 7) ∉ s0x_S24 t) : D02Dn F t :=
  Or.inl (by linarith [pairView_dn F t h2 h0])

/-- A facet through the edge `0 2` and not `6` is down: edge-on at level 1, `x 6 - x 0` decides at level 2. -/
theorem d02_dn_edge (F : S0xFac 9 s0x_S24 x) (t : Fin 9) (h0 : (0 : Fin 7) ∈ s0x_S24 t)
    (h2 : (2 : Fin 7) ∈ s0x_S24 t) (h6 : (6 : Fin 7) ∉ s0x_S24 t) : D02Dn F t := by
  right
  refine ⟨?_, Or.inl ?_⟩
  · rw [F.inner_sub t 0 2, F.zero t 0 h0, F.zero t 2 h2]; ring
  · linarith [pairView_dn F t h0 h6]

/-- **The edge view is a lex cell.** -/
theorem lexAny_of_d02View (F : S0xFac 9 s0x_S24 x) (h : D02ViewOK F) : Gen.LexAny F := by
  obtain ⟨h8, hR⟩ := h
  refine ⟨5, inferInstance, rimDE, UDE, DnDE, x 0 - x 2, x 6 - x 0, x 4 - x 5, by norm_num, rimDE_inj,
    rimDE_cyc, ?_, ?_, hR⟩
  · intro t ht
    simp only [UDE, Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl
    exacts [d02_up_of_mem F 1 (by decide) (by decide), d02_up_of_mem F 3 (by decide) (by decide),
      d02_up_of_mem F 4 (by decide) (by decide), h8]
  · intro t ht
    simp only [DnDE, Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl
    exacts [d02_dn_edge F 0 (by decide) (by decide) (by decide), d02_dn_edge F 2 (by decide) (by decide) (by decide),
      d02_dn_of_mem F 5 (by decide) (by decide), d02_dn_of_mem F 6 (by decide) (by decide),
      d02_dn_of_mem F 7 (by decide) (by decide)]

/-- **The mirror edge view** (`π = (2 6)(4 5)`): the view `(x 0 - x 6, x 2 - x 0, x 5 - x 4)` of `x`. -/
theorem lexAny_of_d02View_sym (F : S0xFac 9 s0x_S24 x) (h : D02ViewOK (Sym.sym24 F)) : Gen.LexAny F :=
  Sym.lexAny_sym F (lexAny_of_d02View (Sym.sym24 F) h)

/-! ### The residue after the diagonal views -/

/-- `Q45ResSTS` where none of the diagonal and edge views (and mirrors) applies. -/
def Q45ResSTG {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (s t : ℝ) : Prop :=
  Q45ResSTS F s t ∧ ¬ D15ViewOK F ∧ ¬ D15ViewOK (Sym.sym24 F) ∧ ¬ D02ViewOK F ∧ ¬ D02ViewOK (Sym.sym24 F)

/-- The branch-tagged residue after the diagonal views. -/
def Q45ResWG {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) : Prop :=
  ∃ s t : ℝ, 0 < s ∧ 0 < t ∧ 1 < s + t ∧ x 3 - x 0 = s • (x 4 - x 0) + t • (x 5 - x 0) ∧ Q45ResSTG F s t

/-- **The diagonal and edge views cut the residue**: a point of `Q45ResSTS` is `LexAny` or in `Q45ResSTG`. -/
theorem q45_resG_local (F : S0xFac 9 s0x_S24 x) {s t : ℝ} (h : Q45ResSTS F s t) :
    Gen.LexAny F ∨ Q45ResSTG F s t := by
  by_cases hA : D15ViewOK F
  · exact Or.inl (lexAny_of_d15View F hA)
  by_cases hB : D15ViewOK (Sym.sym24 F)
  · exact Or.inl (lexAny_of_d15View_sym F hB)
  by_cases hC : D02ViewOK F
  · exact Or.inl (lexAny_of_d02View F hC)
  by_cases hD : D02ViewOK (Sym.sym24 F)
  · exact Or.inl (lexAny_of_d02View_sym F hD)
  exact Or.inr ⟨h, hA, hB, hC, hD⟩

/-- `Q45ResWG ⊆ Q45ResWS`. -/
theorem q45ResWS_of_G {F : S0xFac 9 s0x_S24 x} (h : Q45ResWG F) : Q45ResWS F := by
  obtain ⟨s, t, hs, ht, hst, hd, h⟩ := h
  exact ⟨s, t, hs, ht, hst, hd, h.1⟩

/-- **Global form**: on the corner every point has `LexAny`, `AnyFaceChord`, is Rupert, or lies in `Q45ResWG`. -/
theorem q45_resG (F : S0xFac 9 s0x_S24 x) (h4 : 1 ≤ oblX0 x 4) (h5 : 1 ≤ oblX0 x 5) :
    Gen.LexAny F ∨ Gen.AnyFaceChord F ∨ IsRupert (univ.image x) ∨ Q45ResWG F := by
  rcases q45_resS F h4 h5 with h | h | h | ⟨s, t, hs0, ht, hst, hd, h⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · rcases q45_resG_local F h with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inr ⟨s, t, hs0, ht, hst, hd, h⟩))

/-- [OPEN] **The special piece after the diagonal views, Rupert form**: `OpenSpecialS` with `Q45ResWG` in place of
`Q45ResWS`. -/
def OpenSpecialG : Prop := ∀ (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x), ¬ H24K.SAT.OB1 x →
  1 ≤ oblX0 x 4 → 1 ≤ oblX0 x 5 →
  oblX0 x 4 * oblX6 x 3 - oblX0 x 3 * oblX6 x 4 < 0 →
  0 < oblX0 x 3 * oblX2 x 5 - oblX0 x 5 * oblX2 x 3 →
  0 < oblX0 x 4 * oblX2 x 5 - oblX0 x 5 * oblX2 x 4 →
  0 < oblX0 x 5 * oblX6 x 4 - oblX0 x 4 * oblX6 x 5 →
  Q45ResWG F → HoleFull x F → IsRupert (univ.image x)

/-- [PROVED] `OpenSpecialS → OpenSpecialG` (`q45ResWS_of_G`). -/
theorem openSpecialG_of_openSpecialS (h : OpenSpecialS) : OpenSpecialG :=
  fun x F hO h4 h5 b1 b2 b3 b4 hr hF => h x F hO h4 h5 b1 b2 b3 b4 (q45ResWS_of_G hr) hF

/-- Every `Hole24` point off `OB1` is Rupert, given `OpenSpecialG`. -/
theorem hole24_offOB1_G {F : S0xFac 9 s0x_S24 x} (h : Hole24 x F) (hO : ¬ H24K.SAT.OB1 x)
    (hS : OpenSpecialG) : IsRupert (univ.image x) := by
  obtain ⟨b1, b2, b3⟩ := resid24_frame_signs h.2.2.1 hO
  have b4 := resid24_b1245 h.2.2.1 hO
  obtain ⟨-, h4, h5⟩ := offWall_of_hole24 h hO
  have hF := holeFull_of_hole24 h
  rcases q45_resG F h4 h5 with hL | hA | hR | hr
  · exact (hF.1.2.2.2.1 hL).elim
  · exact (hF.1.2.2.1 hA).elim
  · exact hR
  · exact hS x F hO h4 h5 b1 b2 b3 b4 hr hF

/-- [PROVED] Generic + special (after the diagonal views) assemble to `Open24Rupert`. -/
theorem open24Rupert_of_split_G (h1 : OpenOB1) (h2 : OpenSpecialG) : Open24Rupert := by
  intro x fs hh hH
  by_cases hO : H24K.SAT.OB1 x
  · exact (h1 x _ hO (holeFull_of_hole24 hH)).elim
  · exact hole24_offOB1_G hH hO h2

end D15

end Minimality.T24.OSpec
