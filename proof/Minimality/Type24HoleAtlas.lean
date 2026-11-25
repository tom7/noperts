module

public import Minimality.Type24HoleConfined
public import Minimality.Type24HoleReduce
public import Minimality.Q4Lex
public import Minimality.GenRev24
public import Minimality.WeakChord
public import Minimality.Type24QuadCell
public import Minimality.FiveRim
public import Minimality.FiveRimApex
public import Minimality.SplitApex
public import Minimality.RimOrder
public import Minimality.RimOrderInst
public import Minimality.Type24M42
public import Minimality.Type24Pieces236
public import Minimality.Type24Piece2
public import Minimality.Type24NoWallDA
public import Minimality.Type24Sectors236
public import Minimality.Type24J54
public import Minimality.Type24C0125
public import Minimality.Type24LexRc
public import Minimality.Type24U32
public import Minimality.Type24HiddenCone

/-!
# Type 24: the hole atlas

No new mathematics.  `Hole24 x F` (Type24HoleReduce.lean) is the single named open proposition of type 24.
This file collects, in one place, (A) the implication lattice between the generic leaves (`Q4Any`, `EdgeAny`,
`LexAny`, `SplitAny`, `FaceChordView`, ...) and (B) the "atlas": for each merged region leaf (a lemma
"criterion on a rim at a view gives `IsRupert`"), the contrapositive on the hole "the criterion fails".

Every atlas fact is obtained by running the leaf's own cell data through a generic leaf (`LexAny`, `AnyFaceChord`,
`SplitAny`), which `Hole24` excludes (`hole24_leaves`).  The hole supplies `CbarIn x` and injectivity of `x`
(`inj_of_fac`); `OB1`, `Delta24 > 0`, `b3 < 1` and the other region hypotheses of the leaves are kept as explicit
hypotheses (they are not consequences of `Hole24`).  See nopert229 notes/TYPE24-HOLE-ATLAS.md.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21 Minimality.T24.SAT Minimality.RimCell Minimality.T24.HC

namespace Minimality.T24.Atlas

variable {x : Fin 7 → ℝ³} {fs : Fin 9 → ℝ³ →ᵃ[ℝ] ℝ} {F : S0xFac 9 s0x_S24 x}

/-! ## Section A: the leaf implication lattice -/

/-- `Q4Any F → LexAny F` (Q4 on a closed rim cone is a lex closed cell). -/
theorem q4Any_lexAny {m n : ℕ} {S : Fin m → Finset (Fin n)} {y : Fin n → ℝ³} (F : S0xFac m S y)
    (hx : Function.Injective y) (h : GenPlus.Q4Any F) : Gen.LexAny F :=
  GenRev.lexAny_of_q4Any F hx h

/-- `EdgeAny F → LexAny F` (a Helly point of the edge-cone forms is a closed-cell view). -/
theorem edgeAny_lexAny {m n : ℕ} {S : Fin m → Finset (Fin n)} {y : Fin n → ℝ³} (F : S0xFac m S y)
    (h : GenPlus.EdgeAny F) : Gen.LexAny F :=
  GenRev.lexAny_of_edgeAny F h

/-- The closed-cell lemma: strict cone point, closed-cell point `u₀` with `RobUni` rim depths give `LexAny`
(tilt `a - u₀`). -/
theorem closedCell_lexAny {m n : ℕ} {S : Fin m → Finset (Fin n)} {y : Fin n → ℝ³} {k : ℕ} [NeZero k]
    (hk : 4 ≤ k) (F : S0xFac m S y) {c : ZMod k → Fin n} (hc : Function.Injective c)
    {U Dn : Finset (Fin m)} (hcyc : S0xCycUD S c U Dn) {a u₀ : ℝ³} (ha : CellAt F U Dn a)
    (hu : CellLe F U Dn u₀) (hR : RobUni (fun i => ⟪y (c i), u₀⟫)) : Gen.LexAny F :=
  GenRev.lexAny_of_closedCell hk F hc hcyc ha hu hR

/-- `SplitAny F → SplitLexAny F` (a split cell is a lex split cell). -/
theorem splitAny_splitLexAny {m n : ℕ} {S : Fin m → Finset (Fin n)} {y : Fin n → ℝ³} (F : S0xFac m S y)
    (h : Gen.SplitAny F) : GenRev.SplitLexAny F :=
  GenRev.splitLexAny_of_splitAny F h

/-- A split cell on a 4-rim is a lex cell. -/
theorem splitAny_four_lexAny {m n : ℕ} {S : Fin m → Finset (Fin n)} {y : Fin n → ℝ³} (F : S0xFac m S y)
    (hx : Function.Injective y) {c : ZMod 4 → Fin n} {pat : Fin m → Bool} {u v : ℝ³}
    (hc : Function.Injective c) (hcyc : S0xCycOK S c pat) (hfac : S0xFacOK F pat u v)
    (a cc : ZMod 4) (σ : ℝ) (hca : cc ≠ a) (hca1 : cc ≠ a + 1)
    (hrows : Split.SplitRows (fun i => y (c i)) u a cc σ) : Gen.LexAny F :=
  GenRev.lexAny_of_splitAny_four F hx hc hcyc hfac a cc σ hca hca1 hrows

/-- A face-chord view on a non-quad facet (`t ≠ 3`) is a weak chord arc. -/
theorem faceChordView_weakChordArc (F : S0xFac 9 s0x_S24 x) {t : Fin 9} (ht : t ≠ 3)
    (h : FaceChord.FaceChordView F t) : GenPlus.WeakChordArc F t :=
  GenRev.weakChordArc_of_faceChordView F ht h

/-- A weak chord arc on a non-quad facet gives `LexAny` or `SplitAny24`. -/
theorem weakChordArc_lexAny_or_splitAny (F : S0xFac 9 s0x_S24 x) {t : Fin 9} (ht : t ≠ 3)
    (h : GenPlus.WeakChordArc F t) : Gen.LexAny F ∨ T24.RCell.SplitAny24 F :=
  GenPlus.lexAny_or_splitAny24_of_weakChordArc F ht h

/-- Off `LexAny` and `SplitAny24`, `AnyFaceChord` is a face-chord view on the quad facet 3 only. -/
theorem anyFaceChord_iff_quad (F : S0xFac 9 s0x_S24 x) (hL : ¬ Gen.LexAny F)
    (hS : ¬ T24.RCell.SplitAny24 F) : Gen.AnyFaceChord F ↔ FaceChord.FaceChordView F 3 :=
  GenRev.anyFaceChord_iff_quad F hL hS

/-- `FacetCellF F` (cell with one facet up and its edge-neighbours down) iff `FacetCell24 fs`. -/
theorem facetCellF_iff (h : ∀ t i, (i ∈ s0x_S24 t → fs t (x i) = 0) ∧ (i ∉ s0x_S24 t → fs t (x i) < 0)) :
    T24.Z0.FacetCellF (T24.mkFac24 fs h) ↔ T24.Z0.FacetCell24 fs :=
  T24.Z0.facetCellF_iff_facetCell24 fs h

/-- A strict facet cell on the planar quad facet 0345 gives `LexAny`. -/
theorem quadCell_lexAny (F : S0xFac 9 s0x_S24 x) {a : ℝ³} (ha : CellAt F {3} (T24.Z0.nb 3) a) :
    T24.RCell.LexAny F :=
  T24.lexAny_of_quadCell F ha

/-- Lemma A5: a strict row at the apex edge of a 5-rim gives `LexAny`. -/
theorem a5_lexAny {m n : ℕ} {S : Fin m → Finset (Fin n)} {y : Fin n → ℝ³} (F : S0xFac m S y)
    {c : ZMod 5 → Fin n} (hc : Function.Injective c) {U Dn : Finset (Fin m)} (hcyc : S0xCycUD S c U Dn)
    {a u₀ : ℝ³} (ha : CellAt F U Dn a) (hu : CellLe F U Dn u₀) {ρ : ℝ}
    (hcvx : StrictConvex5 (fun i => y (c i)) u₀ ρ) {a₀ ε : ZMod 5}
    (hpat : A5.ApexPat (fun i => y (c i)) u₀ a₀ ε) (hlt : ⟪y (c a₀), u₀⟫ < ⟪y (c (a₀ + ε)), u₀⟫) :
    Gen.LexAny F :=
  A5.lexAny_of_a5_row F hc hcyc ha hu hcvx hpat hlt

/-- SplitRows from a screen apex: strictly unimodal height along the chain, plus signed depths on the two arcs. -/
alias splitRows_apex := Split.splitRows_of_unimodal_separated

/-- RobUni from "no alternating quadruple of weak extrema" (any order type; `RimOrder`). -/
alias robUni_noAlt := GenRev.robUni_of_noAlt

/-- Order-generic form of the same. -/
alias robUniO_noAlt := GenRev.robUniO_of_noAlt

/-- A strictly unimodal cycle is `RobUni`. -/
alias robUni_strictUnimodal := GenRev.robUni_of_strictUnimodal

/-- `RobUni` of a 4-cycle from one negative and one positive diagonal form. -/
alias robUni_four_mixed := robUni_four_of_mixed

/-! ## The hole itself, from several angles -/

/-- `Hole24` unfolded (definitional). -/
theorem hole24_unfold :
    Hole24 x F ↔ (HoleLeaf x F ∧ Hole24Lemmas x ∧ Resid24 x ∧ Region24 x F) := Iff.rfl

/-- Re-export: the generic negated leaves carried by `HoleLeaf` (`holeLeaf_leaves`). -/
theorem holeLeaf_leaves' (h : HoleLeaf x F) :
    CbarIn x ∧ ¬ Gen.AnyFaceChord F ∧ ¬ Gen.LexAny F ∧ ¬ T24.RCell.SplitAny24 F ∧
      ¬ BoxApplies (univ.image x) :=
  holeLeaf_leaves h

/-- Re-export: the generic negated leaves carried by `Hole24`. -/
theorem hole24_leaves' (h : Hole24 x F) :
    CbarIn x ∧ ¬ Gen.AnyFaceChord F ∧ ¬ Gen.LexAny F ∧ ¬ T24.RCell.SplitAny24 F ∧
      ¬ BoxApplies (univ.image x) :=
  hole24_leaves h

/-- Re-export: confinement by the quad-normal region and the 25 meridian / tie-view lemmas. -/
alias holeLeaf_confined' := holeLeaf_confined

/-- Re-export: confinement on `Hole24`. -/
alias hole24_confined' := hole24_confined

/-- Re-export: no weak chord arc on a non-quad facet. -/
theorem holeLeaf_noWeakChord' (h : HoleLeaf x F) {t : Fin 9} (ht : t ≠ 3) :
    ¬ GenPlus.WeakChordArc F t := holeLeaf_noWeakChord h ht

/-- Re-export: no weak chord arc on a non-quad facet (`Hole24`). -/
theorem hole24_noWeakChord' (h : Hole24 x F) {t : Fin 9} (ht : t ≠ 3) :
    ¬ GenPlus.WeakChordArc F t := hole24_noWeakChord h ht

/-- Hole facts that every atlas fact uses: `C̄`, injectivity of `x`, no lex cell. -/
theorem holeLeaf_inputs (h : HoleLeaf x F) : CbarIn x ∧ Function.Injective x ∧ ¬ Gen.LexAny F :=
  ⟨h.1, Minimality.H24.SAT.inj_of_fac F, holeLeaf_not_lexAny h⟩

/-- On `HoleLeaf` there is no Edge-Plane view (`Gen.EdgePlaneAny`, first-order free by the Edge-Plane Lemma).
Census (FREECERT 11-25): every free view found at hole-candidate points was an Edge-Plane view.  CONJECTURE (not
proved): `Gen.SplitAny F → Gen.EdgePlaneAny x` (1624 of 1624 `SplitRows` views tested on a C-covered sample were
also Edge-Plane views), so `¬ EdgePlaneAny` would subsume `¬ SplitAny`. -/
theorem holeLeaf_not_edgePlaneAny (h : HoleLeaf x F) : ¬ Gen.EdgePlaneAny x := h.2.2.2.2.2.2

/-- `Hole24` form of `holeLeaf_not_edgePlaneAny`. -/
theorem hole24_not_edgePlaneAny (h : Hole24 x F) : ¬ Gen.EdgePlaneAny x := holeLeaf_not_edgePlaneAny h.1

theorem hole_inputs (h : Hole24 x F) : CbarIn x ∧ Function.Injective x ∧ ¬ Gen.LexAny F :=
  holeLeaf_inputs h.1

/-- On `HoleLeaf` no face-chord view exists on any facet (including the quad facet 0345). -/
theorem holeLeaf_noFaceChordView (h : HoleLeaf x F) (t : Fin 9) : ¬ FaceChord.FaceChordView F t :=
  fun hv => h.2.2.1 ⟨t, hv⟩

/-- On `Hole24` no face-chord view exists on any facet. -/
theorem hole24_noFaceChordView (h : Hole24 x F) (t : Fin 9) : ¬ FaceChord.FaceChordView F t :=
  holeLeaf_noFaceChordView h.1 t

/-! ## Section B: the atlas, circle 236 -/

/-- The two-end Q4 criterion on a 4-rim `c` at the end views `u`, `v`: some diagonal form negative at an end and
some positive at an end. -/
def TwoEndCrit (x : Fin 7 → ℝ³) (c : ZMod 4 → Fin 7) (u v : ℝ³) : Prop :=
  ((∃ p ∈ diagPairs, ⟪x (c p.1) - x (c p.2), u⟫ < 0) ∨ ∃ p ∈ diagPairs, ⟪x (c p.1) - x (c p.2), v⟫ < 0) ∧
  ((∃ p ∈ diagPairs, 0 < ⟪x (c p.1) - x (c p.2), u⟫) ∨ ∃ p ∈ diagPairs, 0 < ⟪x (c p.1) - x (c p.2), v⟫)

/-- Generic: a 4-rim closed cell with two end views and the two-end criterion gives `LexAny`. -/
theorem twoEnd_lexAny (F : S0xFac 9 s0x_S24 x) {c : ZMod 4 → Fin 7} (hc : Function.Injective c)
    {U Dn : Finset (Fin 9)} (hcyc : S0xCycUD s0x_S24 c U Dn) {a u v : ℝ³} (ha : CellAt F U Dn a)
    (hu : CellLe F U Dn u) (hv : CellLe F U Dn v) (hcrit : TwoEndCrit x c u v) : Gen.LexAny F := by
  have hx := Minimality.H24.SAT.inj_of_fac F
  obtain ⟨hn, hp⟩ := hcrit
  rcases hn with hn | hn <;> rcases hp with hp | hp
  · exact GenRev.lexAny_of_q4Any F hx ⟨c, U, Dn, a, u, u, hc, hcyc, ha, hu, hu, hn, hp⟩
  · exact GenRev.lexAny_of_q4Any F hx ⟨c, U, Dn, a, u, v, hc, hcyc, ha, hu, hv, hn, hp⟩
  · exact GenRev.lexAny_of_q4Any F hx ⟨c, U, Dn, a, v, u, hc, hcyc, ha, hv, hu, hn, hp⟩
  · exact GenRev.lexAny_of_q4Any F hx ⟨c, U, Dn, a, v, v, hc, hcyc, ha, hv, hv, hn, hp⟩

/-- **Circle 236, piece I** (rim `0 5 2 6`; contrapositive of `EG.isRupert_pieceI`).  On the hole, with
`⟨N_4, x_3 - x_2⟩ > 0`, the two-end criterion at `endIL`, `viewM74` fails: all four diagonal forms are `≥ 0`
at both ends, or all `≤ 0` at both ends (`D_A` or `D_B`, in the sense of "at the two ends together"). -/
theorem holeLeaf_pieceI (h : HoleLeaf x F) (h4 : 0 < ⟪F.N 4, x 3 - x 2⟫) :
    ¬ TwoEndCrit x T24.EG.cI (T24.EG.endIL x) (T24.EG.viewM74 x) := fun hcrit => by
  obtain ⟨hL, hR, a, ha⟩ := T24.EG.regionI F (holeLeaf_leaves h).1 h4
  exact holeLeaf_not_lexAny h (twoEnd_lexAny F T24.EG.injI T24.EG.cycI ha hL hR hcrit)

/-- `hole24_pieceI` from `holeLeaf_pieceI`. -/
theorem hole24_pieceI (h : Hole24 x F) (h4 : 0 < ⟪F.N 4, x 3 - x 2⟫) :
    ¬ TwoEndCrit x T24.EG.cI (T24.EG.endIL x) (T24.EG.viewM74 x) :=
  holeLeaf_pieceI h.1 h4

/-- **Circle 236, piece III** (rim `0 2 6 4`; contrapositive of `EG.isRupert_pieceIII`). -/
theorem holeLeaf_pieceIII (h : HoleLeaf x F) (h2 : 0 < ⟪F.N 2, x 3 - x 6⟫) :
    ¬ TwoEndCrit x T24.EG.cIII (T24.EG.viewM27 x) (T24.EG.endIIIR x) := fun hcrit => by
  obtain ⟨hL, hR, a, ha⟩ := T24.EG.regionIII F (holeLeaf_leaves h).1 h2
  exact holeLeaf_not_lexAny h (twoEnd_lexAny F T24.EG.injIII T24.EG.cycIII ha hL hR hcrit)

/-- `hole24_pieceIII` from `holeLeaf_pieceIII`. -/
theorem hole24_pieceIII (h : Hole24 x F) (h2 : 0 < ⟪F.N 2, x 3 - x 6⟫) :
    ¬ TwoEndCrit x T24.EG.cIII (T24.EG.viewM27 x) (T24.EG.endIIIR x) :=
  holeLeaf_pieceIII h.1 h2

/-- **Circle 236, piece II** (5-rim `0 4 6 2 5`; contrapositive of `ES.isRupert_pieceII`, Hydrogen Task ES): in the
hole, with `Delta24 > 0` and the break `brk24 ≠ 0`, the A5 row fails at both ends of the piece. -/
theorem holeLeaf_pieceII (h : HoleLeaf x F) (hD : 0 < Delta24 x) (hb : T24.ES.brk24 x ≠ 0) :
    ¬ (⟪x (T24.ES.apexV x), T24.ES.endIIL x⟫ < ⟪x 0, T24.ES.endIIL x⟫ ∨
      ⟪x (T24.ES.apexV x), T24.ES.endIIR x⟫ < ⟪x 0, T24.ES.endIIR x⟫) := fun hrow =>
  holeLeaf_not_lexAny h (T24.ES.lexAny_pieceII F h.1 hD hb hrow)

/-- `hole24_pieceII` from `holeLeaf_pieceII`. -/
theorem hole24_pieceII (h : Hole24 x F) (hD : 0 < Delta24 x) (hb : T24.ES.brk24 x ≠ 0) :
    ¬ (⟪x (T24.ES.apexV x), T24.ES.endIIL x⟫ < ⟪x 0, T24.ES.endIIL x⟫ ∨
      ⟪x (T24.ES.apexV x), T24.ES.endIIR x⟫ < ⟪x 0, T24.ES.endIIR x⟫) :=
  holeLeaf_pieceII h.1 hD hb

/-- **Piece I at the wall end** (contrapositive of `EP.isRupert_pieceI_wall`).  Under `OB1` and `b_3 ≤ 1`, on the
hole no diagonal form of `0 5 2 6` is positive at `endIL` or at `viewM74`: `D_B` holds at both ends.  (`OB1` and
`b_3 ≤ 1` are not consequences of `Hole24`; they are explicit hypotheses.) -/
theorem holeLeaf_pieceI_wall (h : HoleLeaf x F) (hob : H24K.SAT.OB1 x) (hb : oblX2 x 3 ≤ 1) :
    ¬ ((∃ p ∈ diagPairs, 0 < ⟪x (T24.EG.cI p.1) - x (T24.EG.cI p.2), T24.EG.endIL x⟫) ∨
      ∃ p ∈ diagPairs, 0 < ⟪x (T24.EG.cI p.1) - x (T24.EG.cI p.2), T24.EG.viewM74 x⟫) := fun hp =>
  holeLeaf_not_lexAny h (by
    have hC := (holeLeaf_leaves h).1
    have hn : ∃ p ∈ diagPairs, ⟪x (T24.EG.cI p.1) - x (T24.EG.cI p.2), T24.EG.endIL x⟫ < 0 := by
      have hnot := T24.EP.noWallDA_I F hC hob
      push Not at hnot
      simpa [T24.EG.endIL, hb] using hnot
    obtain ⟨hL, hR, a, ha⟩ := T24.EG.regionI F hC (T24.EG.h4_of_b3_le F hC hb)
    exact twoEnd_lexAny F T24.EG.injI T24.EG.cycI ha hL hR ⟨Or.inl hn, hp⟩)

/-- `hole24_pieceI_wall` from `holeLeaf_pieceI_wall`. -/
theorem hole24_pieceI_wall (h : Hole24 x F) (hob : H24K.SAT.OB1 x) (hb : oblX2 x 3 ≤ 1) :
    ¬ ((∃ p ∈ diagPairs, 0 < ⟪x (T24.EG.cI p.1) - x (T24.EG.cI p.2), T24.EG.endIL x⟫) ∨
      ∃ p ∈ diagPairs, 0 < ⟪x (T24.EG.cI p.1) - x (T24.EG.cI p.2), T24.EG.viewM74 x⟫) :=
  holeLeaf_pieceI_wall h.1 hob hb

/-- **Piece III at the wall end** (contrapositive of `EP.isRupert_pieceIII_wall`; hypotheses `OB1`, `c_3 ≤ 1`). -/
theorem holeLeaf_pieceIII_wall (h : HoleLeaf x F) (hob : H24K.SAT.OB1 x) (hc : oblX6 x 3 ≤ 1) :
    ¬ ((∃ p ∈ diagPairs, 0 < ⟪x (T24.EG.cIII p.1) - x (T24.EG.cIII p.2), T24.EG.viewM27 x⟫) ∨
      ∃ p ∈ diagPairs, 0 < ⟪x (T24.EG.cIII p.1) - x (T24.EG.cIII p.2), T24.EG.endIIIR x⟫) := fun hp =>
  holeLeaf_not_lexAny h (by
    have hC := (holeLeaf_leaves h).1
    have hn : ∃ p ∈ diagPairs, ⟪x (T24.EG.cIII p.1) - x (T24.EG.cIII p.2), T24.EG.endIIIR x⟫ < 0 := by
      have hnot := T24.EP.noWallDA_III F hC hob
      push Not at hnot
      simpa [T24.EG.endIIIR, hc] using hnot
    obtain ⟨hL, hR, a, ha⟩ := T24.EG.regionIII F hC (T24.EG.h2_of_c3_le F hC hc)
    exact twoEnd_lexAny F T24.EG.injIII T24.EG.cycIII ha hL hR ⟨Or.inr hn, hp⟩)

/-- `hole24_pieceIII_wall` from `holeLeaf_pieceIII_wall`. -/
theorem hole24_pieceIII_wall (h : Hole24 x F) (hob : H24K.SAT.OB1 x) (hc : oblX6 x 3 ≤ 1) :
    ¬ ((∃ p ∈ diagPairs, 0 < ⟪x (T24.EG.cIII p.1) - x (T24.EG.cIII p.2), T24.EG.viewM27 x⟫) ∨
      ∃ p ∈ diagPairs, 0 < ⟪x (T24.EG.cIII p.1) - x (T24.EG.cIII p.2), T24.EG.endIIIR x⟫) :=
  holeLeaf_pieceIII_wall h.1 hob hc

/-- **Chord-23 sector** (rim `0 2 3 4`, `c_3 > 1`, `sLA < sRA`; contrapositive of `EI.isRupert_pieceA`). -/
theorem holeLeaf_pieceA (h : HoleLeaf x F) (hc : 1 < oblX6 x 3) (hlt : T24.EI.sLA F < T24.EI.sRA F) :
    ¬ TwoEndCrit x T24.EI.cA (T24.EI.pivotView x (T24.EI.sLA F)) (T24.EI.pivotView x (T24.EI.sRA F)) :=
  fun hcrit => by
  obtain ⟨hL, hR, a, ha⟩ := T24.EI.regionA F hc hlt
  exact holeLeaf_not_lexAny h (twoEnd_lexAny F T24.EI.injA T24.EI.cycA ha hL hR hcrit)

/-- `hole24_pieceA` from `holeLeaf_pieceA`. -/
theorem hole24_pieceA (h : Hole24 x F) (hc : 1 < oblX6 x 3) (hlt : T24.EI.sLA F < T24.EI.sRA F) :
    ¬ TwoEndCrit x T24.EI.cA (T24.EI.pivotView x (T24.EI.sLA F)) (T24.EI.pivotView x (T24.EI.sRA F)) :=
  holeLeaf_pieceA h.1 hc hlt

/-- **Chord-36 sector** (rim `0 5 3 6`, `b_3 > 1`, `sLB < sRB`; contrapositive of `EI.isRupert_pieceB`). -/
theorem holeLeaf_pieceB (h : HoleLeaf x F) (hb : 1 < oblX2 x 3) (hlt : T24.EI.sLB F < T24.EI.sRB F) :
    ¬ TwoEndCrit x T24.EI.cB (T24.EI.pivotView x (T24.EI.sLB F)) (T24.EI.pivotView x (T24.EI.sRB F)) :=
  fun hcrit => by
  obtain ⟨hL, hR, a, ha⟩ := T24.EI.regionB F hb hlt
  exact holeLeaf_not_lexAny h (twoEnd_lexAny F T24.EI.injB T24.EI.cycB ha hL hR hcrit)

/-- `hole24_pieceB` from `holeLeaf_pieceB`. -/
theorem hole24_pieceB (h : Hole24 x F) (hb : 1 < oblX2 x 3) (hlt : T24.EI.sLB F < T24.EI.sRB F) :
    ¬ TwoEndCrit x T24.EI.cB (T24.EI.pivotView x (T24.EI.sLB F)) (T24.EI.pivotView x (T24.EI.sRB F)) :=
  holeLeaf_pieceB h.1 hb hlt

/-! ### J_54 (cone of facet 0345) -/

/-- **J_54, criterion form** (contrapositive of `EJ.isRupert_J54` / `faceChordView_J54`).  The nondegeneracy
hypotheses `hne`, `hf3`, `hoff`, `hinj_J` of the leaf are hypotheses here (the hole does not give them). -/
theorem holeLeaf_J54 (h : HoleLeaf x F) (hne : 0 < T24.EJ.caL x ∨ 0 < T24.EJ.caR x)
    (hf3 : F.f 3 (x 2) ≠ F.f 3 (x 6))
    (hoff : ⟪F.N 3, cross (x 4 - x 5) (x (if F.f 3 (x 2) < F.f 3 (x 6) then 2 else 6) - x 5)⟫ ≠ 0 ∨
      ⟪x (if F.f 3 (x 2) < F.f 3 (x 6) then 2 else 6) - x 5, x 4 - x 5⟫ < 0 ∨
      ⟪x (if F.f 3 (x 2) < F.f 3 (x 6) then 2 else 6) - x 4, x 5 - x 4⟫ < 0)
    (hinj_J : ∀ i j : ZMod 4, i ≠ j →
      ⟪x (T24.EJ.cJ i) - x (T24.EJ.cJ j), T24.EJ.WL x⟫ ≠ 0 ∨ ⟪x (T24.EJ.cJ i) - x (T24.EJ.cJ j), T24.EJ.WR x⟫ ≠ 0) :
    ¬ TwoEndCrit x T24.EJ.cJ (T24.EJ.WL x) (T24.EJ.WR x) := fun ⟨hn, hp⟩ =>
  holeLeaf_noFaceChordView h 3 (T24.EJ.faceChordView_J54 F hne hn hp hf3 hoff hinj_J)

/-- `hole24_J54` from `holeLeaf_J54`. -/
theorem hole24_J54 (h : Hole24 x F) (hne : 0 < T24.EJ.caL x ∨ 0 < T24.EJ.caR x)
    (hf3 : F.f 3 (x 2) ≠ F.f 3 (x 6))
    (hoff : ⟪F.N 3, cross (x 4 - x 5) (x (if F.f 3 (x 2) < F.f 3 (x 6) then 2 else 6) - x 5)⟫ ≠ 0 ∨
      ⟪x (if F.f 3 (x 2) < F.f 3 (x 6) then 2 else 6) - x 5, x 4 - x 5⟫ < 0 ∨
      ⟪x (if F.f 3 (x 2) < F.f 3 (x 6) then 2 else 6) - x 4, x 5 - x 4⟫ < 0)
    (hinj_J : ∀ i j : ZMod 4, i ≠ j →
      ⟪x (T24.EJ.cJ i) - x (T24.EJ.cJ j), T24.EJ.WL x⟫ ≠ 0 ∨ ⟪x (T24.EJ.cJ i) - x (T24.EJ.cJ j), T24.EJ.WR x⟫ ≠ 0) :
    ¬ TwoEndCrit x T24.EJ.cJ (T24.EJ.WL x) (T24.EJ.WR x) :=
  holeLeaf_J54 h.1 hne hf3 hoff hinj_J

/-- **J_54, RobUni form** (contrapositive of `EJ.isRupert_J54_rob5`): at every `W_s = (1-s) W_L + s W_R` neither
5-rim `cM`, `cP` is robustly unimodal. -/
theorem holeLeaf_J54_rob5 (h : HoleLeaf x F) (hne : 0 < T24.EJ.caL x ∨ 0 < T24.EJ.caR x) {s : ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    ¬ RobUni (fun i : ZMod 5 => ⟪x (T24.EJ.cM i), (1 - s) • T24.EJ.WL x + s • T24.EJ.WR x⟫) ∧
    ¬ RobUni (fun i : ZMod 5 => ⟪x (T24.EJ.cP i), (1 - s) • T24.EJ.WL x + s • T24.EJ.WR x⟫) := by
  obtain ⟨hL, hR, ⟨aP, haP⟩, ⟨aM, haM⟩⟩ := T24.EJ.regionJ F hne
  have hc := T24.EJ.jcore_comb F hL hR hs0 hs1
  exact ⟨fun hr => holeLeaf_not_lexAny h (GenRev.lexAny_of_closedCell (by norm_num) F T24.EJ.injM T24.EJ.cycM haM
      (T24.EJ.cellLe_M_of_core F hc) hr),
    fun hr => holeLeaf_not_lexAny h (GenRev.lexAny_of_closedCell (by norm_num) F T24.EJ.injP T24.EJ.cycP haP
      (T24.EJ.cellLe_P_of_core F hc) hr)⟩

/-- `hole24_J54_rob5` from `holeLeaf_J54_rob5`. -/
theorem hole24_J54_rob5 (h : Hole24 x F) (hne : 0 < T24.EJ.caL x ∨ 0 < T24.EJ.caR x) {s : ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    ¬ RobUni (fun i : ZMod 5 => ⟪x (T24.EJ.cM i), (1 - s) • T24.EJ.WL x + s • T24.EJ.WR x⟫) ∧
    ¬ RobUni (fun i : ZMod 5 => ⟪x (T24.EJ.cP i), (1 - s) • T24.EJ.WL x + s • T24.EJ.WR x⟫) :=
  holeLeaf_J54_rob5 h.1 hne hs0 hs1

/-! ### The ray c0125 -/

/-- **Ray `c_*` of the cone `N_c`, rim `0 1 2 5`** (contrapositive of `EL.isRupert_c0125`).  Under its sign
hypotheses (`ω_5 ≥ 0`, three facet inner products with `x_6 - x_1` positive) the rim is crowned at `viewC`:
`D_A` (all diagonal forms `≥ 0`) or `D_B` (all `≤ 0`). -/
theorem holeLeaf_c0125 (h : HoleLeaf x F) (h5 : 0 ≤ omega5 x)
    (h3 : 0 < ⟪F.N 3, x 6 - x 1⟫) (h6 : 0 < ⟪F.N 6, x 6 - x 1⟫) (h8 : 0 < ⟪F.N 8, x 6 - x 1⟫) :
    (∀ p ∈ diagPairs, 0 ≤ ⟪x (T24.EL.cC p.1) - x (T24.EL.cC p.2), T24.EL.viewC F⟫) ∨
    (∀ p ∈ diagPairs, ⟪x (T24.EL.cC p.1) - x (T24.EL.cC p.2), T24.EL.viewC F⟫ ≤ 0) := by
  by_contra hcon
  push Not at hcon
  obtain ⟨⟨p, hp, hpn⟩, ⟨q, hq, hqp⟩⟩ := hcon
  have ha := T24.EL.regionC F h5 h3 h6 h8
  have hR : RobUni (fun i => ⟪x (T24.EL.cC i), T24.EL.viewC F⟫) := robUni_four_of_mixed
    ⟨p, hp, by rw [← inner_sub_left]; exact hpn⟩ ⟨q, hq, by rw [← inner_sub_left]; exact hqp⟩
  exact holeLeaf_not_lexAny h (GenRev.lexAny_of_closedCell le_rfl F T24.EL.injC T24.EL.cycC ha ha.cellLe hR)

/-- `hole24_c0125` from `holeLeaf_c0125`. -/
theorem hole24_c0125 (h : Hole24 x F) (h5 : 0 ≤ omega5 x)
    (h3 : 0 < ⟪F.N 3, x 6 - x 1⟫) (h6 : 0 < ⟪F.N 6, x 6 - x 1⟫) (h8 : 0 < ⟪F.N 8, x 6 - x 1⟫) :
    (∀ p ∈ diagPairs, 0 ≤ ⟪x (T24.EL.cC p.1) - x (T24.EL.cC p.2), T24.EL.viewC F⟫) ∨
    (∀ p ∈ diagPairs, ⟪x (T24.EL.cC p.1) - x (T24.EL.cC p.2), T24.EL.viewC F⟫ ≤ 0) :=
  holeLeaf_c0125 h.1 h5 h3 h6 h8

/-! ### The meridian view M_42 -/

/-- **`M_42`** (contrapositive of `EO.isRupert_m42`; `Δ24 > 0` is a hypothesis, the facet-cell exclusion is
part of `HoleLeaf`).  On the hole, in each sub-region of the sign pattern of
`(N_6 . M, N_8 . M)` the bordering rim (`M3`: `0 5 3 6`, `M2`: `0 2 3 4`, `M1`: `0 2 3 6`) fails the Q4 criterion at
`M_42`: all diagonal forms `≥ 0` or all `≤ 0` there. -/
theorem holeLeaf_m42 (h : HoleLeaf x F) (hD : 0 < Delta24 x) :
    (⟪F.N 6, T24.EO.viewM42 x⟫ ≤ 0 → 0 ≤ ⟪F.N 8, T24.EO.viewM42 x⟫ →
      ¬ T24.EO.Crit x T24.EO.cM3 (T24.EO.viewM42 x)) ∧
    (0 ≤ ⟪F.N 6, T24.EO.viewM42 x⟫ → ⟪F.N 8, T24.EO.viewM42 x⟫ ≤ 0 →
      ¬ T24.EO.Crit x T24.EO.cM2 (T24.EO.viewM42 x)) ∧
    (0 < ⟪F.N 6, T24.EO.viewM42 x⟫ → 0 < ⟪F.N 8, T24.EO.viewM42 x⟫ →
      ¬ T24.EO.Crit x T24.EO.cM1 (T24.EO.viewM42 x)) := by
  have hC := (holeLeaf_leaves h).1
  have hnL := holeLeaf_not_lexAny h
  refine ⟨fun h6 h8 hc => ?_, fun h6 h8 hc => ?_, fun h6 h8 hc => ?_⟩
  · obtain ⟨a, ha⟩ := T24.EO.m42_cellAt_M3 F hC hD h6 h8
    have hL := T24.EO.m42_cellLe_M3 F hC hD h6 h8
    exact hnL (GenRev.lexAny_of_q4Any F (Minimality.H24.SAT.inj_of_fac F)
      ⟨_, _, _, a, _, _, T24.EO.injM3, T24.EO.cycM3, ha, hL, hL, hc.1, hc.2⟩)
  · obtain ⟨a, ha⟩ := T24.EO.m42_cellAt_M2 F hC hD h6 h8
    have hL := T24.EO.m42_cellLe_M2 F hC hD h6 h8
    exact hnL (GenRev.lexAny_of_q4Any F (Minimality.H24.SAT.inj_of_fac F)
      ⟨_, _, _, a, _, _, T24.EO.injM2, T24.EO.cycM2, ha, hL, hL, hc.1, hc.2⟩)
  · obtain ⟨a, ha⟩ := T24.EO.m42_cellAt_M1 F hC hD h6 h8
    have hL := T24.EO.m42_cellLe_M1 F hC hD h6.le h8.le
    exact hnL (GenRev.lexAny_of_q4Any F (Minimality.H24.SAT.inj_of_fac F)
      ⟨_, _, _, a, _, _, T24.EO.injM1, T24.EO.cycM1, ha, hL, hL, hc.1, hc.2⟩)

/-- `hole24_m42` from `holeLeaf_m42`. -/
theorem hole24_m42 (h : Hole24 x F) (hD : 0 < Delta24 x) :
    (⟪F.N 6, T24.EO.viewM42 x⟫ ≤ 0 → 0 ≤ ⟪F.N 8, T24.EO.viewM42 x⟫ →
      ¬ T24.EO.Crit x T24.EO.cM3 (T24.EO.viewM42 x)) ∧
    (0 ≤ ⟪F.N 6, T24.EO.viewM42 x⟫ → ⟪F.N 8, T24.EO.viewM42 x⟫ ≤ 0 →
      ¬ T24.EO.Crit x T24.EO.cM2 (T24.EO.viewM42 x)) ∧
    (0 < ⟪F.N 6, T24.EO.viewM42 x⟫ → 0 < ⟪F.N 8, T24.EO.viewM42 x⟫ →
      ¬ T24.EO.Crit x T24.EO.cM1 (T24.EO.viewM42 x)) :=
  holeLeaf_m42 h.1 hD

/-! ### The edge view u_32 -/

/-- **`u_32 = x_3 - x_2`** (`b_3 < 1`; contrapositive of `EQ.isRupert_u32_any`): on the hole none of the four
leaves applies: neither 5-rim `0.1.6.3.5`, `0.1.6.2.5` is `RobUni` at `u_32` and neither carries split rows. -/
theorem holeLeaf_u32 (h : HoleLeaf x F) (hb3 : oblX2 x 3 < 1) :
    ¬ RobUni (fun i : ZMod 5 => ⟪x (T24.EQ.cMM i), x 3 - x 2⟫) ∧
    ¬ RobUni (fun i : ZMod 5 => ⟪x (T24.EQ.cPP i), x 3 - x 2⟫) ∧
    ¬ T24.EQ.SplitAny5 x T24.EQ.cMM ∧ ¬ T24.EQ.SplitAny5 x T24.EQ.cPP :=
  have hC := (holeLeaf_leaves h).1
  ⟨fun hR => holeLeaf_not_lexAny h (by
      obtain ⟨a, ha⟩ := T24.EQ.u32_cellAt_MM F hC hb3
      exact GenRev.lexAny_of_closedCell (by norm_num) F T24.EQ.injMM T24.EQ.cycMM ha
        (T24.EQ.u32_cellLe_MM F hC hb3) hR),
   fun hR => holeLeaf_not_lexAny h (by
      obtain ⟨a, ha⟩ := T24.EQ.u32_cellAt_PP F hC hb3
      exact GenRev.lexAny_of_closedCell (by norm_num) F T24.EQ.injPP T24.EQ.cycPP ha
        (T24.EQ.u32_cellLe_PP F hC hb3) hR),
   fun ⟨a, cc, σ, hca, hca1, hrows⟩ => (holeLeaf_leaves h).2.2.2.1 (by
      have hlp := T24.EQ.u32_lp_MM F hC hb3
      have hfac : S0xFacOK F (fun t => decide (t ∈ T24.EQ.UMM)) (x 3 - x 2) ((x 6 - x 2) + (x 5 - x 2)) := by
        intro t
        refine ⟨fun h => hlp.1 t (by simpa using h), fun h => hlp.2 t ?_⟩
        have ht : t ∉ T24.EQ.UMM := by simpa using h
        revert ht
        revert t
        decide
      have hcyc : S0xCycOK s0x_S24 T24.EQ.cMM (fun t => decide (t ∈ T24.EQ.UMM)) := by decide
      exact ⟨5, inferInstance, T24.EQ.cMM, _, x 3 - x 2, (x 6 - x 2) + (x 5 - x 2), a, cc, σ, by norm_num,
        T24.EQ.injMM, hcyc, hfac, hca, hca1, hrows⟩),
   fun ⟨a, cc, σ, hca, hca1, hrows⟩ => (holeLeaf_leaves h).2.2.2.1 (by
      have hlp := T24.EQ.u32_lp_PP F hC hb3
      have hfac : S0xFacOK F (fun t => decide (t ∈ T24.EQ.UPP)) (x 3 - x 2) ((x 2 - x 6) + (x 2 - x 5)) := by
        intro t
        refine ⟨fun h => hlp.1 t (by simpa using h), fun h => hlp.2 t ?_⟩
        have ht : t ∉ T24.EQ.UPP := by simpa using h
        revert ht
        revert t
        decide
      have hcyc : S0xCycOK s0x_S24 T24.EQ.cPP (fun t => decide (t ∈ T24.EQ.UPP)) := by decide
      exact ⟨5, inferInstance, T24.EQ.cPP, _, x 3 - x 2, (x 2 - x 6) + (x 2 - x 5), a, cc, σ, by norm_num,
        T24.EQ.injPP, hcyc, hfac, hca, hca1, hrows⟩)⟩

/-- `hole24_u32` from `holeLeaf_u32`. -/
theorem hole24_u32 (h : Hole24 x F) (hb3 : oblX2 x 3 < 1) :
    ¬ RobUni (fun i : ZMod 5 => ⟪x (T24.EQ.cMM i), x 3 - x 2⟫) ∧
    ¬ RobUni (fun i : ZMod 5 => ⟪x (T24.EQ.cPP i), x 3 - x 2⟫) ∧
    ¬ T24.EQ.SplitAny5 x T24.EQ.cMM ∧ ¬ T24.EQ.SplitAny5 x T24.EQ.cPP :=
  holeLeaf_u32 h.1 hb3

/-! ### Lex triples R^(c) -/

/-- **`R^(c)` lex triples** (contrapositives of `EM.lexAny_R1 .. lexAny_R5p`).  The lex view `R^(c)_s` of the
given rim never lies in that rim's cell once the order condition holds.  The order conditions are the
hypotheses; `IsRcView x s b d1 d2` pins the triple. -/
theorem holeLeaf_R1 (h : HoleLeaf x F) {b d1 d2 : ℝ³} (hv : T24.EM.IsRcView x 1 b d1 d2) :
    ¬ T24.EM.LexCellAt F T24.EM.U1 T24.EM.D1 b d1 d2 := fun hc =>
  holeLeaf_not_lexAny h (T24.EM.lexAny_R1 F hv hc)

/-- `hole24_R1` from `holeLeaf_R1`. -/
theorem hole24_R1 (h : Hole24 x F) {b d1 d2 : ℝ³} (hv : T24.EM.IsRcView x 1 b d1 d2) :
    ¬ T24.EM.LexCellAt F T24.EM.U1 T24.EM.D1 b d1 d2 :=
  holeLeaf_R1 h.1 hv

theorem holeLeaf_R2 (h : HoleLeaf x F) (h4 : oblX0 x 4 + oblX2 x 4 < 1) (h5 : 1 < oblX0 x 5 + oblX2 x 5)
    {b d1 d2 : ℝ³} (hv : T24.EM.IsRcView x 1 b d1 d2) : ¬ T24.EM.LexCellAt F T24.EM.U2 T24.EM.D2 b d1 d2 :=
  fun hc => holeLeaf_not_lexAny h (T24.EM.lexAny_R2 F h4 h5 hv hc)

/-- `hole24_R2` from `holeLeaf_R2`. -/
theorem hole24_R2 (h : Hole24 x F) (h4 : oblX0 x 4 + oblX2 x 4 < 1) (h5 : 1 < oblX0 x 5 + oblX2 x 5)
    {b d1 d2 : ℝ³} (hv : T24.EM.IsRcView x 1 b d1 d2) : ¬ T24.EM.LexCellAt F T24.EM.U2 T24.EM.D2 b d1 d2 :=
  holeLeaf_R2 h.1 h4 h5 hv

theorem holeLeaf_R3 (h : HoleLeaf x F) (h4 : oblX0 x 4 + oblX2 x 4 < 1)
    {b d1 d2 : ℝ³} (hv : T24.EM.IsRcView x (-1) b d1 d2) : ¬ T24.EM.LexCellAt F T24.EM.U3 T24.EM.D3 b d1 d2 :=
  fun hc => holeLeaf_not_lexAny h (T24.EM.lexAny_R3 F h4 hv hc)

/-- `hole24_R3` from `holeLeaf_R3`. -/
theorem hole24_R3 (h : Hole24 x F) (h4 : oblX0 x 4 + oblX2 x 4 < 1)
    {b d1 d2 : ℝ³} (hv : T24.EM.IsRcView x (-1) b d1 d2) : ¬ T24.EM.LexCellAt F T24.EM.U3 T24.EM.D3 b d1 d2 :=
  holeLeaf_R3 h.1 h4 hv

theorem holeLeaf_R4p (h : HoleLeaf x F) (h3 : oblX0 x 3 + oblX2 x 3 < 1) (h5 : 1 < oblX0 x 5 + oblX2 x 5)
    {b d1 d2 : ℝ³} (hv : T24.EM.IsRcView x 1 b d1 d2) : ¬ T24.EM.LexCellAt F T24.EM.U4 T24.EM.D4 b d1 d2 :=
  fun hc => holeLeaf_not_lexAny h (T24.EM.lexAny_R4p F h3 h5 hv hc)

/-- `hole24_R4p` from `holeLeaf_R4p`. -/
theorem hole24_R4p (h : Hole24 x F) (h3 : oblX0 x 3 + oblX2 x 3 < 1) (h5 : 1 < oblX0 x 5 + oblX2 x 5)
    {b d1 d2 : ℝ³} (hv : T24.EM.IsRcView x 1 b d1 d2) : ¬ T24.EM.LexCellAt F T24.EM.U4 T24.EM.D4 b d1 d2 :=
  holeLeaf_R4p h.1 h3 h5 hv

theorem holeLeaf_R4m (h : HoleLeaf x F) (h3 : oblX0 x 3 + oblX2 x 3 < 1) (h5 : 1 < oblX0 x 5 + oblX2 x 5)
    {b d1 d2 : ℝ³} (hv : T24.EM.IsRcView x (-1) b d1 d2) : ¬ T24.EM.LexCellAt F T24.EM.U4 T24.EM.D4 b d1 d2 :=
  fun hc => holeLeaf_not_lexAny h (T24.EM.lexAny_R4m F h3 h5 hv hc)

/-- `hole24_R4m` from `holeLeaf_R4m`. -/
theorem hole24_R4m (h : Hole24 x F) (h3 : oblX0 x 3 + oblX2 x 3 < 1) (h5 : 1 < oblX0 x 5 + oblX2 x 5)
    {b d1 d2 : ℝ³} (hv : T24.EM.IsRcView x (-1) b d1 d2) : ¬ T24.EM.LexCellAt F T24.EM.U4 T24.EM.D4 b d1 d2 :=
  holeLeaf_R4m h.1 h3 h5 hv

theorem holeLeaf_R5m (h : HoleLeaf x F) (hh : oblX0 x 4 + oblX2 x 4 < 1 ∨ 1 < oblX0 x 3 + oblX2 x 3)
    {b d1 d2 : ℝ³} (hv : T24.EM.IsRcView x (-1) b d1 d2) : ¬ T24.EM.LexCellAt F T24.EM.U5 T24.EM.D5 b d1 d2 :=
  fun hc => holeLeaf_not_lexAny h (T24.EM.lexAny_R5m F hh hv hc)

/-- `hole24_R5m` from `holeLeaf_R5m`. -/
theorem hole24_R5m (h : Hole24 x F) (hh : oblX0 x 4 + oblX2 x 4 < 1 ∨ 1 < oblX0 x 3 + oblX2 x 3)
    {b d1 d2 : ℝ³} (hv : T24.EM.IsRcView x (-1) b d1 d2) : ¬ T24.EM.LexCellAt F T24.EM.U5 T24.EM.D5 b d1 d2 :=
  holeLeaf_R5m h.1 hh hv

theorem holeLeaf_R5p (h : HoleLeaf x F) (hh : oblX0 x 3 + oblX2 x 3 < 1 ∨ 1 < oblX0 x 4 + oblX2 x 4)
    {b d1 d2 : ℝ³} (hv : T24.EM.IsRcView x 1 b d1 d2) : ¬ T24.EM.LexCellAt F T24.EM.U5 T24.EM.D5 b d1 d2 :=
  fun hc => holeLeaf_not_lexAny h (T24.EM.lexAny_R5p F hh hv hc)

/-- `hole24_R5p` from `holeLeaf_R5p`. -/
theorem hole24_R5p (h : Hole24 x F) (hh : oblX0 x 3 + oblX2 x 3 < 1 ∨ 1 < oblX0 x 4 + oblX2 x 4)
    {b d1 d2 : ℝ³} (hv : T24.EM.IsRcView x 1 b d1 d2) : ¬ T24.EM.LexCellAt F T24.EM.U5 T24.EM.D5 b d1 d2 :=
  holeLeaf_R5p h.1 hh hv

/-! ### Hidden-cap frame facts -/

/-- At a hidden-cap cone view `u = capView x ca cb cc` (`ca, cb, cc > 0`) facets 0, 1, 5 are back (frame fact,
`HC.back24_of_cone`); conversely every `u` with these three signs is such a view (`cone24_of_back`).  Not a
contrapositive: the cone is where vertex 1 is hidden (`hiddenAt24_of_cone`), so the six-point rim there is the
whole story. -/
theorem cone_backs (F : S0xFac 9 s0x_S24 x) {ca cb cc : ℝ} (ha : 0 < ca) (hb : 0 < cb) (hc : 0 < cc) :
    ⟪F.N 0, capView x ca cb cc⟫ < 0 ∧ ⟪F.N 1, capView x ca cb cc⟫ < 0 ∧ ⟪F.N 5, capView x ca cb cc⟫ < 0 :=
  back24_of_cone F ca cb cc ha hb hc

theorem cone_of_backs (F : S0xFac 9 s0x_S24 x) (u : ℝ³)
    (h0 : ⟪F.N 0, u⟫ < 0) (h1 : ⟪F.N 1, u⟫ < 0) (h5 : ⟪F.N 5, u⟫ < 0) :
    ∃ ca cb cc : ℝ, 0 < ca ∧ 0 < cb ∧ 0 < cc ∧ u = capView x ca cb cc :=
  cone24_of_back F u h0 h1 h5

/-- Vertex 1 is hidden at every cone view. -/
theorem cone_hidden (F : S0xFac 9 s0x_S24 x) {ca cb cc : ℝ} (ha : 0 < ca) (hb : 0 < cb) (hc : 0 < cc) :
    HiddenAt ((univ.erase 1).image x) (capView x ca cb cc) (x 1) :=
  hiddenAt24_of_cone F ca cb cc ha hb hc

end Minimality.T24.Atlas
