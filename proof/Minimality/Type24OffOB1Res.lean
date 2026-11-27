module

public import Minimality.Type24OffOB1
public import Minimality.Q45

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21 Minimality.FaceChord Minimality.T24.SAT Minimality.T24.Stmt Minimality.T24.Q45
  Minimality.T24.Reg Minimality.T24.A19

/-!
# Type 24 off `OB1`: the branch-tagged Q45 residue (job OSPEC2, nopert229 notes/OPENSPECIAL-STRATEGY.md)

`OpenSpecialW` (Type24OffOB1.lean) asks for `¬ HoleFull` on the walls `a4 = 1`, `a5 = 1` and on all of `Q45Special'`
(a union of loci of ALL dispatcher branches).  Here the Q45 dispatcher (`q45_half_cell_local`) is rerun on the whole
corner `a4, a5 ≥ 1` (no `Q45HalfPred`: each branch's sign `⟪N5, ·⟫ < 0` either holds or puts the point on a wall), with
two observations:

* the corner cells are lex cells (`q45_B1_cell_lex` .. `q45_C2_cell_lex`, via `lexAny_of_closedCell_q4`), so a hole
  point (`¬ LexAny`) never takes a cell exit;
* in a corner branch (`h6hi` / `h2hi`) the failure of the cell condition `Hlex` FORCES the three-vertex tie of that
  branch (`tieB1_of_not_hlex` ..): there the residue is codimension 2 and the S3 / S4 / S2 loci are never reached.

The result `q45_res`: off-`OB1`-free, every point of the corner has `LexAny`, `AnyFaceChord` or lies in `Q45ResW`,
the disjunction of `ResWall` (the walls only in the branches whose sign fails: `K+, s ≤ 1, a5 = 1`; `K-, t ≤ 1,
a4 = 1`; `kJ = 0` on a wall; `a4 = a5 = 1`), four codim-2 corner ties (`ResB1T` ..), the codim-2 pieces `ResBs1`,
`ResCt1`, `ResK0`, and the four face-chord branches `ResJ0a` .. `ResJ0d` with the loci S3 / S4J0 / S2J0.
`OpenSpecialR` is `OpenSpecialW` with `Q45ResW` in place of walls ∨ `Q45Special'`; it is implied by `OpenSpecialW`
(`openSpecialR_of_openSpecialW`) and still closes the hole (`not_hole24_of_namedCoverEmpty_R`, `open24_of_split_R`).
-/

namespace Minimality.T24.OSpec

variable {x : Fin 7 → ℝ³}

/-- `kJ · Ω`, the sign that splits the dispatcher into `K+` (`< 0`), `K0` and `K-` (`> 0`). -/
noncomputable def kOm (x : Fin 7 → ℝ³) : ℝ :=
  det3 (x 5 - x 6) (x 2 - x 6) (x 4 - x 6) * det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1)

/-- The face-chord loci of the `J0` leaves (rim `6 4 5 2`) with the second test direction `e`. -/
def LociJ0 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (S2 : Prop) : Prop :=
  F.f 3 (x 2) = F.f 3 (x 6) ∨ Q45S4LocusJ0 F ∨ S2

/-- Walls, only where the branch sign fails. -/
def ResWall (x : Fin 7 → ℝ³) (s t : ℝ) : Prop :=
  (kOm x < 0 ∧ s ≤ 1 ∧ oblX0 x 5 = 1) ∨ (0 < kOm x ∧ t ≤ 1 ∧ oblX0 x 4 = 1) ∨
    (det3 (x 5 - x 6) (x 2 - x 6) (x 4 - x 6) = 0 ∧ (oblX0 x 4 = 1 ∨ oblX0 x 5 = 1)) ∨
    (oblX0 x 4 = 1 ∧ oblX0 x 5 = 1)

/-- Corner `B1` (`K+`, `s < 1`, `h6hi`) without its cell: the tie `T-B1` (codim 2). -/
def ResB1T (x : Fin 7 → ℝ³) (s : ℝ) : Prop :=
  kOm x < 0 ∧ s < 1 ∧ max ⟪x 4, x 5 - x 0⟫ ⟪x 2, x 5 - x 0⟫ ≤ ⟪x 6, x 5 - x 0⟫ ∧ ¬ HlexB1 x ∧ Q45TieLocusB1 x
/-- `K+`, `s = 1`, `h6hi`: the `Bs1` loci (codim 2). -/
def ResBs1 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (s : ℝ) : Prop :=
  kOm x < 0 ∧ s = 1 ∧ max ⟪x 4, x 5 - x 0⟫ ⟪x 2, x 5 - x 0⟫ ≤ ⟪x 6, x 5 - x 0⟫ ∧
    (Q45TieLocusBs1 x ∨ F.f 3 (x 2) = F.f 3 (x 6) ∨ Q45S4LocusBs1 F ∨ Q45S2LocusBs1 x)
/-- `K+`, `s ≤ 1`, not `h6hi`: face chord `q45_Kplus_s_le_one` fails only on its loci (codim 1). -/
def ResJ0a {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (s : ℝ) : Prop :=
  kOm x < 0 ∧ s ≤ 1 ∧ ⟪x 6, x 5 - x 0⟫ < max ⟪x 4, x 5 - x 0⟫ ⟪x 2, x 5 - x 0⟫ ∧ LociJ0 F (Q45S2LocusJ0_e5 x)
/-- Corner `B2` (`K+`, `1 < s`, `h6hi`) without its cell: the tie `T-B2` (codim 2). -/
def ResB2T (x : Fin 7 → ℝ³) (s : ℝ) : Prop :=
  kOm x < 0 ∧ 1 < s ∧ max ⟪x 4, x 3 - x 4⟫ ⟪x 2, x 3 - x 4⟫ ≤ min ⟪x 6, x 3 - x 4⟫ ⟪x 5, x 3 - x 4⟫ ∧
    ¬ HlexB2 x ∧ Q45TieLocusB2 x
/-- `K+`, `1 < s`, not `h6hi` (codim 1). -/
def ResJ0b {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (s : ℝ) : Prop :=
  kOm x < 0 ∧ 1 < s ∧ min ⟪x 6, x 3 - x 4⟫ ⟪x 5, x 3 - x 4⟫ < max ⟪x 4, x 3 - x 4⟫ ⟪x 2, x 3 - x 4⟫ ∧
    LociJ0 F (Q45S2LocusJ0_e34 x)
/-- `kJ = 0` with the `J0` loci (codim 2). -/
def ResK0 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) : Prop :=
  det3 (x 5 - x 6) (x 2 - x 6) (x 4 - x 6) = 0 ∧ LociJ0 F (Q45S2LocusJ0_e5 x)
/-- Corner `C1` (`K-`, `t < 1`, `h2hi`) without its cell: the tie `T-C1` (codim 2). -/
def ResC1T (x : Fin 7 → ℝ³) (t : ℝ) : Prop :=
  0 < kOm x ∧ t < 1 ∧ max ⟪x 6, x 4 - x 0⟫ ⟪x 5, x 4 - x 0⟫ ≤ ⟪x 2, x 4 - x 0⟫ ∧ ¬ HlexC1 x ∧ Q45TieLocusC1 x
/-- `K-`, `t = 1`, `h2hi`: the `Ct1` loci (codim 2). -/
def ResCt1 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (t : ℝ) : Prop :=
  0 < kOm x ∧ t = 1 ∧ max ⟪x 6, x 4 - x 0⟫ ⟪x 5, x 4 - x 0⟫ ≤ ⟪x 2, x 4 - x 0⟫ ∧
    (Q45TieLocusCt1 x ∨ F.f 3 (x 2) = F.f 3 (x 6) ∨ Q45S4LocusCt1 F ∨ Q45S2LocusCt1 x)
/-- `K-`, `t ≤ 1`, not `h2hi` (codim 1). -/
def ResJ0c {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (t : ℝ) : Prop :=
  0 < kOm x ∧ t ≤ 1 ∧ ⟪x 2, x 4 - x 0⟫ < max ⟪x 6, x 4 - x 0⟫ ⟪x 5, x 4 - x 0⟫ ∧ LociJ0 F (Q45S2LocusJ0_e5 x)
/-- Corner `C2` (`K-`, `1 < t`, `h2hi`) without its cell: the tie `T-C2` (codim 2). -/
def ResC2T (x : Fin 7 → ℝ³) (t : ℝ) : Prop :=
  0 < kOm x ∧ 1 < t ∧ max ⟪x 6, x 3 - x 5⟫ ⟪x 5, x 3 - x 5⟫ ≤ min ⟪x 2, x 3 - x 5⟫ ⟪x 4, x 3 - x 5⟫ ∧
    ¬ HlexC2 x ∧ Q45TieLocusC2 x
/-- `K-`, `1 < t`, not `h2hi` (codim 1). -/
def ResJ0d {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (t : ℝ) : Prop :=
  0 < kOm x ∧ 1 < t ∧ min ⟪x 2, x 3 - x 5⟫ ⟪x 4, x 3 - x 5⟫ < max ⟪x 6, x 3 - x 5⟫ ⟪x 5, x 3 - x 5⟫ ∧
    LociJ0 F (Q45S2LocusJ0_e35 x)

/-- The residue of the Q45 dispatcher at the decomposition `(s, t)`. -/
def Q45ResST {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (s t : ℝ) : Prop :=
  ResWall x s t ∨ ResB1T x s ∨ ResBs1 F s ∨ ResJ0a F s ∨ ResB2T x s ∨ ResJ0b F s ∨ ResK0 F ∨
    ResC1T x t ∨ ResCt1 F t ∨ ResJ0c F t ∨ ResC2T x t ∨ ResJ0d F t

/-- The branch-tagged residue (`s, t` = the Lemma M decomposition of `x 3 - x 0`, unique). -/
def Q45ResW {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) : Prop :=
  ∃ s t : ℝ, 0 < s ∧ 0 < t ∧ 1 < s + t ∧ x 3 - x 0 = s • (x 4 - x 0) + t • (x 5 - x 0) ∧ Q45ResST F s t

/-! ### The corner ties are forced -/

theorem tieB1_of_not_hlex (h6hi : max ⟪x 4, x 5 - x 0⟫ ⟪x 2, x 5 - x 0⟫ ≤ ⟪x 6, x 5 - x 0⟫)
    (hl : ¬ HlexB1 x) : Q45TieLocusB1 x := by
  have h4 : 0 ≤ ⟪x 4 - x 6, x 5 - x 0⟫ := by
    by_contra h; exact hl ⟨4, by decide, 6, by decide, Or.inl (not_le.mp h)⟩
  have h2 : 0 ≤ ⟪x 2 - x 6, x 5 - x 0⟫ := by
    by_contra h; exact hl ⟨2, by decide, 6, by decide, Or.inl (not_le.mp h)⟩
  rw [inner_sub_left] at h4 h2
  have := le_max_left ⟪x 4, x 5 - x 0⟫ ⟪x 2, x 5 - x 0⟫
  have := le_max_right ⟪x 4, x 5 - x 0⟫ ⟪x 2, x 5 - x 0⟫
  exact ⟨by linarith, by linarith⟩

theorem tieB2_of_not_hlex
    (h6hi : max ⟪x 4, x 3 - x 4⟫ ⟪x 2, x 3 - x 4⟫ ≤ min ⟪x 6, x 3 - x 4⟫ ⟪x 5, x 3 - x 4⟫)
    (hl : ¬ HlexB2 x) : Q45TieLocusB2 x := by
  have h6 : 0 ≤ ⟪x 2 - x 6, x 3 - x 4⟫ := by
    by_contra h; exact hl ⟨2, by decide, 6, by decide, Or.inl (not_le.mp h)⟩
  have h5 : 0 ≤ ⟪x 2 - x 5, x 3 - x 4⟫ := by
    by_contra h; exact hl ⟨2, by decide, 5, by decide, Or.inl (not_le.mp h)⟩
  rw [inner_sub_left] at h6 h5
  have := le_max_right ⟪x 4, x 3 - x 4⟫ ⟪x 2, x 3 - x 4⟫
  have := min_le_left ⟪x 6, x 3 - x 4⟫ ⟪x 5, x 3 - x 4⟫
  have := min_le_right ⟪x 6, x 3 - x 4⟫ ⟪x 5, x 3 - x 4⟫
  exact ⟨by linarith, by linarith⟩

theorem tieC1_of_not_hlex (h2hi : max ⟪x 6, x 4 - x 0⟫ ⟪x 5, x 4 - x 0⟫ ≤ ⟪x 2, x 4 - x 0⟫)
    (hl : ¬ HlexC1 x) : Q45TieLocusC1 x := by
  have h6 : 0 ≤ ⟪x 6 - x 2, x 4 - x 0⟫ := by
    by_contra h; exact hl ⟨6, by decide, 2, by decide, Or.inl (not_le.mp h)⟩
  have h5 : 0 ≤ ⟪x 5 - x 2, x 4 - x 0⟫ := by
    by_contra h; exact hl ⟨5, by decide, 2, by decide, Or.inl (not_le.mp h)⟩
  rw [inner_sub_left] at h6 h5
  have := le_max_left ⟪x 6, x 4 - x 0⟫ ⟪x 5, x 4 - x 0⟫
  have := le_max_right ⟪x 6, x 4 - x 0⟫ ⟪x 5, x 4 - x 0⟫
  exact ⟨by linarith, by linarith⟩

theorem tieC2_of_not_hlex
    (h2hi : max ⟪x 6, x 3 - x 5⟫ ⟪x 5, x 3 - x 5⟫ ≤ min ⟪x 2, x 3 - x 5⟫ ⟪x 4, x 3 - x 5⟫)
    (hl : ¬ HlexC2 x) : Q45TieLocusC2 x := by
  have h4 : 0 ≤ ⟪x 6 - x 4, x 3 - x 5⟫ := by
    by_contra h; exact hl ⟨6, by decide, 4, by decide, Or.inl (not_le.mp h)⟩
  have h2 : 0 ≤ ⟪x 6 - x 2, x 3 - x 5⟫ := by
    by_contra h; exact hl ⟨6, by decide, 2, by decide, Or.inl (not_le.mp h)⟩
  rw [inner_sub_left] at h4 h2
  have := le_max_left ⟪x 6, x 3 - x 5⟫ ⟪x 5, x 3 - x 5⟫
  have := min_le_left ⟪x 2, x 3 - x 5⟫ ⟪x 4, x 3 - x 5⟫
  have := min_le_right ⟪x 2, x 3 - x 5⟫ ⟪x 4, x 3 - x 5⟫
  exact ⟨by linarith, by linarith⟩

/-! ### The branch signs on the corner `a4, a5 ≥ 1` -/

private theorem f5_obl (F : S0xFac 9 s0x_S24 x) (v : Fin 7) : F.f 5 (x v) = oblX0 x v * F.f 5 (x 0) := by
  rw [Minimality.T24.M4.fac_eval F 5 v, F.zero 5 1 (by decide), F.zero 5 2 (by decide), F.zero 5 6 (by decide)]
  ring

theorem sgn_a (F : S0xFac 9 s0x_S24 x) (v : Fin 7) (h : 1 ≤ oblX0 x v) :
    ⟪F.N 5, x v - x 0⟫ < 0 ∨ oblX0 x v = 1 := by
  rcases h.lt_or_eq with h | h
  · left
    have h0 : F.f 5 (x 0) < 0 := F.neg 5 0 (by decide)
    rw [← F.hN 5 (x v) (x 0), f5_obl F v]; nlinarith
  · exact Or.inr h.symm

/-- `⟪N5, x3 - x4⟫ < 0` for `1 < s` on the corner, unless `a4 = a5 = 1`. -/
theorem sgn_34 (F : S0xFac 9 s0x_S24 x) (h4 : 1 ≤ oblX0 x 4) (h5 : 1 ≤ oblX0 x 5) {s t : ℝ} (hs : 1 < s)
    (ht : 0 < t) (hdec : x 3 - x 0 = s • (x 4 - x 0) + t • (x 5 - x 0)) :
    ⟪F.N 5, x 3 - x 4⟫ < 0 ∨ (oblX0 x 4 = 1 ∧ oblX0 x 5 = 1) := by
  by_cases hw : oblX0 x 4 = 1 ∧ oblX0 x 5 = 1
  · exact Or.inr hw
  left
  have h0 : F.f 5 (x 0) < 0 := F.neg 5 0 (by decide)
  have ev := congrArg (fun v => ⟪F.N 5, v⟫) hdec
  simp only [inner_add_right, real_inner_smul_right] at ev
  rw [← F.hN 5 (x 3) (x 0), ← F.hN 5 (x 4) (x 0), ← F.hN 5 (x 5) (x 0), f5_obl F 3, f5_obl F 4,
    f5_obl F 5] at ev
  rw [← F.hN 5 (x 3) (x 4), f5_obl F 3, f5_obl F 4]
  have key : oblX0 x 3 - oblX0 x 4 = (s - 1) * (oblX0 x 4 - 1) + t * (oblX0 x 5 - 1) := by
    have := mul_right_cancel₀ h0.ne (by linarith : (oblX0 x 3 - 1) * F.f 5 (x 0) =
      (s * (oblX0 x 4 - 1) + t * (oblX0 x 5 - 1)) * F.f 5 (x 0))
    linarith
  have hpos : 0 < oblX0 x 3 - oblX0 x 4 := by
    rcases h4.lt_or_eq with h4' | h4'
    · rw [key]; nlinarith
    · have h5' : 1 < oblX0 x 5 := lt_of_le_of_ne h5 (fun e => hw ⟨h4'.symm, e.symm⟩)
      rw [key]; nlinarith
  nlinarith

/-- `⟪N5, x3 - x5⟫ < 0` for `1 < t` on the corner, unless `a4 = a5 = 1`. -/
theorem sgn_35 (F : S0xFac 9 s0x_S24 x) (h4 : 1 ≤ oblX0 x 4) (h5 : 1 ≤ oblX0 x 5) {s t : ℝ} (hs : 0 < s)
    (ht : 1 < t) (hdec : x 3 - x 0 = s • (x 4 - x 0) + t • (x 5 - x 0)) :
    ⟪F.N 5, x 3 - x 5⟫ < 0 ∨ (oblX0 x 4 = 1 ∧ oblX0 x 5 = 1) := by
  by_cases hw : oblX0 x 4 = 1 ∧ oblX0 x 5 = 1
  · exact Or.inr hw
  left
  have h0 : F.f 5 (x 0) < 0 := F.neg 5 0 (by decide)
  have ev := congrArg (fun v => ⟪F.N 5, v⟫) hdec
  simp only [inner_add_right, real_inner_smul_right] at ev
  rw [← F.hN 5 (x 3) (x 0), ← F.hN 5 (x 4) (x 0), ← F.hN 5 (x 5) (x 0), f5_obl F 3, f5_obl F 4,
    f5_obl F 5] at ev
  rw [← F.hN 5 (x 3) (x 5), f5_obl F 3, f5_obl F 5]
  have key : oblX0 x 3 - oblX0 x 5 = s * (oblX0 x 4 - 1) + (t - 1) * (oblX0 x 5 - 1) := by
    have := mul_right_cancel₀ h0.ne (by linarith : (oblX0 x 3 - 1) * F.f 5 (x 0) =
      (s * (oblX0 x 4 - 1) + t * (oblX0 x 5 - 1)) * F.f 5 (x 0))
    linarith
  have hpos : 0 < oblX0 x 3 - oblX0 x 5 := by
    rcases h5.lt_or_eq with h5' | h5'
    · rw [key]; nlinarith
    · have h4' : 1 < oblX0 x 4 := lt_of_le_of_ne h4 (fun e => hw ⟨e.symm, h5'.symm⟩)
      rw [key]; nlinarith
  nlinarith

/-! ### The dispatcher with the branch-tagged residue -/

/-- **Q45 dispatcher on the corner `a4, a5 ≥ 1`, residue form.**  At the decomposition `(s, t)` every point has a
lex cell, a face chord on facet `0345`, or lies in `Q45ResST F s t`.  Same branches and leaves as
`q45_half_cell_local`; no `Q45HalfHyp` (`sgn_a`, `sgn_34`, `sgn_35`), the corner cells as lex cells. -/
theorem q45_res_local (F : S0xFac 9 s0x_S24 x) (h4 : 1 ≤ oblX0 x 4) (h5 : 1 ≤ oblX0 x 5)
    (s t : ℝ) (hs0 : 0 < s) (ht : 0 < t) (hst : 1 < s + t)
    (hdecomp : x 3 - x 0 = s • (x 4 - x 0) + t • (x 5 - x 0)) :
    Gen.LexAny F ∨ Gen.AnyFaceChord F ∨ Q45ResST F s t := by
  have h_om := omega_ne_zero F
  have res : Q45ResST F s t → Gen.LexAny F ∨ Gen.AnyFaceChord F ∨ Q45ResST F s t := fun h => Or.inr (Or.inr h)
  have fc : FaceChordView F 3 → Gen.LexAny F ∨ Gen.AnyFaceChord F ∨ Q45ResST F s t :=
    fun h => Or.inr (Or.inl ⟨3, h⟩)
  rcases lt_trichotomy (kOm x) 0 with hk | hk0 | hk
  · -- K+
    have hk' : det3 (x 5 - x 6) (x 2 - x 6) (x 4 - x 6) * det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1) < 0 := hk
    rcases le_or_gt s 1 with hs | hs
    · rcases sgn_a F 5 h5 with ha5 | hw
      · by_cases h6hi : max ⟪x 4, x 5 - x 0⟫ ⟪x 2, x 5 - x 0⟫ ≤ ⟪x 6, x 5 - x 0⟫
        · rcases lt_or_eq_of_le hs with hs_lt | hs_eq
          · by_cases hlex : HlexB1 x
            · exact Or.inl (q45_B1_cell_lex F ha5 s t hs0 ht hst hdecomp hs_lt hlex)
            · exact res (Or.inr (Or.inl ⟨hk, hs_lt, h6hi, hlex, tieB1_of_not_hlex h6hi hlex⟩))
          · by_cases hL : Q45TieLocusBs1 x ∨ F.f 3 (x 2) = F.f 3 (x 6) ∨ Q45S4LocusBs1 F ∨ Q45S2LocusBs1 x
            · exact res (Or.inr (Or.inr (Or.inl ⟨hk, hs_eq, h6hi, hL⟩)))
            · simp only [not_or] at hL
              obtain ⟨htie, hs3, hs4, hs2⟩ := hL
              exact fc (q45_Bs1 F ha5 s t ht hdecomp hs_eq h6hi htie (not_not.mp hs2) hs3 (not_not.mp hs4))
        · have h6lo : min ⟪x 6, x 5 - x 0⟫ ⟪x 5, x 5 - x 0⟫ < max ⟪x 4, x 5 - x 0⟫ ⟪x 2, x 5 - x 0⟫ :=
            lt_of_le_of_lt (min_le_left _ _) (not_le.mp h6hi)
          by_cases hL : LociJ0 F (Q45S2LocusJ0_e5 x)
          · exact res (Or.inr (Or.inr (Or.inr (Or.inl ⟨hk, hs, not_le.mp h6hi, hL⟩))))
          · simp only [LociJ0, not_or] at hL
            obtain ⟨hs3, hs4, hs2⟩ := hL
            exact fc (q45_Kplus_s_le_one F ha5 s t hs0 ht hst hdecomp hk' hs h6lo (not_not.mp hs2) hs3
              (not_not.mp hs4))
      · exact res (Or.inl (Or.inl ⟨hk, hs, hw⟩))
    · rcases sgn_34 F h4 h5 hs ht hdecomp with ha34 | hw
      · by_cases h6hi : max ⟪x 4, x 3 - x 4⟫ ⟪x 2, x 3 - x 4⟫ ≤ min ⟪x 6, x 3 - x 4⟫ ⟪x 5, x 3 - x 4⟫
        · by_cases hlex : HlexB2 x
          · exact Or.inl (q45_B2_cell_lex F ha34 s t ht hdecomp hs hlex)
          · exact res (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hk, hs, h6hi, hlex,
              tieB2_of_not_hlex h6hi hlex⟩)))))
        · have h6lo : min ⟪x 6, x 3 - x 4⟫ ⟪x 5, x 3 - x 4⟫ < max ⟪x 4, x 3 - x 4⟫ ⟪x 2, x 3 - x 4⟫ :=
            not_le.mp h6hi
          by_cases hL : LociJ0 F (Q45S2LocusJ0_e34 x)
          · exact res (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hk, hs, h6lo, hL⟩))))))
          · simp only [LociJ0, not_or] at hL
            obtain ⟨hs3, hs4, hs2⟩ := hL
            exact fc (q45_Kplus_s_gt_one F ha34 s t hs0 ht hst hdecomp hk' hs h6lo (not_not.mp hs2) hs3
              (not_not.mp hs4))
      · exact res (Or.inl (Or.inr (Or.inr (Or.inr hw))))
  · -- K0
    have hkJ : det3 (x 5 - x 6) (x 2 - x 6) (x 4 - x 6) = 0 := (mul_eq_zero.mp hk0).resolve_right h_om
    rcases sgn_a F 4 h4 with ha4 | hw4
    · rcases sgn_a F 5 h5 with ha5 | hw5
      · by_cases hL : LociJ0 F (Q45S2LocusJ0_e5 x)
        · exact res (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hkJ, hL⟩)))))))
        · simp only [LociJ0, not_or] at hL
          obtain ⟨hs3, hs4, hs2⟩ := hL
          exact fc (q45_K0 F ha4 ha5 s t hs0 ht hst hdecomp hkJ (not_not.mp hs2) hs3 (not_not.mp hs4))
      · exact res (Or.inl (Or.inr (Or.inr (Or.inl ⟨hkJ, Or.inr hw5⟩))))
    · exact res (Or.inl (Or.inr (Or.inr (Or.inl ⟨hkJ, Or.inl hw4⟩))))
  · -- K-
    have hk' : 0 < det3 (x 5 - x 6) (x 2 - x 6) (x 4 - x 6) * det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1) := hk
    rcases le_or_gt t 1 with ht1 | ht1
    · rcases sgn_a F 4 h4 with ha4 | hw
      · by_cases h2hi : max ⟪x 6, x 4 - x 0⟫ ⟪x 5, x 4 - x 0⟫ ≤ ⟪x 2, x 4 - x 0⟫
        · rcases lt_or_eq_of_le ht1 with ht_lt | ht_eq
          · by_cases hlex : HlexC1 x
            · exact Or.inl (q45_C1_cell_lex F ha4 s t hs0 ht hst hdecomp ht_lt hlex)
            · exact res (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
                ⟨hk, ht_lt, h2hi, hlex, tieC1_of_not_hlex h2hi hlex⟩))))))))
          · by_cases hL : Q45TieLocusCt1 x ∨ F.f 3 (x 2) = F.f 3 (x 6) ∨ Q45S4LocusCt1 F ∨ Q45S2LocusCt1 x
            · exact res (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
                ⟨hk, ht_eq, h2hi, hL⟩)))))))))
            · simp only [not_or] at hL
              obtain ⟨htie, hs3, hs4, hs2⟩ := hL
              exact fc (q45_Ct1 F ha4 s t hs0 hdecomp ht_eq h2hi htie (not_not.mp hs2) hs3 (not_not.mp hs4))
        · have h2lo : min ⟪x 4, x 4 - x 0⟫ ⟪x 2, x 4 - x 0⟫ < max ⟪x 6, x 4 - x 0⟫ ⟪x 5, x 4 - x 0⟫ :=
            lt_of_le_of_lt (min_le_right _ _) (not_le.mp h2hi)
          by_cases hL : LociJ0 F (Q45S2LocusJ0_e5 x)
          · exact res (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
              ⟨hk, ht1, not_le.mp h2hi, hL⟩))))))))))
          · simp only [LociJ0, not_or] at hL
            obtain ⟨hs3, hs4, hs2⟩ := hL
            have hs2' : ∀ i j : ZMod 4, i ≠ j →
                ⟪quad (x 6) (x 4) (x 5) (x 2) i - quad (x 6) (x 4) (x 5) (x 2) j, x 4 - x 0⟫ ≠ 0 ∨
                ⟪quad (x 6) (x 4) (x 5) (x 2) i - quad (x 6) (x 4) (x 5) (x 2) j, x 5 - x 0⟫ ≠ 0 := by
              intro i j hij; exact ((not_not.mp hs2) i j hij).symm
            exact fc (q45_Kminus_t_le_one F ha4 s t hs0 ht hst hdecomp hk' ht1 h2lo hs2' hs3 (not_not.mp hs4))
      · exact res (Or.inl (Or.inr (Or.inl ⟨hk, ht1, hw⟩)))
    · rcases sgn_35 F h4 h5 hs0 ht1 hdecomp with ha35 | hw
      · by_cases h2hi : max ⟪x 6, x 3 - x 5⟫ ⟪x 5, x 3 - x 5⟫ ≤ min ⟪x 2, x 3 - x 5⟫ ⟪x 4, x 3 - x 5⟫
        · by_cases hlex : HlexC2 x
          · exact Or.inl (q45_C2_cell_lex F ha35 s t hs0 hdecomp ht1 hlex)
          · exact res (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
              (Or.inl ⟨hk, ht1, h2hi, hlex, tieC2_of_not_hlex h2hi hlex⟩)))))))))))
        · have h2lo : min ⟪x 4, x 3 - x 5⟫ ⟪x 2, x 3 - x 5⟫ < max ⟪x 6, x 3 - x 5⟫ ⟪x 5, x 3 - x 5⟫ := by
            rw [min_comm]; exact not_le.mp h2hi
          by_cases hL : LociJ0 F (Q45S2LocusJ0_e35 x)
          · exact res (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
              (Or.inr ⟨hk, ht1, not_le.mp h2hi, hL⟩)))))))))))
          · simp only [LociJ0, not_or] at hL
            obtain ⟨hs3, hs4, hs2⟩ := hL
            exact fc (q45_Kminus_t_gt_one F ha35 s t hs0 ht hst hdecomp hk' ht1 h2lo (not_not.mp hs2) hs3
              (not_not.mp hs4))
      · exact res (Or.inl (Or.inr (Or.inr (Or.inr hw))))

/-- **Global form** (`s, t` from `lemmaM_quad_decomp`). -/
theorem q45_res (F : S0xFac 9 s0x_S24 x) (h4 : 1 ≤ oblX0 x 4) (h5 : 1 ≤ oblX0 x 5) :
    Gen.LexAny F ∨ Gen.AnyFaceChord F ∨ Q45ResW F := by
  obtain ⟨s, t, hs0, ht, hst, hdecomp⟩ := Minimality.T24.RimFromSigns.lemmaM_quad_decomp F
  rcases q45_res_local F h4 h5 s t hs0 ht hst hdecomp with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr ⟨s, t, hs0, ht, hst, hdecomp, h⟩)

/-! ### The residue lies in the old special set; the new open Prop -/

/-- `Q45ResW` lies in walls ∨ `Q45Special'` (so `OpenSpecialR` is weaker than `OpenSpecialW`). -/
theorem q45ResW_special {F : S0xFac 9 s0x_S24 x} (h : Q45ResW F) :
    (oblX0 x 4 = 1 ∨ oblX0 x 5 = 1) ∨ Q45Special' F := by
  obtain ⟨s, t, -, -, -, -, h⟩ := h
  rcases h with hw | ⟨-, -, -, hl, ht⟩ | ⟨-, -, -, hL⟩ | ⟨-, -, -, hL⟩ | ⟨-, -, -, hl, ht⟩ | ⟨-, -, -, hL⟩ |
      ⟨-, hL⟩ | ⟨-, -, -, hl, ht⟩ | ⟨-, -, -, hL⟩ | ⟨-, -, -, hL⟩ | ⟨-, -, -, hl, ht⟩ | ⟨-, -, -, hL⟩
  · left
    rcases hw with ⟨-, -, h⟩ | ⟨-, -, h⟩ | ⟨-, h⟩ | ⟨h, -⟩
    exacts [Or.inr h, Or.inl h, h, Or.inl h]
  · exact Or.inr (Or.inl ⟨hl, Or.inl ht⟩)
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by
      rcases hL with h | h | h | h
      exacts [Or.inl h, Or.inr (Or.inr (Or.inl h)), Or.inr (Or.inr (Or.inr (Or.inl h))),
        Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))]))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by
      rcases hL with h | h | h
      exacts [Or.inl h, Or.inr (Or.inl h), Or.inr (Or.inr (Or.inl h))]))))))
  · exact Or.inr (Or.inr (Or.inl ⟨hl, Or.inl ht⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by
      rcases hL with h | h | h
      exacts [Or.inl h, Or.inr (Or.inl h), Or.inr (Or.inr (Or.inr (Or.inl h)))]))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by
      rcases hL with h | h | h
      exacts [Or.inl h, Or.inr (Or.inl h), Or.inr (Or.inr (Or.inl h))]))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hl, Or.inl ht⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by
      rcases hL with h | h | h | h
      exacts [Or.inr (Or.inl h), Or.inr (Or.inr (Or.inl h)), Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))),
        Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))]))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by
      rcases hL with h | h | h
      exacts [Or.inl h, Or.inr (Or.inl h), Or.inr (Or.inr (Or.inl h))]))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hl, Or.inl ht⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by
      rcases hL with h | h | h
      exacts [Or.inl h, Or.inr (Or.inl h), Or.inr (Or.inr (Or.inr (Or.inr h)))]))))))

/-- [OPEN] **The special piece, branch-tagged**: off `OB1`, on the corner `a4, a5 ≥ 1` with the four frame
brackets, on the Q45 residue `Q45ResW` (walls only where the branch sign fails; codim-2 corner ties; the codim-1
face-chord loci S3 / S4J0 / S2J0 of the `J0` branches), `HoleFull` fails. -/
def OpenSpecialR : Prop := ∀ (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x), ¬ H24K.SAT.OB1 x →
  1 ≤ oblX0 x 4 → 1 ≤ oblX0 x 5 →
  oblX0 x 4 * oblX6 x 3 - oblX0 x 3 * oblX6 x 4 < 0 →
  0 < oblX0 x 3 * oblX2 x 5 - oblX0 x 5 * oblX2 x 3 →
  0 < oblX0 x 4 * oblX2 x 5 - oblX0 x 5 * oblX2 x 4 →
  0 < oblX0 x 5 * oblX6 x 4 - oblX0 x 4 * oblX6 x 5 →
  Q45ResW F → ¬ HoleFull x F

/-- [PROVED] `OpenSpecialW → OpenSpecialR` (`q45ResW_special`). -/
theorem openSpecialR_of_openSpecialW (h : OpenSpecialW) : OpenSpecialR :=
  fun x F hO h4 h5 b1 b2 b3 b4 hr => h x F hO h4 h5 b1 b2 b3 b4 (q45ResW_special hr)

/-- Every `Hole24` point off `OB1` meets the hypotheses of `OpenSpecialR`. -/
theorem hole24_offOB1_R {F : S0xFac 9 s0x_S24 x} (h : Hole24 x F) (hO : ¬ H24K.SAT.OB1 x)
    (hS : OpenSpecialR) : False := by
  obtain ⟨b1, b2, b3⟩ := resid24_frame_signs h.2.2.1 hO
  have b4 := resid24_b1245 h.2.2.1 hO
  obtain ⟨-, h4, h5⟩ := offWall_of_hole24 h hO
  have hF := holeFull_of_hole24 h
  rcases q45_res F h4 h5 with hL | hA | hr
  · exact hF.1.2.2.2.1 hL
  · exact hF.1.2.2.1 hA
  · exact hS x F hO h4 h5 b1 b2 b3 b4 hr hF

/-- [PROVED] `NamedCoverEmpty` and the branch-tagged special piece rule out every `Hole24` point. -/
theorem not_hole24_of_namedCoverEmpty_R (hN : TwoCone.NamedCoverEmpty) (hS : OpenSpecialR) :
    ∀ (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x), ¬ Hole24 x F := by
  intro x F hH
  by_cases hO : H24K.SAT.OB1 x
  · have hres := TwoCone.hole24_namedCoverResidue hH
    exact hN x F hres.1 hO hres
  · exact hole24_offOB1_R hH hO hS

/-- [PROVED] Generic + branch-tagged special assemble to `Open24`. -/
theorem open24_of_split_R (h1 : OpenOB1) (h2 : OpenSpecialR) : Open24 := by
  intro x fs hh hH
  by_cases hO : H24K.SAT.OB1 x
  · exact h1 x _ hO (holeFull_of_hole24 hH)
  · exact hole24_offOB1_R hH hO h2

end Minimality.T24.OSpec
