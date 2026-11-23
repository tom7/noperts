module

public import Minimality.Type24Hole
public import Minimality.Type24Regions
public import Minimality.Type24ROffTie
public import Minimality.Type24A1Closed
public import Minimality.Type24A2Band
public import Minimality.Type24Wlog
public import Minimality.Type24BSharp
public import Minimality.Type24BUstar2
public import Minimality.Type24W63Radon
public import Minimality.Type24C3One
public import Minimality.Type24E23
public import Minimality.Type24W63Ties
public import Minimality.Type24T2b
public import Minimality.Type24SVCCells
public import Minimality.Type24SVCCellsLex5
public import Minimality.Type24SVCCellsLex_c06
public import Minimality.Type24SVCCellsLex_c10
public import Minimality.Type24SVCCellsLex_c16
public import Minimality.Type24SVCCellsLex_c21
public import Minimality.Type24TBCells
public import Minimality.Type24PairL3u27
public import Minimality.Type24Triple1
public import Minimality.Type24Triple2
public import Minimality.Type24Triple3
public import Minimality.Type24Triple4
public import Minimality.Type24Triple5
public import Minimality.Type24Triple6
public import Minimality.Type24Triple7
public import Minimality.Type24Triple8
public import Minimality.Type24Triple9
public import Minimality.Type24Triple10

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21 Minimality.T24.SAT Minimality.T24.NC Minimality.T24.Z0
  Minimality.T24.Adj

namespace Minimality.T24

/-!
# Type 24: Reduction of `Hole24R` to `Hole24R1`

Combines `Reg.hole24R_cases`, `A19.rOff_closed`, `A1.a1_closed`, `A20.a2_band_closed`, and
`Reg.ba4_to_a` / `ca_to_a1` / `ca2_to_a2` / `cflip_to_brest` to shrink `Hole24R` inside
`Hole24` to `Hole24R1`.
-/

/-- Conjunction of the 19 shape, front, and facing hypotheses of `A20.a2_band_closed`. -/
def A2BandHyp (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  omega5 x * (omega3 x - A7.Lam5 x) < 1 ∧
  oblX0 x 3 ≤ oblX0 x 5 ∧
  oblX6 x 3 < 1 ∧
  oblX6 x 5 < oblX6 x 3 ∧
  A7.Lam5 x < 1 + omega3 x ∧
  oblX0 x 3 * oblX2 x 5 < oblX0 x 5 * oblX2 x 3 ∧
  oblX0 x 3 * oblX6 x 5 ≤ oblX0 x 5 * oblX6 x 3 ∧
  (1 - oblX6 x 3) * (oblX0 x 5 + oblX2 x 5) < (1 - oblX6 x 5) * (oblX0 x 3 + oblX2 x 3) ∧
  0 < ⟪F.N 8, Q24.bW02 x⟫ ∧
  GenQuad.FrontDet (x 1) (x 5) (x 2) (x 3) (Q24.bW02 x) ∧
  GenQuad.FrontDet (x 1) (x 5) (x 2) (x 6) (Q24.bW02 x) ∧
  GenQuad.FrontDet (x 1) (x 3) (x 2) (x 6) (Q24.bW02 x) ∧
  GenQuad.FrontDet (x 5) (x 6) (x 1) (x 3) (Q24.bW02 x) ∧
  GenQuad.FrontDet (x 5) (x 6) (x 2) (x 3) (Q24.bW02 x) ∧
  GenQuad.FrontDet (x 0) (x 6) (x 1) (x 3) (Q24.bW02 x) ∧
  GenQuad.FrontDet (x 0) (x 6) (x 1) (x 5) (Q24.bW02 x) ∧
  GenQuad.FrontDet (x 0) (x 3) (x 1) (x 5) (Q24.bW02 x) ∧
  GenQuad.FrontDet (x 0) (x 3) (x 6) (x 5) (Q24.bW02 x) ∧
  GenQuad.FrontDet (x 6) (x 5) (x 1) (x 3) (Q24.bW02 x) ∧
  0 < ⟪F.N 3, A10.u27 x⟫ ∧
  0 < ⟪F.N 8, A10.u27 x⟫

/-- Residual piece: `OffWall` (outside `OB1`, confined to the walls `a4 = 1 ∨ a5 = 1`). -/
def OffWallRes (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  Hole24R x F ∧ Reg.OffWall x

/-- Residual piece: `A1` inside `OB1`, missing at least one of the three `a1_closed` sample bundles. -/
def A1Res (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  Hole24R x F ∧ H24K.SAT.OB1 x ∧ Reg.A1 x F ∧
    ¬ ((if 0 < det24 x then A1.A1TieSmall x F else A1.A1TieSmall (fun i => -x i) (A1.facNeg F)) ∧
       (if 0 < det24 x then A1.A1E25Small x F else A1.A1E25Small (fun i => -x i) (A1.facNeg F)) ∧
       A1.A1Z54Sample x F)

/-- Residual piece: `A2` inside `OB1`, outside `a2_band_closed` (`¬ A2BandHyp`). -/
def A2Res (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  Hole24R x F ∧ H24K.SAT.OB1 x ∧ Reg.A2 x F ∧ ¬ A2BandHyp x F

/-- Residual piece: codimension-2 wall corner `a4 = a5 = 1` inside `OB1`, outside `a2_band_closed_gen`. -/
def WallA45Res (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  Hole24R x F ∧ H24K.SAT.OB1 x ∧ oblX0 x 5 = 1 ∧ oblX0 x 4 = 1 ∧ ¬ A2BandHyp x F

/-- Residual piece: wall `a5 = 1` with `a4 < 1` inside `OB1`, outside `ustar_closed_W26_full` and `a2_band_closed_gen`. -/
def WallA5BRes (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  Hole24R x F ∧ H24K.SAT.OB1 x ∧ oblX0 x 5 = 1 ∧ oblX0 x 4 < 1 ∧
    ¬ (oblX6 x 3 < 1 ∧ ⟪F.N 8, A10.ustar x⟫ < 0 ∧
       max 0 ⟪x 6 - x 1, A10.ustar x⟫ < ⟪x 5 - x 1, A10.ustar x⟫) ∧
    ¬ A2BandHyp x F

/-- Hypothesis bundle for `Type24BSharp.ustar_closed_W26_full`. -/
def UstarW26Hyp (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  oblX6 x 3 < 1 ∧ A10.Dl x < 0 ∧ ⟪F.N 8, A10.ustar x⟫ < 0 ∧ A7.nB x < A7.nC x ∧
    max 0 ⟪x 6 - x 1, A10.ustar x⟫ < ⟪x 5 - x 1, A10.ustar x⟫

/-- Hypothesis bundle for `Type24BUstar.ustar_collapse`. -/
def UstarHyp (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  oblX6 x 3 < 1 ∧ A10.Dl x < 0 ∧ ⟪F.N 8, A10.ustar x⟫ < 0 ∧
    max 0 ⟪x 6 - x 1, A10.ustar x⟫ < min ⟪x 3 - x 1, A10.ustar x⟫ ⟪x 5 - x 1, A10.ustar x⟫

/-- Hypothesis bundle for `Type24BUstar2.ustar2_collapse`. -/
def Ustar2Hyp (x : Fin 7 → ℝ³) (_F : S0xFac 9 s0x_S24 x) : Prop :=
  oblX6 x 4 < 1 ∧ A10.Dl4 x < 0 ∧ 0 < oblX0 x 4 * oblX2 x 3 - oblX0 x 3 * oblX2 x 4 ∧
    0 < A10.nu346b x ∧ 0 < A10.Qu2 x ∧
    max 0 ⟪x 6 - x 1, A10.ustar2 x⟫ <
      min ⟪x 4 - x 1, A10.ustar2 x⟫ (min ⟪x 3 - x 1, A10.ustar2 x⟫ ⟪x 5 - x 1, A10.ustar2 x⟫)

/-- Hypothesis bundle for `M4cType24.splitAny24_E0416`. -/
def E0416Hyp (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  F.f 3 (x 6) < F.f 3 (x 1) ∧
    (1 - oblX0 x 4) * (1 - oblX2 x 5) < oblX0 x 5 * oblX2 x 4 ∧
    max 0 (max ⟪x 2 - x 1, x 4 - x 0⟫ ⟪x 5 - x 1, x 4 - x 0⟫) < ⟪x 4 - x 1, x 4 - x 0⟫ ∧
    ⟪x 4 - x 1, x 4 - x 0⟫ < ⟪x 6 - x 1, x 4 - x 0⟫

/-- Residual piece: `BE0416` inside `OB1`, outside `ustar_closed_W26_full`, `ustar_collapse`, `ustar2_collapse`, and `splitAny24_E0416`. -/
def BE0416Res (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  Hole24R x F ∧ H24K.SAT.OB1 x ∧ Reg.BE0416 x F ∧
    ¬ UstarW26Hyp x F ∧ ¬ UstarHyp x F ∧ ¬ Ustar2Hyp x F ∧ ¬ E0416Hyp x F

/-- Residual piece: `BRest` inside `OB1`, outside `ustar_closed_W26_full`, `ustar_collapse`, and `ustar2_collapse`. -/
def BRestRes (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  Hole24R x F ∧ H24K.SAT.OB1 x ∧ Reg.BRest x F ∧
    ¬ UstarW26Hyp x F ∧ ¬ UstarHyp x F ∧ ¬ Ustar2Hyp x F

/-- Residual piece: self-twin part of `CC` (`a4 < 1`, `τ ≥ 1`) inside `OB1`. -/
def CCSelfRes (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  Hole24R x F ∧ H24K.SAT.OB1 x ∧ Reg.CC x F ∧ oblX0 x 4 < 1 ∧ F.f 6 (x 4) ≤ F.f 6 (x 0)

/-- Shrunken residual of `Hole24R` after `rOff_closed`, `a1_closed`, `a2_band_closed`, `wall` reductions, and `pi24` wlog. -/
def Hole24R1 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  OffWallRes x F ∨
  A1Res x F ∨ A2Res x F ∨ WallA45Res x F ∨ WallA5BRes x F ∨
  BE0416Res x F ∨ BRestRes x F ∨
  CCSelfRes x F ∨
  A1Res (x ∘ Sym.pi24) (Sym.sym24 F) ∨
  A2Res (x ∘ Sym.pi24) (Sym.sym24 F) ∨
  WallA5BRes (x ∘ Sym.pi24) (Sym.sym24 F) ∨
  BRestRes (x ∘ Sym.pi24) (Sym.sym24 F)

private theorem pi24_invol (x : Fin 7 → ℝ³) : (x ∘ Sym.pi24) ∘ Sym.pi24 = x := by
  funext i; fin_cases i <;> rfl

private theorem sig24_invol (t : Fin 9) : Sym.sig24 (Sym.sig24 t) = t := by
  fin_cases t <;> rfl

private theorem transport_sym24_invol {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (P : ∀ {y : Fin 7 → ℝ³}, S0xFac 9 s0x_S24 y → Prop) (h : P F) :
    P (Sym.sym24 (Sym.sym24 F)) := by
  have hgen : ∀ (y : Fin 7 → ℝ³), y = x → ∀ (G : S0xFac 9 s0x_S24 y),
      G.f = F.f → G.N = F.N → P G := by
    rintro y rfl ⟨f, N, hN', hz, hn⟩ rfl rfl
    exact h
  exact hgen _ (pi24_invol x) (Sym.sym24 (Sym.sym24 F))
    (funext fun t => congrArg F.f (sig24_invol t))
    (funext fun t => congrArg F.N (sig24_invol t))

private theorem hole24R_of_comp_pi24 {x : Fin 7 → ℝ³} {F : S0xFac 9 s0x_S24 x}
    (h : Hole24R (x ∘ Sym.pi24) (Sym.sym24 F)) : Hole24R x F := by
  obtain ⟨hC, hR, hQ, hA, hL, hS⟩ := Reg.hole24R_comp_pi24 h
  rw [pi24_invol] at hC hR
  refine ⟨hC, hR, ?_, ?_, ?_, ?_⟩
  · intro hq; exact hQ (transport_sym24_invol F (fun G => Q45HalfPred G) hq)
  · intro ha; exact hA (transport_sym24_invol F (fun G => RCell.AnyFaceChord G) ha)
  · intro hl; exact hL (transport_sym24_invol F (fun G => RCell.LexAny G) hl)
  · intro hs; exact hS (transport_sym24_invol F (fun G => RCell.SplitAny24 G) hs)

/-- Every point of `Hole24R1` lies in `Hole24R`. -/
theorem hole24R_of_hole24R1 {x : Fin 7 → ℝ³} {F : S0xFac 9 s0x_S24 x}
    (h : Hole24R1 x F) : Hole24R x F := by
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · exact h.1
  · exact h.1
  · exact h.1
  · exact h.1
  · exact h.1
  · exact h.1
  · exact h.1
  · exact h.1
  · exact hole24R_of_comp_pi24 h.1
  · exact hole24R_of_comp_pi24 h.1
  · exact hole24R_of_comp_pi24 h.1
  · exact hole24R_of_comp_pi24 h.1

private theorem close_A1 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (hR : Hole24R x F)
    (hO : H24K.SAT.OB1 x) (hA1 : Reg.A1 x F) :
    IsRupert (univ.image x) ∨ A1Res x F := by
  by_cases hS :
      (if 0 < det24 x then A1.A1TieSmall x F else A1.A1TieSmall (fun i => -x i) (A1.facNeg F)) ∧
      (if 0 < det24 x then A1.A1E25Small x F else A1.A1E25Small (fun i => -x i) (A1.facNeg F)) ∧
      A1.A1Z54Sample x F
  · exact Or.inl (A1.a1_closed F hR hA1 hO hS.1 hS.2.1 hS.2.2)
  · exact Or.inr ⟨hR, hO, hA1, hS⟩

private theorem close_A2_band {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (hR : Hole24R x F)
    (hO : H24K.SAT.OB1 x) (hB : A2BandHyp x F) : False := by
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, u3, u8⟩ := hB
  rcases A20.a2_band_closed_gen F hR.1 hO b1 b2 b3 b4 b5 b6 b7 b8 b9
      ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, f10⟩ u3 u8 with hL | hS
  · exact hR.2.2.2.2.1 hL
  · exact hR.2.2.2.2.2 hS

private theorem close_A2 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (hR : Hole24R x F)
    (hO : H24K.SAT.OB1 x) (hA2 : Reg.A2 x F) :
    A2Res x F := by
  by_contra hnot
  have hB : A2BandHyp x F := by
    by_contra hnb
    exact hnot ⟨hR, hO, hA2, hnb⟩
  exact close_A2_band F hR hO hB

private theorem close_wallA45 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (hR : Hole24R x F)
    (hO : H24K.SAT.OB1 x) (h5 : oblX0 x 5 = 1) (h4 : oblX0 x 4 = 1) :
    WallA45Res x F := by
  by_contra hnot
  have hB : A2BandHyp x F := by
    by_contra hnb
    exact hnot ⟨hR, hO, h5, h4, hnb⟩
  exact close_A2_band F hR hO hB

private theorem close_wallA5_a4lt {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (hR : Hole24R x F)
    (hO : H24K.SAT.OB1 x) (h5 : oblX0 x 5 = 1) (h4 : oblX0 x 4 < 1) :
    WallA5BRes x F := by
  by_contra hnot
  have hU : oblX6 x 3 < 1 ∧ ⟪F.N 8, A10.ustar x⟫ < 0 ∧
      max 0 ⟪x 6 - x 1, A10.ustar x⟫ < ⟪x 5 - x 1, A10.ustar x⟫ := by
    by_contra hnu
    have hB : A2BandHyp x F := by
      by_contra hnb
      exact hnot ⟨hR, hO, h5, h4, hnu, hnb⟩
    exact close_A2_band F hR hO hB
  rcases A10.ustar_closed_W26_full F ⟨hR.1, h5.le, hU.1, A10.dl_neg_of_wallA5 F h5, hU.2.1,
      hO.1, hO.2.1⟩ hO.2.2 (A10.nB_lt_nC_of_wallA5_a4lt F h5 h4) hU.2.2 with hL | hS
  · exact hR.2.2.2.2.1 hL
  · exact hR.2.2.2.2.2 hS

private theorem close_B_ustar {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (hR : Hole24R x F)
    (hO : H24K.SAT.OB1 x) (ha5 : oblX0 x 5 ≤ 1)
    (hB : UstarW26Hyp x F ∨ UstarHyp x F ∨ Ustar2Hyp x F) : False := by
  rcases hB with ⟨hc3, hD, h8, hn, hz5⟩ | ⟨hc3, hD, h8, hz⟩ | ⟨hc4, hD4, hΔ, hnu, hQ, hz⟩
  · rcases A10.ustar_closed_W26_full F ⟨hR.1, ha5, hc3, hD, h8, hO.1, hO.2.1⟩
        hO.2.2 hn hz5 with hL | hS
    · exact hR.2.2.2.2.1 hL
    · exact hR.2.2.2.2.2 hS
  · rcases A10.ustar_collapse F ⟨hR.1, ha5, hc3, hD, h8, hO.1, hO.2.1⟩ hz with hL | hS
    · exact hR.2.2.2.2.1 hL
    · exact hR.2.2.2.2.2 hS
  · rcases A10.ustar2_collapse F hR.1 ha5 hc4 hD4 hΔ hnu hQ hO.1 hO.2.1 hz with hL | hS
    · exact hR.2.2.2.2.1 hL
    · exact hR.2.2.2.2.2 hS

private theorem close_BE0416 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (hR : Hole24R x F)
    (hO : H24K.SAT.OB1 x) (hBE : Reg.BE0416 x F) : BE0416Res x F := by
  by_contra hnot
  by_cases h1 : UstarW26Hyp x F
  · exact close_B_ustar F hR hO hBE.1.le (Or.inl h1)
  by_cases h2 : UstarHyp x F
  · exact close_B_ustar F hR hO hBE.1.le (Or.inr (Or.inl h2))
  by_cases h3 : Ustar2Hyp x F
  · exact close_B_ustar F hR hO hBE.1.le (Or.inr (Or.inr h3))
  by_cases h4 : E0416Hyp x F
  · exact hR.2.2.2.2.2 (A8.splitAny24_E0416 F hR.1 hBE.2.2.1 h4.1 hBE.2.2.2.2 h4.2.1 h4.2.2)
  exact hnot ⟨hR, hO, hBE, h1, h2, h3, h4⟩

private theorem close_BRest {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (hR : Hole24R x F)
    (hO : H24K.SAT.OB1 x) (hBR : Reg.BRest x F) : BRestRes x F := by
  by_contra hnot
  by_cases h1 : UstarW26Hyp x F
  · exact close_B_ustar F hR hO hBR.1.le (Or.inl h1)
  by_cases h2 : UstarHyp x F
  · exact close_B_ustar F hR hO hBR.1.le (Or.inr (Or.inl h2))
  by_cases h3 : Ustar2Hyp x F
  · exact close_B_ustar F hR hO hBR.1.le (Or.inr (Or.inr h3))
  exact hnot ⟨hR, hO, hBR, h1, h2, h3⟩

/-- **Reduction of `Hole24R` to `Hole24R1`**: closes `ROff`, `A1` (modulo its 3 sample bundles),
`A2` (modulo `A2BandHyp`), `WallA5`/`WallA4C` (via `pi24`, `ustar_closed_W26_full`, and `a2_band_closed_gen`),
and transports `BA4`, `CA`, `CA2`, `CFlip` via `pi24`. -/
theorem hole24R_reduce {x : Fin 7 → ℝ³} {F : S0xFac 9 s0x_S24 x} (hR : Hole24R x F) :
    IsRupert (univ.image x) ∨ Hole24R1 x F := by
  rcases Reg.hole24R_cases hR with hRo | hOW | ⟨hO, hreg⟩
  · exact (A19.rOff_closed hR hRo).elim
  · exact Or.inr (Or.inl ⟨hR, hOW⟩)
  · rcases hreg with hA1 | hA2 | hWA5 | hBA4 | hBE | hBR | hCA | hCA2 | hCB | hCC
    · rcases close_A1 F hR hO hA1 with hRup | hres
      · exact Or.inl hRup
      · exact Or.inr (Or.inr (Or.inl hres))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (close_A2 F hR hO hA2))))
    · rcases lt_trichotomy (oblX0 x 4) 1 with h4 | h4 | h4
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (close_wallA5_a4lt F hR hO hWA5 h4))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (close_wallA45 F hR hO hWA5 h4)))))
      · have hR' := Reg.hole24R_comp_pi24 hR
        have hO' := (A19.ob1_comp_pi24 x).2 hO
        rcases Reg.wallA5_a4gt_to_a hWA5 h4 with hA1' | hA2'
        · rcases close_A1 (Sym.sym24 F) hR' hO' hA1' with hRup | hres
          · exact Or.inl (Sym.isRupert_of_comp_pi24 hRup)
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hres)))))))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
            (close_A2 (Sym.sym24 F) hR' hO' hA2')))))))))))
    · have hR' := Reg.hole24R_comp_pi24 hR
      have hO' := (A19.ob1_comp_pi24 x).2 hO
      rcases Reg.ba4_to_a hBA4 with hA1' | hA2'
      · rcases close_A1 (Sym.sym24 F) hR' hO' hA1' with hRup | hres
        · exact Or.inl (Sym.isRupert_of_comp_pi24 hRup)
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hres)))))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
          (close_A2 (Sym.sym24 F) hR' hO' hA2')))))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (close_BE0416 F hR hO hBE)))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (close_BRest F hR hO hBR))))))))
    · have hR' := Reg.hole24R_comp_pi24 hR
      have hO' := (A19.ob1_comp_pi24 x).2 hO
      rcases close_A1 (Sym.sym24 F) hR' hO' (Reg.ca_to_a1 hCA) with hRup | hres
      · exact Or.inl (Sym.isRupert_of_comp_pi24 hRup)
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hres)))))))))
    · have hR' := Reg.hole24R_comp_pi24 hR
      have hO' := (A19.ob1_comp_pi24 x).2 hO
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        (close_A2 (Sym.sym24 F) hR' hO' (Reg.ca2_to_a2 hCA2))))))))))))
    · rcases lt_or_eq_of_le hCB.2.2.1 with h4 | h4
      · have hR' := Reg.hole24R_comp_pi24 hR
        have hO' := (A19.ob1_comp_pi24 x).2 hO
        exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
          Or.inr <| Or.inr <| Or.inr <| Or.inr
          (close_BRest (Sym.sym24 F) hR' hO' (Reg.cflip_to_brest (Reg.cb_a4lt_cflip hCB h4)))
      · have hR' := Reg.hole24R_comp_pi24 hR
        have hO' := (A19.ob1_comp_pi24 x).2 hO
        have hw := Reg.wallA4C_to_wallA5 hCB.1 hCB.2.1 h4
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
          (close_wallA5_a4lt (Sym.sym24 F) hR' hO' hw.1 hw.2.1))))))))))))
    · rcases lt_or_eq_of_le hCC.2.2.1 with h4 | h4
      · rcases lt_or_ge (F.f 6 (x 0)) (F.f 6 (x 4)) with ht | ht
        · have hR' := Reg.hole24R_comp_pi24 hR
          have hO' := (A19.ob1_comp_pi24 x).2 hO
          exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
            Or.inr <| Or.inr <| Or.inr <| Or.inr
            (close_BRest (Sym.sym24 F) hR' hO' (Reg.cflip_to_brest (Reg.cc_tau_cflip hCC h4 ht)))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
            ⟨hR, hO, hCC, h4, ht⟩))))))))
      · have hR' := Reg.hole24R_comp_pi24 hR
        have hO' := (A19.ob1_comp_pi24 x).2 hO
        have hw := Reg.wallA4C_to_wallA5 hCC.1 hCC.2.1 h4
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
          (close_wallA5_a4lt (Sym.sym24 F) hR' hO' hw.1 hw.2.1))))))))))))

/-- Further shrunken residual of `Hole24R1` removing `{1 < oblX6 x 3, 0 < mustar x}` off the
`w63`-failure star locus `W63Star x`, via `A20.w63_closes_star`. -/
def Hole24R2 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  Hole24R1 x F ∧
    ¬ (1 < oblX6 x 3 ∧ 0 < A20.mustar x ∧ ¬ A20.W63Star x)

/-- Every point of `Hole24R1` reduces to `Hole24R2`. -/
theorem hole24R1_reduce {x : Fin 7 → ℝ³} {F : S0xFac 9 s0x_S24 x}
    (h : Hole24R1 x F) : Hole24R2 x F := by
  refine ⟨h, ?_⟩
  rintro ⟨hc3, hmu, hnot⟩
  have hR := hole24R_of_hole24R1 h
  exact hR.2.2.2.2.1 (A20.w63_closes_star F hc3 hmu hnot)

/-- Further shrunken residual of `Hole24R2` removing the `{c3 = 1}` stratum off the depth ties on
`{0,1,2,3,4,6}` at `w63`, via `A20.c3eq1_closed` (no sample facts since C3FACTS). -/
def Hole24R3 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  Hole24R2 x F ∧
    ¬ (oblX6 x 3 = 1 ∧
      ∀ i ∈ ({0, 1, 2, 3, 4, 6} : Finset (Fin 7)),
        ∀ j ∈ ({0, 1, 2, 3, 4, 6} : Finset (Fin 7)),
        i ≠ j → ⟪x i, x 3 - x 6⟫ ≠ ⟪x j, x 3 - x 6⟫)

/-- Every point of `Hole24R2` reduces to `Hole24R3`. -/
theorem hole24R2_reduce {x : Fin 7 → ℝ³} {F : S0xFac 9 s0x_S24 x}
    (h : Hole24R2 x F) : Hole24R3 x F := by
  refine ⟨h, ?_⟩
  rintro ⟨hc3, hgen⟩
  have hR := hole24R_of_hole24R1 h.1
  exact hR.2.2.2.2.1 (A20.c3eq1_closed F hR.1 hc3 hgen)

/-- Further shrunken residual of `Hole24R3` removing `{1 < oblX2 x 3, 0 < mu23 x}` off the
`E23`-failure star locus `E23Star x`, via `A20.e23_closes_star`. -/
def Hole24R4 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  Hole24R3 x F ∧
    ¬ (1 < oblX2 x 3 ∧ 0 < A20.mu23 x ∧ ¬ A20.E23Star x)

/-- Every point of `Hole24R3` reduces to `Hole24R4`. -/
theorem hole24R3_reduce {x : Fin 7 → ℝ³} {F : S0xFac 9 s0x_S24 x}
    (h : Hole24R3 x F) : Hole24R4 x F := by
  refine ⟨h, ?_⟩
  rintro ⟨hb3, hmu, hnot⟩
  have hR := hole24R_of_hole24R1 h.1.1
  exact hR.2.2.2.2.1 (A20.e23_closes_star F hb3 hmu hnot)

/-- Further shrunken residual of `Hole24R4` removing generic wall points
`{1 < oblX6 x 3, mustar x = 0}` via `A20.w63_closes_wall` and
`{1 < oblX2 x 3, mu23 x = 0}` via `A20.e23_closes_wall`. -/
def Hole24R5 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  Hole24R4 x F ∧
    ¬ (1 < oblX6 x 3 ∧ A20.mustar x = 0 ∧
      ∀ i ∈ ({0, 2, 3, 4, 5, 6} : Finset (Fin 7)),
        ∀ j ∈ ({0, 2, 3, 4, 5, 6} : Finset (Fin 7)),
        i ≠ j → ⟪x i, x 3 - x 6⟫ ≠ ⟪x j, x 3 - x 6⟫) ∧
    ¬ (1 < oblX2 x 3 ∧ A20.mu23 x = 0 ∧
      ∀ i ∈ ({0, 2, 3, 4, 5, 6} : Finset (Fin 7)),
        ∀ j ∈ ({0, 2, 3, 4, 5, 6} : Finset (Fin 7)),
        i ≠ j → ⟪x i, x 3 - x 2⟫ ≠ ⟪x j, x 3 - x 2⟫)

/-- Every point of `Hole24R4` reduces to `Hole24R5`. -/
theorem hole24R4_reduce {x : Fin 7 → ℝ³} {F : S0xFac 9 s0x_S24 x}
    (h : Hole24R4 x F) : Hole24R5 x F := by
  refine ⟨h, ?_, ?_⟩
  · rintro ⟨hc3, hmu, hgen⟩
    have hR := hole24R_of_hole24R1 h.1.1.1
    exact hR.2.2.2.2.1 (A20.w63_closes_wall F hc3 hmu hgen)
  · rintro ⟨hb3, hmu, hgen⟩
    have hR := hole24R_of_hole24R1 h.1.1.1
    exact hR.2.2.2.2.1 (A20.e23_closes_wall F hb3 hmu hgen)

/-- Shrunken `Q45` residual removing the same five A20/DI loci as `Hole24R2..R5`:
`w63` off `W63Star`, `c3 = 1`, `E23` off `E23Star`, and the two walls
(`1 < c3, mu* = 0` and `1 < b3, mu23 = 0`). -/
def Hole24Q45R (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  Hole24Q45Special x F ∧
    ¬ (1 < oblX6 x 3 ∧ 0 < A20.mustar x ∧ ¬ A20.W63Star x) ∧
    ¬ (oblX6 x 3 = 1 ∧
      ∀ i ∈ ({0, 1, 2, 3, 4, 6} : Finset (Fin 7)), ∀ j ∈ ({0, 1, 2, 3, 4, 6} : Finset (Fin 7)),
        i ≠ j → ⟪x i, x 3 - x 6⟫ ≠ ⟪x j, x 3 - x 6⟫) ∧
    ¬ (1 < oblX2 x 3 ∧ 0 < A20.mu23 x ∧ ¬ A20.E23Star x) ∧
    ¬ (1 < oblX6 x 3 ∧ A20.mustar x = 0 ∧
      ∀ i ∈ ({0, 2, 3, 4, 5, 6} : Finset (Fin 7)), ∀ j ∈ ({0, 2, 3, 4, 5, 6} : Finset (Fin 7)),
        i ≠ j → ⟪x i, x 3 - x 6⟫ ≠ ⟪x j, x 3 - x 6⟫) ∧
    ¬ (1 < oblX2 x 3 ∧ A20.mu23 x = 0 ∧
      ∀ i ∈ ({0, 2, 3, 4, 5, 6} : Finset (Fin 7)), ∀ j ∈ ({0, 2, 3, 4, 5, 6} : Finset (Fin 7)),
        i ≠ j → ⟪x i, x 3 - x 2⟫ ≠ ⟪x j, x 3 - x 2⟫)

/-- Every point of `Hole24Q45Special` reduces to `Hole24Q45R`. -/
theorem hole24Q45_reduce {x : Fin 7 → ℝ³} {F : S0xFac 9 s0x_S24 x}
    (hQ : Hole24Q45Special x F) : Hole24Q45R x F := by
  refine ⟨hQ, ?_, ?_, ?_, ?_, ?_⟩
  · rintro ⟨hc3, hmu, hnot⟩
    exact hQ.2.2.2.2.2.1 (A20.w63_closes_star F hc3 hmu hnot)
  · rintro ⟨hc3, hgen⟩
    exact hQ.2.2.2.2.2.1 (A20.c3eq1_closed F hQ.1 hc3 hgen)
  · rintro ⟨hb3, hmu, hnot⟩
    exact hQ.2.2.2.2.2.1 (A20.e23_closes_star F hb3 hmu hnot)
  · rintro ⟨hc3, hmu, hgen⟩
    exact hQ.2.2.2.2.2.1 (A20.w63_closes_wall F hc3 hmu hgen)
  · rintro ⟨hb3, hmu, hgen⟩
    exact hQ.2.2.2.2.2.1 (A20.e23_closes_wall F hb3 hmu hgen)

private theorem mkFac24_linear_eq {x : Fin 7 → ℝ³} (fs : Fin 9 → ℝ³ →ᵃ[ℝ] ℝ)
    (hh : ∀ t i, (i ∈ s0x_S24 t → fs t (x i) = 0) ∧ (i ∉ s0x_S24 t → fs t (x i) < 0))
    (s : Fin 9) (u : ℝ³) :
    ⟪(mkFac24 fs hh).N s, u⟫ = (fs s).linear u := by
  have h1 := (mkFac24 fs hh).hN s u 0
  have h2 : (fs s).linear u = fs s u - fs s 0 := by simpa using (fs s).linear_apply_vsub u 0
  have h3 : (mkFac24 fs hh).f s = fs s := rfl
  rw [h2, ← h3, ← sub_zero u, ← h1]
  simp [sub_zero]

private theorem facetCell24_of_n346 {x : Fin 7 → ℝ³} (fs : Fin 9 → ℝ³ →ᵃ[ℝ] ℝ)
    (hh : ∀ t i, (i ∈ s0x_S24 t → fs t (x i) = 0) ∧ (i ∉ s0x_S24 t → fs t (x i) < 0))
    (hu : ∃ u : ℝ³, 0 < ⟪(mkFac24 fs hh).N 8, u⟫ ∧ ⟪(mkFac24 fs hh).N 3, u⟫ < 0 ∧
      ⟪(mkFac24 fs hh).N 4, u⟫ < 0 ∧ ⟪(mkFac24 fs hh).N 7, u⟫ < 0) :
    FacetCell24 fs := by
  obtain ⟨u, h8, h3, h4, h7⟩ := hu
  refine ⟨8, u, by rwa [← mkFac24_linear_eq fs hh 8 u], ?_⟩
  intro s hs
  rw [← mkFac24_linear_eq fs hh s u]
  fin_cases s <;> first | exact absurd hs (by decide) | exact h3 | exact h4 | exact h7

private theorem facetCell24_of_n235 {x : Fin 7 → ℝ³} (fs : Fin 9 → ℝ³ →ᵃ[ℝ] ℝ)
    (hh : ∀ t i, (i ∈ s0x_S24 t → fs t (x i) = 0) ∧ (i ∉ s0x_S24 t → fs t (x i) < 0))
    (hu : ∃ u : ℝ³, 0 < ⟪(mkFac24 fs hh).N 6, u⟫ ∧ ⟪(mkFac24 fs hh).N 3, u⟫ < 0 ∧
      ⟪(mkFac24 fs hh).N 2, u⟫ < 0 ∧ ⟪(mkFac24 fs hh).N 7, u⟫ < 0) :
    FacetCell24 fs := by
  obtain ⟨u, h6, h3, h2, h7⟩ := hu
  refine ⟨6, u, by rwa [← mkFac24_linear_eq fs hh 6 u], ?_⟩
  intro s hs
  rw [← mkFac24_linear_eq fs hh s u]
  fin_cases s <;> first | exact absurd hs (by decide) | exact h2 | exact h3 | exact h7

/-- Combining `W63Star` with `t2b_closes`, `{1 < oblX6 x 3, 0 < mustar x}` gives `LexAny` unless
`FacetCell24 fs` holds. -/
theorem w63_closes_star_or_facetCell {x : Fin 7 → ℝ³} (fs : Fin 9 → ℝ³ →ᵃ[ℝ] ℝ)
    (hh : ∀ t i, (i ∈ s0x_S24 t → fs t (x i) = 0) ∧ (i ∉ s0x_S24 t → fs t (x i) < 0))
    (hc3 : 1 < oblX6 x 3) (hmu : 0 < A20.mustar x) :
    Gen.LexAny (mkFac24 fs hh) ∨ FacetCell24 fs := by
  by_cases hW : A20.W63Star x
  · rcases A20.t2b_closes (mkFac24 fs hh) hW.1 hW.2.1 with hLex | hu
    · exact Or.inl hLex
    · exact Or.inr (facetCell24_of_n346 fs hh hu)
  · exact Or.inl (A20.w63_closes_star (mkFac24 fs hh) hc3 hmu hW)

/-- Combining `E23Star` with `t2b_closes_e23`, `{1 < oblX2 x 3, 0 < mu23 x}` gives `LexAny` unless
`FacetCell24 fs` holds. -/
theorem e23_closes_star_or_facetCell {x : Fin 7 → ℝ³} (fs : Fin 9 → ℝ³ →ᵃ[ℝ] ℝ)
    (hh : ∀ t i, (i ∈ s0x_S24 t → fs t (x i) = 0) ∧ (i ∉ s0x_S24 t → fs t (x i) < 0))
    (hb3 : 1 < oblX2 x 3) (hmu : 0 < A20.mu23 x) :
    Gen.LexAny (mkFac24 fs hh) ∨ FacetCell24 fs := by
  by_cases hE : A20.E23Star x
  · rcases A20.t2b_closes_e23 (mkFac24 fs hh) hE.1 hE.2.1 with hLex | hu
    · exact Or.inl hLex
    · exact Or.inr (facetCell24_of_n235 fs hh hu)
  · exact Or.inl (A20.e23_closes_star (mkFac24 fs hh) hb3 hmu hE)

/-! ### Non-triangle SVC cells (`Type24SVCCells`) and two-view pair closure (`Type24PairL3u27`) -/

def Cell_012_0345_zpmzppmpp (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  ∃ w : ℝ³, ⟪F.N 0, w⟫ = 0 ∧ 0 < ⟪F.N 1, w⟫ ∧ ⟪F.N 2, w⟫ < 0 ∧ ⟪F.N 3, w⟫ = 0 ∧
    0 < ⟪F.N 4, w⟫ ∧ 0 < ⟪F.N 5, w⟫ ∧ ⟪F.N 6, w⟫ < 0 ∧ 0 < ⟪F.N 7, w⟫ ∧ 0 < ⟪F.N 8, w⟫

def Cell_0345_236_ppmzppmzp (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  ∃ w : ℝ³, 0 < ⟪F.N 0, w⟫ ∧ ⟪F.N 2, w⟫ < 0 ∧ ⟪F.N 3, w⟫ = 0 ∧
    0 < ⟪F.N 4, w⟫ ∧ 0 < ⟪F.N 5, w⟫ ∧ ⟪F.N 6, w⟫ < 0 ∧ ⟪F.N 7, w⟫ = 0 ∧ 0 < ⟪F.N 8, w⟫

def Cell_0345_236_pppzmppzm (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  ∃ w : ℝ³, 0 < ⟪F.N 1, w⟫ ∧ 0 < ⟪F.N 2, w⟫ ∧ ⟪F.N 3, w⟫ = 0 ∧ ⟪F.N 4, w⟫ < 0 ∧
    0 < ⟪F.N 5, w⟫ ∧ 0 < ⟪F.N 6, w⟫ ∧ ⟪F.N 7, w⟫ = 0 ∧ ⟪F.N 8, w⟫ < 0

def Cell_025_046_ppzmzpppp (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  ∃ w : ℝ³, 0 < ⟪F.N 0, w⟫ ∧ 0 < ⟪F.N 1, w⟫ ∧ ⟪F.N 2, w⟫ = 0 ∧ ⟪F.N 3, w⟫ < 0 ∧
    ⟪F.N 4, w⟫ = 0 ∧ 0 < ⟪F.N 6, w⟫ ∧ 0 < ⟪F.N 8, w⟫

def Cell_025_235_ppzmppzpp (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  0 < ⟪F.N 4, x 2 - x 5⟫ ∧ 0 < ⟪F.N 8, x 2 - x 5⟫

def Cell_025_346_ppzmppppz (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  ∃ w : ℝ³, 0 < ⟪F.N 0, w⟫ ∧ ⟪F.N 2, w⟫ = 0 ∧ ⟪F.N 3, w⟫ < 0 ∧ 0 < ⟪F.N 4, w⟫ ∧
    0 < ⟪F.N 6, w⟫ ∧ 0 < ⟪F.N 7, w⟫ ∧ ⟪F.N 8, w⟫ = 0 ∧
    ⟪F.N 2, F.N 2⟫ * ⟪F.N 8, F.N 8⟫ - ⟪F.N 2, F.N 8⟫ ^ 2 ≠ 0

def Cell_046_235_pppmzpzpp (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  ∃ w : ℝ³, 0 < ⟪F.N 1, w⟫ ∧ 0 < ⟪F.N 2, w⟫ ∧ ⟪F.N 3, w⟫ < 0 ∧ ⟪F.N 4, w⟫ = 0 ∧
    ⟪F.N 6, w⟫ = 0 ∧ 0 < ⟪F.N 7, w⟫ ∧ 0 < ⟪F.N 8, w⟫ ∧
    ⟪F.N 4, F.N 4⟫ * ⟪F.N 6, F.N 6⟫ - ⟪F.N 4, F.N 6⟫ ^ 2 ≠ 0

def Cell_046_346_mmmpzmmmz (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  ⟪F.N 2, x 4 - x 6⟫ < 0 ∧ ⟪F.N 6, x 4 - x 6⟫ < 0

def Cell_235_236_pppmmpzzm (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  0 < ⟪F.N 1, x 2 - x 3⟫ ∧ ⟪F.N 4, x 2 - x 3⟫ < 0 ∧
    ⟪x 5, x 2 - x 3⟫ ≠ ⟪x 6, x 2 - x 3⟫

def Cell_235_346_pppmppzpz (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  ∃ w : ℝ³, 0 < ⟪F.N 2, w⟫ ∧ ⟪F.N 3, w⟫ < 0 ∧ 0 < ⟪F.N 4, w⟫ ∧ ⟪F.N 6, w⟫ = 0 ∧
    0 < ⟪F.N 7, w⟫ ∧ ⟪F.N 8, w⟫ = 0

def Cell_236_346_mmppmmpzz (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  ⟪F.N 0, x 3 - x 6⟫ < 0 ∧ 0 < ⟪F.N 2, x 3 - x 6⟫ ∧
    ⟪x 2, x 3 - x 6⟫ ≠ ⟪x 4, x 3 - x 6⟫

def Cell_016_0345_pzpzmpppm (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  ∃ w : ℝ³, 0 < ⟪F.N 0, w⟫ ∧ ⟪F.N 1, w⟫ = 0 ∧ 0 < ⟪F.N 2, w⟫ ∧ ⟪F.N 3, w⟫ = 0 ∧
    ⟪F.N 4, w⟫ < 0 ∧ 0 < ⟪F.N 5, w⟫ ∧ 0 < ⟪F.N 6, w⟫ ∧ 0 < ⟪F.N 7, w⟫ ∧ ⟪F.N 8, w⟫ < 0

/-- Disjunction of the 12 non-triangle SVC cells from `Minimality.Type24SVCCells`. -/
def SVCCellHyp (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  Cell_012_0345_zpmzppmpp x F ∨
  Cell_0345_236_ppmzppmzp x F ∨
  Cell_0345_236_pppzmppzm x F ∨
  Cell_025_046_ppzmzpppp x F ∨
  Cell_025_235_ppzmppzpp x F ∨
  Cell_025_346_ppzmppppz x F ∨
  Cell_046_235_pppmzpzpp x F ∨
  Cell_046_346_mmmpzmmmz x F ∨
  Cell_235_236_pppmmpzzm x F ∨
  Cell_235_346_pppmppzpz x F ∨
  Cell_236_346_mmppmmpzz x F ∨
  Cell_016_0345_pzpzmpppm x F

/-- Any of the 12 non-triangle SVC cells closes to `Gen.LexAny F`. -/
theorem svcCell_lexAny {x : Fin 7 → ℝ³} {F : S0xFac 9 s0x_S24 x}
    (h : SVCCellHyp x F) : Gen.LexAny F := by
  rcases h with
      ⟨w, h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
    | ⟨w, h0, h2, h3, h4, h5, h6, h7, h8⟩
    | ⟨w, h1, h2, h3, h4, h5, h6, h7, h8⟩
    | ⟨w, h0, h1, h2, h3, h4, h6, h8⟩
    | ⟨h4, h8⟩
    | ⟨w, h0, h2, h3, h4, h6, h7, h8, hD⟩
    | ⟨w, h1, h2, h3, h4, h6, h7, h8, hD⟩
    | ⟨h2, h6⟩
    | ⟨h1, h4, h56⟩
    | ⟨w, h2, h3, h4, h6, h7, h8⟩
    | ⟨h0, h2, h24⟩
    | ⟨w, h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  · exact SVCC.CellsTB.cell_012_0345_zpmzppmpp_tb F w h0 h1 h2 h3 h4 h5 h6 h7 h8
  · exact SVCC.CellsTB.cell_0345_236_ppmzppmzp_tb F w h0 h2 h3 h4 h5 h6 h7 h8
  · exact SVCC.CellsTB.cell_0345_236_pppzmppzm_tb F w h1 h2 h3 h4 h5 h6 h7 h8
  · exact SVCC.CellsLex.cell_025_046_ppzmzpppp_lex F w h0 h1 h2 h3 h4 h6 h8
  · exact SVCC.CellsLex.cell_025_235_ppzmppzpp_lex F h4 h8
  · exact SVCC.CellsLex.cell_025_346_ppzmppppz_lex F w h0 h2 h3 h4 h6 h7 h8 hD
  · exact SVCC.CellsLex.cell_046_235_pppmzpzpp_lex F w h1 h2 h3 h4 h6 h7 h8 hD
  · exact SVCC.CellsLex.cell_046_346_mmmpzmmmz_lex F h2 h6
  · exact SVCC.CellsLex.cell_235_236_pppmmpzzm_lex F h1 h4 h56
  · exact SVCC.CellsLex.cell_235_346_pppmppzpz_lex F w h2 h3 h4 h6 h7 h8
  · exact SVCC.CellsLex.cell_236_346_mmppmmpzz_lex F h0 h2 h24
  · exact SVCC.CellsTB.cell_016_0345_pzpzmpppm_tb F w h0 h1 h2 h3 h4 h5 h6 h7 h8

/-- Hypothesis bundle for the two-view pair closure `Minimality.PSVC.L3u27.lexAny_L3_u27`
(`L3 = F016xF0345` at `w1`, `u27 = F025xF236` at `w2`). -/
def PairL3u27Hyp (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  ∃ w1 w2 : ℝ³,
    (0 < ⟪F.N 0, w1⟫ ∧ ⟪F.N 1, w1⟫ = 0 ∧ 0 < ⟪F.N 2, w1⟫ ∧ ⟪F.N 3, w1⟫ = 0 ∧
     ⟪F.N 4, w1⟫ < 0 ∧ ⟪F.N 5, w1⟫ < 0 ∧ ⟪F.N 6, w1⟫ < 0 ∧ ⟪F.N 8, w1⟫ < 0) ∧
    (0 < ⟪F.N 0, w2⟫ ∧ ⟪F.N 2, w2⟫ = 0 ∧ ⟪F.N 3, w2⟫ < 0 ∧ 0 < ⟪F.N 4, w2⟫ ∧
     0 < ⟪F.N 5, w2⟫ ∧ ⟪F.N 6, w2⟫ < 0 ∧ ⟪F.N 7, w2⟫ = 0 ∧ 0 < ⟪F.N 8, w2⟫) ∧
    (∀ i j : Fin 7, i ≠ j → ⟪x i, w1⟫ ≠ ⟪x j, w1⟫) ∧
    (∀ i j : Fin 7, i ≠ j → ⟪x i, w2⟫ ≠ ⟪x j, w2⟫)

/-- `PairL3u27Hyp` closes to `Gen.LexAny F`. -/
theorem pairL3u27_lexAny {x : Fin 7 → ℝ³} {F : S0xFac 9 s0x_S24 x}
    (h : PairL3u27Hyp x F) : Gen.LexAny F := by
  obtain ⟨w1, w2, ⟨a0, a1, a2, a3, a4, a5, a6, a8⟩,
    ⟨b0, b2, b3, b4, b5, b6, b7, b8⟩, hg1, hg2⟩ := h
  exact PSVC.L3u27.lexAny_L3_u27 F w1 w2 a0 a1 a2 a3 a4 a5 a6 a8
    b0 b2 b3 b4 b5 b6 b7 b8 hg1 hg2

/-- Further shrunken residual of `Hole24R5` removing the 12 non-triangle SVC cells and the
`L3 × u27` two-view pair. -/
def Hole24R6 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  Hole24R5 x F ∧ ¬ SVCCellHyp x F ∧ ¬ PairL3u27Hyp x F

/-- Every point of `Hole24R5` is Rupert or reduces to `Hole24R6`. -/
theorem hole24R5_reduce {x : Fin 7 → ℝ³} {F : S0xFac 9 s0x_S24 x}
    (h : Hole24R5 x F) : IsRupert (univ.image x) ∨ Hole24R6 x F := by
  by_cases hsvc : SVCCellHyp x F
  · exact Or.inl (Gen.lexAny_isRupert F (EdgeViewLink.inj_of_fac24 F) (svcCell_lexAny hsvc))
  · by_cases hpair : PairL3u27Hyp x F
    · exact Or.inl (Gen.lexAny_isRupert F (EdgeViewLink.inj_of_fac24 F) (pairL3u27_lexAny hpair))
    · exact Or.inr ⟨h, hsvc, hpair⟩

/-- Further shrunken `Q45` residual removing the 12 non-triangle SVC cells and the
`L3 × u27` two-view pair. -/
def Hole24Q45R6 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  Hole24Q45R x F ∧ ¬ SVCCellHyp x F ∧ ¬ PairL3u27Hyp x F

/-- Every point of `Hole24Q45R` is Rupert or reduces to `Hole24Q45R6`. -/
theorem hole24Q45R_reduce {x : Fin 7 → ℝ³} {F : S0xFac 9 s0x_S24 x}
    (h : Hole24Q45R x F) : IsRupert (univ.image x) ∨ Hole24Q45R6 x F := by
  by_cases hsvc : SVCCellHyp x F
  · exact Or.inl (Gen.lexAny_isRupert F (EdgeViewLink.inj_of_fac24 F) (svcCell_lexAny hsvc))
  · by_cases hpair : PairL3u27Hyp x F
    · exact Or.inl (Gen.lexAny_isRupert F (EdgeViewLink.inj_of_fac24 F) (pairL3u27_lexAny hpair))
    · exact Or.inr ⟨h, hsvc, hpair⟩

/-! ### Three-view triple closures (`Type24Triple1..10`) -/

def Triple1Hyp (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  ∃ w1 w2 : ℝ³,
    (0 < ⟪F.N 1, x 0 - x 2⟫ ∧ 0 < ⟪F.N 3, x 0 - x 2⟫ ∧ ⟪F.N 5, x 0 - x 2⟫ < 0 ∧
     ⟪F.N 6, x 0 - x 2⟫ < 0 ∧ ⟪F.N 7, x 0 - x 2⟫ < 0 ∧ 0 < ⟪F.N 8, x 0 - x 2⟫) ∧
    (0 < ⟪F.N 0, w1⟫ ∧ ⟪F.N 2, w1⟫ = 0 ∧ ⟪F.N 3, w1⟫ < 0 ∧ 0 < ⟪F.N 4, w1⟫ ∧
     0 < ⟪F.N 5, w1⟫ ∧ ⟪F.N 6, w1⟫ < 0 ∧ ⟪F.N 7, w1⟫ = 0 ∧ 0 < ⟪F.N 8, w1⟫) ∧
    (0 < ⟪F.N 0, w2⟫ ∧ ⟪F.N 1, w2⟫ = 0 ∧ 0 < ⟪F.N 2, w2⟫ ∧ ⟪F.N 3, w2⟫ = 0 ∧
     ⟪F.N 4, w2⟫ < 0 ∧ ⟪F.N 5, w2⟫ < 0 ∧ 0 < ⟪F.N 6, w2⟫ ∧ ⟪F.N 7, w2⟫ < 0 ∧ ⟪F.N 8, w2⟫ < 0) ∧
    (∀ i j : Fin 7, i ≠ j → ⟪x i, x 0 - x 2⟫ ≠ ⟪x j, x 0 - x 2⟫) ∧
    (∀ i j : Fin 7, i ≠ j → ⟪x i, w1⟫ ≠ ⟪x j, w1⟫) ∧
    (∀ i j : Fin 7, i ≠ j → ⟪x i, w2⟫ ≠ ⟪x j, w2⟫)

def Triple2Hyp (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  ∃ w0 w2 : ℝ³,
    (0 < ⟪F.N 0, w0⟫ ∧ 0 < ⟪F.N 1, w0⟫ ∧ 0 < ⟪F.N 2, w0⟫ ∧ ⟪F.N 3, w0⟫ = 0 ∧
     ⟪F.N 4, w0⟫ < 0 ∧ ⟪F.N 5, w0⟫ = 0 ∧ ⟪F.N 6, w0⟫ < 0 ∧ ⟪F.N 7, w0⟫ < 0 ∧ ⟪F.N 8, w0⟫ < 0) ∧
    (0 < ⟪F.N 1, x 1 - x 2⟫ ∧ ⟪F.N 2, x 1 - x 2⟫ < 0 ∧ ⟪F.N 3, x 1 - x 2⟫ < 0 ∧
     0 < ⟪F.N 4, x 1 - x 2⟫ ∧ ⟪F.N 6, x 1 - x 2⟫ < 0 ∧ ⟪F.N 7, x 1 - x 2⟫ < 0 ∧ 0 < ⟪F.N 8, x 1 - x 2⟫) ∧
    (0 < ⟪F.N 0, w2⟫ ∧ ⟪F.N 2, w2⟫ = 0 ∧ ⟪F.N 3, w2⟫ < 0 ∧ 0 < ⟪F.N 4, w2⟫ ∧
     0 < ⟪F.N 5, w2⟫ ∧ ⟪F.N 6, w2⟫ < 0 ∧ ⟪F.N 7, w2⟫ = 0 ∧ 0 < ⟪F.N 8, w2⟫) ∧
    (∀ i j : Fin 7, i ≠ j → ⟪x i, w0⟫ ≠ ⟪x j, w0⟫) ∧
    (∀ i j : Fin 7, i ≠ j → ⟪x i, x 1 - x 2⟫ ≠ ⟪x j, x 1 - x 2⟫) ∧
    (∀ i j : Fin 7, i ≠ j → ⟪x i, w2⟫ ≠ ⟪x j, w2⟫)

def Triple3Hyp (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  ∃ w0 w1 : ℝ³,
    (0 < ⟪F.N 0, w0⟫ ∧ 0 < ⟪F.N 1, w0⟫ ∧ 0 < ⟪F.N 2, w0⟫ ∧ ⟪F.N 3, w0⟫ = 0 ∧
     ⟪F.N 4, w0⟫ < 0 ∧ ⟪F.N 5, w0⟫ = 0 ∧ ⟪F.N 6, w0⟫ < 0 ∧ ⟪F.N 7, w0⟫ < 0 ∧ ⟪F.N 8, w0⟫ < 0) ∧
    (0 < ⟪F.N 0, w1⟫ ∧ ⟪F.N 2, w1⟫ = 0 ∧ ⟪F.N 3, w1⟫ < 0 ∧ 0 < ⟪F.N 4, w1⟫ ∧
     0 < ⟪F.N 5, w1⟫ ∧ ⟪F.N 6, w1⟫ < 0 ∧ ⟪F.N 7, w1⟫ = 0 ∧ 0 < ⟪F.N 8, w1⟫) ∧
    (0 < ⟪F.N 1, x 1 - x 2⟫ ∧ ⟪F.N 2, x 1 - x 2⟫ < 0 ∧ ⟪F.N 3, x 1 - x 2⟫ < 0 ∧
     0 < ⟪F.N 4, x 1 - x 2⟫ ∧ ⟪F.N 6, x 1 - x 2⟫ < 0 ∧ ⟪F.N 7, x 1 - x 2⟫ < 0 ∧ ⟪F.N 8, x 1 - x 2⟫ < 0) ∧
    (∀ i j : Fin 7, i ≠ j → ⟪x i, w0⟫ ≠ ⟪x j, w0⟫) ∧
    (∀ i j : Fin 7, i ≠ j → ⟪x i, w1⟫ ≠ ⟪x j, w1⟫) ∧
    (∀ i j : Fin 7, i ≠ j → ⟪x i, x 1 - x 2⟫ ≠ ⟪x j, x 1 - x 2⟫)

def Triple4Hyp (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  ∃ w1 w2 : ℝ³,
    (0 < ⟪F.N 1, x 0 - x 2⟫ ∧ 0 < ⟪F.N 3, x 0 - x 2⟫ ∧ ⟪F.N 5, x 0 - x 2⟫ < 0 ∧
     ⟪F.N 6, x 0 - x 2⟫ < 0 ∧ ⟪F.N 7, x 0 - x 2⟫ < 0 ∧ 0 < ⟪F.N 8, x 0 - x 2⟫) ∧
    (0 < ⟪F.N 0, w1⟫ ∧ ⟪F.N 2, w1⟫ = 0 ∧ ⟪F.N 3, w1⟫ < 0 ∧ 0 < ⟪F.N 4, w1⟫ ∧
     0 < ⟪F.N 5, w1⟫ ∧ ⟪F.N 6, w1⟫ < 0 ∧ ⟪F.N 7, w1⟫ = 0 ∧ 0 < ⟪F.N 8, w1⟫) ∧
    (0 < ⟪F.N 0, w2⟫ ∧ 0 < ⟪F.N 1, w2⟫ ∧ 0 < ⟪F.N 2, w2⟫ ∧ ⟪F.N 3, w2⟫ = 0 ∧
     ⟪F.N 4, w2⟫ < 0 ∧ ⟪F.N 5, w2⟫ = 0 ∧ 0 < ⟪F.N 6, w2⟫ ∧ ⟪F.N 7, w2⟫ < 0 ∧ ⟪F.N 8, w2⟫ < 0) ∧
    ⟪F.N 3, F.N 3⟫ * ⟪F.N 5, F.N 5⟫ - ⟪F.N 3, F.N 5⟫ ^ 2 ≠ 0 ∧
    (∀ i j : Fin 7, i ≠ j → ⟪x i, x 0 - x 2⟫ ≠ ⟪x j, x 0 - x 2⟫) ∧
    (∀ i j : Fin 7, i ≠ j → ⟪x i, w1⟫ ≠ ⟪x j, w1⟫) ∧
    (∀ i j : Fin 7, i ≠ j → ⟪x i, w2⟫ ≠ ⟪x j, w2⟫)

def Triple5Hyp (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  ∃ w0 w1 : ℝ³,
    (0 < ⟪F.N 0, w0⟫ ∧ ⟪F.N 1, w0⟫ = 0 ∧ 0 < ⟪F.N 2, w0⟫ ∧ ⟪F.N 3, w0⟫ = 0 ∧
     ⟪F.N 4, w0⟫ < 0 ∧ 0 < ⟪F.N 5, w0⟫ ∧ ⟪F.N 6, w0⟫ < 0 ∧ ⟪F.N 7, w0⟫ < 0 ∧ ⟪F.N 8, w0⟫ < 0) ∧
    (0 < ⟪F.N 0, w1⟫ ∧ ⟪F.N 2, w1⟫ = 0 ∧ ⟪F.N 3, w1⟫ < 0 ∧ 0 < ⟪F.N 4, w1⟫ ∧
     0 < ⟪F.N 5, w1⟫ ∧ ⟪F.N 6, w1⟫ < 0 ∧ ⟪F.N 7, w1⟫ = 0 ∧ 0 < ⟪F.N 8, w1⟫) ∧
    (0 < ⟪F.N 2, x 0 - x 1⟫ ∧ 0 < ⟪F.N 3, x 0 - x 1⟫ ∧ 0 < ⟪F.N 4, x 0 - x 1⟫ ∧
     ⟪F.N 5, x 0 - x 1⟫ < 0 ∧ 0 < ⟪F.N 6, x 0 - x 1⟫ ∧ ⟪F.N 7, x 0 - x 1⟫ < 0 ∧ 0 < ⟪F.N 8, x 0 - x 1⟫) ∧
    (∀ i j : Fin 7, i ≠ j → ⟪x i, w0⟫ ≠ ⟪x j, w0⟫) ∧
    (∀ i j : Fin 7, i ≠ j → ⟪x i, w1⟫ ≠ ⟪x j, w1⟫) ∧
    (∀ i j : Fin 7, i ≠ j → ⟪x i, x 0 - x 1⟫ ≠ ⟪x j, x 0 - x 1⟫)

def Triple6Hyp (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  ∃ w0 w1 : ℝ³,
    (0 < ⟪F.N 0, w0⟫ ∧ ⟪F.N 1, w0⟫ = 0 ∧ 0 < ⟪F.N 2, w0⟫ ∧ ⟪F.N 3, w0⟫ = 0 ∧
     ⟪F.N 4, w0⟫ < 0 ∧ 0 < ⟪F.N 5, w0⟫ ∧ ⟪F.N 6, w0⟫ < 0 ∧ ⟪F.N 7, w0⟫ < 0 ∧ ⟪F.N 8, w0⟫ < 0) ∧
    (0 < ⟪F.N 0, w1⟫ ∧ ⟪F.N 2, w1⟫ = 0 ∧ ⟪F.N 3, w1⟫ < 0 ∧ 0 < ⟪F.N 4, w1⟫ ∧
     0 < ⟪F.N 5, w1⟫ ∧ ⟪F.N 6, w1⟫ < 0 ∧ ⟪F.N 7, w1⟫ = 0 ∧ 0 < ⟪F.N 8, w1⟫) ∧
    (0 < ⟪F.N 2, x 0 - x 1⟫ ∧ 0 < ⟪F.N 3, x 0 - x 1⟫ ∧ 0 < ⟪F.N 4, x 0 - x 1⟫ ∧
     ⟪F.N 5, x 0 - x 1⟫ < 0 ∧ 0 < ⟪F.N 6, x 0 - x 1⟫ ∧ ⟪F.N 7, x 0 - x 1⟫ < 0 ∧ ⟪F.N 8, x 0 - x 1⟫ < 0) ∧
    (∀ i j : Fin 7, i ≠ j → ⟪x i, w0⟫ ≠ ⟪x j, w0⟫) ∧
    (∀ i j : Fin 7, i ≠ j → ⟪x i, w1⟫ ≠ ⟪x j, w1⟫) ∧
    (∀ i j : Fin 7, i ≠ j → ⟪x i, x 0 - x 1⟫ ≠ ⟪x j, x 0 - x 1⟫)

def Triple7Hyp (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  ∃ w0 w1 w2 : ℝ³,
    (0 < ⟪F.N 0, w0⟫ ∧ ⟪F.N 1, w0⟫ = 0 ∧ 0 < ⟪F.N 2, w0⟫ ∧ ⟪F.N 3, w0⟫ = 0 ∧
     ⟪F.N 4, w0⟫ < 0 ∧ 0 < ⟪F.N 5, w0⟫ ∧ ⟪F.N 6, w0⟫ < 0 ∧ ⟪F.N 7, w0⟫ < 0 ∧ ⟪F.N 8, w0⟫ < 0) ∧
    (0 < ⟪F.N 0, w1⟫ ∧ ⟪F.N 2, w1⟫ = 0 ∧ ⟪F.N 3, w1⟫ < 0 ∧ 0 < ⟪F.N 4, w1⟫ ∧
     0 < ⟪F.N 5, w1⟫ ∧ ⟪F.N 6, w1⟫ < 0 ∧ ⟪F.N 7, w1⟫ = 0 ∧ 0 < ⟪F.N 8, w1⟫) ∧
    (0 < ⟪F.N 0, w2⟫ ∧ ⟪F.N 1, w2⟫ = 0 ∧ 0 < ⟪F.N 2, w2⟫ ∧ ⟪F.N 3, w2⟫ < 0 ∧
     ⟪F.N 4, w2⟫ < 0 ∧ 0 < ⟪F.N 5, w2⟫ ∧ ⟪F.N 6, w2⟫ < 0 ∧ ⟪F.N 7, w2⟫ = 0 ∧ ⟪F.N 8, w2⟫ < 0) ∧
    (∀ i j : Fin 7, i ≠ j → ⟪x i, w0⟫ ≠ ⟪x j, w0⟫) ∧
    (∀ i j : Fin 7, i ≠ j → ⟪x i, w1⟫ ≠ ⟪x j, w1⟫) ∧
    (∀ i j : Fin 7, i ≠ j → ⟪x i, w2⟫ ≠ ⟪x j, w2⟫)

def Triple8Hyp (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  ∃ w0 w1 : ℝ³,
    (0 < ⟪F.N 0, w0⟫ ∧ ⟪F.N 1, w0⟫ < 0 ∧ 0 < ⟪F.N 2, w0⟫ ∧ ⟪F.N 3, w0⟫ < 0 ∧
     ⟪F.N 4, w0⟫ < 0 ∧ 0 < ⟪F.N 5, w0⟫ ∧ ⟪F.N 6, w0⟫ = 0 ∧ 0 < ⟪F.N 7, w0⟫ ∧ ⟪F.N 8, w0⟫ = 0) ∧
    (0 < ⟪F.N 0, w1⟫ ∧ ⟪F.N 2, w1⟫ = 0 ∧ ⟪F.N 3, w1⟫ < 0 ∧ 0 < ⟪F.N 4, w1⟫ ∧
     0 < ⟪F.N 5, w1⟫ ∧ ⟪F.N 6, w1⟫ < 0 ∧ ⟪F.N 7, w1⟫ = 0 ∧ 0 < ⟪F.N 8, w1⟫) ∧
    (⟪F.N 0, x 3 - x 5⟫ < 0 ∧ ⟪F.N 1, x 3 - x 5⟫ < 0 ∧ ⟪F.N 2, x 3 - x 5⟫ < 0 ∧
     ⟪F.N 4, x 3 - x 5⟫ < 0 ∧ 0 < ⟪F.N 5, x 3 - x 5⟫ ∧ 0 < ⟪F.N 7, x 3 - x 5⟫ ∧ 0 < ⟪F.N 8, x 3 - x 5⟫) ∧
    (∀ i j : Fin 7, i ≠ j → ⟪x i, w0⟫ ≠ ⟪x j, w0⟫) ∧
    (∀ i j : Fin 7, i ≠ j → ⟪x i, w1⟫ ≠ ⟪x j, w1⟫) ∧
    (∀ i j : Fin 7, i ≠ j → ⟪x i, x 3 - x 5⟫ ≠ ⟪x j, x 3 - x 5⟫)

def Triple9Hyp (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  ∃ w1 w2 : ℝ³,
    (0 < ⟪F.N 1, x 0 - x 4⟫ ∧ 0 < ⟪F.N 2, x 0 - x 4⟫ ∧ 0 < ⟪F.N 5, x 0 - x 4⟫ ∧
     ⟪F.N 6, x 0 - x 4⟫ < 0 ∧ ⟪F.N 7, x 0 - x 4⟫ < 0 ∧ ⟪F.N 8, x 0 - x 4⟫ < 0) ∧
    (0 < ⟪F.N 0, w1⟫ ∧ ⟪F.N 2, w1⟫ = 0 ∧ ⟪F.N 3, w1⟫ < 0 ∧ 0 < ⟪F.N 4, w1⟫ ∧
     0 < ⟪F.N 5, w1⟫ ∧ ⟪F.N 6, w1⟫ < 0 ∧ ⟪F.N 7, w1⟫ = 0 ∧ 0 < ⟪F.N 8, w1⟫) ∧
    (⟪F.N 0, w2⟫ = 0 ∧ 0 < ⟪F.N 1, w2⟫ ∧ ⟪F.N 2, w2⟫ < 0 ∧ ⟪F.N 3, w2⟫ < 0 ∧
     ⟪F.N 4, w2⟫ = 0 ∧ 0 < ⟪F.N 5, w2⟫ ∧ ⟪F.N 6, w2⟫ < 0 ∧ 0 < ⟪F.N 7, w2⟫ ∧ ⟪F.N 8, w2⟫ < 0) ∧
    (∀ i j : Fin 7, i ≠ j → ⟪x i, x 0 - x 4⟫ ≠ ⟪x j, x 0 - x 4⟫) ∧
    (∀ i j : Fin 7, i ≠ j → ⟪x i, w1⟫ ≠ ⟪x j, w1⟫) ∧
    (∀ i j : Fin 7, i ≠ j → ⟪x i, w2⟫ ≠ ⟪x j, w2⟫)

def Triple10Hyp (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  ∃ w1 w2 : ℝ³,
    (0 < ⟪F.N 0, x 0 - x 4⟫ ∧ 0 < ⟪F.N 1, x 0 - x 4⟫ ∧ 0 < ⟪F.N 2, x 0 - x 4⟫ ∧
     0 < ⟪F.N 5, x 0 - x 4⟫ ∧ ⟪F.N 6, x 0 - x 4⟫ < 0 ∧ ⟪F.N 7, x 0 - x 4⟫ < 0 ∧ ⟪F.N 8, x 0 - x 4⟫ < 0) ∧
    (0 < ⟪F.N 0, w1⟫ ∧ ⟪F.N 2, w1⟫ = 0 ∧ ⟪F.N 3, w1⟫ < 0 ∧ 0 < ⟪F.N 4, w1⟫ ∧
     0 < ⟪F.N 5, w1⟫ ∧ ⟪F.N 6, w1⟫ < 0 ∧ ⟪F.N 7, w1⟫ = 0 ∧ 0 < ⟪F.N 8, w1⟫) ∧
    (⟪F.N 0, w2⟫ = 0 ∧ 0 < ⟪F.N 1, w2⟫ ∧ ⟪F.N 2, w2⟫ < 0 ∧ ⟪F.N 3, w2⟫ < 0 ∧
     ⟪F.N 4, w2⟫ = 0 ∧ 0 < ⟪F.N 5, w2⟫ ∧ 0 < ⟪F.N 6, w2⟫ ∧ 0 < ⟪F.N 8, w2⟫) ∧
    (∀ i j : Fin 7, i ≠ j → ⟪x i, x 0 - x 4⟫ ≠ ⟪x j, x 0 - x 4⟫) ∧
    (∀ i j : Fin 7, i ≠ j → ⟪x i, w1⟫ ≠ ⟪x j, w1⟫) ∧
    (∀ i j : Fin 7, i ≠ j → ⟪x i, w2⟫ ≠ ⟪x j, w2⟫)

/-- Disjunction of the 10 three-view triple closure hypotheses (`Type24Triple1..10`). -/
def TripleHyp (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  Triple1Hyp x F ∨ Triple2Hyp x F ∨ Triple3Hyp x F ∨ Triple4Hyp x F ∨ Triple5Hyp x F ∨
  Triple6Hyp x F ∨ Triple7Hyp x F ∨ Triple8Hyp x F ∨ Triple9Hyp x F ∨ Triple10Hyp x F

/-- Any of the 10 three-view triple closures gives `Gen.LexAny F`. -/
theorem triple_lexAny {x : Fin 7 → ℝ³} {F : S0xFac 9 s0x_S24 x}
    (h : TripleHyp x F) : Gen.LexAny F := by
  rcases h with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10
  · obtain ⟨w1, w2, ⟨a1, a3, a5, a6, a7, a8⟩, ⟨b0, b2, b3, b4, b5, b6, b7, b8⟩,
      ⟨c0, c1, c2, c3, c4, c5, c6, c7, c8⟩, hg0, hg1, hg2⟩ := h1
    exact PSVC.T1.lexAny_T1 F w1 w2 a1 a3 a5 a6 a7 a8 b0 b2 b3 b4 b5 b6 b7 b8
      c0 c1 c2 c3 c4 c5 c6 c7 c8 hg0 hg1 hg2
  · obtain ⟨w0, w2, ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8⟩, ⟨b1, b2, b3, b4, b6, b7, b8⟩,
      ⟨c0, c2, c3, c4, c5, c6, c7, c8⟩, hg0, hg1, hg2⟩ := h2
    exact PSVC.T2.lexAny_T2 F w0 w2 a0 a1 a2 a3 a4 a5 a6 a7 a8 b1 b2 b3 b4 b6 b7 b8
      c0 c2 c3 c4 c5 c6 c7 c8 hg0 hg1 hg2
  · obtain ⟨w0, w1, ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8⟩, ⟨b0, b2, b3, b4, b5, b6, b7, b8⟩,
      ⟨c1, c2, c3, c4, c6, c7, c8⟩, hg0, hg1, hg2⟩ := h3
    exact PSVC.T3.lexAny_T3 F w0 w1 a0 a1 a2 a3 a4 a5 a6 a7 a8 b0 b2 b3 b4 b5 b6 b7 b8
      c1 c2 c3 c4 c6 c7 c8 hg0 hg1 hg2
  · obtain ⟨w1, w2, ⟨a1, a3, a5, a6, a7, a8⟩, ⟨b0, b2, b3, b4, b5, b6, b7, b8⟩,
      ⟨c0, c1, c2, c3, c4, c5, c6, c7, c8⟩, hD2, hg0, hg1, hg2⟩ := h4
    exact PSVC.T4.lexAny_T4 F w1 w2 a1 a3 a5 a6 a7 a8 b0 b2 b3 b4 b5 b6 b7 b8
      c0 c1 c2 c3 c4 c5 c6 c7 c8 hD2 hg0 hg1 hg2
  · obtain ⟨w0, w1, ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8⟩, ⟨b0, b2, b3, b4, b5, b6, b7, b8⟩,
      ⟨c2, c3, c4, c5, c6, c7, c8⟩, hg0, hg1, hg2⟩ := h5
    exact PSVC.T5.lexAny_T5 F w0 w1 a0 a1 a2 a3 a4 a5 a6 a7 a8 b0 b2 b3 b4 b5 b6 b7 b8
      c2 c3 c4 c5 c6 c7 c8 hg0 hg1 hg2
  · obtain ⟨w0, w1, ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8⟩, ⟨b0, b2, b3, b4, b5, b6, b7, b8⟩,
      ⟨c2, c3, c4, c5, c6, c7, c8⟩, hg0, hg1, hg2⟩ := h6
    exact PSVC.T6.lexAny_T6 F w0 w1 a0 a1 a2 a3 a4 a5 a6 a7 a8 b0 b2 b3 b4 b5 b6 b7 b8
      c2 c3 c4 c5 c6 c7 c8 hg0 hg1 hg2
  · obtain ⟨w0, w1, w2, ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8⟩, ⟨b0, b2, b3, b4, b5, b6, b7, b8⟩,
      ⟨c0, c1, c2, c3, c4, c5, c6, c7, c8⟩, hg0, hg1, hg2⟩ := h7
    exact PSVC.T7.lexAny_T7 F w0 w1 w2 a0 a1 a2 a3 a4 a5 a6 a7 a8 b0 b2 b3 b4 b5 b6 b7 b8
      c0 c1 c2 c3 c4 c5 c6 c7 c8 hg0 hg1 hg2
  · obtain ⟨w0, w1, ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8⟩, ⟨b0, b2, b3, b4, b5, b6, b7, b8⟩,
      ⟨c0, c1, c2, c4, c5, c7, c8⟩, hg0, hg1, hg2⟩ := h8
    exact PSVC.T8.lexAny_T8 F w0 w1 a0 a1 a2 a3 a4 a5 a6 a7 a8 b0 b2 b3 b4 b5 b6 b7 b8
      c0 c1 c2 c4 c5 c7 c8 hg0 hg1 hg2
  · obtain ⟨w1, w2, ⟨a1, a2, a5, a6, a7, a8⟩, ⟨b0, b2, b3, b4, b5, b6, b7, b8⟩,
      ⟨c0, c1, c2, c3, c4, c5, c6, c7, c8⟩, hg0, hg1, hg2⟩ := h9
    exact PSVC.T9.lexAny_T9 F w1 w2 a1 a2 a5 a6 a7 a8 b0 b2 b3 b4 b5 b6 b7 b8
      c0 c1 c2 c3 c4 c5 c6 c7 c8 hg0 hg1 hg2
  · obtain ⟨w1, w2, ⟨a0, a1, a2, a5, a6, a7, a8⟩, ⟨b0, b2, b3, b4, b5, b6, b7, b8⟩,
      ⟨c0, c1, c2, c3, c4, c5, c6, c8⟩, hg0, hg1, hg2⟩ := h10
    exact PSVC.T10.lexAny_T10 F w1 w2 a0 a1 a2 a5 a6 a7 a8 b0 b2 b3 b4 b5 b6 b7 b8
      c0 c1 c2 c3 c4 c5 c6 c8 hg0 hg1 hg2

/-- Further shrunken residual of `Hole24R6` removing the 10 three-view triple closures. -/
def Hole24R7 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  Hole24R6 x F ∧ ¬ TripleHyp x F

/-- Every point of `Hole24R6` is Rupert or reduces to `Hole24R7`. -/
theorem hole24R6_reduce {x : Fin 7 → ℝ³} {F : S0xFac 9 s0x_S24 x}
    (h : Hole24R6 x F) : IsRupert (univ.image x) ∨ Hole24R7 x F := by
  by_cases htri : TripleHyp x F
  · exact Or.inl (Gen.lexAny_isRupert F (EdgeViewLink.inj_of_fac24 F) (triple_lexAny htri))
  · exact Or.inr ⟨h, htri⟩

/-- Further shrunken `Q45` residual of `Hole24Q45R6` removing the 10 three-view triple closures. -/
def Hole24Q45R7 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  Hole24Q45R6 x F ∧ ¬ TripleHyp x F

/-- Every point of `Hole24Q45R6` is Rupert or reduces to `Hole24Q45R7`. -/
theorem hole24Q45R6_reduce {x : Fin 7 → ℝ³} {F : S0xFac 9 s0x_S24 x}
    (h : Hole24Q45R6 x F) : IsRupert (univ.image x) ∨ Hole24Q45R7 x F := by
  by_cases htri : TripleHyp x F
  · exact Or.inl (Gen.lexAny_isRupert F (EdgeViewLink.inj_of_fac24 F) (triple_lexAny htri))
  · exact Or.inr ⟨h, htri⟩

/-- The single named Type-24 open hole proposition for `Minimality.lean`, with `Hole24Q45R7`,
`Hole24R7`, and the two star-closed `{1 < c3, 0 < mustar}` / `{1 < b3, 0 < mu23}` exclusions
discharged via `Hole24Flags.1` (`¬ FacetCell24 fs`) and `Type24T2b`. -/
def Hole24 (x : Fin 7 → ℝ³) (fs : Fin 9 → ℝ³ →ᵃ[ℝ] ℝ) (F : S0xFac 9 s0x_S24 x) : Prop :=
  Hole24Flags x fs ∧ (Hole24Q45R7 x F ∨ Hole24R7 x F) ∧
    ¬ (1 < oblX6 x 3 ∧ 0 < A20.mustar x) ∧
    ¬ (1 < oblX2 x 3 ∧ 0 < A20.mu23 x)

/-- On `{1 < oblX2 x 3, 1 < oblX6 x 3, 0 ≤ al, 0 ≤ be, be ≤ 1, al ≤ 1}` (where `al, be` are the
`par2546_quad` coefficients `s = be, t = al` in `x 3 - x 0 = al • (x 5 - x 0) + be • (x 4 - x 0)`),
any point of `Hole24 x fs (mkFac24 fs hh)` lies in the wall `{mustar = 0}` / `{mu23 = 0}` tie loci
on `{0, 2, 3, 4, 5, 6}` (the star loci are closed by `Type24T2b` + `¬ FacetCell24 fs`). -/
theorem hole24_b3_c3_st_le_ties {x : Fin 7 → ℝ³} {fs : Fin 9 → ℝ³ →ᵃ[ℝ] ℝ}
    (hh : ∀ t i, (i ∈ s0x_S24 t → fs t (x i) = 0) ∧ (i ∉ s0x_S24 t → fs t (x i) < 0))
    (hH : Hole24 x fs (mkFac24 fs hh))
    (hb3 : 1 < oblX2 x 3) (hc3 : 1 < oblX6 x 3)
    {al be : ℝ} (halp : 0 ≤ al) (hbep : 0 ≤ be)
    (hq : x 3 - x 0 = al • (x 5 - x 0) + be • (x 4 - x 0))
    (hbe : be ≤ 1) (hal : al ≤ 1) :
    (A20.mustar x = 0 ∧ ∃ i ∈ ({0, 2, 3, 4, 5, 6} : Finset (Fin 7)),
      ∃ j ∈ ({0, 2, 3, 4, 5, 6} : Finset (Fin 7)), i ≠ j ∧ ⟪x i, x 3 - x 6⟫ = ⟪x j, x 3 - x 6⟫) ∨
    (A20.mu23 x = 0 ∧ ∃ i ∈ ({0, 2, 3, 4, 5, 6} : Finset (Fin 7)),
      ∃ j ∈ ({0, 2, 3, 4, 5, 6} : Finset (Fin 7)), i ≠ j ∧ ⟪x i, x 3 - x 2⟫ = ⟪x j, x 3 - x 2⟫) := by
  rcases hH with ⟨hflags, hQ | hR7, hnow, hnoe⟩
  · rcases A20.mustar_or_mu23_nonneg fs hh hflags.1 halp hbep hq hbe hal with hmu | hmu23
    · rcases eq_or_lt_of_le hmu with hzero | hpos
      · left
        refine ⟨hzero.symm, ?_⟩
        by_contra hno; push Not at hno
        exact hQ.1.1.2.2.2.2.1 ⟨hc3, hzero.symm, hno⟩
      · exact False.elim (hnow ⟨hc3, hpos⟩)
    · rcases eq_or_lt_of_le hmu23 with hzero | hpos
      · right
        refine ⟨hzero.symm, ?_⟩
        by_contra hno; push Not at hno
        exact hQ.1.1.2.2.2.2.2 ⟨hb3, hzero.symm, hno⟩
      · exact False.elim (hnoe ⟨hb3, hpos⟩)
  · rcases A20.mustar_or_mu23_nonneg fs hh hflags.1 halp hbep hq hbe hal with hmu | hmu23
    · rcases eq_or_lt_of_le hmu with hzero | hpos
      · left
        refine ⟨hzero.symm, ?_⟩
        by_contra hno; push Not at hno
        exact hR7.1.1.2.1 ⟨hc3, hzero.symm, hno⟩
      · exact False.elim (hnow ⟨hc3, hpos⟩)
    · rcases eq_or_lt_of_le hmu23 with hzero | hpos
      · right
        refine ⟨hzero.symm, ?_⟩
        by_contra hno; push Not at hno
        exact hR7.1.1.2.2 ⟨hb3, hzero.symm, hno⟩
      · exact False.elim (hnoe ⟨hb3, hpos⟩)

/-- The strict region `{1 < oblX2 x 3, 1 < oblX6 x 3, 0 ≤ al, 0 ≤ be, be < 1, al < 1}` is
**empty** in `Hole24 x fs (mkFac24 fs hh)`. -/
theorem hole24_b3_c3_st_lt_empty {x : Fin 7 → ℝ³} {fs : Fin 9 → ℝ³ →ᵃ[ℝ] ℝ}
    (hh : ∀ t i, (i ∈ s0x_S24 t → fs t (x i) = 0) ∧ (i ∉ s0x_S24 t → fs t (x i) < 0))
    (hH : Hole24 x fs (mkFac24 fs hh))
    (hb3 : 1 < oblX2 x 3) (hc3 : 1 < oblX6 x 3)
    {al be : ℝ} (halp : 0 ≤ al) (hbep : 0 ≤ be)
    (hq : x 3 - x 0 = al • (x 5 - x 0) + be • (x 4 - x 0))
    (hbe : be < 1) (hal : al < 1) : False := by
  rcases hH with ⟨hflags, _, hnow, hnoe⟩
  rcases A20.mustar_or_mu23_pos fs hh hflags.1 halp hbep hq hbe hal with hmu | hmu23
  · exact hnow ⟨hc3, hmu⟩
  · exact hnoe ⟨hb3, hmu23⟩

/-- Main Type-24 reduction leaving `Hole24` (with `Hole24Q45R7`, `Hole24R7`, and the star-closed
exclusions). -/
theorem type24_rupert_or_hole {x : Fin 7 → ℝ³}
    (fA fB fC fD fE fF fG fH fI : ℝ³ →ᵃ[ℝ] ℝ)
    (hA : ∀ i, (i ∈ ({0, 1, 2} : Finset (Fin 7)) → fA (x i) = 0) ∧
      (i ∉ ({0, 1, 2} : Finset (Fin 7)) → fA (x i) < 0))
    (hB : ∀ i, (i ∈ ({0, 1, 6} : Finset (Fin 7)) → fB (x i) = 0) ∧
      (i ∉ ({0, 1, 6} : Finset (Fin 7)) → fB (x i) < 0))
    (hC : ∀ i, (i ∈ ({1, 2, 6} : Finset (Fin 7)) → fC (x i) = 0) ∧
      (i ∉ ({1, 2, 6} : Finset (Fin 7)) → fC (x i) < 0))
    (hD : ∀ i, (i ∈ ({2, 3, 6} : Finset (Fin 7)) → fD (x i) = 0) ∧
      (i ∉ ({2, 3, 6} : Finset (Fin 7)) → fD (x i) < 0))
    (hE : ∀ i, (i ∈ ({0, 4, 6} : Finset (Fin 7)) → fE (x i) = 0) ∧
      (i ∉ ({0, 4, 6} : Finset (Fin 7)) → fE (x i) < 0))
    (hF : ∀ i, (i ∈ ({0, 2, 5} : Finset (Fin 7)) → fF (x i) = 0) ∧
      (i ∉ ({0, 2, 5} : Finset (Fin 7)) → fF (x i) < 0))
    (hG : ∀ i, (i ∈ ({0, 3, 4, 5} : Finset (Fin 7)) → fG (x i) = 0) ∧
      (i ∉ ({0, 3, 4, 5} : Finset (Fin 7)) → fG (x i) < 0))
    (hH : ∀ i, (i ∈ ({2, 3, 5} : Finset (Fin 7)) → fH (x i) = 0) ∧
      (i ∉ ({2, 3, 5} : Finset (Fin 7)) → fH (x i) < 0))
    (hI : ∀ i, (i ∈ ({3, 4, 6} : Finset (Fin 7)) → fI (x i) = 0) ∧
      (i ∉ ({3, 4, 6} : Finset (Fin 7)) → fI (x i) < 0)) :
    IsRupert (univ.image x) ∨
      ∃ hh : ∀ t i, (i ∈ s0x_S24 t → ![fA, fB, fF, fG, fE, fC, fH, fD, fI] t (x i) = 0) ∧
        (i ∉ s0x_S24 t → ![fA, fB, fF, fG, fE, fC, fH, fD, fI] t (x i) < 0),
        Hole24 x ![fA, fB, fF, fG, fE, fC, fH, fD, fI]
          (mkFac24 ![fA, fB, fF, fG, fE, fC, fH, fD, fI] hh) := by
  let fs := ![fA, fB, fF, fG, fE, fC, fH, fD, fI]
  rcases type24_rupert_or_holeR fA fB fC fD fE fF fG fH fI hA hB hC hD hE hF hG hH hI with
    hRup | ⟨hh, hflags, hQ | hR⟩
  · exact Or.inl hRup
  · by_cases hnow : 1 < oblX6 x 3 ∧ 0 < A20.mustar x
    · rcases w63_closes_star_or_facetCell fs hh hnow.1 hnow.2 with hLex | hFac
      · exact Or.inl (Gen.lexAny_isRupert (mkFac24 fs hh) (EdgeViewLink.inj_of_fac24 (mkFac24 fs hh)) hLex)
      · exact False.elim (hflags.1 hFac)
    · by_cases hnoe : 1 < oblX2 x 3 ∧ 0 < A20.mu23 x
      · rcases e23_closes_star_or_facetCell fs hh hnoe.1 hnoe.2 with hLex | hFac
        · exact Or.inl (Gen.lexAny_isRupert (mkFac24 fs hh) (EdgeViewLink.inj_of_fac24 (mkFac24 fs hh)) hLex)
        · exact False.elim (hflags.1 hFac)
      · rcases hole24Q45R_reduce (hole24Q45_reduce hQ) with hRup | hQ6
        · exact Or.inl hRup
        · rcases hole24Q45R6_reduce hQ6 with hRup | hQ7
          · exact Or.inl hRup
          · exact Or.inr ⟨hh, hflags, Or.inl hQ7, hnow, hnoe⟩
  · rcases hole24R_reduce hR with hRup | hR'
    · exact Or.inl hRup
    · by_cases hnow : 1 < oblX6 x 3 ∧ 0 < A20.mustar x
      · rcases w63_closes_star_or_facetCell fs hh hnow.1 hnow.2 with hLex | hFac
        · exact Or.inl (Gen.lexAny_isRupert (mkFac24 fs hh) (EdgeViewLink.inj_of_fac24 (mkFac24 fs hh)) hLex)
        · exact False.elim (hflags.1 hFac)
      · by_cases hnoe : 1 < oblX2 x 3 ∧ 0 < A20.mu23 x
        · rcases e23_closes_star_or_facetCell fs hh hnoe.1 hnoe.2 with hLex | hFac
          · exact Or.inl (Gen.lexAny_isRupert (mkFac24 fs hh) (EdgeViewLink.inj_of_fac24 (mkFac24 fs hh)) hLex)
          · exact False.elim (hflags.1 hFac)
        · rcases hole24R5_reduce (hole24R4_reduce (hole24R3_reduce (hole24R2_reduce (hole24R1_reduce hR')))) with
            hRup | hR6
          · exact Or.inl hRup
          · rcases hole24R6_reduce hR6 with hRup | hR7
            · exact Or.inl hRup
            · exact Or.inr ⟨hh, hflags, Or.inr hR7, hnow, hnoe⟩

end Minimality.T24
