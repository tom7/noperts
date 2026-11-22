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

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21 Minimality.T24.SAT Minimality.T24.NC Minimality.T24.Z0
  Minimality.T24.Adj

namespace Minimality.T24

/-!
# Type 24: Reduction of `Hole24R` to `Hole24R'`

Combines `Reg.hole24R_cases`, `A19.rOff_closed`, `A1.a1_closed`, `A20.a2_band_closed`, and
`Reg.ba4_to_a` / `ca_to_a1` / `ca2_to_a2` / `cflip_to_brest` to shrink `Hole24R` inside
`Hole24` to `Hole24R'`.
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
def Hole24R' (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
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

/-- Every point of `Hole24R'` lies in `Hole24R`. -/
theorem hole24R_of_hole24R' {x : Fin 7 → ℝ³} {F : S0xFac 9 s0x_S24 x}
    (h : Hole24R' x F) : Hole24R x F := by
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

/-- **Reduction of `Hole24R` to `Hole24R'`**: closes `ROff`, `A1` (modulo its 3 sample bundles),
`A2` (modulo `A2BandHyp`), `WallA5`/`WallA4C` (via `pi24`, `ustar_closed_W26_full`, and `a2_band_closed_gen`),
and transports `BA4`, `CA`, `CA2`, `CFlip` via `pi24`. -/
theorem hole24R_reduce {x : Fin 7 → ℝ³} {F : S0xFac 9 s0x_S24 x} (hR : Hole24R x F) :
    IsRupert (univ.image x) ∨ Hole24R' x F := by
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

/-- Further shrunken residual of `Hole24R'` removing generic `{1 < oblX6 x 3, 0 < mustar x}` points
via `A20.w63_closes_mustar_pos`. -/
def Hole24R'' (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  Hole24R' x F ∧
    ¬ (1 < oblX6 x 3 ∧ 0 < A20.mustar x ∧
      ∀ i ∈ ({0, 2, 3, 4, 6} : Finset (Fin 7)), ∀ j ∈ ({0, 2, 3, 4, 6} : Finset (Fin 7)),
        i ≠ j → ⟪x i, x 3 - x 6⟫ ≠ ⟪x j, x 3 - x 6⟫)

/-- Every point of `Hole24R'` reduces to `Hole24R''`. -/
theorem hole24R'_reduce {x : Fin 7 → ℝ³} {F : S0xFac 9 s0x_S24 x}
    (h : Hole24R' x F) : Hole24R'' x F := by
  refine ⟨h, ?_⟩
  rintro ⟨hc3, hmu, hgen⟩
  have hR := hole24R_of_hole24R' h
  exact hR.2.2.2.2.1 (A20.w63_closes_mustar_pos F hR.1 hc3 hmu hgen)

/-- Further shrunken residual of `Hole24R''` removing generic `{c3 = 1}` stratum points satisfying
the four sample inequalities (`hc4`, `hh4_bd`, `hs_B`, `h1234`) via `A20.c3eq1_closed`. -/
def Hole24R''' (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  Hole24R'' x F ∧
    ¬ (oblX6 x 3 = 1 ∧ oblX6 x 4 ≤ 1 ∧
      0 ≤ (oblX6 x 4 - 1) * (omega3 x + 1) + A20.h236 x 4 ∧
      0 ≤ (omega3 x + 1) * (oblX0 x 3 * oblX6 x 4 - oblX0 x 4) + A20.h236 x 4 ∧
      oblX0 x 3 * oblX6 x 4 ≤ oblX0 x 4 ∧
      ∀ i ∈ ({0, 1, 2, 3, 4, 6} : Finset (Fin 7)),
        ∀ j ∈ ({0, 1, 2, 3, 4, 6} : Finset (Fin 7)),
        i ≠ j → ⟪x i, x 3 - x 6⟫ ≠ ⟪x j, x 3 - x 6⟫)

/-- Every point of `Hole24R''` reduces to `Hole24R'''`. -/
theorem hole24R''_reduce {x : Fin 7 → ℝ³} {F : S0xFac 9 s0x_S24 x}
    (h : Hole24R'' x F) : Hole24R''' x F := by
  refine ⟨h, ?_⟩
  rintro ⟨hc3, hc4, hh4_bd, hs_B, h1234, hgen⟩
  have hR := hole24R_of_hole24R' h.1
  exact hR.2.2.2.2.1 (A20.c3eq1_closed F hR.1 hc3 hc4 hh4_bd hs_B h1234 hgen)

/-- Further shrunken residual of `Hole24R'''` removing generic `{1 < oblX2 x 3, 0 < mu23 x}` points
via `A20.e23_closes_mu23_pos`. -/
def Hole24R'''' (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  Hole24R''' x F ∧
    ¬ (1 < oblX2 x 3 ∧ 0 < A20.mu23 x ∧
      ∀ i ∈ ({0, 2, 3, 5, 6} : Finset (Fin 7)),
        ∀ j ∈ ({0, 2, 3, 5, 6} : Finset (Fin 7)),
        i ≠ j → ⟪x i, x 3 - x 2⟫ ≠ ⟪x j, x 3 - x 2⟫)

/-- Every point of `Hole24R'''` reduces to `Hole24R''''`. -/
theorem hole24R'''_reduce {x : Fin 7 → ℝ³} {F : S0xFac 9 s0x_S24 x}
    (h : Hole24R''' x F) : Hole24R'''' x F := by
  refine ⟨h, ?_⟩
  rintro ⟨hb3, hmu, hgen⟩
  have hR := hole24R_of_hole24R' h.1.1
  exact hR.2.2.2.2.1 (A20.e23_closes_mu23_pos F hR.1 hb3 hmu hgen)

/-- Further shrunken residual of `Hole24R''''` removing generic wall points
`{1 < oblX6 x 3, mustar x = 0}` via `A20.w63_closes_wall` and
`{1 < oblX2 x 3, mu23 x = 0}` via `A20.e23_closes_wall`. -/
def Hole24R5 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  Hole24R'''' x F ∧
    ¬ (1 < oblX6 x 3 ∧ A20.mustar x = 0 ∧
      ∀ i ∈ ({0, 2, 3, 4, 5, 6} : Finset (Fin 7)),
        ∀ j ∈ ({0, 2, 3, 4, 5, 6} : Finset (Fin 7)),
        i ≠ j → ⟪x i, x 3 - x 6⟫ ≠ ⟪x j, x 3 - x 6⟫) ∧
    ¬ (1 < oblX2 x 3 ∧ A20.mu23 x = 0 ∧
      ∀ i ∈ ({0, 2, 3, 4, 5, 6} : Finset (Fin 7)),
        ∀ j ∈ ({0, 2, 3, 4, 5, 6} : Finset (Fin 7)),
        i ≠ j → ⟪x i, x 3 - x 2⟫ ≠ ⟪x j, x 3 - x 2⟫)

/-- Every point of `Hole24R''''` reduces to `Hole24R5`. -/
theorem hole24R4_reduce {x : Fin 7 → ℝ³} {F : S0xFac 9 s0x_S24 x}
    (h : Hole24R'''' x F) : Hole24R5 x F := by
  refine ⟨h, ?_, ?_⟩
  · rintro ⟨hc3, hmu, hgen⟩
    have hR := hole24R_of_hole24R' h.1.1.1
    exact hR.2.2.2.2.1 (A20.w63_closes_wall F hR.1 hc3 hmu hgen)
  · rintro ⟨hb3, hmu, hgen⟩
    have hR := hole24R_of_hole24R' h.1.1.1
    exact hR.2.2.2.2.1 (A20.e23_closes_wall F hR.1 hb3 hmu hgen)

/-- On `{1 < oblX2 x 3, 1 < oblX6 x 3, be ≤ 1, al ≤ 1}` (where `al, be` are the `par2546_quad`
coefficients `s = be, t = al` in `x 3 - x 0 = al • (x 5 - x 0) + be • (x 4 - x 0)`), any point of
`Hole24 x fs (mkFac24 fs hh)` (with `Hole24R5`) off `Hole24Q45Special` lies in the `w63` or `E23`
tie locus on `{0, 2, 3, 4, 5, 6}`.
Uses `Hole24Flags.1 : ¬ FacetCell24 fs`, `Hole24R''''`, `Hole24R'''`, and `Hole24R5`. -/
theorem hole24_b3_c3_st_le_ties {x : Fin 7 → ℝ³} {fs : Fin 9 → ℝ³ →ᵃ[ℝ] ℝ}
    (hh : ∀ t i, (i ∈ s0x_S24 t → fs t (x i) = 0) ∧ (i ∉ s0x_S24 t → fs t (x i) < 0))
    (hH : Hole24Flags x fs ∧ (Hole24Q45Special x (mkFac24 fs hh) ∨ Hole24R5 x (mkFac24 fs hh)))
    (hb3 : 1 < oblX2 x 3) (hc3 : 1 < oblX6 x 3)
    {al be : ℝ} (halp : 0 < al) (hbep : 0 < be)
    (hq : x 3 - x 0 = al • (x 5 - x 0) + be • (x 4 - x 0))
    (hbe : be ≤ 1) (hal : al ≤ 1)
    (hnotQ : ¬ Hole24Q45Special x (mkFac24 fs hh)) :
    (∃ i ∈ ({0, 2, 3, 4, 5, 6} : Finset (Fin 7)), ∃ j ∈ ({0, 2, 3, 4, 5, 6} : Finset (Fin 7)),
      i ≠ j ∧ ⟪x i, x 3 - x 6⟫ = ⟪x j, x 3 - x 6⟫) ∨
    (∃ i ∈ ({0, 2, 3, 4, 5, 6} : Finset (Fin 7)), ∃ j ∈ ({0, 2, 3, 4, 5, 6} : Finset (Fin 7)),
      i ≠ j ∧ ⟪x i, x 3 - x 2⟫ = ⟪x j, x 3 - x 2⟫) := by
  rcases hH with ⟨hflags, hQ | hR5⟩
  · exact absurd hQ hnotQ
  · rcases A20.mustar_or_mu23_nonneg fs hh hflags.1 halp hbep hq hbe hal with hmu | hmu23
    · left
      by_contra hno
      push Not at hno
      rcases eq_or_lt_of_le hmu with hzero | hpos
      · exact hR5.2.1 ⟨hc3, hzero.symm, hno⟩
      · exact hR5.1.1.1.2 ⟨hc3, hpos, fun i hi j hj hij =>
          hno i (by fin_cases i <;> simp at hi ⊢) j (by fin_cases j <;> simp at hj ⊢) hij⟩
    · right
      by_contra hno
      push Not at hno
      rcases eq_or_lt_of_le hmu23 with hzero | hpos
      · exact hR5.2.2 ⟨hb3, hzero.symm, hno⟩
      · exact hR5.1.2 ⟨hb3, hpos, fun i hi j hj hij =>
          hno i (by fin_cases i <;> simp at hi ⊢) j (by fin_cases j <;> simp at hj ⊢) hij⟩

/-- On `{1 < oblX2 x 3, 1 < oblX6 x 3, be < 1, al < 1}` (where `al, be` are the `par2546_quad`
coefficients `s = be, t = al` in `x 3 - x 0 = al • (x 5 - x 0) + be • (x 4 - x 0)`), any point of
`Hole24 x fs (mkFac24 fs hh)` off `Hole24Q45Special` lies in the `w63` or `E23` tie locus.
Uses `Hole24Flags.1 : ¬ FacetCell24 fs`, `Hole24R''''.2 : ¬(1 < b3 ∧ 0 < mu23 ∧ hgen_E23)`,
and `Hole24R'''.1.2 : ¬(1 < c3 ∧ 0 < mustar ∧ hgen_w63)`. -/
theorem hole24_b3_c3_st_lt_ties {x : Fin 7 → ℝ³} {fs : Fin 9 → ℝ³ →ᵃ[ℝ] ℝ}
    (hh : ∀ t i, (i ∈ s0x_S24 t → fs t (x i) = 0) ∧ (i ∉ s0x_S24 t → fs t (x i) < 0))
    (hH : Hole24Flags x fs ∧ (Hole24Q45Special x (mkFac24 fs hh) ∨ Hole24R5 x (mkFac24 fs hh)))
    (hb3 : 1 < oblX2 x 3) (hc3 : 1 < oblX6 x 3)
    {al be : ℝ} (halp : 0 < al) (hbep : 0 < be)
    (hq : x 3 - x 0 = al • (x 5 - x 0) + be • (x 4 - x 0))
    (hbe : be < 1) (hal : al < 1)
    (hnotQ : ¬ Hole24Q45Special x (mkFac24 fs hh)) :
    (∃ i ∈ ({0, 2, 3, 4, 6} : Finset (Fin 7)), ∃ j ∈ ({0, 2, 3, 4, 6} : Finset (Fin 7)),
      i ≠ j ∧ ⟪x i, x 3 - x 6⟫ = ⟪x j, x 3 - x 6⟫) ∨
    (∃ i ∈ ({0, 2, 3, 5, 6} : Finset (Fin 7)), ∃ j ∈ ({0, 2, 3, 5, 6} : Finset (Fin 7)),
      i ≠ j ∧ ⟪x i, x 3 - x 2⟫ = ⟪x j, x 3 - x 2⟫) := by
  rcases hH with ⟨hflags, hQ | hR5⟩
  · exact absurd hQ hnotQ
  · rcases A20.mustar_or_mu23_pos fs hh hflags.1 halp hbep hq hbe hal with hmu | hmu23
    · left
      by_contra hno
      push Not at hno
      exact hR5.1.1.1.2 ⟨hc3, hmu, hno⟩
    · right
      by_contra hno
      push Not at hno
      exact hR5.1.2 ⟨hb3, hmu23, hno⟩

/-- The single named Type-24 open hole proposition for `Minimality.lean`, with `Hole24R` shrunk to `Hole24R5`. -/
def Hole24 (x : Fin 7 → ℝ³) (fs : Fin 9 → ℝ³ →ᵃ[ℝ] ℝ) (F : S0xFac 9 s0x_S24 x) : Prop :=
  Hole24Flags x fs ∧ (Hole24Q45Special x F ∨ Hole24R5 x F)

/-- Main Type-24 reduction leaving `Hole24` (with `Hole24R5`). -/
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
  rcases type24_rupert_or_holeR fA fB fC fD fE fF fG fH fI hA hB hC hD hE hF hG hH hI with
    hRup | ⟨hh, hflags, hQ | hR⟩
  · exact Or.inl hRup
  · exact Or.inr ⟨hh, hflags, Or.inl hQ⟩
  · rcases hole24R_reduce hR with hRup | hR'
    · exact Or.inl hRup
    · exact Or.inr ⟨hh, hflags, Or.inr (hole24R4_reduce (hole24R'''_reduce (hole24R''_reduce (hole24R'_reduce hR'))))⟩

end Minimality.T24
