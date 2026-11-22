module

public import Minimality.Type24Hole
public import Minimality.Type24Regions
public import Minimality.Type24ROffTie
public import Minimality.Type24A1Closed
public import Minimality.Type24A2Band
public import Minimality.Type24Wlog

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

/-- Residual piece: the wall `a5 = 1` inside `OB1`. -/
def WallA5Res (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  Hole24R x F ∧ H24K.SAT.OB1 x ∧ Reg.WallA5 x

/-- Residual piece: `BE0416` inside `OB1` (region `B` not yet closed). -/
def BE0416Res (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  Hole24R x F ∧ H24K.SAT.OB1 x ∧ Reg.BE0416 x F

/-- Residual piece: `BRest` inside `OB1` (region `B` not yet closed). -/
def BRestRes (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  Hole24R x F ∧ H24K.SAT.OB1 x ∧ Reg.BRest x F

/-- Residual piece: `CB` / `CC` on the wall `a4 = 1` inside `OB1`. -/
def WallA4CRes (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  Hole24R x F ∧ H24K.SAT.OB1 x ∧ oblX0 x 5 < 1 ∧ F.f 8 (x 5) ≤ F.f 8 (x 0) ∧ oblX0 x 4 = 1

/-- Residual piece: self-twin part of `CC` (`a4 < 1`, `τ ≥ 1`) inside `OB1`. -/
def CCSelfRes (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  Hole24R x F ∧ H24K.SAT.OB1 x ∧ Reg.CC x F ∧ oblX0 x 4 < 1 ∧ F.f 6 (x 4) ≤ F.f 6 (x 0)

/-- Shrunken residual of `Hole24R` after `rOff_closed`, `a1_closed`, `a2_band_closed`, and `pi24` wlog. -/
def Hole24R' (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  OffWallRes x F ∨
  A1Res x F ∨ A2Res x F ∨ WallA5Res x F ∨
  BE0416Res x F ∨ BRestRes x F ∨
  WallA4CRes x F ∨ CCSelfRes x F ∨
  A1Res (x ∘ Sym.pi24) (Sym.sym24 F) ∨
  A2Res (x ∘ Sym.pi24) (Sym.sym24 F) ∨
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
  rcases h with h | h | h | h | h | h | h | h | h | h | h
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

private theorem close_A1 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (hR : Hole24R x F)
    (hO : H24K.SAT.OB1 x) (hA1 : Reg.A1 x F) :
    IsRupert (univ.image x) ∨ A1Res x F := by
  by_cases hS :
      (if 0 < det24 x then A1.A1TieSmall x F else A1.A1TieSmall (fun i => -x i) (A1.facNeg F)) ∧
      (if 0 < det24 x then A1.A1E25Small x F else A1.A1E25Small (fun i => -x i) (A1.facNeg F)) ∧
      A1.A1Z54Sample x F
  · exact Or.inl (A1.a1_closed F hR hA1 hO hS.1 hS.2.1 hS.2.2)
  · exact Or.inr ⟨hR, hO, hA1, hS⟩

private theorem close_A2 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (hR : Hole24R x F)
    (hO : H24K.SAT.OB1 x) (hA2 : Reg.A2 x F) :
    A2Res x F := by
  by_contra hnot
  have hB : A2BandHyp x F := by
    by_contra hnb
    exact hnot ⟨hR, hO, hA2, hnb⟩
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, u3, u8⟩ := hB
  rcases A20.a2_band_closed F hR.1 hA2 hO b1 b2 b3 b4 b5 b6 b7 b8 b9
      f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 u3 u8 with hL | hS
  · exact hR.2.2.2.2.1 hL
  · exact hR.2.2.2.2.2 hS

/-- **Reduction of `Hole24R` to `Hole24R'`**: closes `ROff`, `A1` (modulo its 3 sample bundles),
`A2` (modulo `A2BandHyp`), and transports `BA4`, `CA`, `CA2`, `CFlip` via `pi24`. -/
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
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hR, hO, hWA5⟩))))
    · have hR' := Reg.hole24R_comp_pi24 hR
      have hO' := (A19.ob1_comp_pi24 x).2 hO
      rcases Reg.ba4_to_a hBA4 with hA1' | hA2'
      · rcases close_A1 (Sym.sym24 F) hR' hO' hA1' with hRup | hres
        · exact Or.inl (Sym.isRupert_of_comp_pi24 hRup)
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hres)))))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
          (close_A2 (Sym.sym24 F) hR' hO' hA2')))))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hR, hO, hBE⟩)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hR, hO, hBR⟩))))))
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
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          ⟨hR', hO', Reg.cflip_to_brest (Reg.cb_a4lt_cflip hCB h4)⟩))))))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hR, hO, hCB.1, hCB.2.1, h4⟩)))))))
    · rcases lt_or_eq_of_le hCC.2.2.1 with h4 | h4
      · rcases lt_or_ge (F.f 6 (x 0)) (F.f 6 (x 4)) with ht | ht
        · have hR' := Reg.hole24R_comp_pi24 hR
          have hO' := (A19.ob1_comp_pi24 x).2 hO
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
            ⟨hR', hO', Reg.cflip_to_brest (Reg.cc_tau_cflip hCC h4 ht)⟩))))))))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
            ⟨hR, hO, hCC, h4, ht⟩))))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hR, hO, hCC.1, hCC.2.1, h4⟩)))))))

/-- The single named Type-24 open hole proposition for `Minimality.lean`, with `Hole24R` shrunk to `Hole24R'`. -/
def Hole24 (x : Fin 7 → ℝ³) (fs : Fin 9 → ℝ³ →ᵃ[ℝ] ℝ) (F : S0xFac 9 s0x_S24 x) : Prop :=
  Hole24Flags x fs ∧ (Hole24Q45Special x F ∨ Hole24R' x F)

/-- Main Type-24 reduction leaving `Hole24` (with `Hole24R'`). -/
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
    · exact Or.inr ⟨hh, hflags, Or.inr hR'⟩

end Minimality.T24
